// test/dpll_test.cpp
#include "dpll_solver.h"
#include <gtest/gtest.h>
#include <filesystem>
#include <chrono>
#include <fstream>
#include <vector>

namespace fs = std::filesystem;

class DPLLTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Проверяем существование тестовых директорий
        test_cases_path_ = fs::path(TEST_CASES_BASE);
        if (!fs::exists(test_cases_path_)) {
            test_cases_path_ = fs::path("..") / TEST_CASES_BASE;
        }
    }

    bool solveWithTimeout(const std::string& filename, int timeout_ms) {
        auto start = std::chrono::steady_clock::now();
        bool result = solve_sat_problem(filename.c_str());
        auto end = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
        
        EXPECT_LE(duration.count(), timeout_ms) 
            << "Timeout exceeded for file: " << filename 
            << " Time: " << duration.count() << "ms";
        
        return result;
    }

    void testProblemSet(const std::string& relative_path, int total_timeout_ms) {
        auto test_dir = test_cases_path_ / relative_path;
        if (!fs::exists(test_dir)) {
            GTEST_SKIP() << "Test directory not found: " << test_dir;
        }

        auto start_total = std::chrono::steady_clock::now();
        int solved_count = 0;
        int total_count = 0;

        for (const auto& entry : fs::recursive_directory_iterator(test_dir)) {
            if (entry.is_regular_file() && entry.path().extension() == ".cnf") {
                total_count++;
                std::string filename = entry.path().string();
                
                try {
                    auto test_start = std::chrono::steady_clock::now();
                    bool result = solve_sat_problem(filename.c_str());
                    auto test_end = std::chrono::steady_clock::now();
                    auto test_duration = std::chrono::duration_cast<std::chrono::milliseconds>(test_end - test_start);
                    
                    // Проверяем, что решение найдено за разумное время (индивидуальный таймаут 60 секунд)
                    EXPECT_LE(test_duration.count(), 60000) 
                        << "Individual test timeout for: " << filename;
                    
                    solved_count++;
                    
                    // Логируем результат
                    std::cout << "Solved: " << filename << " - " << (result ? "SAT" : "UNSAT") 
                              << " in " << test_duration.count() << "ms" << std::endl;
                    
                } catch (const std::exception& e) {
                    ADD_FAILURE() << "Exception solving " << filename << ": " << e.what();
                }
                
                // Проверяем общее время
                auto current_total = std::chrono::steady_clock::now();
                auto total_duration = std::chrono::duration_cast<std::chrono::milliseconds>(current_total - start_total);
                ASSERT_LE(total_duration.count(), total_timeout_ms) 
                    << "Total timeout exceeded after solving " << solved_count << "/" << total_count 
                    << " files. Time: " << total_duration.count() << "ms";
            }
        }
        
        auto end_total = std::chrono::steady_clock::now();
        auto total_duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_total - start_total);
        
        std::cout << "Solved " << solved_count << "/" << total_count 
                  << " problems in " << total_duration.count() << "ms" << std::endl;
        
        EXPECT_EQ(solved_count, total_count) << "Not all problems were solved";
        EXPECT_LE(total_duration.count(), total_timeout_ms) 
            << "Total timeout exceeded. Time: " << total_duration.count() << "ms";
    }

    fs::path test_cases_path_;
    
    static constexpr const char* TEST_CASES_BASE = "test/test_cases";
};

// Тест для hanoi4 - проверка времени и памяти
// TEST_F(DPLLTest, Hanoi4_Performance) {
//     auto hanoi_file = test_cases_path_ / "hanoi/hanoi4.cnf";
//     if (!fs::exists(hanoi_file)) {
//         GTEST_SKIP() << "Hanoi4 test file not found: " << hanoi_file;
//     }

//     // Измеряем время выполнения
//     auto start = std::chrono::steady_clock::now();
//     bool result = solve_sat_problem(hanoi_file.string().c_str());
//     auto end = std::chrono::steady_clock::now();
//     auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    
//     std::cout << "Hanoi4 solved in " << duration.count() << "ms" << std::endl;
    
//     // Проверяем время выполнения (≤ 20 секунд)
//     EXPECT_LE(duration.count(), 20000) << "Hanoi4 timeout exceeded";
    
//     // Проверяем, что решение корректное (hanoi4 должен быть SAT)
//     EXPECT_TRUE(result) << "Hanoi4 should be SAT";
// }

// Тест для набора UF150-645 (общее время ≤ 800 секунд)
TEST_F(DPLLTest, UF150_645_Performance) {
    testProblemSet("uf150-645/UF150.645.100", 800000); // 800 секунд в миллисекундах
}

// Тест для набора UUF150-645 (общее время ≤ 2000 секунд)  
TEST_F(DPLLTest, UUF150_645_Performance) {
    testProblemSet("uuf150-645/UUF150.645.100", 2000000); // 2000 секунд в миллисекундах
}

// Базовые тесты на корректность
TEST_F(DPLLTest, BasicSAT) {
    // Создаем простую выполнимую формулу: (x1 ∨ x2) ∧ (¬x1 ∨ x2)
    const char* temp_cnf = "temp_sat.cnf";
    std::ofstream file(temp_cnf);
    file << "p cnf 2 2\n";
    file << "1 2 0\n";
    file << "-1 2 0\n";
    file.close();
    
    bool result = solve_sat_problem(temp_cnf);
    EXPECT_TRUE(result);
    
    fs::remove(temp_cnf);
}

TEST_F(DPLLTest, BasicUNSAT) {
    // Создаем невыполнимую формулу: (x1) ∧ (¬x1)
    const char* temp_cnf = "temp_unsat.cnf";
    std::ofstream file(temp_cnf);
    file << "p cnf 1 2\n";
    file << "1 0\n";
    file << "-1 0\n";
    file.close();
    
    bool result = solve_sat_problem(temp_cnf);
    EXPECT_FALSE(result);
    
    fs::remove(temp_cnf);
}

// Тест на обработку пустого файла
TEST_F(DPLLTest, EmptyFormula) {
    const char* temp_cnf = "temp_empty.cnf";
    std::ofstream file(temp_cnf);
    file << "p cnf 0 0\n";
    file.close();
    
    bool result = solve_sat_problem(temp_cnf);
    EXPECT_TRUE(result); // Пустая формула выполнима
    
    fs::remove(temp_cnf);
}

// Тест на обработку файла с одной пустой клаузой
TEST_F(DPLLTest, EmptyClause) {
    const char* temp_cnf = "temp_empty_clause.cnf";
    std::ofstream file(temp_cnf);
    file << "p cnf 0 1\n";
    file << "0\n"; // Пустая клауза
    file.close();
    
    bool result = solve_sat_problem(temp_cnf);
    EXPECT_FALSE(result); // Формула с пустой клаузой невыполнима
    
    fs::remove(temp_cnf);
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}