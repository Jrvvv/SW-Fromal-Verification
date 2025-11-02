#ifndef DPLL_SOLVER_H
#define DPLL_SOLVER_H

#include <string>

// Forward declaration for callback functions
struct CNFData;

class DPLLSolver {
public:
    DPLLSolver();
    ~DPLLSolver();

    // Основной метод решения
    bool solve(const std::string& filename);

private:
    CNFData* cnf;

    // Вспомогательные методы
    bool load_cnf(const std::string& filename);
    bool dpll_algorithm();
    bool unit_propagation();
    int find_unit_clause() const;
    int find_pure_literal() const;
    void assign_literal(int literal, bool value);
    void unassign_literal(int literal);
    bool has_empty_clause() const;
    bool all_clauses_satisfied() const;
    int choose_branching_variable() const;
    void simplify();
};

// Функция для использования в main
bool solve_sat_problem(const std::string& filename);

// Callback functions for DIMACS parser
void dimacs_header_callback(void* udata, int num_vars, int num_clauses);
void dimacs_clause_callback(void* udata, int clause_idx, int* literals, int size);

#endif