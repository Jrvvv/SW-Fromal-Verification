#include "dpll_solver.h"
#include "dimacs.h"
#include <vector>
#include <memory>
#include <stack>
#include <iostream>
#include <algorithm>
#include <cmath>
#include <cstring>

struct CNFData {
    int num_vars;
    int num_clauses;
    std::vector<std::vector<int>> clauses;
    std::vector<int> assignment; // 0 - unassigned, 1 - true, -1 - false
    std::vector<bool> clause_satisfied;
    
    CNFData() : num_vars(0), num_clauses(0) {}
};

// Callback functions for DIMACS parser
void dimacs_header_callback(void* udata, int num_vars, int num_clauses) {
    CNFData* cnf = static_cast<CNFData*>(udata);
    cnf->num_vars = num_vars;
    cnf->num_clauses = num_clauses;
    cnf->clauses.reserve(num_clauses);
    cnf->assignment.resize(num_vars + 1, 0); // variables indexed from 1
    cnf->clause_satisfied.resize(num_clauses, false);
}

void dimacs_clause_callback(void* udata, int clause_idx, int* literals, int size) {
    CNFData* cnf = static_cast<CNFData*>(udata);
    std::vector<int> clause;
    for (int i = 0; i < size; i++) {
        clause.push_back(literals[i]);
    }
    cnf->clauses.push_back(clause);
}

DPLLSolver::DPLLSolver() : cnf(nullptr) {}

DPLLSolver::~DPLLSolver() {
    delete cnf;
}

bool DPLLSolver::solve(const std::string& filename) {
    if (!load_cnf(filename)) {
        return false;
    }
    return dpll_algorithm();
}

bool DPLLSolver::load_cnf(const std::string& filename) {
    delete cnf;
    cnf = new CNFData();
    
    FILE* file = fopen(filename.c_str(), "r");
    if (!file) {
        std::cerr << "Cannot open file: " << filename << std::endl;
        return false;
    }
    
    int result = dimacs_fread(file, cnf, dimacs_header_callback, dimacs_clause_callback);
    fclose(file);
    
    if (result != 0) {
        std::cerr << "Error parsing DIMACS file at line: " << result << std::endl;
        return false;
    }
    
    return true;
}

bool DPLLSolver::dpll_algorithm() {
    if (!cnf || cnf->clauses.empty()) {
        return true; // empty formula is always satisfiable
    }
    
    // Используем стек для эмуляции рекурсии
    std::stack<CNFData*> stack;
    
    // Создаем копию начального состояния
    CNFData* initial_state = new CNFData();
    *initial_state = *cnf;
    stack.push(initial_state);
    
    bool result = false;
    
    while (!stack.empty()) {
        CNFData* current = stack.top();
        stack.pop();
        
        // Временно заменяем текущее состояние
        std::swap(cnf, current);
        
        // Упрощение формулы
        simplify();
        
        // Проверка условий завершения
        if (has_empty_clause()) {
            delete current;
            continue; // конфликт - переходим к следующей ветви
        }
        
        if (all_clauses_satisfied()) {
            result = true;
            delete current;
            break; // нашли решение
        }
        
        // Распространение единицы
        while (unit_propagation()) {
            if (has_empty_clause()) {
                break; // конфликт после распространения
            }
        }
        
        if (has_empty_clause()) {
            delete current;
            continue; // конфликт - переходим к следующей ветви
        }
        
        if (all_clauses_satisfied()) {
            result = true;
            delete current;
            break; // нашли решение
        }
        
        // Выбор переменной для ветвления
        int var = choose_branching_variable();
        if (var == 0) {
            delete current;
            continue; // не нашли переменную для ветвления
        }
        
        // Ветвление: пробуем true
        CNFData* true_branch = new CNFData();
        *true_branch = *cnf;
        true_branch->assignment[var] = 1;
        stack.push(true_branch);
        
        // Ветвление: пробуем false  
        CNFData* false_branch = new CNFData();
        *false_branch = *cnf;
        false_branch->assignment[var] = -1;
        stack.push(false_branch);
        
        // Восстанавливаем оригинальное состояние
        std::swap(cnf, current);
        delete current;
    }
    
    // Очищаем оставшиеся состояния в стеке
    while (!stack.empty()) {
        delete stack.top();
        stack.pop();
    }
    
    return result;
}

bool DPLLSolver::unit_propagation() {
    int unit_literal = find_unit_clause();
    if (unit_literal == 0) {
        return false;
    }
    
    bool value = (unit_literal > 0);
    assign_literal(unit_literal, value);
    return true;
}

int DPLLSolver::find_unit_clause() const {
    for (size_t i = 0; i < cnf->clauses.size(); i++) {
        if (cnf->clause_satisfied[i]) {
            continue;
        }
        
        int unassigned_count = 0;
        int unit_literal = 0;
        bool clause_satisfied = false;
        
        for (int literal : cnf->clauses[i]) {
            int var = std::abs(literal);
            if (cnf->assignment[var] == 0) {
                unassigned_count++;
                unit_literal = literal;
            } else if ((cnf->assignment[var] == 1 && literal > 0) || 
                      (cnf->assignment[var] == -1 && literal < 0)) {
                // Клауза уже удовлетворена
                clause_satisfied = true;
                break;
            }
        }
        
        if (!clause_satisfied && unassigned_count == 1) {
            return unit_literal;
        }
    }
    return 0;
}

void DPLLSolver::assign_literal(int literal, bool value) {
    int var = std::abs(literal);
    cnf->assignment[var] = value ? 1 : -1;
    
    // Обновляем статус клауз
    for (size_t i = 0; i < cnf->clauses.size(); i++) {
        if (cnf->clause_satisfied[i]) {
            continue;
        }
        
        for (int lit : cnf->clauses[i]) {
            int v = std::abs(lit);
            if (v == var) {
                if ((cnf->assignment[var] == 1 && lit > 0) || 
                    (cnf->assignment[var] == -1 && lit < 0)) {
                    cnf->clause_satisfied[i] = true;
                    break;
                }
            }
        }
    }
}

bool DPLLSolver::has_empty_clause() const {
    for (size_t i = 0; i < cnf->clauses.size(); i++) {
        if (cnf->clause_satisfied[i]) {
            continue;
        }
        
        bool all_false = true;
        for (int literal : cnf->clauses[i]) {
            int var = std::abs(literal);
            if (cnf->assignment[var] == 0) {
                all_false = false;
                break;
            }
            if ((cnf->assignment[var] == 1 && literal > 0) || 
                (cnf->assignment[var] == -1 && literal < 0)) {
                all_false = false;
                break;
            }
        }
        
        if (all_false) {
            return true;
        }
    }
    return false;
}

bool DPLLSolver::all_clauses_satisfied() const {
    for (bool satisfied : cnf->clause_satisfied) {
        if (!satisfied) {
            return false;
        }
    }
    return true;
}

int DPLLSolver::choose_branching_variable() const {
    // Простая эвристика: выбираем первую не назначенную переменную
    for (int i = 1; i <= cnf->num_vars; i++) {
        if (cnf->assignment[i] == 0) {
            return i;
        }
    }
    return 0;
}

void DPLLSolver::simplify() {
    // Удаление тавтологий
    for (size_t i = 0; i < cnf->clauses.size(); i++) {
        if (cnf->clause_satisfied[i]) {
            continue;
        }
        
        // Проверка на тавтологию
        bool is_tautology = false;
        for (size_t j = 0; j < cnf->clauses[i].size(); j++) {
            for (size_t k = j + 1; k < cnf->clauses[i].size(); k++) {
                if (cnf->clauses[i][j] == -cnf->clauses[i][k]) {
                    is_tautology = true;
                    break;
                }
            }
            if (is_tautology) break;
        }
        
        if (is_tautology) {
            cnf->clause_satisfied[i] = true;
        }
    }
    
    // Поиск чистых литералов
    int pure_literal = find_pure_literal();
    while (pure_literal != 0) {
        assign_literal(pure_literal, pure_literal > 0);
        pure_literal = find_pure_literal();
    }
}

int DPLLSolver::find_pure_literal() const {
    std::vector<int> literal_polarity(cnf->num_vars + 1, 0); // 0 - не встречался, 1 - только положительный, -1 - только отрицательный, 2 - оба
    
    for (size_t i = 0; i < cnf->clauses.size(); i++) {
        if (cnf->clause_satisfied[i]) {
            continue;
        }
        
        for (int literal : cnf->clauses[i]) {
            int var = std::abs(literal);
            if (cnf->assignment[var] != 0) {
                continue; // переменная уже назначена
            }
            
            if (literal > 0) {
                if (literal_polarity[var] == -1) {
                    literal_polarity[var] = 2; // встречался и положительный и отрицательный
                } else if (literal_polarity[var] == 0) {
                    literal_polarity[var] = 1; // только положительный
                }
            } else {
                if (literal_polarity[var] == 1) {
                    literal_polarity[var] = 2; // встречался и положительный и отрицательный
                } else if (literal_polarity[var] == 0) {
                    literal_polarity[var] = -1; // только отрицательный
                }
            }
        }
    }
    
    // Ищем чистый литерал
    for (int i = 1; i <= cnf->num_vars; i++) {
        if (cnf->assignment[i] == 0 && (literal_polarity[i] == 1 || literal_polarity[i] == -1)) {
            return literal_polarity[i] == 1 ? i : -i;
        }
    }
    
    return 0;
}

void DPLLSolver::unassign_literal(int literal) {
    int var = std::abs(literal);
    cnf->assignment[var] = 0;
    
    // Пересчитываем статус клауз
    for (size_t i = 0; i < cnf->clauses.size(); i++) {
        cnf->clause_satisfied[i] = false;
        for (int lit : cnf->clauses[i]) {
            int v = std::abs(lit);
            if (cnf->assignment[v] != 0) {
                if ((cnf->assignment[v] == 1 && lit > 0) || 
                    (cnf->assignment[v] == -1 && lit < 0)) {
                    cnf->clause_satisfied[i] = true;
                    break;
                }
            }
        }
    }
}

bool solve_sat_problem(const std::string& filename) {
    DPLLSolver solver;
    return solver.solve(filename);
}