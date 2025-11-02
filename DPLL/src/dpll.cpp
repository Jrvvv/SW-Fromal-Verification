#include "dpll_solver.h"
#include <iostream>

int main(int argc, char* argv[]) {
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <cnf_file>" << std::endl;
        return 1;
    }

    try {
        bool is_sat = solve_sat_problem(argv[1]);
        std::cout << (is_sat ? "SAT" : "UNSAT") << std::endl;
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
}