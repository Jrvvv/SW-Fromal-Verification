# Обновленный CMakeLists.txt
cmake_minimum_required(VERSION 3.12)
project(dpll_solver C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Compiler flags as specified in the requirements
set(CMAKE_CXX_FLAGS "-Wpedantic -Werror -O2")
set(CMAKE_C_FLAGS "-Wpedantic -Werror -O2")

# Для работы с filesystem в C++17
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -lstdc++fs")

# Find GoogleTest
find_package(GTest REQUIRED)

# Include directories
include_directories(inc third_parties/dpll_dimacs)

# Add the DIMACS parser as C library
add_library(dimacs third_parties/dpll_dimacs/dimacs.c)
set_target_properties(dimacs PROPERTIES LINKER_LANGUAGE C)

# Main DPLL solver library
add_library(dpll_solver STATIC 
    src/dpll_solver.cpp
)
target_link_libraries(dpll_solver dimacs)

# Main DPLL executable
add_executable(dpll src/dpll.cpp)
target_link_libraries(dpll dpll_solver)

# Test executable
add_executable(dpll_test test/dpll_test.cpp)
target_link_libraries(dpll_test 
    GTest::gtest_main
    dpll_solver
    dimacs
)

# Installation
install(TARGETS dpll DESTINATION bin)