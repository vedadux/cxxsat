#include "vars.h"
#include "Solver.h"

using cxxsat::var_t;

var_t operator&(var_t x, var_t y) { return cxxsat::solver->make_and(x, y); }
var_t operator|(var_t x, var_t y) { return cxxsat::solver->make_or(x, y); }
var_t operator^(var_t x, var_t y) { return cxxsat::solver->make_xor(x, y); }

var_t mux(var_t s, var_t t, var_t e) { return cxxsat::solver->make_mux(s, t, e); }
