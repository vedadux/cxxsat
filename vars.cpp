#include "vars.h"
#include "Solver.h"

using var_t = cxxsat::var_t;

var_t cxxsat::operator&(var_t x, var_t y) { return cxxsat::solver->make_and(x, y); }
var_t cxxsat::operator|(var_t x, var_t y) { return cxxsat::solver->make_or(x, y); }
var_t cxxsat::operator^(var_t x, var_t y) { return cxxsat::solver->make_xor(x, y); }

var_t cxxsat::mux(var_t s, var_t t, var_t e) { return cxxsat::solver->make_mux(s, t, e); }
