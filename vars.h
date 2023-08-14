#ifndef CXXSAT_VARS_H
#define CXXSAT_VARS_H

#include "debug.h"
#include <cstdint>

namespace cxxsat {

enum class var_t : int32_t {ILLEGAL = 0, ZERO = -INT32_MAX, ONE  = +INT32_MAX};

inline int32_t as_int(var_t const x) { return static_cast<int32_t>(x); }
inline var_t   as_var(int const x)   { return static_cast<var_t>(x); }

inline var_t operator-(var_t x) { return as_var(-as_int(x)); }
inline var_t operator+(var_t x) { return x; }

var_t operator&(var_t x, var_t y);
var_t operator|(var_t x, var_t y);
var_t operator^(var_t x, var_t y);

var_t mux(var_t s, var_t t, var_t e);

inline bool is_negated(var_t x) { return as_int(x) < 0; }
inline var_t abs_var_t(var_t x) { return is_negated(x) ? -x : +x; }

inline bool is_legal(var_t x) { return (-x != x); }

} // namespace cxxsat

#endif //CXXSAT_VARS_H
