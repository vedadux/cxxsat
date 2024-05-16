#ifndef CXXSAT_VARS_H
#define CXXSAT_VARS_H

#include "debug.h"
#include <cstdint>

namespace cxxsat {

enum class var_t : int32_t {ILLEGAL = 0, ZERO = -INT32_MAX, ONE  = +INT32_MAX};

inline constexpr int32_t as_int(var_t const x) { return static_cast<int32_t>(x); }
inline constexpr var_t   as_var(int const x)   { return static_cast<var_t>(x); }

inline constexpr var_t from_bool(bool val) {return val ? var_t::ONE : var_t::ZERO; }
inline constexpr var_t operator-(var_t x) { return as_var(-as_int(x)); }
inline constexpr var_t operator!(var_t x) { return -x; }
inline constexpr var_t operator+(var_t x) { return x; }


var_t operator&(var_t x, var_t y);
var_t operator|(var_t x, var_t y);
var_t operator^(var_t x, var_t y);

var_t mux(var_t s, var_t t, var_t e);

inline constexpr bool is_negated(var_t x) { return as_int(x) < 0; }
inline constexpr var_t abs_var_t(var_t x) { return is_negated(x) ? -x : +x; }

inline constexpr bool is_legal(var_t x) { return (-x != x); }
inline constexpr bool is_const(var_t x) { return x == var_t::ONE || x == var_t::ZERO; }
} // namespace cxxsat

#endif //CXXSAT_VARS_H
