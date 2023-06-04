#ifndef CXXSAT_KEYS_H
#define CXXSAT_KEYS_H

#include "vars.h"
#include <functional>

using cxxsat::var_t;
using binary_key_t = std::array<var_t, 2>;
using ternary_key_t = std::array<var_t, 3>;

template<>
struct std::hash<binary_key_t>
{
    uint64_t operator()(const binary_key_t& key) const noexcept
    {
        return ((uint64_t) as_int(std::get<1>(key)) << 32) | (uint64_t) as_int(std::get<0>(key));
    }
};

template<>
struct std::hash<ternary_key_t>
{
    uint64_t operator()(const ternary_key_t& key) const noexcept
    {
        return std::_Hash_impl::hash(key.data(), key.size() * sizeof(var_t));
    }
};

#endif //CXXSAT_KEYS_H
