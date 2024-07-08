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
        const uint64_t a = (uint64_t)as_int(std::get<0>(key)) <<  0;
        const uint64_t b = (uint64_t)as_int(std::get<1>(key)) << 32;
        
        return a ^ b;
    }
};

template<>
struct std::hash<ternary_key_t>
{
    inline uint64_t scramble(uint32_t x) const noexcept __attribute__((always_inline)) 
    { 
        return (x & 0x00ffffff) ^ ((x & 0xff000000) >> 8); // compress down to 24-bit
    }
    uint64_t operator()(const ternary_key_t& key) const noexcept
    {
        const uint64_t a = scramble(as_int(std::get<0>(key))) << 0;
        const uint64_t b = scramble(as_int(std::get<1>(key))) << 20;
        const uint64_t c = scramble(as_int(std::get<2>(key))) << 40;
        return a ^ b ^ c;
    }
};

#endif //CXXSAT_KEYS_H
