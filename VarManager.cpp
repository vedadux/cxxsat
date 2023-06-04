#include <cassert>
#include "VarManager.h"

using cxxsat::VarManager;
using cxxsat::var_t;

VarManager::VarManager() : m_num_vars(0), hits(0) { }

///////////////////////////////// AND /////////////////////////////////

var_t VarManager::lookup_and(var_t a, var_t b)
{
    Assert(is_legal(a), ILLEGAL_LITERAL);
    Assert(is_legal(b), ILLEGAL_LITERAL);
    Assert(is_known(a), UNKNOWN_LITERAL);
    Assert(is_known(b), UNKNOWN_LITERAL);

    const binary_key_t key = {a < b ? a : b, a < b ? b : a};
    auto res = m_and_cache.find(key);
    if (res != m_and_cache.end()) return res->second;
    else                          return var_t::ILLEGAL;
}

var_t VarManager::simplify_and(var_t a, var_t b)
{
    Assert(is_legal(a), ILLEGAL_LITERAL);
    Assert(is_legal(b), ILLEGAL_LITERAL);
    Assert(is_known(a), UNKNOWN_LITERAL);
    Assert(is_known(b), UNKNOWN_LITERAL);

    // Standard rules for and with constant
    if (a == var_t::ZERO || b == var_t::ZERO) return var_t::ZERO;
    if (a == var_t::ONE) return b;
    if (b == var_t::ONE) return a;
    // Simplification rules for and
    if (a == b) return a;
    if (a == -b) return var_t::ZERO;

    // See if we already have a variable for this
    return lookup_and(a, b);
}

void VarManager::register_and(var_t a, var_t b, var_t c)
{
    Assert(is_legal(a), ILLEGAL_LITERAL);
    Assert(is_legal(b), ILLEGAL_LITERAL);
    Assert(is_legal(c), ILLEGAL_LITERAL);

    Assert(is_known(a), UNKNOWN_LITERAL);
    Assert(is_known(b), UNKNOWN_LITERAL);
    Assert(is_known(c), UNKNOWN_LITERAL);

    const binary_key_t key = {a < b ? a : b, a < b ? b : a};
    m_and_cache.emplace(key, c);
}

///////////////////////////////// OR /////////////////////////////////

var_t VarManager::lookup_or(var_t a, var_t b)
{
    return -lookup_and(-a, -b);
}

var_t VarManager::simplify_or(var_t a, var_t b)
{
    return -simplify_and(-a, -b);
}

void VarManager::register_or(var_t a, var_t b, var_t c)
{
    return register_and(-a, -b, -c);
}

///////////////////////////////// XOR /////////////////////////////////

var_t VarManager::lookup_xor(var_t a, var_t b)
{
    Assert(is_legal(a), ILLEGAL_LITERAL);
    Assert(is_legal(b), ILLEGAL_LITERAL);
    Assert(is_known(a), UNKNOWN_LITERAL);
    Assert(is_known(b), UNKNOWN_LITERAL);

    bool neg = is_negated(a) ^ is_negated(b);
    a = abs_var_t(a), b = abs_var_t(b);
    const binary_key_t key = {a < b ? a : b, a < b ? b : a};
    auto res = m_xor_cache.find(key);
    if (res != m_xor_cache.end())
    {
        const var_t c = res->second;
        return neg ? -c : +c;
    }
    else return var_t::ILLEGAL;
}

var_t VarManager::simplify_xor(var_t a, var_t b)
{
    Assert(is_legal(a), ILLEGAL_LITERAL);
    Assert(is_legal(b), ILLEGAL_LITERAL);
    Assert(is_known(a), UNKNOWN_LITERAL);
    Assert(is_known(b), UNKNOWN_LITERAL);

    if (a == var_t::ZERO) return b;
    if (b == var_t::ZERO) return a;
    if (a == var_t::ONE) return -b;
    if (b == var_t::ONE) return -a;

    if (a == b) return var_t::ZERO;
    if (a == -b) return var_t::ONE;

    return lookup_xor(a, b);
}

void VarManager::register_xor(var_t a, var_t b, var_t c)
{
    Assert(is_legal(a), ILLEGAL_LITERAL);
    Assert(is_legal(b), ILLEGAL_LITERAL);
    Assert(is_legal(c), ILLEGAL_LITERAL);

    Assert(is_known(a), UNKNOWN_LITERAL);
    Assert(is_known(b), UNKNOWN_LITERAL);
    Assert(is_known(c), UNKNOWN_LITERAL);

    bool neg = is_negated(a) ^ is_negated(b) ^ is_negated(c);
    a = abs_var_t(a), b = abs_var_t(b), c = abs_var_t(c);

    {
        const binary_key_t key = {a < b ? a : b,
                                  a < b ? b : a};
        const var_t res = neg ? -c : c;
        m_xor_cache.emplace(key, res);
    }

    {
        const binary_key_t key = {a < c ? a : c,
                                  a < c ? c : a};
        const var_t res = neg ? -b : b;
        m_xor_cache.emplace(key, res);
    }

    {
        const binary_key_t key = {c < b ? c : b,
                                  c < b ? b : c};
        const var_t res = neg ? -a : a;
        m_xor_cache.emplace(key, res);
    }
}

///////////////////////////////// MUX /////////////////////////////////

var_t VarManager::lookup_mux(var_t s, var_t t, var_t e)
{
    Assert(is_legal(s), ILLEGAL_LITERAL);
    Assert(is_legal(t), ILLEGAL_LITERAL);
    Assert(is_legal(e), ILLEGAL_LITERAL);
    Assert(is_known(s), UNKNOWN_LITERAL);
    Assert(is_known(t), UNKNOWN_LITERAL);
    Assert(is_known(e), UNKNOWN_LITERAL);

    // normalize so that selector is always non-negated
    if (is_negated(s))
    {
        s = -s;
        const var_t swp = t;
        t = e;
        e = swp;
    }

    // normalize so that then is always non-negated
    bool neg = is_negated(t);
    if (neg) { t = -t, e = -e; }

    const ternary_key_t key = {s, t, e};
    auto res = m_mux_cache.find(key);
    if (res != m_mux_cache.end())
    {
        var_t r = res->second;
        return neg ? -r : +r;
    }
    else return var_t::ILLEGAL;
}

var_t VarManager::simplify_mux(var_t s, var_t t, var_t e)
{
    Assert(is_legal(s), ILLEGAL_LITERAL);
    Assert(is_legal(t), ILLEGAL_LITERAL);
    Assert(is_legal(e), ILLEGAL_LITERAL);
    Assert(is_known(s), UNKNOWN_LITERAL);
    Assert(is_known(t), UNKNOWN_LITERAL);
    Assert(is_known(e), UNKNOWN_LITERAL);

    // The formula representation is (s & t) | (-s & e)
    if (s == var_t::ONE) return t;  // ... = t | 0 = t
    if (s == var_t::ZERO) return e; // ... = 0 | e = e

    if (t == e) return t;           // ... = t & (-s | s) = t

    if (t == var_t::ONE) return make_or(s, e);    // ... = s | (-s & e) = s | e
    if (t == var_t::ZERO) return make_and(-s, e); // ... = 0 | (-s & e) = (-s & e)

    if (e == var_t::ONE) return make_or(-s, t);   // ... = (s & t) | -s  = -s | t
    if (e == var_t::ZERO) return make_and(s, t);  // ... = (s & t) | 0 = (s & t)

    if (t == -e) return make_xor(s, e);  // ... = (s & -e) | (-s & e)

    if (t == s) return make_or(s, e);    // ... = s | (-s & e) = s | e
    if (t == -s) return make_and(-s, e); // ... = 0 | (-s & e) = (-s & e);

    if (e == s) return make_and(s, t);   // ... = (s & t) | 0  = (s & t)
    if (e == -s) return make_or(-s, t);  // ... = (s & t) | -s = -s | t

    return lookup_mux(s, t, e);
}

void VarManager::register_mux(var_t s, var_t t, var_t e, var_t r)
{
    Assert(is_legal(s), ILLEGAL_LITERAL);
    Assert(is_legal(t), ILLEGAL_LITERAL);
    Assert(is_legal(e), ILLEGAL_LITERAL);
    Assert(is_legal(r), ILLEGAL_LITERAL);

    Assert(is_known(s), UNKNOWN_LITERAL);
    Assert(is_known(t), UNKNOWN_LITERAL);
    Assert(is_known(e), UNKNOWN_LITERAL);
    Assert(is_known(r), UNKNOWN_LITERAL);

    // normalize so that selector is always non-negated
    if (is_negated(s))
    {
        s = -s;
        const var_t swp = t;
        t = e;
        e = swp;
    }

    // normalize so that then is always non-negated
    bool neg = is_negated(t);
    if (neg) { t = -t, e = -e, r = -r; }

    const ternary_key_t key = {s, t, e};
    m_mux_cache.emplace(key, r);
}
