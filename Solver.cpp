#include "Solver.h"
#include <vector>
#include <cassert>

using cxxsat::Solver;
using cxxsat::var_t;

Solver* cxxsat::solver = nullptr;

Solver::Solver() :
        m_state(STATE_INPUT), m_num_clauses(0), m_solver(ipasir_init())
{ }

Solver::~Solver()
{
    ipasir_release(m_solver);
}

var_t Solver::make_and(const var_t a, const var_t b)
{
    var_t c = simplify_and(a, b);
    if (c != var_t::ILLEGAL) return c;

    // Add the clauses for constraining the variables
    c = new_var();
    add_clause(+a, -c);
    add_clause(+b, -c);
    add_clause(-a, -b, +c);
    m_state = STATE_INPUT;

    register_and(a, b, c);
    return c;
}

var_t Solver::make_and(const std::vector<var_t>& ins)
{
    if (ins.empty()) return var_t::ONE;
    if (ins.size() == 1) return ins[0];
    if (ins.size() == 2) return make_and(ins[0], ins[1]);
    std::vector<var_t> big_clause;
    big_clause.reserve(ins.size() + 1);
    bool is_false = false;
    for (var_t in_var : ins)
    {
        Assert(is_legal(in_var), ILLEGAL_LITERAL);
        Assert(is_known(in_var), UNKNOWN_LITERAL);
        is_false |= (in_var == var_t::ZERO);
    }
    if (is_false) return var_t::ZERO;

    var_t res = new_var();
    for (var_t in_var : ins)
    {
        add_clause(+in_var, -res);
        big_clause.push_back(-in_var);
    }
    big_clause.push_back(res);
    add_clause(big_clause);
    return res;
}

var_t Solver::make_or(const var_t a, const var_t b)
{
    return -make_and(-a, -b);
}

var_t Solver::make_or(const std::vector<var_t>& ins)
{
    std::vector<var_t> neg_ins;
    neg_ins.reserve(ins.size());
    for(var_t in_var : ins) neg_ins.push_back(-in_var);
    return -make_and(neg_ins);
}

var_t Solver::make_xor(var_t a, var_t b)
{
    var_t c = simplify_xor(a, b);
    if (c != var_t::ILLEGAL) return c;

    // Add the clauses for constraining the variables
    c = new_var();
    add_clause(-a, -b, -c);
    add_clause(+a, +b, -c);
    add_clause(-a, +b, +c);
    add_clause(+a, -b, +c);
    m_state = STATE_INPUT;

    register_xor(a, b, c);
    return c;
}

var_t Solver::make_xor(const std::vector<var_t>& ins)
{
    std::vector<var_t> actual;
    uint32_t num_negs = 0;
    for(var_t v: ins)
    {
        if (v == var_t::ZERO)
            continue;
        else if (v == var_t::ONE)
            num_negs += 1;
        else
        {
            if (is_negated(v))
                num_negs += 1;
            actual.push_back(abs_var_t(v));
        }
    }
    if (actual.empty()) return (num_negs % 2 == 0) ? var_t::ZERO : var_t::ONE;

    const uint32_t NUM_EXP = 7;

    std::vector<var_t> n_actual;
    std::vector<var_t> clause(NUM_EXP + 1, var_t::ZERO);

    while (actual.size() != 1)
    {
        n_actual.clear();
        for (uint32_t i = 0; i < actual.size(); i += NUM_EXP)
        {
            if (i == actual.size() - 1)
            {
                n_actual.push_back(actual.at(i));
                continue;
            }
            var_t res = new_var();

            for (uint32_t comb = 0; comb < (1 << NUM_EXP); comb++)
            {
                uint32_t popcnt = 0;
                for (uint32_t j = 0; j < NUM_EXP; j++)
                {
                    const uint32_t sign = (comb >> j) & 1;
                    popcnt += sign;
                    const var_t v = i+j < actual.size() ? actual.at(i+j) : var_t::ZERO;
                    clause.at(j) = sign ? -v : v;
                }
                clause.at(NUM_EXP) = (popcnt % 2 == 0) ? -res : res;
                add_clause(clause);
            }
            n_actual.push_back(res);
        }
        actual = n_actual;
    }

    return (num_negs % 2 == 0) ? actual.at(0) : -actual.at(0);
}

var_t Solver::make_mux(var_t s, var_t t, var_t e)
{
    var_t r = simplify_mux(s, t, e);
    if (r != var_t::ILLEGAL) return r;

    r = new_var();
    add_clause(-s, -t, +r);
    add_clause(-s, +t, -r);
    add_clause(+s, -e, +r);
    add_clause(+s, +e, -r);
    add_clause(-t, -e, +r);
    add_clause(+t, +e, -r);
    m_state = STATE_INPUT;

    register_mux(s, t, e, r);
    return r;
}

// implementation of https://link.springer.com/content/pdf/10.1007%2F11564751_73.pdf
var_t Solver::make_at_most(const std::vector<var_t>& ins, uint32_t k)
{
    if (k == 0) { return -make_or(ins); }
    if (k >= ins.size()) return var_t::ONE;

    const uint32_t nvars_start = num_vars();

    std::vector<var_t> s;
    s.resize(k, var_t::ZERO);

    std::vector<var_t> ns;
    ns.reserve(k);

    std::vector<var_t> v;
    v.reserve(ins.size());

    // Iterate over all but the last input
    for (uint32_t i = 0; i < ins.size() - 1; i++)
    {
        ns.clear(); ns.resize(k, var_t::ILLEGAL);
        ns[0] = make_or(ins[i], s[0]);
        for (uint32_t j = 1; j < k; j++)
        {
            ns[j] = make_or(s[j], make_and(s[j-1], ins[i]));
        }
        v.push_back(make_and(ins[i], s[k-1]));
        s = ns;
    }

    // compute v for last input
    v.push_back(make_and(ins[ins.size() - 1], s[k-1]));

    var_t res = -make_or(v);

    const uint32_t nvars_end = num_vars();
    DEBUG(1) << "at-most constraint added " << nvars_end - nvars_start << " new variables" << std::endl;

    return res;
}

var_t Solver::make_at_least(const std::vector<var_t>& ins, uint32_t k)
{
    if (k == 0) return var_t::ONE;
    return -make_at_most(ins, k - 1);
}


Solver::state_t Solver::check() noexcept
{
    m_state = static_cast<state_t>(ipasir_solve(m_solver));
    return m_state;
}

bool Solver::value(var_t a)
{
    Assert(m_state == STATE_SAT, REQUIRE_SAT);
    if (a == var_t::ZERO) return false;
    if (a == var_t::ONE) return true;
    return ipasir_val(m_solver, as_int(a)) > 0;
}