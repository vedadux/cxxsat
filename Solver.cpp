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
    if (ins.size() == 2) return make_and(ins[0], ins[1]);
    std::vector<var_t> big_clause;
    big_clause.reserve(ins.size() + 1);

    var_t res = new_var();
    for (var_t in_var : ins)
    {
        Assert(is_legal(in_var), ILLEGAL_LITERAL);
        Assert(is_known(in_var), UNKNOWN_LITERAL);

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

var_t Solver::make_at_most(const std::vector<var_t>& ins, uint32_t k)
{
    if (k == 0)
        { return -make_or(ins); }

    if (k >= ins.size()) return var_t::ONE;

    // create k new variables for each input
    std::vector<var_t> ss;
    ss.reserve(ins.size());
    for (uint32_t i = 0; i < ins.size(); i++)
        { ss.push_back(new_vars((int32_t)k)); }

    // vector containing sum(xs[0:i]) > k
    std::vector<var_t> vv_sym;
    vv_sym.reserve(ins.size());

    auto off = [](var_t x, int32_t i) { return as_var(as_int(x) + i); };

    add_clause(-ins[0], +off(ss[0], 0));

    for (int32_t j = 1; j < k; j++)
        { add_clause(-off(ss[0], j)); }
    for (int32_t i = 0; i < k; i++)
        { vv_sym.emplace_back(var_t::ZERO); }
    for (int32_t i = 1; i < ins.size() - 1; i++)
    {
        add_clause(-ins[i], +off(ss[i], 0));
        add_clause(-off(ss[i-1], 0), +off(ss[i], 0));
        for (int32_t j = 1; j < k; j++)
        {
            add_clause(-ins[i], -off(ss[i-1], j-1), +off(ss[i], j));
            add_clause(-off(ss[i-1], j), +off(ss[i], j));
        }
        if (i >= k)
        {
            const var_t s = off(ss[i-1], (int32_t)k-1);
            const var_t v = make_and(s, ins[i]);
            vv_sym.push_back(v);
        }
    }
    {
        const var_t s = off(ss[ins.size()-2], (int32_t)k-1);
        const var_t v = make_and(s, ins[ins.size() - 1]);
        vv_sym.push_back(v);
        assert(vv_sym.size() == ins.size());
    }
    return -make_or(vv_sym);
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