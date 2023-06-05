#include "Solver.h"

#include <iostream>
#include <map>

#ifdef NDEBUG
#define assert(cond) do { if (!(cond)) return 3; } while (0)
#else
#include <cassert>
#endif

using test_func_t = int (*)();
using Solver = cxxsat::Solver;
using var_t = cxxsat::var_t;
const uint32_t MAX_VECTOR_TEST = 8;


int test_and()
{
    Solver solver;

    var_t a = solver.new_var();
    var_t b = solver.new_var();

    assert(a != b);

    assert(a == solver.make_and(a, var_t::ONE));
    assert(a == solver.make_and(var_t::ONE, a));

    assert(var_t::ZERO == solver.make_and(a, var_t::ZERO));
    assert(var_t::ZERO == solver.make_and(var_t::ZERO, a));

    assert(a == solver.make_and(a, a));
    assert(var_t::ZERO == solver.make_and(a, -a));

    var_t c = solver.make_and(a, b);
    assert(c != a);
    assert(c != b);

    assert(c == solver.make_and(a, b));

    for (int row = 0; row < 4; row++)
    {
        bool pos_a = row & 1;
        bool pos_b = row & 2;

        solver.assume(pos_a ? +a : -a);
        solver.assume(pos_b ? +b : -b);
        assert(Solver::state_t::STATE_SAT == solver.check());

        std::cout << pos_a << " & " << pos_b << " == " << solver.value(c) << std::endl;
        assert(solver.value(c) == (pos_a && pos_b));
    }

    return 0;
}


int test_or()
{
    Solver solver;

    var_t a = solver.new_var();
    var_t b = solver.new_var();

    assert(a != b);

    assert(a == solver.make_or(a, var_t::ZERO));
    assert(a == solver.make_or(var_t::ZERO, a));

    assert(var_t::ONE == solver.make_or(a, var_t::ONE));
    assert(var_t::ONE == solver.make_or(var_t::ONE, a));

    assert(a == solver.make_or(a, a));
    assert(var_t::ONE == solver.make_or(a, -a));

    var_t c = solver.make_or(a, b);
    assert(c != a);
    assert(c != b);

    assert(c == solver.make_or(a, b));

    for (int row = 0; row < 4; row++)
    {
        bool pos_a = row & 1;
        bool pos_b = row & 2;

        solver.assume(pos_a ? +a : -a);
        solver.assume(pos_b ? +b : -b);
        assert(Solver::state_t::STATE_SAT == solver.check());

        std::cout << pos_a << " | " << pos_b << " == " << solver.value(c) << std::endl;
        assert(solver.value(c) == (pos_a || pos_b));
    }

    return 0;
}


int test_xor()
{
    Solver solver;

    var_t a = solver.new_var();
    var_t b = solver.new_var();

    assert(a != b);

    assert(a == solver.make_xor(a, var_t::ZERO));
    assert(a == solver.make_xor(var_t::ZERO, a));

    assert(-a == solver.make_xor(a, var_t::ONE));
    assert(-a == solver.make_xor(var_t::ONE, a));

    assert(var_t::ZERO == solver.make_xor(a, a));
    assert(var_t::ONE == solver.make_xor(a, -a));

    var_t c = solver.make_xor(a, b);
    assert(c != a);
    assert(c != b);

    assert(c == solver.make_xor(a, b));
    assert(c == solver.make_xor(-a, -b));

    for (int row = 0; row < 4; row++)
    {
        bool pos_a = row & 1;
        bool pos_b = row & 2;

        solver.assume(pos_a ? +a : -a);
        solver.assume(pos_b ? +b : -b);
        assert(Solver::state_t::STATE_SAT == solver.check());

        std::cout << pos_a << " ^ " << pos_b << " == " << solver.value(c) << std::endl;
        assert(solver.value(c) == (pos_a != pos_b));
    }

    return 0;
}


int test_mux()
{
    Solver solver;

    var_t s = solver.new_var();
    var_t t = solver.new_var();
    var_t e = solver.new_var();

    assert(s != t);
    assert(s != e);
    assert(t != e);

    assert(t == solver.make_mux(var_t::ONE, t, var_t::ZERO));
    assert(t == solver.make_mux(var_t::ONE, t, var_t::ONE));
    assert(t == solver.make_mux(var_t::ONE, t, e));

    assert(e == solver.make_mux(var_t::ZERO, var_t::ZERO, e));
    assert(e == solver.make_mux(var_t::ZERO, var_t::ONE, e));
    assert(e == solver.make_mux(var_t::ZERO, t, e));

    assert(s == solver.make_mux(s, var_t::ONE, var_t::ZERO));
    assert(-s == solver.make_mux(s, var_t::ZERO, var_t::ONE));

    assert(t == solver.make_mux(s, t, t));
    assert(e == solver.make_mux(s, e, e));

    assert(solver.make_mux(s, var_t::ONE, e) == solver.make_or(s, e));
    assert(solver.make_mux(s, var_t::ZERO, e) == solver.make_and(-s, e));

    assert(solver.make_mux(s, t, var_t::ONE) == solver.make_or(-s, t));
    assert(solver.make_mux(s, t, var_t::ZERO) == solver.make_and(s, t));

    assert(solver.make_mux(s, t, -t) == -solver.make_xor(s, t));
    assert(solver.make_mux(s, -e, e) == solver.make_xor(s, e));

    var_t r = solver.make_mux(s, t, e);
    assert(r != s && r != t && r != e);
    assert(r == solver.make_mux(-s, e, t));

    for (int row = 0; row < 8; row++)
    {
        bool pos_s = row & 1;
        bool pos_t = row & 2;
        bool pos_e = row & 4;


        solver.assume(pos_s ? +s : -s);
        solver.assume(pos_t ? +t : -t);
        solver.assume(pos_e ? +e : -e);
        assert(Solver::state_t::STATE_SAT == solver.check());

        std::cout << pos_s << " ? " << pos_t << " : " << pos_e << " == " << solver.value(r) << std::endl;
        assert(solver.value(r) == (pos_s ? pos_t : pos_e));
    }

    return 0;
}

int test_and_multi()
{
    Solver solver;

    std::vector<var_t> ins;
    var_t res;

    res = solver.make_and(ins);
    assert(res == var_t::ONE);

    ins.push_back(solver.new_var());
    res = solver.make_and(ins);
    assert(res == ins[0]);

    ins.push_back(solver.new_var());
    res = solver.make_and(ins);
    assert(res == solver.make_and(ins[0], ins[1]));

    do {
        ins.push_back(solver.new_var());
        res = solver.make_and(ins);
        for (uint32_t row = 0; row < (1 << ins.size()); row++)
        {
            bool expected = true;
            for (uint32_t pos_i = 0; pos_i < ins.size(); pos_i++)
            {
                bool pos = row & (1 << pos_i);
                solver.assume(pos ? +ins[pos_i] : -ins[pos_i]);
                std::cout << pos << ((pos_i == ins.size() - 1) ? " == " : " & ");
                expected &= pos;
            }
            assert(Solver::state_t::STATE_SAT == solver.check());
            std::cout << expected << std::endl;
            assert(solver.value(res) == expected);
        }

    } while(ins.size() != MAX_VECTOR_TEST);

    return 0;
}

int test_or_multi()
{
    Solver solver;

    std::vector<var_t> ins;
    var_t res;

    res = solver.make_or(ins);
    assert(res == var_t::ZERO);

    ins.push_back(solver.new_var());
    res = solver.make_or(ins);
    assert(res == ins[0]);

    ins.push_back(solver.new_var());
    res = solver.make_or(ins);
    assert(res == solver.make_or(ins[0], ins[1]));

    do {
        ins.push_back(solver.new_var());
        res = solver.make_or(ins);
        for (uint32_t row = 0; row < (1 << ins.size()); row++)
        {
            bool expected = false;
            for (uint32_t pos_i = 0; pos_i < ins.size(); pos_i++)
            {
                bool pos = row & (1 << pos_i);
                solver.assume(pos ? +ins[pos_i] : -ins[pos_i]);
                std::cout << pos << ((pos_i == ins.size() - 1) ? " == " : " | ");
                expected |= pos;
            }
            assert(Solver::state_t::STATE_SAT == solver.check());
            std::cout << expected << std::endl;
            assert(solver.value(res) == expected);
        }

    } while(ins.size() != MAX_VECTOR_TEST);

    return 0;
}

int test_at_most()
{
    Solver solver;

    std::vector<var_t> ins;
    var_t res;

    res = solver.make_at_most(ins, 0);
    assert(res == var_t::ONE);

    res = solver.make_at_most(ins, 1);
    assert(res == var_t::ONE);

    ins.push_back(solver.new_var());

    res = solver.make_at_most(ins, 0);
    assert(res == -ins[0]);

    res = solver.make_at_most(ins, 1);
    assert(res == var_t::ONE);

    res = solver.make_at_most(ins, 2);
    assert(res == var_t::ONE);

    do {
        ins.push_back(solver.new_var());

        for (uint32_t k = 0; k <= ins.size() + 1; k++)
        {
            res = solver.make_at_most(ins, k);

            for (uint32_t row = 0; row < (1 << ins.size()); row++)
            {
                uint32_t expected = 0;
                for (uint32_t pos_i = 0; pos_i < ins.size(); pos_i++)
                {
                    bool pos = row & (1 << pos_i);
                    solver.assume(pos ? +ins[pos_i] : -ins[pos_i]);
                    std::cout << pos << ((pos_i == ins.size() - 1) ? " <= " : " + ");
                    expected += pos;
                }
                assert(Solver::state_t::STATE_SAT == solver.check());
                std::cout << k << " : " << solver.value(res) << std::endl;
                assert(solver.value(res) == (expected <= k));
            }
        }
    } while (ins.size() != MAX_VECTOR_TEST);

    return 0;
}

int test_at_least()
{
    Solver solver;

    std::vector<var_t> ins;
    var_t res;

    res = solver.make_at_least(ins, 0);
    assert(res == var_t::ONE);

    res = solver.make_at_least(ins, 1);
    assert(res == var_t::ZERO);

    ins.push_back(solver.new_var());

    res = solver.make_at_least(ins, 0);
    assert(res == var_t::ONE);

    res = solver.make_at_least(ins, 1);
    assert(res == ins[0]);

    res = solver.make_at_least(ins, 2);
    assert(res == var_t::ZERO);

    do {
        ins.push_back(solver.new_var());

        for (uint32_t k = 0; k <= ins.size() + 1; k++)
        {
            res = solver.make_at_least(ins, k);

            for (uint32_t row = 0; row < (1 << ins.size()); row++)
            {
                uint32_t expected = 0;
                for (uint32_t pos_i = 0; pos_i < ins.size(); pos_i++)
                {
                    bool pos = row & (1 << pos_i);
                    solver.assume(pos ? +ins[pos_i] : -ins[pos_i]);
                    std::cout << pos << ((pos_i == ins.size() - 1) ? " >= " : " + ");
                    expected += pos;
                }
                assert(Solver::state_t::STATE_SAT == solver.check());
                std::cout << k << " : " << solver.value(res) << std::endl;
                assert(solver.value(res) == (expected >= k));
            }
        }
    } while (ins.size() != MAX_VECTOR_TEST);

    return 0;
}

const std::map<const std::string, test_func_t> tests = {
    {"test_and", test_and},
    {"test_or", test_or},
    {"test_xor", test_xor},
    {"test_mux", test_mux},
    {"test_and_multi", test_and_multi},
    {"test_or_multi", test_or_multi},
    {"test_at_most", test_at_most},
    {"test_at_least", test_at_least},
};

int main(int argc, const char* argv[])
{
    if (argc < 2)
    {
        std::cout << "Usage: " << argv[0] << " TEST_NAME" << std::endl;
        return 1;
    }

    if (argv[1] == std::string("all"))
    {
        int res = 0;
        for (const auto& test : tests)
            { res |= test.second(); }
        return res;
    }

    const auto& test_it = tests.find(argv[1]);
    if (test_it == tests.end())
    {
        std::cout << "Unknown test \"" << argv[1] << "\"" << std::endl;
        return 2;
    }
    return test_it->second();
}
