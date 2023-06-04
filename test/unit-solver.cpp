#include "Solver.h"

#include <iostream>
#include <map>
#include <cassert>

using test_func_t = void (*)();
using Solver = cxxsat::Solver;
using var_t = cxxsat::var_t;

void test_and()
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
}


void test_or()
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
}


void test_xor()
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
}


void test_mux()
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
}


const std::map<const std::string, test_func_t> tests = {
    {"test_and", test_and},
    {"test_or", test_or},
    {"test_xor", test_xor},
    {"test_mux", test_mux},
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
        for (const auto& test : tests)
            test.second();
        return 0;
    }

    const auto& test_it = tests.find(argv[1]);
    if (test_it == tests.end())
    {
        std::cout << "Unknown test \"" << argv[1] << "\"" << std::endl;
        return 2;
    }
    test_it->second();
    return 0;
}
