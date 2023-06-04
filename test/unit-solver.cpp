#include "Solver.h"

#include <iostream>
#include <map>
#include <cassert>

void hello()
{
    std::cout << "Hello, World!" << std::endl;
}

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





const std::map<const std::string, test_func_t> tests = {
    {"test_and", test_and},
    {"test_or", test_or},
    {"test_xor", test_xor},
};

int main(int argc, const char* argv[])
{
    if (argc < 2)
    {
        std::cout << "Usage: " << argv[0] << " TEST_NAME" << std::endl;
        return 1;
    }
    const auto& test_it = tests.find(argv[1]);
    if (test_it == tests.end())
    {
        std::cout << "Unknown test \"" << argv[1] << "\"" << std::endl;
        return 2;
    }
    test_it->second();
}
