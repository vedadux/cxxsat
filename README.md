# cxxsat
`cxxsat` is an enhanced C++ interface for SAT solvers that makes prototyping easier,
encodes commonly required functionality natively and reduces formula bloat, leading to
better SAT solver performance.

`cxxsat` comes pre-packaged with Cadical and uses it through the `ipasir` C interface
used in all competitive incremental solvers. Replacing Cadical with another solver is
therefore as easy as changing the `CMakeLists.txt` file to specify the new solver as
an external project in some git sub-module.

## Example Code

Here is an example of using only the basic features of `cxxsat`, that shows the workflow
of creating a solver, constraints, solving the problem and getting the satisfiable solution:

```C++
#include "Solver.h"
using Solver = cxxsat::Solver;
using var_t = cxxsat::var_t;
using state_t = cxxsat::Solver::state_t;
int main()
{
  Solver solver;
  var_t a = solver.new_var();
  var_t b = solver.new_var();
  var_t c = solver.new_var();
  solver.add_clause(-a, b, -c);
  solver.add_clause(a, -b);
  state_t state = solver.check();
  if (state == state_t::STATE_SAT)
  {
    std::cout << "a = " << solver.value(a);
    std::cout << "b = " << solver.value(b);
    std::cout << "c = " << solver.value(c);
  }
  return 0;
}
```

Here is abother example that focuses on the usability aspect, because usually, you
do not want to implement all the logic operator encoding, simplification and hashing
yourself:

```C++
#include "Solver.h"
using var_t = cxxsat::var_t;
using state_t = cxxsat::Solver::state_t;

int main()
{
  cxxsat::solver = new cxxsat::Solver();
  var_t a = solver->new_var();
  var_t b = solver->new_var();
  var_t c = solver->new_var();
  var_t d = a & b;
  var_t e = -a | -b;
  var_t f = cxxsat::mux(c, d, var_t::ZERO);

  std::vector<var_t> free_vars = {a, b, c};
  var_t le_2 = cxxsat::solver->make_at_most(free_vars, 2);
  cxxsat::solver->add_clause(le_2);
  cxxsat::solver->assume(a);

  state_t state = cxxsat::solver->check();
  if (state == state_t::STATE_SAT)
  {
    std::cout << "a (" << as_int(a) << ") = " << cxxsat::solver->value(a);
    std::cout << "b (" << as_int(b) << ") = " << cxxsat::solver->value(b);
    std::cout << "c (" << as_int(c) << ") = " << cxxsat::solver->value(c);
    std::cout << "d (" << as_int(d) << ") = " << cxxsat::solver->value(d);
    std::cout << "e (" << as_int(e) << ") = " << cxxsat::solver->value(e);
    std::cout << "f (" << as_int(f) << ") = " << cxxsat::solver->value(f);
  }
  delete cxxsat::solver;
  return 0;
}
```
