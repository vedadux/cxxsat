#ifndef CXXSAT_SOLVER_H
#define CXXSAT_SOLVER_H

#include "debug.h"
#include "vars.h"
#include "VarManager.h"

extern "C" {
#include "ipasir.h"
}

namespace cxxsat {

constexpr const char* REQUIRE_SAT = "Solver must be in STATE_SAT state";

class Solver : public VarManager {
public:
    enum state_t {STATE_SAT = 10, STATE_UNSAT = 20, STATE_INPUT = 30};
private:
    /// Current state of the solver
    state_t m_state;
    /// The number of currently added solver clauses
    int m_num_clauses;
    /// IPASIR solver object with generic (void*) type
    void* m_solver;

    /// Internal ipasir_add forwarding
    inline void add(var_t x);

    /// Performs checks whether the clause is a tautology, or contains illegal literals
    template<typename... Ts>
    bool check_clause_inner(var_t head, Ts... tail);

    /// Recursive template function that simplifies and adds a clause into the solver
    template<typename... Ts>
    void add_clause_inner(var_t head, Ts... tail);

public:
    /// Returns the number of currently added clauses
    inline int num_clauses() const noexcept { return m_num_clauses; };
    /// Returns the current state of the solver
    inline state_t state() const { return m_state; }

    /// Creates a new variable representing AND(a, b)
    var_t make_and(var_t a, var_t b) override;
    /// Creates a new variable representing OR(a, b)
    var_t make_or(var_t a, var_t b) override;
    /// Creates a new variable representing XOR(a, b)
    var_t make_xor(var_t a, var_t b) override;
    /// Creates a new variable representing MUX(s, t, e)
    var_t make_mux(var_t s, var_t t, var_t e) override;

    var_t make_and(const std::vector<var_t>& ins);
    var_t make_or(const std::vector<var_t>& ins);
    var_t make_at_most(const std::vector<var_t>& ins, uint32_t k);
    var_t make_at_least(const std::vector<var_t>& ins, uint32_t k);


    /// Public template function for adding clauses into the solver
    template<typename... Ts>
    void add_clause(var_t head, Ts... tail);

    /// Public function for adding clauses from vectors into the solver
    inline void add_clause(const std::vector<var_t>& clause);

    /// Public function for adding clauses from vectors into the solver
    inline void assume(var_t ass);

    /// Main satisfiability checking routine
    state_t check() noexcept;
    /// Return the value assigned to variable \a a
    bool value(var_t a);

    /// Only default constructor is implemented
    Solver();
    /// Destructor destroying the internal IPASIR object
    ~Solver();
};

inline void Solver::add(var_t x)
{
    ipasir_add(m_solver, as_int(x));
    DEBUG(2) << as_int(x) << " ";
}

inline void Solver::assume(var_t ass)
{
    Assert(is_legal(ass), ILLEGAL_LITERAL);
    Assert(is_known(ass), UNKNOWN_LITERAL);
    if (ass == var_t::ONE) return;
    if (ass == var_t::ZERO)
    {
        var_t nv = new_var();
        ipasir_assume(m_solver, as_int(nv));
        ipasir_assume(m_solver, -as_int(nv));
        DEBUG(2) << "assuming false" << std::endl;
        return;
    }
    ipasir_assume(m_solver, as_int(ass));
    DEBUG(2) << "assuming " << as_int(ass) << std::endl;
}

template<>
inline void Solver::add_clause_inner(var_t head)
{
    if (head != var_t::ZERO) add(head);
    add(as_var(0)); // terminate the clause
    m_num_clauses += 1;
    m_state = STATE_INPUT;
}

template<typename... Ts>
inline void Solver::add_clause_inner(var_t head, Ts... tail)
{
    if (head != var_t::ZERO) add(head);
    add_clause_inner(tail...);
}

template<typename... Ts>
inline void Solver::add_clause(var_t head, Ts... tail)
{
    if(!check_clause_inner(head, tail...))
    {
        DEBUG(2) << "Eliminated clause" << std::endl;
        return;
    }
    DEBUG(2) << "Adding clause: ";
    add_clause_inner(head,tail...);
    DEBUG(2) << std::endl;
}

template<>
inline bool Solver::check_clause_inner(var_t head)
{
    Assert(is_legal(head), ILLEGAL_LITERAL);
    Assert(is_known(head), UNKNOWN_LITERAL);
    return (head != var_t::ONE);
}

template<typename... Ts>
inline bool Solver::check_clause_inner(var_t head, Ts... tail) {
    Assert(is_legal(head), ILLEGAL_LITERAL);
    Assert(is_known(head), UNKNOWN_LITERAL);
    return (head != var_t::ONE) && check_clause_inner(tail...);
}

inline void Solver::add_clause(const std::vector<var_t>& clause)
{
    for (const var_t x : clause)
    {
        Assert(is_legal(x), ILLEGAL_LITERAL);
        Assert(is_known(x), UNKNOWN_LITERAL);
        if (x != var_t::ONE) continue;
        DEBUG(2) << "Eliminated clause" << std::endl;
        return;
    }

    for (const var_t x : clause)
        { if (x != var_t::ZERO) add(x); }
    add(as_var(0));
    m_num_clauses += 1;
    m_state = STATE_INPUT;
}

extern Solver* solver;

} // namespace cxxsat

#endif // CXXSAT_SOLVER_H