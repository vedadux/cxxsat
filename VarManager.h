#ifndef CXXSAT_VARMANAGER_H
#define CXXSAT_VARMANAGER_H

#include "debug.h"
#include "vars.h"
#include "keys.h"
#include <unordered_map>

namespace cxxsat {

constexpr const char* ILLEGAL_LITERAL = "Found illegal literal when adding clause";
constexpr const char* UNKNOWN_LITERAL = "Found unknown literal when adding clause";

class VarManager {
private:
    /// The number of currently allocated solver variables
    int32_t m_num_vars;
protected:
    /// Cache for AND gates
    std::unordered_map<binary_key_t , var_t> m_and_cache;
    std::unordered_map<binary_key_t , var_t> m_xor_cache;
    std::unordered_map<ternary_key_t , var_t> m_mux_cache;

    /// Helper functions for the AND(a, b)
    var_t simplify_and(var_t a, var_t b);
    var_t lookup_and(var_t a, var_t b);
    void register_and(var_t a, var_t b, var_t c);

    /// Helper functions for the OR(a, b)
    var_t simplify_or(var_t a, var_t b);
    var_t lookup_or(var_t a, var_t b);
    void register_or(var_t a, var_t b, var_t c);

    /// Helper functions for the XOR(a, b)
    var_t simplify_xor(var_t a, var_t b);
    var_t lookup_xor(var_t a, var_t b);
    void register_xor(var_t a, var_t b, var_t c);

    /// Helper functions for the MUX(s, t, e)
    var_t simplify_mux(var_t s, var_t t, var_t e);
    var_t lookup_mux(var_t s, var_t t, var_t e);
    void register_mux(var_t s, var_t t, var_t e, var_t r);

public:
    uint32_t hits;
    /// Allocates \a number many solver variables and returns the first one
    inline var_t new_vars(int number) noexcept;
    /// Allocates and returns a new solver variable
    inline var_t new_var() noexcept { return new_vars(1); };
    /// Returns the number of currently used variables
    inline int num_vars() const noexcept { return m_num_vars; };
    /// Returns true if provided variable is known
    inline bool is_known(var_t a) const { return (as_int(abs_var_t(a)) <= m_num_vars) || a == var_t::ZERO || a == var_t::ONE; }

    /// Creates a new variable representing AND(a, b)
    virtual var_t make_and(var_t a, var_t b) = 0;
    /// Creates a new variable representing OR(a, b)
    virtual var_t make_or(var_t a, var_t b) = 0;
    /// Creates a new variable representing XOR(a, b)
    virtual var_t make_xor(var_t a, var_t b) = 0;
    /// Creates a new variable representing MUX(s, t, e)
    virtual var_t make_mux(var_t s, var_t t, var_t e) = 0;

    /// Only default constructor is implemented
    VarManager();
    /// We use the default destructor since there are no directly allocated members
    ~VarManager() = default;
};

inline var_t VarManager::new_vars(const int number) noexcept
{
    const int32_t var = m_num_vars;
    m_num_vars += number;
    return as_var(var + 1);
}

} // namespace cxxsat

#endif // CXXSAT_VARMANAGER_H
