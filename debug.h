#ifndef CXXSAT_DEBUG_H
#define CXXSAT_DEBUG_H

#include <iostream>
#include <stdexcept>

#define VERBOSITY 0L
#define DEBUG(l) ((l) <= VERBOSITY) && std::cout

#ifndef NDEBUG
#define Assert(NCOND, MESSAGE) do { if (!(NCOND)) throw std::logic_error(MESSAGE); } while (0)
#else
#define Assert(NCOND, MESSAGE) do {} while (0)
#endif

#endif //CXXSAT_DEBUG_H
