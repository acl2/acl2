#ifndef RAC_H
#define RAC_H

// Assert is sometimes a macro, which screws up our translation.
// If we are using the RAC translator we want to prevent its expansion.
#ifdef __RAC__
#undef assert
#endif

#include <array>
#include <tuple>

#endif

