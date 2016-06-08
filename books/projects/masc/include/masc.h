#ifndef MASC_H
#define MASC_H

// Assert is sometimes a macro, which screws up our translation.
// If we are using the MASC translator we want to prevent its expansion.
#ifdef __MASC__
#undef assert
#endif

#endif

