#include <stdbool.h>

// The function to test:


long  inc_dec (long  x) {
    long  result;

    __asm__ volatile (
        "movq %1, %%rax;"     // rax = x
        "addq $1, %%rax;"     // rax += 1
        "subq $1, %%rax;"     // rax -= 1
        "movq %%rax, %0;"     // result = eax
        : "=r" (result)       // output
        : "r" (x)             // input
        : "%rax"              // clobbered
    );

    return result;
}





unsigned long unsigned_long_add (unsigned long x, unsigned long y) {
  return x+y;
}

// The formal unit test (the add function is commutative).  The Formal Unit Tester
// will prove that this function always returns 1.
bool test_unsigned_long_add_commutative (unsigned long x, unsigned long y) {
  return unsigned_long_add(x, y) == unsigned_long_add(y, x);
}

bool test_unsigned_long_inc_dec (long x) {
  return inc_dec(x) == x;
}

// dummy main function, to allow us to link the executable
int main () { return 0;}
