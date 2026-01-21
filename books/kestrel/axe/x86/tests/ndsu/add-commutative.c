#include <stdbool.h>

// The function to test:

long add_two_longs(long x, long y) {
    long result;

    __asm__ volatile (
        "movq %1, %%rax;"     // rax = x
        "movq %2, %%rbx;"     // rbx = y
        "addq %%rbx, %%rax;"  // rax += rbx
        "movq %%rax, %0;"     // result = rax
        : "=r" (result)       // output
        : "r" (x), "r" (y)     // inputs
        : "%rax", "%rbx"      // clobbered registers
    );

    return result;
}







//check if add instruction is commutative
bool test_long_add_commutative (long x, long y) {
  return add_two_longs(x,y) == add_two_longs(y,x);
}

// dummy main function, to allow us to link the executable
int main () { return 0;}
