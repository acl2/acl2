#include <stdbool.h>

// Following function tests two values and returns the flags in the ah register

unsigned char inst_test_two_longs_return_ah(unsigned long x, unsigned long y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "movq %2, %%rbx;"      // rbx = y
        "testq %%rbx, %%rax;"   // rax & rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs
        : "%rax", "%rbx", "%ah"// clobbered registers
    );

    return ah;
}









//check property for CF
//CF is bit 0 in ah
//CF is always 0 for and inst

bool test_long_test_CF (unsigned long x, unsigned long y) {
    
    unsigned char flags = inst_test_two_longs_return_ah(x, y);

    return (flags & 0x01)==0x00; 

   
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
