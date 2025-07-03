#include <stdbool.h>


// Following function CMPs two values and returns the flags in the ah register

unsigned char cmp_two_longs_return_ah(unsigned long x, unsigned long y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "movq %2, %%rbx;"      // rbx = y
        "cmpq %%rbx, %%rax;"   // rax = rax - rbx
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

bool test_long_cmp_CF (unsigned long x, unsigned long y) {
    unsigned long diff = x - y;
    unsigned char flags = cmp_two_longs_return_ah(x, y);

    if ((y > x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
