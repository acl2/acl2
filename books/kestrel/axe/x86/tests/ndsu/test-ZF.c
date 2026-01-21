#include <stdbool.h>

// Following function tests two values and returns the flags in the ah register

unsigned char inst_test_two_longs_return_ah(long x, long y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "movq %2, %%rbx;"      // rbx = y
        "testq %%rbx, %%rax;"   // rax = rax & rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs
        : "%rax", "%rbx", "%ah"// clobbered registers
    );

    return ah;
}




//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_long_test_ZF (long x, long y) {
  
  long result = x&y;  
    unsigned char flags = inst_test_two_longs_return_ah(x, y);

    if (result==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
    return false; 

    
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
