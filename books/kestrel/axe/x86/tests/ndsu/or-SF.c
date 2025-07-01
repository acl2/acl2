#include <stdbool.h>

// Following function ORs two values and returns the flags in the ah register

unsigned char or_two_longs_return_ah(long x, long y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "movq %2, %%rbx;"      // rbx = y
        "orq %%rbx, %%rax;"   // rax = rax | rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs
        : "%rax", "%rbx", "%ah"// clobbered registers
    );

    return ah;
}




//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_long_or_SF (long x, long y) {
  
  long result = x | y;  
    unsigned char flags = or_two_longs_return_ah(x, y);

    if (result<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    return false; 

    
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
