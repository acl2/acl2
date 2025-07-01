#include <stdbool.h>

// Following function adds two values and returns the flags in the ah register

unsigned char add_two_longs_return_ah(long x, long y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "movq %2, %%rbx;"      // rbx = y
        "addq %%rbx, %%rax;"   // rax += rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs
        : "%rax", "%rbx", "%ah"// clobbered registers
    );

    return ah;
}




//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_long_add_PF () {
  
   
    unsigned char flags = add_two_longs_return_ah(1, 1);

   
      return ((flags & 0x04)==0x00);
    

    
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
