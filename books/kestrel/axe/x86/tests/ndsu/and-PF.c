#include <stdbool.h>
#include <stdint.h>

// Following function ands two values and returns the flags in the ah register

unsigned char and_two_longs_return_ah(long x, long y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "movq %2, %%rbx;"      // rbx = y
        "andq %%rbx, %%rax;"   // rax = rax & rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs
        : "%rax", "%rbx", "%ah"// clobbered registers
    );

    return ah;
}



// Returns 1 if the number of 1 bits is odd (odd parity)
// Returns 0 if the number of 1 bits is even (even parity)
unsigned char parity(unsigned char x) {
    x ^= x >> 4;
    x ^= x >> 2;
    x ^= x >> 1;
    return x & 1;
}





//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_long_and_PF_x_set_0x00 (long x, long y) {
  
    unsigned char flags = and_two_longs_return_ah(x, y);
    unsigned char PF=1; 
    
     unsigned char x_lowest_byte = x & 0xFF;
    unsigned char y_lowest_byte = y & 0xFF;
    
    if ((flags & 0x04)==0x04) {PF=0;}

    if (x_lowest_byte==0x00) {
      return PF==parity(y_lowest_byte); }
    return true; 
       
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
