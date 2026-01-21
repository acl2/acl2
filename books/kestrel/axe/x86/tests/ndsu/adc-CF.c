#include <stdbool.h>
#include <stdint.h>

// Following function adds two values and returns the flags after the addc in the ah register

#include <stdint.h>

unsigned char adc_two_longs_return_ah(unsigned long x, unsigned long y, unsigned char flags) {
    unsigned char ah;

    __asm__ volatile (
        "movzbq %3, %%rcx;"       // Zero-extend 'flags' into rcx
        "movb %%cl, %%ah;"        // Move it to AH (safe because CL is low byte of RCX)
        "sahf;"                   // Set flags (CF, ZF, etc.) from AH
        "movq %1, %%rax;"         // rax = x
        "movq %2, %%rbx;"         // rbx = y
        "adcq %%rbx, %%rax;"      // rax = rax + rbx + CF
        "lahf;"                   // Load flags into AH
        "movb %%ah, %0;"          // Output final AH to 'ah'
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(flags)
        : "%rax", "%rbx", "%rcx", "cc"
    );

    return ah;
}






//check property for CF
//CF is bit 0 in ah

bool test_long_adc_CF (unsigned long x, unsigned long y, unsigned char flags_input) {
    unsigned char CF = flags_input & 0x01;
    long CF_long = (long)CF;  // Zero-extend
    unsigned long sum = x + y + CF_long;
    unsigned char flags = adc_two_longs_return_ah(x, y, flags_input);

    if ((sum < x) ||  (CF_long==1 && sum==x)) {
        return ((flags & 0x01)==0x01); 
    }
    else  {
      return ((flags & 0x01)==0x00); 
    }
    return false;
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
