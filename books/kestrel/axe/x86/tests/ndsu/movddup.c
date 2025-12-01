#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

unsigned char MOVDDUP_xmm_xmm_return_flags(double x, uint8_t y) {
    unsigned char ah_out;

    __asm__ volatile (
        "movsd %1, %%xmm0;"     // Load x into xmm0 
        "movb %2, %%ah;"        // Move y (flag value) to AH
        "sahf;"                 // Store AH into flags
        "movddup %%xmm0, %%xmm1;" // The instruction we are testing
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Output AH to variable
        : "=r"(ah_out)          // Output
        : "m"(x), "r"(y)        // Inputs
        : "%xmm0", "%xmm1", "rax", "cc" // Clobbers
    );
    return ah_out;
}


// Test functions for register variant
bool test_MOVDDUP_xmm_xmm_CF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_xmm_return_flags(x, y);
    return (flags & 0x01) == (y & 0x01);  // Bit 0 = CF
}

// dummy main function, to allow us to link the executable

int main () { return 0;}