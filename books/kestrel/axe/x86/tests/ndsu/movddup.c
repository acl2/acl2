#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
//reg-reg
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

bool test_MOVDDUP_xmm_xmm_PF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_xmm_return_flags(x, y);
    return (flags & 0x04) == (y & 0x04);  // Bit 2 = PF
}

bool test_MOVDDUP_xmm_xmm_AF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_xmm_return_flags(x, y);
    return (flags & 0x10) == (y & 0x10);  // Bit 4 = AF
}

bool test_MOVDDUP_xmm_xmm_ZF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_xmm_return_flags(x, y);
    return (flags & 0x40) == (y & 0x40);  // Bit 6 = ZF
}

bool test_MOVDDUP_xmm_xmm_SF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_xmm_return_flags(x, y);
    return (flags & 0x80) == (y & 0x80);  // Bit 7 = SF
}

unsigned char MOVDDUP_xmm_xmm_return_overflow(double x, uint8_t y) {
	unsigned char of;
	__asm__ volatile (
		"testb $1, %2; "
		"jz 0f; "
		"movb $0x7f, %%al; "
		"addb $1, %%al; "
		"jmp 1f; "
		"0: xor %%al, %%al; "
		"addb $1, %%al; "
		"1: movddup %1, %%xmm0; "
		"seto %0; "
		: "=qm"(of)
		: "x"(x), "q"(y)
		: "al", "xmm0", "cc"
	);
	return of;
}

bool test_MOVDDUP_xmm_xmm_OF(double x, uint8_t y) {
	unsigned char of = MOVDDUP_xmm_xmm_return_overflow(x, y);
	return (of & 0x01) == (y & 0x01);
}

// reg-mem
unsigned char MOVDDUP_xmm_m64_return_flags(double x, uint8_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movb %2, %%ah;"           // Move y (flag value) to AH
        "sahf;"                    // Store AH into flags (set initial flags)
        "movddup %1, %%xmm0;"      // xmm0 = duplicate(m64)
        "lahf;"                    // Load flags into AH
        "movb %%ah, %0;"           // Output AH
        : "=r"(ah)
        : "m"(x), "r"(y)
        : "%xmm0", "%ah", "cc"     // Added "cc" for flags
    );
    return ah;
}

// Test functions for memory variant
bool test_MOVDDUP_xmm_m64_CF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_m64_return_flags(x, y);
    return (flags & 0x01) == (y & 0x01);  // Bit 0 = CF
}

bool test_MOVDDUP_xmm_m64_PF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_m64_return_flags(x, y);
    return (flags & 0x04) == (y & 0x04);  // Bit 2 = PF
}

bool test_MOVDDUP_xmm_m64_AF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_m64_return_flags(x, y);
    return (flags & 0x10) == (y & 0x10);  // Bit 4 = AF
}

bool test_MOVDDUP_xmm_m64_ZF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_m64_return_flags(x, y);
    return (flags & 0x40) == (y & 0x40);  // Bit 6 = ZF
}

bool test_MOVDDUP_xmm_m64_SF(double x, uint8_t y) {
    unsigned char flags = MOVDDUP_xmm_m64_return_flags(x, y);
    return (flags & 0x80) == (y & 0x80);  // Bit 7 = SF
}

unsigned char MOVDDUP_xmm_m64_return_overflow(double x, uint8_t y) {
	unsigned char of;
	__asm__ volatile (
		"testb $1, %2; "          
		"jz 0f; "
		"movb $0x7f, %%al; "      
		"addb $1, %%al; "
		"jmp 1f; "
		"0: xor %%al, %%al; "     
		"addb $1, %%al; "
		"1: movddup %1, %%xmm0; " 
		"seto %0; "
		: "=qm"(of)
		: "m"(x), "q"(y)
		: "al", "xmm0", "cc"
	);
	return of;
}


bool test_MOVDDUP_xmm_m64_OF(double x, uint8_t y) {
	unsigned char of = MOVDDUP_xmm_m64_return_overflow(x, y);
	return (of & 0x01) == (y & 0x01);
}


int main () { return 0;}