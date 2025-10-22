#include <stdint.h>
#include <stdbool.h>

unsigned char mul_AL_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movb %1, %%al;"       // al = x (multiplicand)
        "movb %2, %%bl;"       // bl = y (multiplier)
        "mulb %%bl;"           // F6 E3: ax = al * bl
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "al", "bl", "ah", "ax"  // clobbered registers
    );

    return ah;
}


// Check property for CF (Carry Flag)
// CF is bit 0 in ah - set if result doesn't fit in AL (i.e., AH != 0)
bool test_mul_AL_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = mul_AL_r8_return_flags(x, y);
    uint16_t result = (uint16_t)x * (uint16_t)y;

    if (result > 255) {  // Result doesn't fit in 8 bits
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {             // Result fits in 8 bits
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// Alternative OF extraction using SETO
unsigned char mul_AL_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    
    __asm__ volatile (
        "movb %1, %%al;"       // al = x (multiplicand)
        "movb %2, %%bl;"       // bl = y (multiplier)
        "mulb %%bl;"           // ax = al * bl
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "al", "bl", "ax"     // clobbered registers
    );

    return of;
}

// Check SETO version of OF
bool test_mul_AL_r8_OF(uint8_t x, uint8_t y) {
    unsigned char of = mul_AL_r8_return_OF(x, y);
    uint16_t result = (uint16_t)x * (uint16_t)y;
     if (result > 255) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//****************************************************************************
// AL,m8 */
unsigned char mul_AL_m8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val = y;  // value in memory

    __asm__ volatile (
        "movb %1, %%al;"       // Move x into AL
        "mulb %2;"             // F6 /4: AX = AL * [memory]
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH (with flags) into output
        : "=r"(ah)          // Output: flags
        : "r"(x), "m"(val)     // Inputs: x (for AL), memory operand
        : "al", "ah", "ax"     // Clobbered registers
    );

    return ah;
}

// Test function for CF flag
bool test_mul_AL_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = mul_AL_m8_return_flags(x, y);
    uint16_t result = (uint16_t)x * (uint16_t)y;

    if (result > 255) {
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char mul_AL_m8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val = y;  // Create memory operand
    
    __asm__ volatile (
        "movb %1, %%al;"       // al = x (multiplicand)
        "mulb %2;"             // AX = AL * [memory]
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "m"(val)     // Input operands: x, memory operand
        : "al", "ax"           // clobbered registers
    );

    return of;
}


bool test_mul_AL_m8_OF(uint8_t x, uint8_t y) {
    unsigned char of = mul_AL_m8_return_OF(x, y);
    uint16_t result = (uint16_t)x * (uint16_t)y;
    
    if (result > 255) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//********************************************************************** *
// 

unsigned char mul_REX_AL_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movb %1, %%al;"        // al = x (multiplicand) - MUST use AL!
        "movb %2, %%r8b;"       // r8b = y (multiplier in extended register)
        "mulb %%r8b;"           // REX.B + F6 E0: ax = al * r8b
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // store AH in output
        : "=r" (ah)             // output
        : "r" (x), "r" (y)      // inputs: x, y
        : "al", "r8", "ah", "ax"  // clobbered registers
    );

    return ah;
}


// Check property for CF (Carry Flag)

bool test_mul_REX_AL_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = mul_REX_AL_r8_return_flags(x, y);
    uint16_t result = (uint16_t)x * (uint16_t)y;

    if (result > 255) {  // Result doesn't fit in 8 bits
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {             // Result fits in 8 bits
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char mul_REX_AL_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    
    __asm__ volatile (
        "movb %1, %%al;"       // al = x (multiplicand)
        "movb %2, %%r8b;"       // bl = y (multiplier)
        "mulb %%r8b;"           // ax = al * bl
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "al", "r8", "ax"     // clobbered registers
    );

    return of;
}

// Check SETO version of OF
bool test_mul_REX_AL_r8_OF(uint8_t x, uint8_t y) {
    unsigned char of = mul_REX_AL_r8_return_OF(x, y);
    uint16_t result = (uint16_t)x * (uint16_t)y;
     if (result > 255) {
        return of == 1;
    } else {
        return of == 0;
    }
}
//*****************************************************************8
// REX AL,M8 
unsigned char mul_REX_AL_m8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val = y;  // value in memory

    __asm__ volatile (
        "movb %1, %%al;"       // Move x into AL (CRITICAL: must use AL!)
        "mulb %2;"             // REX + F6 /4: AX = AL * [memory]
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH (with flags) into output
        : "=r"(ah)             // Output: flags
        : "r"(x), "m"(val)     // Inputs: x (for AL), memory operand
        : "al", "ah", "ax", "r8"  // Clobbered registers (added r8 if REX affects it)
    );

    return ah;
}

// Test function for CF flag
bool test_mul_REX_AL_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = mul_REX_AL_m8_return_flags(x, y);
    uint16_t result = (uint16_t)x * (uint16_t)y;

    if (result > 255) {
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char mul_REX_AL_m8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val = y;  // Create memory operand
    
    __asm__ volatile (
        "movb %1, %%al;"       // al = x (multiplicand)
        "mulb %2;"             // AX = AL * [memory]
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "m"(val)     // Input operands: x, memory operand
        : "al", "ax","r8"          // clobbered registers
    );

    return of;
}

// Check SETO version of OF
bool test_mul_REX_AL_m8_OF(uint8_t x, uint8_t y) {
    unsigned char of = mul_REX_AL_m8_return_OF(x, y);
    uint16_t result = (uint16_t)x * (uint16_t)y;
    
    if (result > 255) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//***********************************************************************************
//  AX,R16

unsigned char mul_AX_r16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movw %1, %%ax;"      // AX = x
        "movw %2, %%bx;"      // BX = y
        "mulw %%bx;"          // DX:AX = AX * BX
        "lahf;"               // Load status flags into AH
        "movb %%ah, %0;"      // Store flags in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "ax", "bx", "dx", "ah"
    );
    
    return ah;
}

bool test_mul_AX_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = mul_AX_r16_return_flags(x, y);
    uint32_t result = (uint32_t)x * (uint32_t)y;
    
    if (result > 0xFFFF) {
        return (flags & 0x01) == 0x01;  // Expect CF = 1
    } else {
        return (flags & 0x01) == 0x00;  // Expect CF = 0
    }
}

unsigned char mul_AX_r16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    
    __asm__ volatile (
        "movw %1, %%ax;"      // AX = x
        "movw %2, %%bx;"      // BX = y
        "mulw %%bx;"          // DX:AX = AX * BX
        "seto %0;"            // Set OF
        : "=r" (of)
        : "r" (x), "r" (y)
        : "ax", "bx", "dx"
    );
    
    return of;
}

bool test_mul_AX_r16_OF(uint16_t x, uint16_t y) {
    unsigned char of = mul_AX_r16_return_OF(x, y);
    uint32_t result = (uint32_t)x * (uint32_t)y;

    if (result > 0xFFFF) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//***********************************************************************
//  AX,M16

unsigned char mul_AX_m16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val = y;  

    __asm__ volatile (
        "movw %1, %%ax;"      // AX = x
        "mulw %2;"            // DX:AX = AX * [memory]
        "lahf;"               // Load flags
        "movb %%ah, %0;"      // Store flags
        : "=r" (ah)
        : "r" (x), "m" (val)
        : "ax", "dx", "ah"
    );

    return ah;
}

bool test_mul_AX_m16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = mul_AX_m16_return_flags(x, y);
    uint32_t result = (uint32_t)x * (uint32_t)y;

    if (result > 0xFFFF) {
        return (flags & 0x01) == 0x01;  // Expect CF = 1
    } else {
        return (flags & 0x01) == 0x00;  // Expect CF = 0
    }
}

unsigned char mul_AX_m16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    uint16_t val = y;

    __asm__ volatile (
        "movw %1, %%ax;"      // AX = x
        "mulw %2;"            // DX:AX = AX * [memory]
        "seto %0;"            // Set OF
        : "=r" (of)
        : "r" (x), "m" (val)
        : "ax", "dx"
    );

    return of;
}

bool test_mul_AX_m16_OF(uint16_t x, uint16_t y) {
    unsigned char of = mul_AX_m16_return_OF(x, y);
    uint32_t result = (uint32_t)x * (uint32_t)y;

    if (result > 0xFFFF) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//********************************************************************** 
// EAX,R32

unsigned char mul_EAX_r32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"     // EAX = x
        "movl %2, %%ebx;"     // EBX = y
        "mull %%ebx;"         // EDX:EAX = EAX * EBX (unsigned)
        "lahf;"               // Load status flags into AH
        "movb %%ah, %0;"      // Store flags in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "eax", "ebx", "edx", "ah"
    );

    return ah;
}

bool test_mul_EAX_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = mul_EAX_r32_return_flags(x, y);
    uint64_t result = (uint64_t)x * (uint64_t)y;

    if (result > 0xFFFFFFFF) {
        return (flags & 0x01) == 0x01;  // Expect CF = 1
    } else {
        return (flags & 0x01) == 0x00;  // Expect CF = 0
    }
}


// MUL with r/m32 and return OF using SETO
unsigned char mul_EAX_r32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"      // EAX = x (multiplicand)
        "mull %2;"             // EDX:EAX = EAX * y (multiplicand * multiplier)
        "seto %0;"             // Set OF into 'of'
        : "=r"(of)             // Output operand
        : "r"(x), "r"(y)       // Inputs: x (EAX), y (r/m32)
        : "eax", "edx"         // Clobbered registers
    );

    return of;
}

// Test overflow flag from 32-bit MUL
bool test_mul_EAX_r32_OF(uint32_t x, uint32_t y) {
    unsigned char of = mul_EAX_r32_return_OF(x, y);
    uint64_t result = (uint64_t)x * (uint64_t)y;

    // Overflow if result doesn't fit in 32 bits
    if (result > 0xFFFFFFFF) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//**********************************************************************************
//  EAX,m32

unsigned char mul_EAX_m32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val = y;

    __asm__ volatile (
        "movl %1, %%eax;"     // EAX = x
        "mull %2;"            // EDX:EAX = EAX * [memory]
        "lahf;"               // Load status flags into AH
        "movb %%ah, %0;"      // Return AH (contains flags)
        : "=r" (ah)
        : "r" (x), "m" (val)
        : "eax", "edx", "ah"
    );

    return ah;
}
bool test_mul_EAX_m32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = mul_EAX_m32_return_flags(x, y);
    uint64_t result = (uint64_t)x * (uint64_t)y;

    if (result > 0xFFFFFFFF) {
        return (flags & 0x01) == 0x01;  // CF = 1 expected
    } else {
        return (flags & 0x01) == 0x00;  // CF = 0 expected
    }
}

unsigned char mul_EAX_m32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
    uint32_t val = y;

    __asm__ volatile (
        "movl %1, %%eax;"     // EAX = x
        "mull %2;"            // EDX:EAX = EAX * [memory]
        "seto %0;"            // Set OF
        : "=r" (of)
        : "r" (x), "m" (val)
        : "eax", "edx"
    );

    return of;
}

bool test_mul_EAX_m32_OF(uint32_t x, uint32_t y) {
    unsigned char of = mul_EAX_m32_return_OF(x, y);
    uint64_t result = (uint64_t)x * (uint64_t)y;

    if (result > 0xFFFFFFFF) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//***************************************************************************
//  */

unsigned char mul_RAX_r64_return_flags(uint64_t x, uint64_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // RAX = x
        "movq %2, %%rbx;"      // RBX = y
        "mulq %%rbx;"          // RDX:RAX = RAX * RBX (unsigned)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH into output
        : "=r"(ah)             // Output operand
        : "r"(x), "r"(y)       // Inputs
        : "rax", "rbx", "rdx", "ah"  // Clobbered
    );

    return ah;
}

bool test_mul_RAX_r64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = mul_RAX_r64_return_flags(x, y);
    __uint128_t result = (__uint128_t)x * (__uint128_t)y;

    
    if ((result >> 64) != 0) {
        return (flags & 0x01) == 0x01;  // Expect CF = 1
    } else {
        return (flags & 0x01) == 0x00;  // Expect CF = 0
    }
}

unsigned char mul_RAX_r64_return_OF(uint64_t x, uint64_t y) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"      // RAX = x
        "movq %2, %%rbx;"      // RBX = y
        "mulq %%rbx;"          // RDX:RAX = RAX * RBX (unsigned)
        "seto %0;"             // OF set if upper 64 bits (RDX) ≠ 0
        : "=r"(of)             // Output operand
        : "r"(x), "r"(y)       // Inputs
        : "rax", "rbx", "rdx"  // Clobbered
    );

    return of;
}

bool test_mul_RAX_r64_OF(uint64_t x, uint64_t y) {
    unsigned char of = mul_RAX_r64_return_OF(x, y);
    __uint128_t result = (__uint128_t)x * (__uint128_t)y;

    if ((result >> 64) != 0) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//************************************************************************************
//  */

unsigned char mul_RAX_m64_return_flags(uint64_t x, uint64_t y) {
    unsigned char ah;
    uint64_t val = y; 

    __asm__ volatile (
        "movq %1, %%rax;"       // rax = x (multiplicand)
        "mulq %2;"              // F7 /4: rdx:rax = rax * [memory]
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH (flags) to output
        : "=r"(ah)              // output
        : "r"(x), "m"(val)      // inputs: x (register), y (memory)
        : "rax", "rdx", "ah"    // clobbered
    );

    return ah;
}
bool test_mul_RAX_m64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = mul_RAX_m64_return_flags(x, y);
    __uint128_t result = (__uint128_t)x * (__uint128_t)y;

    // CF=1 if upper 64 bits (RDX) are non-zero
    return ((result >> 64) > 0) ? ((flags & 0x01) == 0x01)
                                : ((flags & 0x01) == 0x00);
}

unsigned char mul_RAX_m64_return_OF(uint64_t x, uint64_t y) {
    unsigned char of;
    uint64_t val = y;

    __asm__ volatile (
        "movq %1, %%rax;"       // rax = x
        "mulq %2;"              // rdx:rax = rax * [mem]
        "seto %0;"              // OF -> 1 if overflow
        : "=r"(of)
        : "r"(x), "m"(val)
        : "rax", "rdx"
    );

    return of;
}

bool test_mul_RAX_m64_OF(uint64_t x, uint64_t y) {
    unsigned char of = mul_RAX_m64_return_OF(x, y);
    __uint128_t result = (__uint128_t)x * (__uint128_t)y;

   
    return ((result >> 64) > 0) ? (of == 1) : (of == 0);
}






// dummy main function, to allow us to link the executable
int main () { return 0;}