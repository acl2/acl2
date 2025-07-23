#include <stdbool.h>
#include <stdint.h>

uint8_t calculate_parity(uint8_t value) {
    value ^= value >> 4;
    value ^= value >> 2;
    value ^= value >> 1;
    return (~value) & 0x01 ? 0x04 : 0x00;  // Return 0x04 if even parity
}

//***************************************************************
// AL,i8 

unsigned char and_AL_i8_return_CF(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // al = x 
        "andb $0x02, %%al;"    // al &= imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%al", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_AL_i8_CF(uint8_t x) {
    unsigned char flags = and_AL_i8_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_AL_i8_return_flags(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // al = x 
        "andb $0x02, %%al;"    // al &= imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%al", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_AL_i8_SF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_AL_i8_return_flags(x);

    if (result & 0x80) {  // Check if bit 7 is set
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_AL_i8_ZF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_AL_i8_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}


// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_AL_i8_PF(uint8_t x) {
    unsigned char flags = and_AL_i8_return_flags(x);
    
    uint8_t result = x & 0x02;  // AND operation
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char and_AL_i8_return_OF(uint8_t x) {
    unsigned char of;
    __asm__ volatile (
        "movb %1, %%al;"       // Load x into AL
        "andb $0x02, %%al;"    // al &= imm 
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x)               // Input operands
        : "%al"                // clobbered registers
    );

    return of;
}

// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_AL_i8_OF(uint8_t x) {
    unsigned char of = and_AL_i8_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}

//***************************************************
// AX,i16 


unsigned char and_AX_i16_return_CF(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x 
        "andw $0x0002, %%ax;"  // ax &= imm16 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_AX_i16_CF(uint16_t x) {
    unsigned char flags = and_AX_i16_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_AX_i16_return_flags(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x 
        "andw $0x0002, %%ax;"  // ax &= imm16 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_AX_i16_SF(uint16_t x) {
    uint16_t result = x & 0x0002;  // AND operation
    unsigned char flags = and_AX_i16_return_flags(x);

    if (result & 0x8000) {  // Check if bit 15 is set (16-bit sign bit)
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_AX_i16_ZF(uint16_t x) {
    uint16_t result = x & 0x0002;  // AND operation
    unsigned char flags = and_AX_i16_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_AX_i16_PF(uint16_t x) {
    unsigned char flags = and_AX_i16_return_flags(x);
    
    uint16_t result = x & 0x0002;  // AND operation
    uint8_t result_low_byte = result & 0xFF;  // Take only the low byte for parity
    uint8_t expected_parity = calculate_parity(result_low_byte);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char and_AX_i16_return_OF(uint16_t x) {
    unsigned char of;
    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "andw $0x0002, %%ax;"  // ax &= imm16 
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x)               // Input operands
        : "%ax"                // clobbered registers
    );

    return of;
}

// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_AX_i16_OF(uint16_t x) {
    unsigned char of = and_AX_i16_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}

//*************************************************************
// EAX,i16 

unsigned char and_EAX_i32_return_CF(uint32_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"         // eax = x
        "andl $0x00000002, %%eax;"// eax &= imm32
        "lahf;"                   // load flags into AH
        "movb %%ah, %0;"          // move AH to output variable
        : "=r" (ah)
        : "r" (x)
        : "%eax", "%ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_EAX_i32_CF(uint32_t x) {
    unsigned char flags = and_EAX_i32_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_EAX_i32_return_flags(uint32_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"
        "andl $0x00000002, %%eax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x)
        : "%eax", "%ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 31 of result
bool test_and_EAX_i32_SF(uint32_t x) {
    uint32_t result = x & 0x00000002;
    unsigned char flags = and_EAX_i32_return_flags(x);
    if (result & 0x80000000) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_EAX_i32_ZF(uint32_t x) {
    uint32_t result = x & 0x00000002;
    unsigned char flags = and_EAX_i32_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_EAX_i32_PF(uint32_t x) {
    unsigned char flags = and_EAX_i32_return_flags(x);
    uint32_t result = x & 0x00000002;
    uint8_t result_low_byte = result & 0xFF;
    uint8_t expected_parity = calculate_parity(result_low_byte);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_EAX_i32_return_OF(uint32_t x) {
    unsigned char of;
    __asm__ volatile (
        "movl %1, %%eax;"
        "andl $0x00000002, %%eax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%eax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_EAX_i32_OF(uint32_t x) {
    unsigned char of = and_EAX_i32_return_OF(x);
    return (of == 0);
}

//************************************************************
// RAX,i32 

unsigned char and_RAX_i32_return_CF(unsigned long long x) {
    unsigned char ah;
    __asm__ volatile (
        "movq %1, %%rax;"         // rax = x
        "andq $0x00000002, %%rax;"// eax &= imm32 (zero-extends to rax)
        "lahf;"                   // load flags into AH
        "movb %%ah, %0;"          // move AH to output variable
        : "=r" (ah)
        : "r" (x)
        : "rax", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_RAX_i32_CF(unsigned long long x) {
    unsigned char flags = and_RAX_i32_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_RAX_i32_return_flags(unsigned long long x) {
    unsigned char ah;
    __asm__ volatile (
        "movq %1, %%rax;"
        "andq $0x00000002, %%rax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x)
        : "rax", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 31 of result (since andl zero-extends)
bool test_and_RAX_i32_SF(unsigned long long x) {
    unsigned long long result = x & 0x00000002; // Only low 32 bits matter
    unsigned char flags = and_RAX_i32_return_flags(x);
    if (result & 0x80000000) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_RAX_i32_ZF(unsigned long long x) {
    unsigned long long result = x & 0x00000002;
    unsigned char flags = and_RAX_i32_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_RAX_i32_PF(unsigned long long x) {
    unsigned char flags = and_RAX_i32_return_flags(x);
     unsigned long long result= x & 0x00000002;
    uint8_t result_low_byte = result & 0xFF;
    uint8_t expected_parity = calculate_parity(result_low_byte);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_RAX_i32_return_OF(unsigned long long x) {
    unsigned char of;
    __asm__ volatile (
        "movq %1, %%rax;"
        "andq $0x00000002, %%rax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "rax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_RAX_i32_OF(unsigned long long x) {
    unsigned char of = and_RAX_i32_return_OF(x);
    return (of == 0);
}

//********************************************************
// r8,i8 

unsigned char and_r8_i8_return_CF(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // al = x 
        "andb $0x02, %%al;"    // al &= imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "al", "ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_r8_i8_CF(uint8_t x) {
    unsigned char flags = and_r8_i8_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_r8_i8_return_flags(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // al = x 
        "andb $0x02, %%al;"    // al &= imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "al", "ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_r8_i8_SF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_r8_i8_return_flags(x);

    if (result & 0x80) {  // Check if bit 7 is set
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_r8_i8_ZF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_r8_i8_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}


// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_r8_i8_PF(uint8_t x) {
    unsigned char flags = and_r8_i8_return_flags(x);
    
    uint8_t result = x & 0x02;  // AND operation
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char and_r8_i8_return_OF(uint8_t x) {
    unsigned char of;
    __asm__ volatile (
        "movb %1, %%al;"       // Load x into AL
        "andb $0x02, %%al;"    // al &= imm 
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x)               // Input operands
        : "al"                // clobbered registers
    );

    return of;
}

// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_r8_i8_OF(uint8_t x) {
    unsigned char of = and_r8_i8_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}

//******************************************************************
// m8,i8 

unsigned char and_m8_i8_return_CF(uint8_t x) {
    unsigned char ah;
    uint8_t val;

     __asm__ volatile (
        "movb %1, (%2);"        // store x in memory location
        "andb $0x02, (%2);"     // AND [memory], imm8
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)              // output
        : "r"(x), "r"(&val)     // inputs: x, memory address
        : "ah"                 // clobbered registers
    );
    
    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_m8_i8_CF(uint8_t x) {
    unsigned char flags = and_m8_i8_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_m8_i8_return_flags(uint8_t x) {
    unsigned char ah;
     uint8_t val;

        __asm__ volatile (
        "movb %1, (%2);"        // store x in memory location
        "andb $0x02, (%2);"     // AND [memory], imm8
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)              // output
        : "r"(x), "r"(&val)     // inputs: x, memory address
        : "ah"                 // clobbered registers
    );
    
    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_m8_i8_SF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_m8_i8_return_flags(x);

    if (result & 0x80) {  // Check if bit 7 is set
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_m8_i8_ZF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_m8_i8_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}


// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_m8_i8_PF(uint8_t x) {
    unsigned char flags = and_m8_i8_return_flags(x);
    
    uint8_t result = x & 0x02;  // AND operation
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char and_m8_i8_return_OF(uint8_t x) {
    unsigned char of;
    uint8_t val;
    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "andb $0x02, (%2);"    // AND [memory], imm8 (memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // outputs:
        : "r"(x), "r" (&val)    // inputs: memory address
        : 
        "cc" 
    );
    return of;
}


// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_m8_i8_OF(uint8_t x) {
    unsigned char of = and_m8_i8_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}
//**********************************************************
// REX R8,i8 

unsigned char and_REX_r8_i8_return_CF(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r8b;"      // R8B = x (forces REX prefix)
        "andb $0x02, %%r8b;"   // REX + 80 /4 ib: AND R8B, imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "r8", "ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_REX_r8_i8_CF(uint8_t x) {
    unsigned char flags = and_REX_r8_i8_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_REX_r8_i8_return_flags(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r9b;"      // R9B = x (forces REX prefix)
        "andb $0x02, %%r9b;"   // REX + 80 /4 ib: AND R9B, imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "r9", "ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_REX_r8_i8_SF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_REX_r8_i8_return_flags(x);

    if (result & 0x80) {  // Check if bit 7 is set
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_REX_r8_i8_ZF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_REX_r8_i8_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}


// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_REX_r8_i8_PF(uint8_t x) {
    unsigned char flags = and_REX_r8_i8_return_flags(x);
    
    uint8_t result = x & 0x02;  // AND operation
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char and_REX_r8_i8_return_OF(uint8_t x) {
    unsigned char of;
    __asm__ volatile (
        "movb %1, %%r10b;"     // R10B = x (forces REX prefix)
        "andb $0x02, %%r10b;"  // REX + 80 /4 ib: AND R10B, imm8
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x)               // Input operands
        : "%r10"               // clobbered registers
    );

    return of;
}

// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_REX_r8_i8_OF(uint8_t x) {
    unsigned char of = and_REX_r8_i8_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}

//*********************************************************
// REX m8,i8


unsigned char and_REX_m8_i8_return_CF(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movq %2, %%r9;"       // r9 = &val (memory address, forces REX prefix)
        "movb %1, (%%r9);"     // [r9] = x (store value in memory)
        "andb $0x02, (%%r9);"  // REX + 80 /4 ib: AND [R9], imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r"(ah)             // outputs
        : "r"(x), "r"(&val)    // inputs: value, address
        : "r9", "ah"           // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_REX_m8_i8_CF(uint8_t x) {
    unsigned char flags = and_REX_m8_i8_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_REX_m8_i8_return_flags(uint8_t x) {
    unsigned char ah;
     uint8_t val;
   __asm__ volatile (
        "movq %2, %%r9;"       // R8 = memory address (forces REX prefix)
        "movb %1, (%%r9);"      // [r9] = x
        "andb $0x02, (%%r9);"  // REX + 80 /4 ib: AND [R8], imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r"(ah)           // outputs: ah, memory constraint
        :  "r"(x), "r"(&val)            // inputs: memory address
        : "r9", "ah"         // clobbered registers
    );

    return ah;
}


// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_REX_m8_i8_SF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_REX_m8_i8_return_flags(x);

    if (result & 0x80) {  // Check if bit 7 is set
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_REX_m8_i8_ZF(uint8_t x) {
    uint8_t result = x & 0x02;  // AND operation
    unsigned char flags = and_REX_m8_i8_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}


// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_REX_m8_i8_PF(uint8_t x) {
    unsigned char flags = and_REX_m8_i8_return_flags(x);
    
    uint8_t result = x & 0x02;  // AND operation
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char and_REX_m8_i8_return_OF(uint8_t x) {
    unsigned char of;
    uint8_t val;
    __asm__ volatile (
        "movq %2, %%r10;"        // r10 = &val (memory address, forces REX prefix)
        "movb %1, (%%r10);"      // [r10] = x (store value in memory)
        "andb $0x02, (%%r10);"   // REX + 80 /4 ib: AND [r10], 0x02
        "seto %0;"               // Set OF to output
        : "=r"(of)
        : "r"(x), "r"(&val)      // inputs: value, address
        : "r10"                  // clobbered registers
    );
    return of;
} 

// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_REX_m8_i8_OF(uint8_t x) {
    unsigned char of = and_REX_m8_i8_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}


//**************************************************************************
// r16, i16 

unsigned char and_r16_i16_return_CF(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x 
        "andw $0x0002, %%ax;"  // ax &= imm16 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "ax", "ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_r16_i16_CF(uint16_t x) {
    unsigned char flags = and_r16_i16_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_r16_i16_return_flags(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x 
        "andw $0x0002, %%ax;"  // ax &= imm16 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "ax", "ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_r16_i16_SF(uint16_t x) {
    uint16_t result = x & 0x0002;  // AND operation
    unsigned char flags = and_r16_i16_return_flags(x);

    if (result & 0x8000) {  // Check if bit 15 is set (16-bit sign bit)
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_r16_i16_ZF(uint16_t x) {
    uint16_t result = x & 0x0002;  // AND operation
    unsigned char flags = and_r16_i16_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_r16_i16_PF(uint16_t x) {
    unsigned char flags = and_r16_i16_return_flags(x);
    
    uint16_t result = x & 0x0002;  // AND operation
    uint8_t result_low_byte = result & 0xFF;  // Take only the low byte for parity
    uint8_t expected_parity = calculate_parity(result_low_byte);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r16_i16_return_OF(uint16_t x) {
    unsigned char of;
    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "andw $0x0002, %%ax;"  // ax &= imm16 
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x)               // Input operands
        : "ax"                // clobbered registers
    );

    return of;
}

// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_r16_i16_OF(uint16_t x) {
    unsigned char of = and_r16_i16_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}


//**********************************************************************
// m16,i16 

unsigned char and_m16_i16_return_CF(uint16_t x) {
    unsigned char ah;
    uint16_t val;
        __asm__ volatile (
        "movw %1, (%2);"        // store x in memory location
        "andw $0x0002, (%2);"     // AND [memory], imm8
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)              // output
        : "r"(x), "r"(&val)     // inputs: x, memory address
        : "ah"                 // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_m16_i16_CF(uint16_t x) {
    unsigned char flags = and_m16_i16_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_m16_i16_return_flags(uint16_t x) {
    unsigned char ah;
    uint16_t val;

      __asm__ volatile (
        "movw %1, (%2);"        // store x in memory location
        "andw $0x0002, (%2);"     // AND [memory], imm8
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)              // output
        : "r"(x), "r"(&val)     // inputs: x, memory address
        : "%ah"                 // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_m16_i16_SF(uint16_t x) {
    uint16_t result = x & 0x0002;  // AND operation
    unsigned char flags = and_m16_i16_return_flags(x);

    if (result & 0x8000) {  // Check if bit 15 is set (16-bit sign bit)
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_m16_i16_ZF(uint16_t x) {
    uint16_t result = x & 0x0002;  // AND operation
    unsigned char flags = and_m16_i16_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_m16_i16_PF(uint16_t x) {
    unsigned char flags = and_m16_i16_return_flags(x);
    
    uint16_t result = x & 0x0002;  // AND operation
    uint8_t result_low_byte = result & 0xFF;  // Take only the low byte for parity
    uint8_t expected_parity = calculate_parity(result_low_byte);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m16_i16_return_OF(uint16_t x) {
    unsigned char of;
       uint16_t val;
    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "andw $0x0002, (%2);"    // AND [memory], imm8 (memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // outputs:
        : "r"(x), "r" (&val)    // inputs: memory address
        : 
        "cc" 
    );
    return of;
}



// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_m16_i16_OF(uint16_t x) {
    unsigned char of = and_m16_i16_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}

//**************************************************************88
// R32,i32 


unsigned char and_r32_i32_return_CF(uint32_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"         // eax = x
        "andl $0x00000002, %%eax;"// eax &= imm32
        "lahf;"                   // load flags into AH
        "movb %%ah, %0;"          // move AH to output variable
        : "=r" (ah)
        : "r" (x)
        : "eax", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r32_i32_CF(uint32_t x) {
    unsigned char flags = and_r32_i32_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r32_i32_return_flags(uint32_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"
        "andl $0x00000002, %%eax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x)
        : "eax", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 31 of result
bool test_and_r32_i32_SF(uint32_t x) {
    uint32_t result = x & 0x00000002;
    unsigned char flags = and_r32_i32_return_flags(x);
    if (result & 0x80000000) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r32_i32_ZF(uint32_t x) {
    uint32_t result = x & 0x00000002;
    unsigned char flags = and_r32_i32_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_r32_i32_PF(uint32_t x) {
    unsigned char flags = and_r32_i32_return_flags(x);
    uint32_t result = x & 0x00000002;
    uint8_t result_low_byte = result & 0xFF;
    uint8_t expected_parity = calculate_parity(result_low_byte);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r32_i32_return_OF(uint32_t x) {
    unsigned char of;
    __asm__ volatile (
        "movl %1, %%eax;"
        "andl $0x00000002, %%eax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "eax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r32_i32_OF(uint32_t x) {
    unsigned char of = and_r32_i32_return_OF(x);
    return (of == 0);
}

//********************************************* 

unsigned char and_m32_i32_return_CF(uint32_t x) {
    unsigned char ah;
    uint32_t val;
    __asm__ volatile (
        "movl %1, (%2);"        // store x in memory location
        "andl $0x00000002, (%2);" // AND [memory], imm32
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)              // output
        : "r"(x), "r"(&val)     // inputs: x, memory address
        : "ah"                 // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// For AND operations, CF is always cleared (set to 0)
bool test_and_m32_i32_CF(uint32_t x) {
    unsigned char flags = and_m32_i32_return_CF(x);
    
    // CF is always 0 for AND operations
    return ((flags & 0x01) == 0x00);  // Expect CF = 0 always
}

unsigned char and_m32_i32_return_flags(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"        // store x in memory location
        "andl $0x00000002, (%2);" // AND [memory], imm32
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)              // output
        : "r"(x), "r"(&val)     // inputs: x, memory address
        : "ah"                 // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_and_m32_i32_SF(uint32_t x) {
    uint32_t result = x & 0x00000002;  // AND operation
    unsigned char flags = and_m32_i32_return_flags(x);

    if (result & 0x80000000) {  // Check if bit 31 is set (32-bit sign bit)
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_and_m32_i32_ZF(uint32_t x) {
    uint32_t result = x & 0x00000002;  // AND operation
    unsigned char flags = and_m32_i32_return_flags(x);

    if (result == 0) {  // Zero result
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_and_m32_i32_PF(uint32_t x) {
    unsigned char flags = and_m32_i32_return_flags(x);
    
    uint32_t result = x & 0x00000002;  // AND operation
    uint8_t result_low_byte = result & 0xFF;  // Take only the low byte for parity
    uint8_t expected_parity = calculate_parity(result_low_byte);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m32_i32_return_OF(uint32_t x) {
    unsigned char of;
    uint32_t val;
    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "andl $0x00000002, (%2);" // AND [memory], imm32
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // outputs:
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :
         "cc"                 // clobber condition codes
    );
    return of;
}


// Check property for OF
// For AND operations, OF is always cleared (set to 0)
bool test_and_m32_i32_OF(uint32_t x) {
    unsigned char of = and_m32_i32_return_OF(x);
    
    // OF is always 0 for AND operations
    return (of == 0);  // Expect OF = 0 always
}

//*************************************************************************
// r64,i32 


unsigned char and_R64__i32_return_CF(unsigned long long x) {
    unsigned char ah;
    __asm__ volatile (
        "movq %1, %%rax;"         // R64_ = x
        "andq $0x00000002, %%rax;"// eax &= imm32 (zero-extends to R64_)
        "lahf;"                   // load flags into AH
        "movb %%ah, %0;"          // move AH to output variable
        : "=r" (ah)
        : "r" (x)
        : "%rax", "%ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_R64__i32_CF(unsigned long long x) {
    unsigned char flags = and_R64__i32_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_R64__i32_return_flags(unsigned long long x) {
    unsigned char ah;
    __asm__ volatile (
        "movq %1, %%rax;"
        "andq $0x00000002, %%rax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x)
        : "%rax", "%ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 31 of result (since andl zero-extends)
bool test_and_R64__i32_SF(unsigned long long x) {
    unsigned long long  result = x & 0x00000002; // Only low 32 bits matter
    unsigned char flags = and_R64__i32_return_flags(x);
    if (result & 0x80000000) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_R64__i32_ZF(unsigned long long x) {
    unsigned long long result = x & 0x00000002;  // 
    unsigned char flags = and_R64__i32_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_R64__i32_PF(unsigned long long x) {
    unsigned char flags = and_R64__i32_return_flags(x);
     unsigned long long result = x & 0x00000002; 
    uint8_t result_low_byte = result & 0xFF;
    uint8_t expected_parity = calculate_parity(result_low_byte);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_R64__i32_return_OF(unsigned long long x) {
    unsigned char of;
    __asm__ volatile (
        "movq %1, %%rax;"
        "andq $0x00000002, %%rax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "rax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_R64__i32_OF(unsigned long long x) {
    unsigned char of = and_R64__i32_return_OF(x);
    return (of == 0);
}

//**********************************************************88
// m64,i32 */
   unsigned char and_m64_i32_return_CF(unsigned long long x) {
    unsigned char ah;
    unsigned long long val;

    __asm__ volatile (
        "movq %1, %%r9;"
        "movq %2, (%%r9);"
        "andq $0x00000002, (%%r9);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(&val), "r"(x)
        : "r9", "ah", "memory"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_m64_i32_CF(unsigned long long x) {
    unsigned char flags = and_m64_i32_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_m64_i32_return_flags(unsigned long long x) {
    unsigned char ah;
     unsigned long long val;

    __asm__ volatile (
        "movq %1, %%r9;"
        "movq %2, (%%r9);"
        "andq $0x00000002, (%%r9);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(&val), "r"(x)
        : "r9", "ah"
    );
    return ah;
}


// SF: bit 7 in ah, reflects bit 31 of result (since andl zero-extends)
bool test_and_m64_i32_SF(unsigned long long x) {
    unsigned long long result = x & 0x00000002; // Only low 32 bits matter
    unsigned char flags = and_m64_i32_return_flags(x);
    if (result & 0x80000000) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_m64_i32_ZF(unsigned long long x) {
    unsigned long long result = x  & 0x00000002;
    unsigned char flags = and_m64_i32_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte

bool test_and_m64_i32_PF(unsigned long long x) {
    unsigned char flags = and_m64_i32_return_flags(x);
    unsigned long long result = x & 0x00000002;  
    uint8_t result_low_byte = result & 0xFF;
    uint8_t expected_parity = calculate_parity(result_low_byte);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m64_i32_return_OF(unsigned long long x) {
    unsigned char of;
      unsigned long long val;
 __asm__ volatile (
        "movq %1, %%r9;"
        "movq %2, (%%r9);"
        "andq $0x00000002, (%%r9);"
        "seto %0;"
        : "=r"(of)
        : "r"(&val), "r"(x)
        : "r9"
    );

    return of;
}

// OF is always 0 for AND
bool test_and_m64_i32_OF(unsigned long long x) {
    unsigned char of = and_m64_i32_return_OF(x);
    return (of == 0);
}

//***********************************************************************
// AND r16,i8 

unsigned char and_r16_i8_return_CF(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"        // Load x into AX
        "andw $0x02, %%ax;"     // AND AL with imm8 (only low byte affected)
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Extract AH
        : "=r" (ah)
        : "r" (x)
        : "ax", "%ah"
    );

    return ah;
}
    

// CF is always 0 for AND
bool test_and_r16_i8_CF(uint16_t x) {
    unsigned char flags = and_r16_i8_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r16_i8_return_flags(uint16_t x) {
    unsigned char ah;

      __asm__ volatile (
        "movw %1, %%ax;"        // Load x into AX
        "andw $0x02, %%ax;"     // AND AL with imm8 (only low byte affected)
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Extract AH
        : "=r" (ah)
        : "r" (x)
        : "ax", "%ah"
    );

    return ah;
}
  

// SF: bit 7 in ah, reflects bit 7 of result (since andb is 8-bit)
bool test_and_r16_i8_SF(uint16_t x) {
    uint8_t result = x & 0x02;  // Only low byte ANDed
    unsigned char flags = and_r16_i8_return_flags(x);
    if (result & 0x80) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r16_i8_ZF(uint16_t x) {
    uint8_t result = x & 0x02;
    unsigned char flags = and_r16_i8_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_r16_i8_PF(uint16_t x) {
    unsigned char flags = and_r16_i8_return_flags(x);
    uint8_t result = x & 0x02;
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r16_i8_return_OF(uint16_t x) {
    unsigned char of;
    __asm__ volatile (
        "movw %1, %%ax;"
        "andw $0x02, %%ax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "ax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r16_i8_OF(uint16_t x) {
    unsigned char of = and_r16_i8_return_OF(x);
    return (of == 0);
}

//**********************************************************8
// m16,i8 

unsigned char and_m16_i8_return_CF(uint16_t x) {
    unsigned char ah;
    uint16_t val;
    __asm__ volatile (
        "movw %1, (%2);"           // store x into memory
        "andw $0x02, (%2);"        // AND imm8 (zero-extended or sign-extended to 16-bit)
        "lahf;"                    // load flags
        "movb %%ah, %0;"           // store flags
        : "=r"(ah)
        : "r"(x), "r"(&val)
        :  "ah"
    );

    return ah;
}

// CF is always 0 for AND
bool test_and_m16_i8_CF(uint16_t x) {
    unsigned char flags = and_m16_i8_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_m16_i8_return_flags(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"           // store x into memory
        "andw $0x02, (%2);"        // AND imm8 (zero-extended or sign-extended to 16-bit)
        "lahf;"                    // load flags
        "movb %%ah, %0;"           // store flags
        : "=r"(ah)
        : "r"(x), "r"(&val)
        :  "ah"
    );

    return ah;
}
       

// SF: bit 7 in ah, reflects bit 7 of result (since andb is 8-bit)
bool test_and_m16_i8_SF(uint16_t x) {
    uint8_t result = x & 0x02;  // Only low byte ANDed
    unsigned char flags = and_m16_i8_return_flags(x);
    if (result & 0x80) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_m16_i8_ZF(uint16_t x) {
    uint8_t result = x & 0x02;
    unsigned char flags = and_m16_i8_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_m16_i8_PF(uint16_t x) {
    unsigned char flags = and_m16_i8_return_flags(x);
    uint16_t result = x & 0x02;
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m16_i8_return_OF(uint16_t x) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"         // store x in memory location
        "andw $0x02, (%2);"      // AND [mem16], imm8 (sign-extended)
        "seto %0;"               // set OF flag into result
        : "=r"(of)
        : "r"(x), "r"(&val)
        : 
         "cc"
    );

    return of;
}

// OF is always 0 for AND
bool test_and_m16_i8_OF(uint16_t x) {
    unsigned char of = and_m16_i8_return_OF(x);
    return (of == 0);
}


//******************************************************
// r32,i8 

unsigned char and_r32_i8_return_CF(uint32_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"       // eax = x
        "andl $0x02, %%eax;"     // eax &= imm8
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r" (ah)
        : "r" (x)
        : "eax", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r32_i8_CF(uint32_t x) {
    unsigned char flags = and_r32_i8_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r32_i8_return_flags(uint32_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"
        "andl $0x02, %%eax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x)
        : "eax", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 7 of result (since andb is 8-bit)
bool test_and_r32_i8_SF(uint32_t x) {
    uint32_t result = x & 0x02;  // Only low byte ANDed
    unsigned char flags = and_r32_i8_return_flags(x);
    if (result & 0x80) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r32_i8_ZF(uint32_t x) {
    uint32_t result = x & 0x02;
    unsigned char flags = and_r32_i8_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_r32_i8_PF(uint32_t x) {
    unsigned char flags = and_r32_i8_return_flags(x);
    uint8_t result = x & 0x02;
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r32_i8_return_OF(uint32_t x) {
    unsigned char of;
    __asm__ volatile (
        "movl %1, %%eax;"
        "andl $0x02, %%eax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "eax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r32_i8_OF(uint32_t x) {
    unsigned char of = and_r32_i8_return_OF(x);
    return (of == 0);
}

//***************************************************************
// m32,i8 

//*******************************************************************
// m32,i8

unsigned char and_m32_i8_return_CF(uint32_t x) {
    unsigned char ah;
    uint32_t val;
    __asm__ volatile (
        "movl %1, (%2);"        // store x in memory location
        "andl $0x02, (%2);"     // AND [memory], imm8 (sign-extended to 32-bit)
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r"(&val)
        : "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_m32_i8_CF(uint32_t x) {
    unsigned char flags = and_m32_i8_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_m32_i8_return_flags(uint32_t x) {
    unsigned char ah;
    uint32_t val;
    __asm__ volatile (
        "movl %1, (%2);"
        "andl $0x02, (%2);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x), "r"(&val)
        : "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 31 of result (32-bit operation)
bool test_and_m32_i8_SF(uint32_t x) {
    uint32_t result = x & 0x02;  // 8-bit imm sign-extended to 32-bit
    unsigned char flags = and_m32_i8_return_flags(x);
    if (result & 0x80000000) {  // Check bit 31 for 32-bit operation
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_m32_i8_ZF(uint32_t x) {
    uint32_t result = x & 0x02;
    unsigned char flags = and_m32_i8_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_m32_i8_PF(uint32_t x) {
    unsigned char flags = and_m32_i8_return_flags(x);
    uint8_t result = x & 0x02;  // Low 8 bits for parity
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m32_i8_return_OF(uint32_t x) {
    unsigned char of;
    uint32_t val;
    __asm__ volatile (
        "movl %1, (%2);"
        "andl $0x02, (%2);"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(&val)
        :
    );
    return of;
}

// OF is always 0 for AND
bool test_and_m32_i8_OF(uint32_t x) {
    unsigned char of = and_m32_i8_return_OF(x);
    return (of == 0);
}

//*******************************************************************
// r64,i8 */

unsigned char and_r64_i8_return_CF(unsigned long long x) {
    unsigned char ah;
    __asm__ volatile (
        "movq %1, %%rax;"       // rax = x
        "andq $0x02, %%rax;"    // rax &= imm8 (sign-extended to 64-bit)
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r" (ah)
        : "r" (x)
        : "rax", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r64_i8_CF(unsigned long long x) {
    unsigned char flags = and_r64_i8_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r64_i8_return_flags(unsigned long long x) {
    unsigned char ah;
    __asm__ volatile (
        "movq %1, %%rax;"
        "andq $0x02, %%rax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x)
        : "rax", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 63 of 64-bit result
bool test_and_r64_i8_SF(unsigned long long x) {
    unsigned long long result = x & 0x02;  // 8-bit imm sign-extended to 64-bit
    unsigned char flags = and_r64_i8_return_flags(x);
    if (result & 0x8000000000000000ULL) {  // Check bit 63
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r64_i8_ZF(unsigned long long x) {
    unsigned long long result = x & 0x02;
    unsigned char flags = and_r64_i8_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_r64_i8_PF(unsigned long long x) {
    unsigned char flags = and_r64_i8_return_flags(x);
    uint8_t result = x & 0x02;  // Low 8 bits for parity
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r64_i8_return_OF(unsigned long long x) {
    unsigned char of;
    __asm__ volatile (
        "movq %1, %%rax;"
        "andq $0x02, %%rax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "rax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r64_i8_OF(unsigned long long x) {
    unsigned char of = and_r64_i8_return_OF(x);
    return (of == 0);
}

//*********************************************************************
// m64,i8 
unsigned char and_m64_i8_return_CF(unsigned long long x) {
    unsigned char ah;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, (%2);"        // store x in memory location
        "andq $0x02, (%2);"     // AND [memory], imm8 (sign-extended)
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(&val)
        : "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_m64_i8_CF(unsigned long long x) {
    unsigned char flags = and_m64_i8_return_CF(x);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_m64_i8_return_flags(unsigned long long x) {
    unsigned char ah;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, (%2);"
        "andq $0x02, (%2);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(&val)
        : "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 63 of 64-bit result
bool test_and_m64_i8_SF(unsigned long long x) {
    unsigned result = x & 0x02;  // 8-bit imm sign-extended to 64-bit
    unsigned char flags = and_m64_i8_return_flags(x);
    if (result & 0x8000000000000000ULL) {  // Check bit 63
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_m64_i8_ZF(unsigned long long x) {
    unsigned long long result = x & 0x02;
    unsigned char flags = and_m64_i8_return_flags(x);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low byte
bool test_and_m64_i8_PF(unsigned long long x) {
    unsigned char flags = and_m64_i8_return_flags(x);
    uint8_t result = x & 0x02;  // Low 8 bits for parity
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m64_i8_return_OF(unsigned long long x) {
    unsigned char of;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, (%2);"
        "andq $0x02, (%2);"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(&val)
        :
        "cc"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_m64_i8_OF(unsigned long long x) {
    unsigned char of = and_m64_i8_return_OF(x);
    return (of == 0);
}

//*********************************************************************8
// r8,r8 
unsigned char and_r8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movb %1, %%al;"        // al = x (destination)
        "movb %2, %%bl;"        // bl = y (source)
        "andb %%bl, %%al;"      // al = al AND bl
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "al", "bl", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = and_r8_r8_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movb %1, %%al;"
        "movb %2, %%bl;"
        "andb %%bl, %%al;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "al", "bl", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 7 of 8-bit result
bool test_and_r8_r8_SF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_r8_r8_return_flags(x, y);
    if (result & 0x80) {  // Check bit 7 of 8-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r8_r8_ZF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_r8_r8_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of full 8-bit result
bool test_and_r8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = and_r8_r8_return_flags(x, y);
    uint8_t result = x & y;
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    __asm__ volatile (
        "movb %1, %%al;"
        "movb %2, %%bl;"
        "andb %%bl, %%al;"
        "seto %0;"
        : "=r"(of)
        : "r" (x), "r" (y)
        : "al", "bl"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r8_r8_OF(uint8_t x, uint8_t y) {
    unsigned char of = and_r8_r8_return_OF(x, y);
    return (of == 0);
}

//*****************************************************************
// M8,R8 

unsigned char and_m8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    __asm__ volatile (
        "movb %1, (%3);"        // store x in memory location (destination)
        "movb %2, %%bl;"        // bl = y (source register)
        "andb %%bl, (%3);"      // [memory] = [memory] AND bl
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "bl", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_m8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = and_m8_r8_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_m8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    __asm__ volatile (
        "movb %1, (%3);"
        "movb %2, %%bl;"
        "andb %%bl, (%3);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "bl", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 7 of 8-bit result
bool test_and_m8_r8_SF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_m8_r8_return_flags(x, y);
    if (result & 0x80) {  // Check bit 7 of 8-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_m8_r8_ZF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_m8_r8_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of full 8-bit result
bool test_and_m8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = and_m8_r8_return_flags(x, y);
    uint8_t result = x & y;
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;
    __asm__ volatile (
        "movb %1, (%3);"
        "movb %2, %%bl;"
        "andb %%bl, (%3);"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "bl"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_m8_r8_OF(uint8_t x, uint8_t y) {
    unsigned char of = and_m8_r8_return_OF(x, y);
    return (of == 0);
}

//********************************************************888
// rex r8,r8 

unsigned char and_REX_r8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movb %1, %%r8b;"       // r8b = x (destination, extended register)
        "movb %2, %%r9b;"       // r9b = y (source, extended register)
        "andb %%r9b, %%r8b;"    // r8b = r8b AND r9b
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "r8", "r9", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_REX_r8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = and_REX_r8_r8_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_REX_r8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movb %1, %%r8b;"
        "movb %2, %%r9b;"
        "andb %%r9b, %%r8b;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "r8", "r9", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 7 of 8-bit result
bool test_and_REX_r8_r8_SF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_REX_r8_r8_return_flags(x, y);
    if (result & 0x80) {  // Check bit 7 of 8-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_REX_r8_r8_ZF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_REX_r8_r8_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of full 8-bit result
bool test_and_REX_r8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = and_REX_r8_r8_return_flags(x, y);
    uint8_t result = x & y;
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_REX_r8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    __asm__ volatile (
        "movb %1, %%r8b;"
        "movb %2, %%r9b;"
        "andb %%r9b, %%r8b;"
        "seto %0;"
        : "=r"(of)
        : "r" (x), "r" (y)
        : "r8", "r9"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_REX_r8_r8_OF(uint8_t x, uint8_t y) {
    unsigned char of = and_REX_r8_r8_return_OF(x, y);
    return (of == 0);
}

//********************************************************************
// REX M8,R8 

unsigned char and_REX_m8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    __asm__ volatile (
        "movb %1, (%3);"        // store x in memory location (destination)
        "movb %2, %%r9b;"       // r9b = y (source, extended register)
        "andb %%r9b, (%3);"     // [memory] = [memory] AND r9b
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "r9", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_REX_m8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = and_REX_m8_r8_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_REX_m8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    __asm__ volatile (
        "movb %1, (%3);"
        "movb %2, %%r9b;"
        "andb %%r9b, (%3);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "r9", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 7 of 8-bit result
bool test_and_REX_m8_r8_SF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_REX_m8_r8_return_flags(x, y);
    if (result & 0x80) {  // Check bit 7 of 8-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_REX_m8_r8_ZF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_REX_m8_r8_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of full 8-bit result
bool test_and_REX_m8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = and_REX_m8_r8_return_flags(x, y);
    uint8_t result = x & y;
    uint8_t expected_parity = calculate_parity(result);
    return (flags & 0x04) == expected_parity;
}

unsigned char and_REX_m8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;
    __asm__ volatile (
        "movb %1, (%3);"
        "movb %2, %%r9b;"
        "andb %%r9b, (%3);"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "r9"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_REX_m8_r8_OF(uint8_t x, uint8_t y) {
    unsigned char of = and_REX_m8_r8_return_OF(x, y);
    return (of == 0);
}

//******************************************************************
// R16,R16 

unsigned char and_r16_r16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movw %1, %%ax;"        // ax = x (destination)
        "movw %2, %%bx;"        // bx = y (source)
        "andw %%bx, %%ax;"      // ax = ax AND bx
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "ax", "bx", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r16_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = and_r16_r16_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r16_r16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movw %1, %%ax;"
        "movw %2, %%bx;"
        "andw %%bx, %%ax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "ax", "bx", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 15 of 16-bit result
bool test_and_r16_r16_SF(uint16_t x, uint16_t y) {
    uint16_t result = x & y;
    unsigned char flags = and_r16_r16_return_flags(x, y);
    if (result & 0x8000) {  // Check bit 15 of 16-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r16_r16_ZF(uint16_t x, uint16_t y) {
    uint16_t result = x & y;
    unsigned char flags = and_r16_r16_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_r16_r16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = and_r16_r16_return_flags(x, y);
    uint16_t result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 16-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r16_r16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    __asm__ volatile (
        "movw %1, %%ax;"
        "movw %2, %%bx;"
        "andw %%bx, %%ax;"
        "seto %0;"
        : "=r"(of)
        : "r" (x), "r" (y)
        : "ax", "bx"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r16_r16_OF(uint16_t x, uint16_t y) {
    unsigned char of = and_r16_r16_return_OF(x, y);
    return (of == 0);
}
//******************************************************************
// M16,R16 

unsigned char and_m16_r16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;
    __asm__ volatile (
        "movw %1, (%3);"        // store x in memory location (destination)
        "movw %2, %%bx;"        // bx = y (source register)
        "andw %%bx, (%3);"      // [memory] = [memory] AND bx
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "bx", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_m16_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = and_m16_r16_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_m16_r16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;
    __asm__ volatile (
        "movw %1, (%3);"
        "movw %2, %%bx;"
        "andw %%bx, (%3);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "bx", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 15 of 16-bit result
bool test_and_m16_r16_SF(uint16_t x, uint16_t y) {
    uint16_t result = x & y;
    unsigned char flags = and_m16_r16_return_flags(x, y);
    if (result & 0x8000) {  // Check bit 15 of 16-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_m16_r16_ZF(uint16_t x, uint16_t y) {
    uint16_t result = x & y;
    unsigned char flags = and_m16_r16_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_m16_r16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = and_m16_r16_return_flags(x, y);
    uint16_t result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 16-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m16_r16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    uint16_t val;
    __asm__ volatile (
        "movw %1, (%3);"
        "movw %2, %%bx;"
        "andw %%bx, (%3);"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "bx"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_m16_r16_OF(uint16_t x, uint16_t y) {
    unsigned char of = and_m16_r16_return_OF(x, y);
    return (of == 0);
}

//*********************************************************************
// R32,R32 

unsigned char and_r32_r32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"       // eax = x (destination)
        "movl %2, %%ebx;"       // ebx = y (source)
        "andl %%ebx, %%eax;"    // eax = eax AND ebx
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "eax", "ebx", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r32_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = and_r32_r32_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r32_r32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"
        "movl %2, %%ebx;"
        "andl %%ebx, %%eax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "eax", "ebx", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 31 of 32-bit result
bool test_and_r32_r32_SF(uint32_t x, uint32_t y) {
    uint32_t result = x & y;
    unsigned char flags = and_r32_r32_return_flags(x, y);
    if (result & 0x80000000) {  // Check bit 31 of 32-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r32_r32_ZF(uint32_t x, uint32_t y) {
    uint32_t result = x & y;
    unsigned char flags = and_r32_r32_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_r32_r32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = and_r32_r32_return_flags(x, y);
    uint32_t result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 32-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r32_r32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
    __asm__ volatile (
        "movl %1, %%eax;"
        "movl %2, %%ebx;"
        "andl %%ebx, %%eax;"
        "seto %0;"
        : "=r"(of)
        : "r" (x), "r" (y)
        : "eax", "ebx"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r32_r32_OF(uint32_t x, uint32_t y) {
    unsigned char of = and_r32_r32_return_OF(x, y);
    return (of == 0);
}


//***************************************************************
// m32,r32 

unsigned char and_m32_r32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;
    __asm__ volatile (
        "movl %1, (%3);"        // store x in memory location (destination)
        "movl %2, %%ebx;"       // ebx = y (source register)
        "andl %%ebx, (%3);"     // [memory] = [memory] AND ebx
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "ebx", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_m32_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = and_m32_r32_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_m32_r32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;
    __asm__ volatile (
        "movl %1, (%3);"
        "movl %2, %%ebx;"
        "andl %%ebx, (%3);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "ebx", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 31 of 32-bit result
bool test_and_m32_r32_SF(uint32_t x, uint32_t y) {
    uint32_t result = x & y;
    unsigned char flags = and_m32_r32_return_flags(x, y);
    if (result & 0x80000000) {  // Check bit 31 of 32-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_m32_r32_ZF(uint32_t x, uint32_t y) {
    uint32_t result = x & y;
    unsigned char flags = and_m32_r32_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_m32_r32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = and_m32_r32_return_flags(x, y);
    uint32_t result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 32-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m32_r32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
    uint32_t val;
    __asm__ volatile (
        "movl %1, (%3);"
        "movl %2, %%ebx;"
        "andl %%ebx, (%3);"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "ebx"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_m32_r32_OF(uint32_t x, uint32_t y) {
    unsigned char of = and_m32_r32_return_OF(x, y);
    return (of == 0);
}

//***************************************************************
// r64,r64 

unsigned char and_r64_r64_return_CF(unsigned long long x, unsigned long long y) {
    unsigned char ah;
    __asm__ volatile (
        "movq %1, %%rax;"       // rax = x (destination)
        "movq %2, %%rbx;"       // rbx = y (source)
        "andq %%rbx, %%rax;"    // rax = rax AND rbx
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "rax", "rbx", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r64_r64_CF(unsigned long long x, unsigned long long y) {
    unsigned char flags = and_r64_r64_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r64_r64_return_flags(unsigned long long x, unsigned long long y) {
    unsigned char ah;
    __asm__ volatile (
        "movq %1, %%rax;"
        "movq %2, %%rbx;"
        "andq %%rbx, %%rax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "rax", "rbx", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 63 of 64-bit result
bool test_and_r64_r64_SF(unsigned long long x, unsigned long long y) {
    unsigned long long result = x & y;
    unsigned char flags = and_r64_r64_return_flags(x, y);
    if (result & 0x8000000000000000ULL) {  // Check bit 63 of 64-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r64_r64_ZF(unsigned long long x, unsigned long long y) {
    unsigned long long result = x & y;
    unsigned char flags = and_r64_r64_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_r64_r64_PF(unsigned long long x, unsigned long long y) {
    unsigned char flags = and_r64_r64_return_flags(x, y);
    unsigned long long result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 64-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r64_r64_return_OF(unsigned long long x, unsigned long long y) {
    unsigned char of;
    __asm__ volatile (
        "movq %1, %%rax;"
        "movq %2, %%rbx;"
        "andq %%rbx, %%rax;"
        "seto %0;"
        : "=r"(of)
        : "r" (x), "r" (y)
        : "rax", "rbx"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r64_r64_OF(unsigned long long x, unsigned long long y) {
    unsigned char of = and_r64_r64_return_OF(x, y);
    return (of == 0);
}
//******************************************************************
// m64,r64 

unsigned char and_m64_r64_return_CF(unsigned long long x, unsigned long long y) {
    unsigned char ah;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, (%3);"        // store x in memory location (destination)
        "movq %2, %%rbx;"       // rbx = y (source register)
        "andq %%rbx, (%3);"     // [memory] = [memory] AND rbx
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "rbx", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_m64_r64_CF(unsigned long long x, unsigned long long y) {
    unsigned char flags = and_m64_r64_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_m64_r64_return_flags(unsigned long long x, unsigned long long y) {
    unsigned char ah;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, (%3);"
        "movq %2, %%rbx;"
        "andq %%rbx, (%3);"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "rbx", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 63 of 64-bit result
bool test_and_m64_r64_SF(unsigned long long x, unsigned long long y) {
    unsigned long long result = x & y;
    unsigned char flags = and_m64_r64_return_flags(x, y);
    if (result & 0x8000000000000000ULL) {  // Check bit 63 of 64-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_m64_r64_ZF(unsigned long long x, unsigned long long y) {
    unsigned long long result = x & y;
    unsigned char flags = and_m64_r64_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_m64_r64_PF(unsigned long long x, unsigned long long y) {
    unsigned char flags = and_m64_r64_return_flags(x, y);
    unsigned long long result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 64-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_m64_r64_return_OF(unsigned long long x, unsigned long long y) {
    unsigned char of;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, (%3);"
        "movq %2, %%rbx;"
        "andq %%rbx, (%3);"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "rbx"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_m64_r64_OF(unsigned long long x, unsigned long long y) {
    unsigned char of = and_m64_r64_return_OF(x, y);
    return (of == 0);
}

//************************************************************
// R8,M8 

unsigned char and_r8_m8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    __asm__ volatile (
        "movb %1, %%al;"        // al = x (destination register)
        "movb %2, (%3);"        // store y in memory location (source)
        "andb (%3), %%al;"      // al = al AND [memory]
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "al", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r8_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = and_r8_m8_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r8_m8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    __asm__ volatile (
        "movb %1, %%al;"
        "movb %2, (%3);"
        "andb (%3), %%al;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "al", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 7 of 8-bit result
bool test_and_r8_m8_SF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_r8_m8_return_flags(x, y);
    if (result & 0x80) {  // Check bit 7 of 8-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r8_m8_ZF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_r8_m8_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of full 8-bit result
bool test_and_r8_m8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = and_r8_m8_return_flags(x, y);
    uint8_t result = x & y;
    uint8_t expected_parity = calculate_parity(result);  // Full 8-bit for 8-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r8_m8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;
    __asm__ volatile (
        "movb %1, %%al;"
        "movb %2, (%3);"
        "andb (%3), %%al;"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "al"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r8_m8_OF(uint8_t x, uint8_t y) {
    unsigned char of = and_r8_m8_return_OF(x, y);
    return (of == 0);
}

//************************************************************************8
// REX R8,M8 

unsigned char and_REX_r8_m8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    __asm__ volatile (
        "movb %1, %%r8b;"       // r8b = x (destination, extended register)
        "movb %2, (%3);"        // store y in memory location (source)
        "andb (%3), %%r8b;"     // r8b = r8b AND [memory]
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "r8", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_REX_r8_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = and_REX_r8_m8_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_REX_r8_m8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    __asm__ volatile (
        "movb %1, %%r8b;"
        "movb %2, (%3);"
        "andb (%3), %%r8b;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "r8", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 7 of 8-bit result
bool test_and_REX_r8_m8_SF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_REX_r8_m8_return_flags(x, y);
    if (result & 0x80) {  // Check bit 7 of 8-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_REX_r8_m8_ZF(uint8_t x, uint8_t y) {
    uint8_t result = x & y;
    unsigned char flags = and_REX_r8_m8_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of full 8-bit result
bool test_and_REX_r8_m8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = and_REX_r8_m8_return_flags(x, y);
    uint8_t result = x & y;
    uint8_t expected_parity = calculate_parity(result);  // Full 8-bit for 8-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_REX_r8_m8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;
    __asm__ volatile (
        "movb %1, %%r8b;"
        "movb %2, (%3);"
        "andb (%3), %%r8b;"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "r8"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_REX_r8_m8_OF(uint8_t x, uint8_t y) {
    unsigned char of = and_REX_r8_m8_return_OF(x, y);
    return (of == 0);
}

//******************************************************************
// M16,R16 

unsigned char and_r16_m16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;
    __asm__ volatile (
        "movw %1, %%ax;"        // ax = x (destination register)
        "movw %2, (%3);"        // store y in memory location (source)
        "andw (%3), %%ax;"      // ax = ax AND [memory]
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "ax", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r16_m16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = and_r16_m16_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r16_m16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;
    __asm__ volatile (
        "movw %1, %%ax;"
        "movw %2, (%3);"
        "andw (%3), %%ax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "ax", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 15 of 16-bit result
bool test_and_r16_m16_SF(uint16_t x, uint16_t y) {
    uint16_t result = x & y;
    unsigned char flags = and_r16_m16_return_flags(x, y);
    if (result & 0x8000) {  // Check bit 15 of 16-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r16_m16_ZF(uint16_t x, uint16_t y) {
    uint16_t result = x & y;
    unsigned char flags = and_r16_m16_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_r16_m16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = and_r16_m16_return_flags(x, y);
    uint16_t result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 16-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r16_m16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    uint16_t val;
    __asm__ volatile (
        "movw %1, %%ax;"
        "movw %2, (%3);"
        "andw (%3), %%ax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "ax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r16_m16_OF(uint16_t x, uint16_t y) {
    unsigned char of = and_r16_m16_return_OF(x, y);
    return (of == 0);
}

//**************************************************************
// R32,M32 

unsigned char and_r32_m32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;
    __asm__ volatile (
        "movl %1, %%eax;"       // eax = x (destination register)
        "movl %2, (%3);"        // store y in memory location (source)
        "andl (%3), %%eax;"     // eax = eax AND [memory]
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "eax", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r32_m32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = and_r32_m32_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r32_m32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;
    __asm__ volatile (
        "movl %1, %%eax;"
        "movl %2, (%3);"
        "andl (%3), %%eax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "eax", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 31 of 32-bit result
bool test_and_r32_m32_SF(uint32_t x, uint32_t y) {
    uint32_t result = x & y;
    unsigned char flags = and_r32_m32_return_flags(x, y);
    if (result & 0x80000000) {  // Check bit 31 of 32-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r32_m32_ZF(uint32_t x, uint32_t y) {
    uint32_t result = x & y;
    unsigned char flags = and_r32_m32_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_r32_m32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = and_r32_m32_return_flags(x, y);
    uint32_t result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 32-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r32_m32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
    uint32_t val;
    __asm__ volatile (
        "movl %1, %%eax;"
        "movl %2, (%3);"
        "andl (%3), %%eax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "eax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r32_m32_OF(uint32_t x, uint32_t y) {
    unsigned char of = and_r32_m32_return_OF(x, y);
    return (of == 0);
}

//**********************************************************
// r64,m64
unsigned char and_r64_m64_return_CF(unsigned long long x, unsigned long long y) {
    unsigned char ah;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, %%rax;"       // rax = x (destination register)
        "movq %2, (%3);"        // store y in memory location (source)
        "andq (%3), %%rax;"     // rax = rax AND [memory]
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output variable
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "rax", "ah"
    );
    return ah;
}

// CF is always 0 for AND
bool test_and_r64_m64_CF(unsigned long long x, unsigned long long y) {
    unsigned char flags = and_r64_m64_return_CF(x, y);
    return ((flags & 0x01) == 0x00);
}

unsigned char and_r64_m64_return_flags(unsigned long long x, unsigned long long y) {
    unsigned char ah;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, %%rax;"
        "movq %2, (%3);"
        "andq (%3), %%rax;"
        "lahf;"
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y), "r"(&val)
        : "rax", "ah"
    );
    return ah;
}

// SF: bit 7 in ah, reflects bit 63 of 64-bit result
bool test_and_r64_m64_SF(unsigned long long x, unsigned long long y) {
    unsigned long long result = x & y;
    unsigned char flags = and_r64_m64_return_flags(x, y);
    if (result & 0x8000000000000000ULL) {  // Check bit 63 of 64-bit result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// ZF: bit 6 in ah
bool test_and_r64_m64_ZF(unsigned long long x, unsigned long long y) {
    unsigned long long result = x & y;
    unsigned char flags = and_r64_m64_return_flags(x, y);
    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// PF: bit 2 in ah, parity of low 8 bits of result
bool test_and_r64_m64_PF(unsigned long long x, unsigned long long y) {
    unsigned char flags = and_r64_m64_return_flags(x, y);
    unsigned long long result = x & y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Low 8 bits for 64-bit ops
    return (flags & 0x04) == expected_parity;
}

unsigned char and_r64_m64_return_OF(unsigned long long x, unsigned long long y) {
    unsigned char of;
    unsigned long long val;
    __asm__ volatile (
        "movq %1, %%rax;"
        "movq %2, (%3);"
        "andq (%3), %%rax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "rax"
    );
    return of;
}

// OF is always 0 for AND
bool test_and_r64_m64_OF(unsigned long long x, unsigned long long y) {
    unsigned char of = and_r64_m64_return_OF(x, y);
    return (of == 0);
}


// dummy main function, to allow us to link the executable
int main () { return 0;}