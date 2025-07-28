#include <stdbool.h>
#include <stdint.h>

uint8_t calculate_parity(long x) {
    uint8_t v = (uint8_t)(x & 0xFF);  // Only consider low 8 bits
    
    // XOR folding to compute parity
    v ^= v >> 4;
    v ^= v >> 2; 
    v ^= v >> 1;
    
    // If even number of 1's → return 0x04, else → return 0x00
    return (~v & 1) ? 0x04 : 0x00;
}

// Get the flags from XOR AL, imm8
unsigned char xor_AL_i8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // al = x 
        "xorb $0x02, %%al;"    // al ^= 0x02 (bitwise XOR)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output variable
        : "=r" (ah)
        : "r" (x)
        : "%al", "%ah"
    );

    return ah;
}

// Test Carry Flag (CF) — should always be 0 for XOR
bool test_xor_AL_i8_CF(uint8_t x) {
    unsigned char flags = xor_AL_i8_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF is bit 0
}

// Test Sign Flag (SF) — bit 7 of result
bool test_xor_AL_i8_SF(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = xor_AL_i8_return_flags(x);
    return ((result < 0) == ((flags & 0x80) == 0x80));
}

// Test Zero Flag (ZF) — bit 6 of result
bool test_xor_AL_i8_ZF(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = xor_AL_i8_return_flags(x);
    return ((result == 0) == ((flags & 0x40) == 0x40));
}

// Test Parity Flag (PF) — bit 2 of result
bool test_xor_AL_i8_PF(int8_t x) {
    unsigned char flags = xor_AL_i8_return_flags(x);
    int8_t result = x ^ 0x02;
    uint8_t parity = calculate_parity((uint8_t)result);
    return ((flags & 0x04) != 0) == (parity != 0);
}

// Get Overflow Flag (OF) using SETO — should be 0
unsigned char xor_AL_i8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%al;"       // AL = x
        "xorb $0x02, %%al;"    // XOR AL with 0x02
        "seto %0;"             // Set overflow flag
        : "=r"(of)
        : "r"(x)
        : "%al"
    );

    return of;
}

// Test Overflow Flag (OF) — should always be 0 for XOR
bool test_xor_AL_i8_OF(int8_t x) {
    return xor_AL_i8_return_OF(x) == 0;
}
//****************************************************************
// AL,i16 

// Return full flags (from AH) after XOR AX, imm16
unsigned char xor_AX_i16_return_flags(uint16_t x) {
    unsigned char ah;
    
    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "xorw $0x0002, %%ax;"  // XOR AX with immediate 0x0002
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%ax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_AX_i16_CF(uint16_t x) {
    unsigned char flags = xor_AX_i16_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}
  
// Sign Flag (SF) is bit 7
bool test_xor_AX_i16_SF(int16_t x) {
    int16_t result = x ^ 0x0002;
    unsigned char flags = xor_AX_i16_return_flags((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_AX_i16_ZF(int16_t x) {
    int16_t result = x ^ 0x0002;
    unsigned char flags = xor_AX_i16_return_flags((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

bool test_xor_AX_i16_PF(uint16_t x) {
    unsigned char flags = xor_AX_i16_return_flags(x);
    int16_t result = x ^ 0x02;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // Cast to uint8_t
    
    return ((flags & 0x04) != 0) == (result_parity != 0); 
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_AX_i16_return_OF(uint16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"
        "xorw $0x0002, %%ax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%ax"
    );

    return of;
}

bool test_xor_AX_i16_OF(uint16_t x) {
    return xor_AX_i16_return_OF(x) == 0;  // Expect OF = 0
}

//*************************************************************
// EAX,i32 
// Get flags after XOR EAX, imm32
unsigned char xor_EAX_i32_return_flags(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"           // Load x into EAX
        "xorl $0x00000002, %%eax;"  // XOR EAX with immediate
        "lahf;"                     // Load flags into AH
        "movb %%ah, %0;"            // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%eax", "%ah"
    );

    return ah;
}

// Test CF: XOR always clears Carry Flag
bool test_xor_EAX_i32_CF(uint32_t x) {
    unsigned char flags = xor_EAX_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF is bit 0
}

// Test SF: Sign Flag is bit 7 (set if result is negative)
bool test_xor_EAX_i32_SF(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_EAX_i32_return_flags((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Test ZF: Zero Flag is bit 6 (set if result is zero)
bool test_xor_EAX_i32_ZF(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_EAX_i32_return_flags((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Test PF: Parity Flag is bit 2 (even parity of low byte)
bool test_xor_EAX_i32_PF(uint32_t x) {
    unsigned char flags = xor_EAX_i32_return_flags(x);
    uint32_t result = x ^ 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Test OF: XOR always clears Overflow Flag
unsigned char xor_EAX_i32_return_OF(uint32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"
        "xorl $0x00000002, %%eax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%eax"
    );

    return of;
}

bool test_xor_EAX_i32_OF(uint32_t x) {
    return xor_EAX_i32_return_OF(x) == 0;  // OF should be 0
}
//*********************************************************
// RAX,i32 

unsigned char xor_RAX_i32_return_flags(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"       // Load x into RAX
        "xorq $0x00000002, %%rax;" // XOR RAX with 32-bit immediate 0x00000002
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%rax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_RAX_i32_CF(uint64_t x) {
    unsigned char flags = xor_RAX_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_xor_RAX_i32_SF(int64_t x) {
    int64_t result = x ^ 0x00000002;
    unsigned char flags = xor_RAX_i32_return_flags((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_RAX_i32_ZF(int64_t x) {
    int64_t result = x ^ 0x00000002;
    unsigned char flags = xor_RAX_i32_return_flags((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_xor_RAX_i32_PF(uint64_t x) {
    unsigned char flags = xor_RAX_i32_return_flags(x);
    uint64_t result = x ^ 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
     return ((flags & 0x04) != 0) == (result_parity != 0);  
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_RAX_i32_return_OF(uint64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"
        "xorq $0x00000002, %%rax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%rax"
    );

    return of;
}

bool test_xor_RAX_i32_OF(uint64_t x) {
    return xor_RAX_i32_return_OF(x) == 0;  // Expect OF = 0
}
//**********************************************************
// r8,i8 

// Return flags after XOR CL, imm8
unsigned char xor_r8_i8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%cl;"       // CL = x
        "xorb $0x02, %%cl;"    // CL ^= 0x02 (XOR with imm8)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%cl", "%ah"
    );

    return ah;
}

// Carry Flag (CF) – XOR always clears CF
bool test_xor_r8_i8_CF(uint8_t x) {
    unsigned char flags = xor_r8_i8_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF is bit 0
}

// Sign Flag (SF) – based on MSB of result
bool test_xor_r8_i8_SF(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = xor_r8_i8_return_flags(x);
    return ((result < 0) == ((flags & 0x80) == 0x80));
}

// Zero Flag (ZF) – set if result == 0
bool test_xor_r8_i8_ZF(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = xor_r8_i8_return_flags(x);
    return ((result == 0) == ((flags & 0x40) == 0x40));
}

// Parity Flag (PF) – based on parity of lower 8 bits
bool test_xor_r8_i8_PF(int8_t x) {
    unsigned char flags = xor_r8_i8_return_flags(x);
    int8_t result = x ^ 0x02;
    uint8_t result_parity = calculate_parity(result);  // your parity utility function
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_r8_i8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%cl;"       // CL = x
        "xorb $0x02, %%cl;"    // XOR CL with imm8
        "seto %0;"             // Set OF if overflow occurred
        : "=r"(of)
        : "r"(x)
        : "%cl"
    );

    return of;
}

bool test_xor_r8_i8_OF(int8_t x) {
    return xor_r8_i8_return_OF(x) == 0;  // OF should be 0
}

//*******************************************************
// m8,i8 

unsigned char xor_M8_i8_return_flags_mem(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "xorb $0x02, (%2);"    // 80/6 ib: [memory] ^= 0x02
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"                // clobbered register
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_M8_i8_CF_mem(uint8_t x) {
    unsigned char flags = xor_M8_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_M8_i8_SF_mem(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = xor_M8_i8_return_flags_mem((uint8_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_M8_i8_ZF_mem(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = xor_M8_i8_return_flags_mem((uint8_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2
bool test_xor_M8_i8_PF_mem(uint8_t x) {
    unsigned char flags = xor_M8_i8_return_flags_mem(x);
    uint8_t result = x ^ 0x02;
    uint8_t result_parity = calculate_parity(result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_M8_i8_return_OF_mem(uint8_t x) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "xorb $0x02, (%2);"    // 80/6 ib: [memory] ^= 0x02
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(&val)
    );

    return of;
}

bool test_xor_M8_i8_OF_mem(uint8_t x) {
    return xor_M8_i8_return_OF_mem(x) == 0;
}

//**************************************************
// REX r8,i8 

unsigned char rex_xor_R8L_i8_return_flags_reg(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r8b;"        // Load x into R8B
        "xorb $0x02, %%r8b;"     // REX + 80/6 ib: XOR R8B with 0x02
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%r8", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_rex_xor_R8L_i8_CF_reg(uint8_t x) {
    unsigned char flags = rex_xor_R8L_i8_return_flags_reg(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_rex_xor_R8L_i8_SF_reg(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = rex_xor_R8L_i8_return_flags_reg((uint8_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_rex_xor_R8L_i8_ZF_reg(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = rex_xor_R8L_i8_return_flags_reg((uint8_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2
bool test_rex_xor_R8L_i8_PF_reg(uint8_t x) {
    unsigned char flags = rex_xor_R8L_i8_return_flags_reg(x);
    uint8_t result = x ^ 0x02;
    uint8_t result_parity = calculate_parity(result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char rex_xor_R8L_i8_return_OF_reg(uint8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%r8b;"         // Load x into R8B
        "xorb $0x02, %%r8b;"      // XOR R8B with 0x02
        "seto %0;"                // Set OF to 'of'
        : "=r"(of)
        : "r"(x)
        : "%r8"
    );

    return of;
}

bool test_rex_xor_R8L_i8_OF_reg(uint8_t x) {
    return rex_xor_R8L_i8_return_OF_reg(x) == 0;
}

//***************************************************************
// REX m8,i8 

unsigned char rex_xor_M8_i8_return_flags_mem(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"        // store x into memory location
        "xorb $0x02, (%2);"     // REX + 80/6 ib: [memory] ^= 0x02
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output
        : "=r" (ah)
        : "r" (x), "r" (&val)
        : "%ah"
    );

    return ah;
}

// CF — Carry Flag is bit 0; XOR always clears CF
bool test_rex_xor_M8_i8_CF_mem(uint8_t x) {
    unsigned char flags = rex_xor_M8_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);
}

// SF — Sign Flag is bit 7
bool test_rex_xor_M8_i8_SF_mem(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = rex_xor_M8_i8_return_flags_mem((uint8_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// ZF — Zero Flag is bit 6
bool test_rex_xor_M8_i8_ZF_mem(int8_t x) {
    int8_t result = x ^ 0x02;
    unsigned char flags = rex_xor_M8_i8_return_flags_mem((uint8_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// PF — Parity Flag is bit 2
bool test_rex_xor_M8_i8_PF_mem(uint8_t x) {
    unsigned char flags = rex_xor_M8_i8_return_flags_mem(x);
    uint8_t result = x ^ 0x02;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// OF — Overflow Flag; XOR always clears OF
unsigned char rex_xor_M8_i8_return_OF_mem(uint8_t x) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"        // store x in memory
        "xorb $0x02, (%2);"     // XOR memory with 0x02
        "seto %0;"              // set OF into variable
        : "=r"(of)
        : "r"(x), "r"(&val)
    );

    return of;
}

bool test_rex_xor_M8_i8_OF_mem(uint8_t x) {
    return rex_xor_M8_i8_return_OF_mem(x) == 0;
}

//*************************************************************
// r16,i16 

// Return flags from AH after XOR CX, imm16
unsigned char xor_r16_i16_return_flags(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%cx;"         // Load x into CX
        "xorw $0x0002, %%cx;"    // XOR CX with immediate 0x0002
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%cx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0 — XOR always clears CF
bool test_xor_r16_i16_CF(uint16_t x) {
    unsigned char flags = xor_r16_i16_return_flags(x);
    return ((flags & 0x01) == 0x00);  // Expect CF = 0
}

// Sign Flag (SF) is bit 7
bool test_xor_r16_i16_SF(int16_t x) {
    int16_t result = x ^ 0x0002;
    unsigned char flags = xor_r16_i16_return_flags((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r16_i16_ZF(int16_t x) {
    int16_t result = x ^ 0x0002;
    unsigned char flags = xor_r16_i16_return_flags((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 — calculated from lower byte of result
bool test_xor_r16_i16_PF(uint16_t x) {
    unsigned char flags = xor_r16_i16_return_flags(x);
    uint16_t result = x ^ 0x0002;
    uint8_t result_parity = calculate_parity((uint8_t)result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_r16_i16_return_OF(uint16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%cx;"
        "xorw $0x0002, %%cx;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%cx"
    );

    return of;
}

bool test_xor_r16_i16_OF(uint16_t x) {
    return xor_r16_i16_return_OF(x) == 0;  // Expect OF = 0
}

//*************************************************************
// m16,i16
unsigned char xor_m16_i16_return_flags(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"         // store x in memory location
        "xorw $0x0002, (%2);"    // 81/6 iw: [memory] ^= 0x0002
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output variable
        : "=r" (ah)              // output
        : "r" (x), "r" (&val)    // inputs: x, memory address
        : "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_m16_i16_CF(uint16_t x) {
    unsigned char flags = xor_m16_i16_return_flags(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7 (refers to the MSB of the result)
bool test_xor_m16_i16_SF(int16_t x) {
    int16_t result = x ^ 0x0002;
    unsigned char flags = xor_m16_i16_return_flags((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_m16_i16_ZF(int16_t x) {
    int16_t result = x ^ 0x0002;
    unsigned char flags = xor_m16_i16_return_flags((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2, calculated from least significant byte
bool test_xor_m16_i16_PF(uint16_t x) {
    unsigned char flags = xor_m16_i16_return_flags(x);
    int16_t result = x ^ 0x0002;
    uint8_t result_parity = calculate_parity((uint8_t)result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_m16_i16_return_OF_mem(uint16_t x) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"         // store x in memory location
        "xorw $0x0002, (%2);"    // 81/6 iw: [memory] ^= 0x0002
        "seto %0;"               // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(&val)
        
    );

    return of;
}

bool test_xor_m16_i16_OF_mem(uint16_t x) {
    return xor_m16_i16_return_OF_mem(x) == 0;  // Expect OF = 0
}

//*********************************************************
// r32,i32 

unsigned char xor_r32_i32_return_flags(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%ecx;"           // Load x into ECX
        "xorl $0x00000002, %%ecx;"  // XOR ECX with immediate 0x00000002
        "lahf;"                     // Load flags into AH
        "movb %%ah, %0;"            // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%ecx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_r32_i32_CF(uint32_t x) {
    unsigned char flags = xor_r32_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_r32_i32_SF(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_r32_i32_return_flags((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r32_i32_ZF(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_r32_i32_return_flags((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 – determined from low byte of result
bool test_xor_r32_i32_PF(uint32_t x) {
    unsigned char flags = xor_r32_i32_return_flags(x);
    uint32_t result = x ^ 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_r32_i32_return_OF(uint32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%ecx;"
        "xorl $0x00000002, %%ecx;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%ecx"
    );

    return of;
}

bool test_xor_r32_i32_OF(uint32_t x) {
    return xor_r32_i32_return_OF(x) == 0;
}
//********************************************************************
// m32,i32 
// XOR [memory], imm32 and return flags from AH
unsigned char xor_m32_i32_return_flags(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"           // store x into memory
        "xorl $0x00000002, (%2);"  // XOR [mem], imm32
        "lahf;"                    // load flags into AH
        "movb %%ah, %0;"           // store AH in output
        : "=r" (ah)
        : "r" (x), "r" (&val)
        : "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0 — XOR always clears CF
bool test_xor_m32_i32_CF(uint32_t x) {
    unsigned char flags = xor_m32_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_m32_i32_SF(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_m32_i32_return_flags((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_m32_i32_ZF(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_m32_i32_return_flags((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 — calculated from low byte of result
bool test_xor_m32_i32_PF(uint32_t x) {
    unsigned char flags = xor_m32_i32_return_flags(x);
    uint32_t result = x ^ 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_m32_i32_return_OF(uint32_t x) {
    unsigned char of;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"           // store x in memory
        "xorl $0x00000002, (%2);"  // XOR [mem], imm32
        "seto %0;"                 // set OF into variable
        : "=r"(of)
        : "r"(x), "r"(&val)
    );

    return of;
}

bool test_xor_m32_i32_OF(uint32_t x) {
    return xor_m32_i32_return_OF(x) == 0;  // OF should be 0
}
//***********************************************************
// r64,i32 

// Return flags from AH after XOR RCX, imm32
unsigned char xor_R64_i32_return_flags(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rcx;"         // Load x into RCX
        "xorq $0x00000002, %%rcx;"// XOR RCX with immediate 0x00000002
        "lahf;"                   // Load flags into AH
        "movb %%ah, %0;"          // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%rcx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) — XOR always clears CF
bool test_xor_R64_i32_CF(uint64_t x) {
    unsigned char flags = xor_R64_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_R64_i32_SF(int64_t x) {
    int64_t result = x ^ 0x00000002;
    unsigned char flags = xor_R64_i32_return_flags((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_R64_i32_ZF(int64_t x) {
    int64_t result = x ^ 0x00000002;
    unsigned char flags = xor_R64_i32_return_flags((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 — based on low byte of result
bool test_xor_R64_i32_PF(uint64_t x) {
    unsigned char flags = xor_R64_i32_return_flags(x);
    uint64_t result = x ^ 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result); // PF only uses lowest byte
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_R64_i32_return_OF(uint64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rcx;"
        "xorq $0x00000002, %%rcx;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%rcx"
    );

    return of;
}

bool test_xor_R64_i32_OF(uint64_t x) {
    return xor_R64_i32_return_OF(x) == 0;  // Expect OF = 0
}
//*****************************************************************
// m64,i32 

unsigned char xor_m64_i32_return_flags(uint64_t x) {
    unsigned char ah;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"            // store x in memory location (64-bit)
        "xorq $0x00000002, (%2);"   // XOR [memory] with 32-bit immediate (sign-extended to 64-bit)
        "lahf;"                     // load flags into AH
        "movb %%ah, %0;"            // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (&val)
        : "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_m64_i32_CF(uint64_t x) {
    unsigned char flags = xor_m64_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_m64_i32_SF(int64_t x) {
    int64_t result = x ^ 0x00000002;
    unsigned char flags = xor_m64_i32_return_flags((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_m64_i32_ZF(int64_t x) {
    int64_t result = x ^ 0x00000002;
    unsigned char flags = xor_m64_i32_return_flags((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 – determined from the least significant byte
bool test_xor_m64_i32_PF(uint64_t x) {
    unsigned char flags = xor_m64_i32_return_flags(x);
    uint64_t result = x ^ 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_m64_i32_return_OF(uint64_t x) {
    unsigned char of;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"            // store x in memory location (64-bit)
        "xorq $0x00000002, (%2);"   // XOR [memory] with 32-bit immediate
        "seto %0;"                  // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(&val)
    );

    return of;
}

bool test_xor_m64_i32_OF(uint64_t x) {
    return xor_m64_i32_return_OF(x) == 0;
}

//****************************************************************
// r16,i8 

unsigned char xor_r16_i8_return_flags_reg(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"         // Load x into AX
        "xorw $0x02, %%ax;"      // XOR AX with sign-extended 8-bit immediate
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%ax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_r16_i8_CF_reg(uint16_t x) {
    unsigned char flags = xor_r16_i8_return_flags_reg(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_r16_i8_SF_reg(int16_t x) {
    int16_t result = x ^ 0x0002;  // 0x02 sign-extended to 16-bit
    unsigned char flags = xor_r16_i8_return_flags_reg((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r16_i8_ZF_reg(int16_t x) {
    int16_t result = x ^ 0x0002;
    unsigned char flags = xor_r16_i8_return_flags_reg((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 – determined from lower byte
bool test_xor_r16_i8_PF_reg(uint16_t x) {
    unsigned char flags = xor_r16_i8_return_flags_reg(x);
    uint16_t result = x ^ 0x0002;
    uint8_t result_parity = calculate_parity((uint8_t)result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_r16_i8_return_OF_reg(uint16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"
        "xorw $0x02, %%ax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%ax"
    );

    return of;
}

bool test_xor_r16_i8_OF_reg(uint16_t x) {
    return xor_r16_i8_return_OF_reg(x) == 0;
}

//********************************************************
// m16,i8 

// XOR [memory], imm8 (sign-extended) and return flags from AH
unsigned char xor_m16_i8_return_flags_mem(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"         // store x in memory location
        "xorw $0x02, (%2);"      // XOR [memory] with sign-extended imm8 (83/6 ib)
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output
        : "=r" (ah)
        : "r" (x), "r" (&val)
        : "%ah"
    );

    return ah;
}

// CF — Carry Flag (bit 0); XOR always clears CF
bool test_xor_m16_i8_CF_mem(uint16_t x) {
    unsigned char flags = xor_m16_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);
}

// SF — Sign Flag (bit 7)
bool test_xor_m16_i8_SF_mem(int16_t x) {
    int16_t result = x ^ 0x0002;  // XOR with sign-extended 0x02
    unsigned char flags = xor_m16_i8_return_flags_mem((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// ZF — Zero Flag (bit 6)
bool test_xor_m16_i8_ZF_mem(int16_t x) {
    int16_t result = x ^ 0x0002;
    unsigned char flags = xor_m16_i8_return_flags_mem((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// PF — Parity Flag (bit 2), computed from low byte
bool test_xor_m16_i8_PF_mem(uint16_t x) {
    unsigned char flags = xor_m16_i8_return_flags_mem(x);
    uint16_t result = x ^ 0x0002;
    uint8_t result_parity = calculate_parity((uint8_t)result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// OF — Overflow Flag (bit 11); XOR always clears OF
unsigned char xor_m16_i8_return_OF_mem(uint16_t x) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"         // store x in memory location
        "xorw $0x02, (%2);"      // XOR [memory] with sign-extended imm8
        "seto %0;"               // set overflow flag into output
        : "=r"(of)
        : "r"(x), "r"(&val)
    );

    return of;
}

bool test_xor_m16_i8_OF_mem(uint16_t x) {
    return xor_m16_i8_return_OF_mem(x) == 0;
}

//****************************************************************
// r32,i8 

// XOR ECX, imm8 (sign-extended) and return flags from AH
unsigned char xor_r32_i8_return_flags_reg(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%ecx;"        // Load x into ECX
        "xorl $0x02, %%ecx;"     // XOR ECX with sign-extended 8-bit immediate (83/6 ib)
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%ecx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0 — XOR always clears CF
bool test_xor_r32_i8_CF_reg(uint32_t x) {
    unsigned char flags = xor_r32_i8_return_flags_reg(x);
    return ((flags & 0x01) == 0x00);  // CF = 0
}

// Sign Flag (SF) is bit 7
bool test_xor_r32_i8_SF_reg(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_r32_i8_return_flags_reg((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r32_i8_ZF_reg(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_r32_i8_return_flags_reg((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 — based on least-significant byte
bool test_xor_r32_i8_PF_reg(uint32_t x) {
    unsigned char flags = xor_r32_i8_return_flags_reg(x);
    uint32_t result = x ^ 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only uses LSB
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_r32_i8_return_OF_reg(uint32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%ecx;"
        "xorl $0x02, %%ecx;"   // XOR ECX with sign-extended imm8
        "seto %0;"             // Set overflow flag
        : "=r"(of)
        : "r"(x)
        : "%ecx"
    );

    return of;
}

bool test_xor_r32_i8_OF_reg(uint32_t x) {
    return xor_r32_i8_return_OF_reg(x) == 0;  // Expect OF = 0
}
//*******************************************************8
// m32,i8 

unsigned char xor_m32_i8_return_flags_mem(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"         // store x in memory location
        "xorl $0x02, (%2);"      // 83/6 ib: XOR [memory] with sign-extended 8-bit immediate
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (&val)
        : "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_m32_i8_CF_mem(uint32_t x) {
    unsigned char flags = xor_m32_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_m32_i8_SF_mem(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_m32_i8_return_flags_mem((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_m32_i8_ZF_mem(int32_t x) {
    int32_t result = x ^ 0x00000002;
    unsigned char flags = xor_m32_i8_return_flags_mem((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_xor_m32_i8_PF_mem(uint32_t x) {
    unsigned char flags = xor_m32_i8_return_flags_mem(x);
    uint32_t result = x ^ 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_m32_i8_return_OF_mem(uint32_t x) {
    unsigned char of;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"         // store x in memory location
        "xorl $0x02, (%2);"      // XOR [memory] with sign-extended 8-bit immediate
        "seto %0;"               // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(&val)
    );

    return of;
}

bool test_xor_m32_i8_OF_mem(uint32_t x) {
    return xor_m32_i8_return_OF_mem(x) == 0;
}

//*************************************************************
// r64,i8 

// XOR RAX, imm8 (sign-extended) and return flags from AH
unsigned char xor_r64_i8_return_flags_reg(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"        // Load x into RAX
        "xorq $0x02, %%rax;"     // XOR RAX with sign-extended 8-bit immediate (REX.W + 83/6 ib)
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%rax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0 — XOR always clears CF
bool test_xor_r64_i8_CF_reg(uint64_t x) {
    unsigned char flags = xor_r64_i8_return_flags_reg(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_r64_i8_SF_reg(int64_t x) {
    int64_t result = x ^ 0x0000000000000002;
    unsigned char flags = xor_r64_i8_return_flags_reg((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r64_i8_ZF_reg(int64_t x) {
    int64_t result = x ^ 0x0000000000000002;
    unsigned char flags = xor_r64_i8_return_flags_reg((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 — based on lowest byte of result
bool test_xor_r64_i8_PF_reg(uint64_t x) {
    unsigned char flags = xor_r64_i8_return_flags_reg(x);
    uint64_t result = x ^ 0x0000000000000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // Only low 8 bits matter for PF
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_r64_i8_return_OF_reg(uint64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"
        "xorq $0x02, %%rax;"     // XOR RAX with sign-extended 8-bit imm
        "seto %0;"               // Set overflow flag to OF
        : "=r"(of)
        : "r"(x)
        : "%rax"
    );

    return of;
}

bool test_xor_r64_i8_OF_reg(uint64_t x) {
    return xor_r64_i8_return_OF_reg(x) == 0;  // Expect OF = 0
}

//*****************************************************************
// m64,i8 

unsigned char xor_m64_i8_return_flags_mem(uint64_t x) {
    unsigned char ah;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"         // store x in memory location
        "xorq $0x02, (%2);"      // REX.W + 83/6 ib: XOR [memory] with sign-extended 8-bit immediate
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (&val)
        : "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_m64_i8_CF_mem(uint64_t x) {
    unsigned char flags = xor_m64_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_m64_i8_SF_mem(int64_t x) {
    int64_t result = x ^ 0x0000000000000002;
    unsigned char flags = xor_m64_i8_return_flags_mem((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_m64_i8_ZF_mem(int64_t x) {
    int64_t result = x ^ 0x0000000000000002;
    unsigned char flags = xor_m64_i8_return_flags_mem((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_xor_m64_i8_PF_mem(uint64_t x) {
    unsigned char flags = xor_m64_i8_return_flags_mem(x);
    uint64_t result = x ^ 0x0000000000000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_m64_i8_return_OF_mem(uint64_t x) {
    unsigned char of;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"         // store x in memory location
        "xorq $0x02, (%2);"      // REX.W + 83/6 ib: XOR [memory] with sign-extended 8-bit immediate
        "seto %0;"               // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(&val)
    );

    return of;
}

bool test_xor_m64_i8_OF_mem(uint64_t x) {
    return xor_m64_i8_return_OF_mem(x) == 0;
}

//************************************************************
// r8,r8 

unsigned char xor_r8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"        // Load x into AL
        "movb %2, %%bl;"        // Load y into BL
        "xorb %%bl, %%al;"      // 30/r: XOR AL with BL
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%al", "%bl", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_r8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = xor_r8_r8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_r8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = xor_r8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = xor_r8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2
bool test_xor_r8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = xor_r8_r8_return_flags(x, y);
    uint8_t result = x ^ y;
    uint8_t result_parity = calculate_parity(result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_r8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%al;"
        "movb %2, %%bl;"
        "xorb %%bl, %%al;"      // XOR AL with BL
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%al", "%bl"
    );

    return of;
}

bool test_xor_r8_r8_OF(uint8_t x, uint8_t y) {
    return xor_r8_r8_return_OF(x, y) == 0;
}

//***********************************************************
// m8,r8 

// XOR [memory], r8 (BL) and return flags from AH
unsigned char xor_m8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"        // store x into memory
        "movb %2, %%bl;"        // load y into BL
        "xorb %%bl, (%3);"      // XOR [memory], BL
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%bl", "%ah"
    );

    return ah;
}

// Carry Flag (CF) — XOR always clears CF
bool test_xor_m8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = xor_m8_r8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) — bit 7
bool test_xor_m8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = xor_m8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) — bit 6
bool test_xor_m8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = xor_m8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) — bit 2, only low byte
bool test_xor_m8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = xor_m8_r8_return_flags(x, y);
    uint8_t result = x ^ y;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_m8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"        // store x into memory
        "movb %2, %%bl;"        // load y into BL
        "xorb %%bl, (%3);"      // XOR [memory], BL
        "seto %0;"              // set overflow flag
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%bl"
    );

    return of;
}

bool test_xor_m8_r8_OF(uint8_t x, uint8_t y) {
    return xor_m8_r8_return_OF(x, y) == 0;
}

//***********************************************************************
// REX,r8,r8 

// XOR R8B, R9B and return flags from AH
unsigned char rex_xor_r8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r8b;"       // Load x into R8B
        "movb %2, %%r9b;"       // Load y into R9B
        "xorb %%r9b, %%r8b;"    // XOR R8B with R9B (REX + 30/r)
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%r8", "%r9", "%ah"
    );

    return ah;
}

// Carry Flag (CF) — XOR always clears CF
bool test_rex_xor_r8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_xor_r8_r8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) — bit 7
bool test_rex_xor_r8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = rex_xor_r8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) — bit 6
bool test_rex_xor_r8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = rex_xor_r8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) — bit 2
bool test_rex_xor_r8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_xor_r8_r8_return_flags(x, y);
    uint8_t result = x ^ y;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char rex_xor_r8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%r8b;"
        "movb %2, %%r9b;"
        "xorb %%r9b, %%r8b;"    // REX + 30/r: XOR R8B, R9B
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%r8", "%r9"
    );

    return of;
}

bool test_rex_xor_r8_r8_OF(uint8_t x, uint8_t y) {
    return rex_xor_r8_r8_return_OF(x, y) == 0;
}

//****************************************************
// REX,m8,r8
unsigned char rex_xor_m8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"         // store x in memory location
        "movb %2, %%r9b;"        // load y into R9B (extended register)
        "xorb %%r9b, (%3);"      // REX + 30/r: XOR [memory] with R9B
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%r9", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_rex_xor_m8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_xor_m8_r8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_rex_xor_m8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = rex_xor_m8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_rex_xor_m8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = rex_xor_m8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2
bool test_rex_xor_m8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_xor_m8_r8_return_flags(x, y);
    uint8_t result = x ^ y;
    uint8_t result_parity = calculate_parity(result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char rex_xor_m8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"         // store x in memory location
        "movb %2, %%r9b;"        // load y into R9B
        "xorb %%r9b, (%3);"      // XOR [memory] with R9B
        "seto %0;"               // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%r9"
    );

    return of;
}

bool test_rex_xor_m8_r8_OF(uint8_t x, uint8_t y) {
    return rex_xor_m8_r8_return_OF(x, y) == 0;
}

//****************************************************
// r16,r16 
unsigned char xor_r16_r16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"         // Load x into AX
        "movw %2, %%bx;"         // Load y into BX
        "xorw %%bx, %%ax;"       // XOR AX with BX (0x31 /r)
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%ax", "%bx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_r16_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = xor_r16_r16_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_r16_r16_SF(int16_t x, int16_t y) {
    int16_t result = x ^ y;
    unsigned char flags = xor_r16_r16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r16_r16_ZF(int16_t x, int16_t y) {
    int16_t result = x ^ y;
    unsigned char flags = xor_r16_r16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - based on low byte of result
bool test_xor_r16_r16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = xor_r16_r16_return_flags(x, y);
    uint16_t result = x ^ y;
    uint8_t result_parity = calculate_parity((uint8_t)result);

    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_r16_r16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"
        "movw %2, %%bx;"
        "xorw %%bx, %%ax;"     // 0x31 /r: XOR AX with BX
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%ax", "%bx"
    );

    return of;
}

bool test_xor_r16_r16_OF(uint16_t x, uint16_t y) {
    return xor_r16_r16_return_OF(x, y) == 0;  // OF should be 0
}
//**********************************************************
// m16,r16 

// XOR [memory], BX and return flags from AH
unsigned char xor_m16_r16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%3);"        // store x in memory location
        "movw %2, %%bx;"        // load y into BX
        "xorw %%bx, (%3);"      // XOR [memory], BX
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // store AH in output variable
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%bx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) — XOR always clears CF
bool test_xor_m16_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = xor_m16_r16_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) — bit 7 of result
bool test_xor_m16_r16_SF(int16_t x, int16_t y) {
    int16_t result = x ^ y;
    unsigned char flags = xor_m16_r16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) — bit 6
bool test_xor_m16_r16_ZF(int16_t x, int16_t y) {
    int16_t result = x ^ y;
    unsigned char flags = xor_m16_r16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) — bit 2, based on low byte of result
bool test_xor_m16_r16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = xor_m16_r16_return_flags(x, y);
    uint8_t result = (uint8_t)(x ^ y);
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_m16_r16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%3);"        // store x in memory
        "movw %2, %%bx;"        // load y into BX
        "xorw %%bx, (%3);"      // XOR [memory], BX
        "seto %0;"              // set overflow flag
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%bx"
    );

    return of;
}

bool test_xor_m16_r16_OF(uint16_t x, uint16_t y) {
    return xor_m16_r16_return_OF(x, y) == 0;  // Expect OF = 0
}

//********************************************** */
//r32,r32

// XOR EAX, EBX and return flags from AH
unsigned char xor_r32_r32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"        // Load x into EAX
        "movl %2, %%ebx;"        // Load y into EBX
        "xorl %%ebx, %%eax;"     // XOR EAX with EBX
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%eax", "%ebx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) — XOR always clears CF
bool test_xor_r32_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = xor_r32_r32_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) — based on most significant bit of result
bool test_xor_r32_r32_SF(int32_t x, int32_t y) {
    int32_t result = x ^ y;
    unsigned char flags = xor_r32_r32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) — set if result == 0
bool test_xor_r32_r32_ZF(int32_t x, int32_t y) {
    int32_t result = x ^ y;
    unsigned char flags = xor_r32_r32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) — based on parity of least significant byte
bool test_xor_r32_r32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = xor_r32_r32_return_flags(x, y);
    uint8_t result = (uint8_t)(x ^ y);
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_r32_r32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"
        "movl %2, %%ebx;"
        "xorl %%ebx, %%eax;"     // XOR EAX, EBX
        "seto %0;"               // Set OF into result
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%eax", "%ebx"
    );

    return of;
}

bool test_xor_r32_r32_OF(uint32_t x, uint32_t y) {
    return xor_r32_r32_return_OF(x, y) == 0;  // Expect OF = 0
}

//*******************************************************
// m32,r32 

unsigned char xor_m32_r32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%3);"         // store x in memory location
        "movl %2, %%ebx;"        // load y into EBX
        "xorl %%ebx, (%3);"      // 31/r: XOR [memory] with EBX
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%ebx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_m32_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = xor_m32_r32_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_m32_r32_SF(int32_t x, int32_t y) {
    int32_t result = x ^ y;
    unsigned char flags = xor_m32_r32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_m32_r32_ZF(int32_t x, int32_t y) {
    int32_t result = x ^ y;
    unsigned char flags = xor_m32_r32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 – based on least significant byte of result
bool test_xor_m32_r32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = xor_m32_r32_return_flags(x, y);
    uint8_t result = (uint8_t)(x ^ y);
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_m32_r32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%3);"         // store x in memory location
        "movl %2, %%ebx;"        // load y into EBX
        "xorl %%ebx, (%3);"      // XOR [memory] with EBX
        "seto %0;"               // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%ebx"
    );

    return of;
}

bool test_xor_m32_r32_OF(uint32_t x, uint32_t y) {
    return xor_m32_r32_return_OF(x, y) == 0;
}

//******************************************************
// r64,r64 
unsigned char xor_r64_r64_return_flags(uint64_t x, uint64_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"        // Load x into RAX
        "movq %2, %%rbx;"        // Load y into RBX
        "xorq %%rbx, %%rax;"     // XOR RAX with RBX
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%rax", "%rbx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_r64_r64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = xor_r64_r64_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_r64_r64_SF(int64_t x, int64_t y) {
    int64_t result = x ^ y;
    unsigned char flags = xor_r64_r64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r64_r64_ZF(int64_t x, int64_t y) {
    int64_t result = x ^ y;
    unsigned char flags = xor_r64_r64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 – based on least significant byte of result
bool test_xor_r64_r64_PF(uint64_t x, uint64_t y) {
    unsigned char flags = xor_r64_r64_return_flags(x, y);
    uint8_t result = (uint8_t)(x ^ y);
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_r64_r64_return_OF(uint64_t x, uint64_t y) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"
        "movq %2, %%rbx;"
        "xorq %%rbx, %%rax;"    // XOR RAX with RBX
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%rax", "%rbx"
    );

    return of;
}

bool test_xor_r64_r64_OF(uint64_t x, uint64_t y) {
    return xor_r64_r64_return_OF(x, y) == 0;
}

//******************************************************************
// m64,r64 

// XOR [memory], RBX and return flags from AH
unsigned char xor_m64_r64_return_flags(uint64_t x, uint64_t y) {
    unsigned char ah;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%3);"         // store x in memory
        "movq %2, %%rbx;"        // load y into RBX
        "xorq %%rbx, (%3);"      // XOR [memory], RBX
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%rbx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) — XOR always clears CF
bool test_xor_m64_r64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = xor_m64_r64_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) — MSB of 64-bit result
bool test_xor_m64_r64_SF(int64_t x, int64_t y) {
    int64_t result = x ^ y;
    unsigned char flags = xor_m64_r64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) — set if result == 0
bool test_xor_m64_r64_ZF(int64_t x, int64_t y) {
    int64_t result = x ^ y;
    unsigned char flags = xor_m64_r64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) — parity of least significant byte
bool test_xor_m64_r64_PF(uint64_t x, uint64_t y) {
    unsigned char flags = xor_m64_r64_return_flags(x, y);
    uint8_t result = (uint8_t)(x ^ y);
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_m64_r64_return_OF(uint64_t x, uint64_t y) {
    unsigned char of;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%3);"         // store x in memory
        "movq %2, %%rbx;"        // load y into RBX
        "xorq %%rbx, (%3);"      // XOR [memory], RBX
        "seto %0;"               // set OF flag
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%rbx"
    );

    return of;
}

bool test_xor_m64_r64_OF(uint64_t x, uint64_t y) {
    return xor_m64_r64_return_OF(x, y) == 0;  // Expect OF = 0
}

//******************************************************************
// r8,m8 

// XOR AL with [memory] and return flags from AH
unsigned char xor_r8_m8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %2, (%3);"        // store y in memory (source)
        "movb %1, %%al;"        // load x into AL (destination)
        "xorb (%3), %%al;"      // XOR AL with [memory]
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%al", "%ah"
    );

    return ah;
}

// Carry Flag (CF) — XOR always clears CF
bool test_xor_r8_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = xor_r8_m8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) — based on MSB of result
bool test_xor_r8_m8_SF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = xor_r8_m8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) — set if result == 0
bool test_xor_r8_m8_ZF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = xor_r8_m8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) — based on lowest byte of result
bool test_xor_r8_m8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = xor_r8_m8_return_flags(x, y);
    uint8_t result = x ^ y;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_r8_m8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %2, (%3);"        // store y in memory
        "movb %1, %%al;"        // load x into AL
        "xorb (%3), %%al;"      // XOR AL with [memory]
        "seto %0;"              // set overflow flag
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%al"
    );

    return of;
}

bool test_xor_r8_m8_OF(uint8_t x, uint8_t y) {
    return xor_r8_m8_return_OF(x, y) == 0;
}

//*************************************************************
// REX r8,m8

unsigned char rex_xor_r8_m8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %2, (%3);"         // store y in memory location (source)
        "movb %1, %%r8b;"        // load x into R8B (destination)
        "xorb (%3), %%r8b;"      // XOR R8B with [memory]
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH into result
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%r8", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_rex_xor_r8_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_xor_r8_m8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_rex_xor_r8_m8_SF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = rex_xor_r8_m8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_rex_xor_r8_m8_ZF(int8_t x, int8_t y) {
    int8_t result = x ^ y;
    unsigned char flags = rex_xor_r8_m8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 – depends on low byte of result
bool test_rex_xor_r8_m8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_xor_r8_m8_return_flags(x, y);
    uint8_t result = x ^ y;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char rex_xor_r8_m8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %2, (%3);"         // store y in memory location
        "movb %1, %%r8b;"        // load x into R8B
        "xorb (%3), %%r8b;"      // XOR R8B with [memory]
        "seto %0;"               // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%r8"
    );

    return of;
}

bool test_rex_xor_r8_m8_OF(uint8_t x, uint8_t y) {
    return rex_xor_r8_m8_return_OF(x, y) == 0;
}

//*********************************************************************
// r16,m16 

unsigned char xor_r16_m16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %2, (%3);"         // store y in memory location (source)
        "movw %1, %%ax;"         // load x into AX (destination)
        "xorw (%3), %%ax;"       // XOR AX with [memory]
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%ax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. XOR always clears CF.
bool test_xor_r16_m16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = xor_r16_m16_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) is bit 7
bool test_xor_r16_m16_SF(int16_t x, int16_t y) {
    int16_t result = x ^ y;
    unsigned char flags = xor_r16_m16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_xor_r16_m16_ZF(int16_t x, int16_t y) {
    int16_t result = x ^ y;
    unsigned char flags = xor_r16_m16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_xor_r16_m16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = xor_r16_m16_return_flags(x, y);
    uint16_t result = x ^ y;
    uint8_t result_parity = calculate_parity((uint8_t)result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_r16_m16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %2, (%3);"         // store y in memory location (source)
        "movw %1, %%ax;"         // load x into AX (destination)
        "xorw (%3), %%ax;"       // XOR AX with [memory]
        "seto %0;"               // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%ax"
    );

    return of;
}

bool test_xor_r16_m16_OF(uint16_t x, uint16_t y) {
    return xor_r16_m16_return_OF(x, y) == 0;
}

//*******************************************************
// r32,m32 
// XOR EAX with [memory] and return flags from AH
unsigned char xor_r32_m32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %2, (%3);"         // store y in memory (source)
        "movl %1, %%eax;"        // load x into EAX (destination)
        "xorl (%3), %%eax;"      // XOR EAX with [memory]
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%eax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) — XOR always clears CF
bool test_xor_r32_m32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = xor_r32_m32_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) — MSB of result
bool test_xor_r32_m32_SF(int32_t x, int32_t y) {
    int32_t result = x ^ y;
    unsigned char flags = xor_r32_m32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) — set if result == 0
bool test_xor_r32_m32_ZF(int32_t x, int32_t y) {
    int32_t result = x ^ y;
    unsigned char flags = xor_r32_m32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) — parity of least significant byte
bool test_xor_r32_m32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = xor_r32_m32_return_flags(x, y);
    uint8_t result = (uint8_t)(x ^ y);  // PF is based on low byte
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) — XOR always clears OF
unsigned char xor_r32_m32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
    uint32_t val;

    __asm__ volatile (
        "movl %2, (%3);"         // store y in memory
        "movl %1, %%eax;"        // load x into EAX
        "xorl (%3), %%eax;"      // XOR EAX with [memory]
        "seto %0;"               // set OF flag
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%eax"
    );

    return of;
}

bool test_xor_r32_m32_OF(uint32_t x, uint32_t y) {
    return xor_r32_m32_return_OF(x, y) == 0;
}

//***************************************************
// r64,m64 */

// XOR RAX with [memory] and return flags from AH
unsigned char xor_r64_m64_return_flags(uint64_t x, uint64_t y) {
    unsigned char ah;
    uint64_t val;

    __asm__ volatile (
        "movq %2, (%3);"         // store y in memory location
        "movq %1, %%rax;"        // load x into RAX
        "xorq (%3), %%rax;"      // XOR RAX with [memory]
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output variable
        : "=r" (ah)
        : "r" (x), "r" (y), "r" (&val)
        : "%rax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) – XOR always clears CF
bool test_xor_r64_m64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = xor_r64_m64_return_flags(x, y);
    return ((flags & 0x01) == 0x00);
}

// Sign Flag (SF) – set if MSB of result is 1
bool test_xor_r64_m64_SF(int64_t x, int64_t y) {
    int64_t result = x ^ y;
    unsigned char flags = xor_r64_m64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) – set if result == 0
bool test_xor_r64_m64_ZF(int64_t x, int64_t y) {
    int64_t result = x ^ y;
    unsigned char flags = xor_r64_m64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) – based on parity of least significant byte
bool test_xor_r64_m64_PF(uint64_t x, uint64_t y) {
    unsigned char flags = xor_r64_m64_return_flags(x, y);
    uint8_t result = (uint8_t)(x ^ y);  // PF checks low byte only
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – XOR always clears OF
unsigned char xor_r64_m64_return_OF(uint64_t x, uint64_t y) {
    unsigned char of;
    uint64_t val;

    __asm__ volatile (
        "movq %2, (%3);"         // store y in memory
        "movq %1, %%rax;"        // load x into RAX
        "xorq (%3), %%rax;"      // XOR RAX with [memory]
        "seto %0;"               // set OF flag into 'of'
        : "=r"(of)
        : "r"(x), "r"(y), "r"(&val)
        : "%rax"
    );

    return of;
}

bool test_xor_r64_m64_OF(uint64_t x, uint64_t y) {
    return xor_r64_m64_return_OF(x, y) == 0;  // OF should be 0
}


// dummy main function, to allow us to link the executable
int main () { return 0;}
