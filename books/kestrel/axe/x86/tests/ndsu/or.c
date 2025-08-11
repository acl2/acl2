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


//**************************************************************
// AL,i8 

unsigned char or_AL_i8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"      // al = x 
        "orb $0x02, %%al;"    // al |= imm (bitwise OR)
        "lahf;"               // load flags into AH
        "movb %%ah, %0;"      // store AH in output variable
        : "=r" (ah)           // output
        : "r" (x)             // inputs
        : "%al", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah
//For OR operations, CF is always cleared (0)
bool test_or_AL_i8_CF(uint8_t x) {
    unsigned char flags = or_AL_i8_return_flags(x);
    
    // OR always clears CF flag
    return ((flags & 0x01) == 0x00);
}


//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_or_AL_i8_SF(int8_t x) {
    int8_t result = x | 0x02;  
    unsigned char flags = or_AL_i8_return_flags(x);

    if (result < 0) {  // Check if bit 7 is set in result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_or_AL_i8_ZF(int8_t x) {
    int8_t result = x | 0x02;
    unsigned char flags = or_AL_i8_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_or_AL_i8_PF(int8_t x) {
    unsigned char flags = or_AL_i8_return_flags(x);

    int8_t result = x | 0x02;
    uint8_t result_parity = calculate_parity(result); 
    
    return ((flags & 0x04) != 0) == (result_parity != 0);  
}

unsigned char or_AL_i8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%al;"      // Load x into AL (8-bit)
        "orb $0x02, %%al;"    // OR immediate with AL
        "seto %0;"            // Set OF flag into 'of'
        : "=r"(of)            // Output operand
        : "r"(x)              // input
        : "%al"               // Clobbered register
    );

    return of;
}

//check property for OF
//For OR operations, OF is always cleared (0)
bool test_or_AL_i8_OF(int8_t x) {
    unsigned char of = or_AL_i8_return_OF(x);
    
    // OR always clears OF flag
    return of == 0;
}


//*****************************************************
// AX,i16 

// Return full flags (from AH) after OR AX, imm16
unsigned char or_AX_i16_return_flags(uint16_t x) {
    unsigned char ah;
    

    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "orw $0x0002, %%ax;"   // OR AX with immediate 0x0002
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%ax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_AX_i16_CF(uint16_t x) {
    unsigned char flags = or_AX_i16_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}
  
// Sign Flag (SF) is bit 7
bool test_or_AX_i16_SF(int16_t x) {
    int16_t result = x | 0x0002;
    unsigned char flags = or_AX_i16_return_flags((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_AX_i16_ZF(int16_t x) {
    int16_t result = x | 0x0002;
    unsigned char flags = or_AX_i16_return_flags((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


bool test_or_AX_i16_PF(uint16_t x) {
    unsigned char flags = or_AX_i16_return_flags(x);
    int16_t result = x | 0x02;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // Cast to uint8_t
    
    return ((flags & 0x04) != 0) == (result_parity != 0); 
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_AX_i16_return_OF(uint16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"
        "orw $0x0002, %%ax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%ax"
    );

    return of;
}

bool test_or_AX_i16_OF(uint16_t x) {
    return or_AX_i16_return_OF(x) == 0;  // Expect OF = 0
}

//***************************************************************
//  eax,i32 


// Return full flags (from AH) after OR EAX, imm32
unsigned char or_EAX_i32_return_flags(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"       // Load x into EAX
        "orl $0x00000002, %%eax;" // OR EAX with immediate 0x00000002
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%eax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_EAX_i32_CF(uint32_t x) {
    unsigned char flags = or_EAX_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_EAX_i32_SF(int32_t x) {
    int32_t result = x | 0x00000002;
    unsigned char flags = or_EAX_i32_return_flags((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_EAX_i32_ZF(int32_t x) {
    int32_t result = x | 0x00000002;
    unsigned char flags = or_EAX_i32_return_flags((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_EAX_i32_PF(uint32_t x) {
    unsigned char flags = or_EAX_i32_return_flags(x);
    uint32_t result = x | 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0); 
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_EAX_i32_return_OF(uint32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"
        "orl $0x00000002, %%eax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%eax"
    );

    return of;
}

bool test_or_EAX_i32_OF(uint32_t x) {
    return or_EAX_i32_return_OF(x) == 0;  // Expect OF = 0
}

//********************************************************* 
//RAX,i32

// Return full flags (from AH) after OR RAX, imm32
unsigned char or_RAX_i32_return_flags(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"       // Load x into RAX
        "orq $0x00000002, %%rax;" // OR RAX with 32-bit immediate 0x00000002
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%rax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_RAX_i32_CF(uint64_t x) {
    unsigned char flags = or_RAX_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_RAX_i32_SF(int64_t x) {
    int64_t result = x | 0x00000002;
    unsigned char flags = or_RAX_i32_return_flags((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_RAX_i32_ZF(int64_t x) {
    int64_t result = x | 0x00000002;
    unsigned char flags = or_RAX_i32_return_flags((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_RAX_i32_PF(uint64_t x) {
    unsigned char flags = or_RAX_i32_return_flags(x);
    uint64_t result = x | 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
     return ((flags & 0x04) != 0) == (result_parity != 0);  
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_RAX_i32_return_OF(uint64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"
        "orq $0x00000002, %%rax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%rax"
    );

    return of;
}

bool test_or_RAX_i32_OF(uint64_t x) {
    return or_RAX_i32_return_OF(x) == 0;  // Expect OF = 0
}
//******************************************
//  r8,i8

unsigned char or_r8_i8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%cl;"      // cl = x 
        "orb $0x02, %%cl;"    // cl |= imm (bitwise OR)
        "lahf;"               // load flags into AH
        "movb %%ah, %0;"      // store AH in output variable
        : "=r" (ah)           // output
        : "r" (x)             // inputs
        : "%cl", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah
//For OR operations, CF is always cleared (0)
bool test_or_r8_i8_CF(uint8_t x) {
    unsigned char flags = or_r8_i8_return_flags(x);
    
    // OR always clears CF flag
    return ((flags & 0x01) == 0x00);
}


//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_or_r8_i8_SF(int8_t x) {
    int8_t result = x | 0x02;  
    unsigned char flags = or_r8_i8_return_flags(x);

    if (result < 0) {  // Check if bit 7 is set in result
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_or_r8_i8_ZF(int8_t x) {
    int8_t result = x | 0x02;
    unsigned char flags = or_r8_i8_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}


//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_or_r8_i8_PF(int8_t x) {
    unsigned char flags = or_r8_i8_return_flags(x);

    int8_t result = x | 0x02;
    uint8_t result_parity = calculate_parity(result); 
    
    return ((flags & 0x04) != 0) == (result_parity != 0);  
}

unsigned char or_r8_i8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%cl;"      // Load x into CL (8-bit)
        "orb $0x02, %%cl;"    // OR immediate with CL
        "seto %0;"            // Set OF flag into 'of'
        : "=r"(of)            // Output operand
        : "r"(x)              // input
        : "%cl"               // Clobbered register
    );

    return of;
}

//check property for OF
//For OR operations, OF is always cleared (0)
bool test_or_r8_i8_OF(int8_t x) {
    unsigned char of = or_r8_i8_return_OF(x);
    
    // OR always clears OF flag
    return of == 0;
}



// **********************************************************
// m8,i8
unsigned char or_M8_i8_return_flags_mem(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "orb $0x02, (%2);"     // 80/1 ib: [memory] = [memory] | imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"                // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_M8_i8_CF_mem(uint8_t x) {
    unsigned char flags = or_M8_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_M8_i8_SF_mem(int8_t x) {
    int8_t result = x | 0x02;
    unsigned char flags = or_M8_i8_return_flags_mem((uint8_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_M8_i8_ZF_mem(int8_t x) {
    int8_t result = x | 0x02;
    unsigned char flags = or_M8_i8_return_flags_mem((uint8_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2
bool test_or_M8_i8_PF_mem(uint8_t x) {
    unsigned char flags = or_M8_i8_return_flags_mem(x);
    uint8_t result = x | 0x02;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_M8_i8_return_OF_mem(uint8_t x) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "orb $0x02, (%2);"     // 80/1 ib: [memory] = [memory] | imm8
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :                      // no clobbered registers
    );

    return of;
}

bool test_or_M8_i8_OF_mem(uint8_t x) {
    return or_M8_i8_return_OF_mem(x) == 0;  // Expect OF = 0
}

//*********************************************************************8
// REX r8,i8 

// Return full flags (from AH) after REX + OR reg8, imm8 (register version)
unsigned char rex_or_R8L_i8_return_flags_reg(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r8b;"       // Load x into R8 (64-bit move)
        "orb $0x02, %%r8b;"    // REX + 80/1 ib: OR R8L with immediate 0x02
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%r8", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_rex_or_R8L_i8_CF_reg(uint8_t x) {
    unsigned char flags = rex_or_R8L_i8_return_flags_reg(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_rex_or_R8L_i8_SF_reg(int8_t x) {
    int8_t result = x | 0x02;
    unsigned char flags = rex_or_R8L_i8_return_flags_reg((uint8_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_rex_or_R8L_i8_ZF_reg(int8_t x) {
    int8_t result = x | 0x02;
    unsigned char flags = rex_or_R8L_i8_return_flags_reg((uint8_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2
bool test_rex_or_R8L_i8_PF_reg(uint8_t x) {
    unsigned char flags = rex_or_R8L_i8_return_flags_reg(x);
    uint8_t result = x | 0x02;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char rex_or_R8L_i8_return_OF_reg(uint8_t x) {
    unsigned char of;
    __asm__ volatile (  
        "movb %1, %%r8b;"        
        "orb $0x02, %%r8b;"      
        "seto %0;"               
        : "=r"(of)
        : "r"(x)
        : "%r8"
    );
    return of;
}
bool test_rex_or_R8L_i8_OF_reg(uint8_t x) {
    return rex_or_R8L_i8_return_OF_reg(x) == 0;  // Expect OF = 0
}

//**************************************************
// REX M8,i8 
// Return full flags (from AH) after REX + OR [mem], imm8 (memory version)
unsigned char rex_or_M8_i8_return_flags_mem(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "orb $0x02, (%2);"     // REX + 80/1 ib: [memory] = [memory] | imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"                // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_rex_or_M8_i8_CF_mem(uint8_t x) {
    unsigned char flags = rex_or_M8_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_rex_or_M8_i8_SF_mem(int8_t x) {
    int8_t result = x | 0x02;
    unsigned char flags = rex_or_M8_i8_return_flags_mem((uint8_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_rex_or_M8_i8_ZF_mem(int8_t x) {
    int8_t result = x | 0x02;
    unsigned char flags = rex_or_M8_i8_return_flags_mem((uint8_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2
bool test_rex_or_M8_i8_PF_mem(uint8_t x) {
    unsigned char flags = rex_or_M8_i8_return_flags_mem(x);
    uint8_t result = x | 0x02;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char rex_or_M8_i8_return_OF_mem(uint8_t x) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "orb $0x02, (%2);"     // REX + 80/1 ib: [memory] = [memory] | imm8
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :                      // no clobbered registers
    );

    return of;
}

bool test_rex_or_M8_i8_OF_mem(uint8_t x) {
    return rex_or_M8_i8_return_OF_mem(x) == 0;  // Expect OF = 0
}

//*******************************************************
// r16,i16  

// Return full flags (from AH) after OR AX, imm16
unsigned char or_r16_i16_return_flags(uint16_t x) {
    unsigned char ah;
    

    __asm__ volatile (
        "movw %1, %%cx;"       // Load x into AX
        "orw $0x0002, %%cx;"   // OR AX with immediate 0x0002
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%cx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_r16_i16_CF(uint16_t x) {
    unsigned char flags = or_r16_i16_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}
  
// Sign Flag (SF) is bit 7
bool test_or_r16_i16_SF(int16_t x) {
    int16_t result = x | 0x0002;
    unsigned char flags = or_r16_i16_return_flags((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_r16_i16_ZF(int16_t x) {
    int16_t result = x | 0x0002;
    unsigned char flags = or_r16_i16_return_flags((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


bool test_or_r16_i16_PF(uint16_t x) {
    unsigned char flags = or_r16_i16_return_flags(x);
    int16_t result = x | 0x02;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // Cast to uint8_t
    
    return ((flags & 0x04) != 0) == (result_parity != 0); 
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_r16_i16_return_OF(uint16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%cx;"
        "orw $0x0002, %%cx;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%cx"
    );

    return of;
}

bool test_or_r16_i16_OF(uint16_t x) {
    return or_r16_i16_return_OF(x) == 0;  // Expect OF = 0
}
//*****************************************************
// m16,i16 

unsigned char or_m16_i16_return_flags(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
         "movw %1, (%2);"       // store x in memory location
        "orw $0x02, (%2);"     // 80/1 ib: [memory] = [memory] | imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"
        
    );

    return ah;
}

bool test_or_m16_i16_CF(uint16_t x) {
    unsigned char flags = or_m16_i16_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0 for OR
}

bool test_or_m16_i16_SF(int16_t x) {
    int16_t result = x | 0x0002;
    unsigned char flags = or_m16_i16_return_flags((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_m16_i16_ZF(int16_t x) {
    int16_t result = x | 0x0002;
    unsigned char flags = or_m16_i16_return_flags((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


bool test_or_m16_i16_PF(uint16_t x) {
    unsigned char flags = or_m16_i16_return_flags(x);
    int16_t result = x | 0x02;
    uint8_t result_parity = calculate_parity((uint8_t)result); 
    
    return ((flags & 0x04) != 0) == (result_parity != 0); 
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_m16_i16_return_OF_mem(uint16_t x) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "orw $0x02, (%2);"     // 80/1 ib: [memory] = [memory] | imm8
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :                      // no clobbered registers
    );

    return of;
}

bool test_or_m16_i16_OF_mem(uint8_t x) {
    return or_m16_i16_return_OF_mem(x) == 0;  // Expect OF = 0
}

//******************************************************
// r32,i32 

unsigned char or_r32_i32_return_flags(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%ecx;"       // Load x into ecx
        "orl $0x00000002, %%ecx;" // OR ecx with immediate 0x00000002
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%ecx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_r32_i32_CF(uint32_t x) {
    unsigned char flags = or_r32_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_r32_i32_SF(int32_t x) {
    int32_t result = x | 0x00000002;
    unsigned char flags = or_r32_i32_return_flags((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_r32_i32_ZF(int32_t x) {
    int32_t result = x | 0x00000002;
    unsigned char flags = or_r32_i32_return_flags((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_r32_i32_PF(uint32_t x) {
    unsigned char flags = or_r32_i32_return_flags(x);
    uint32_t result = x | 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0); 
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_r32_i32_return_OF(uint32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%ecx;"
        "orl $0x00000002, %%ecx;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%ecx"
    );

    return of;
}

bool test_or_r32_i32_OF(uint32_t x) {
    return or_r32_i32_return_OF(x) == 0;  // Expect OF = 0
}
//***************************************************
// m32,i32 

// Return full flags (from AH) after OR [mem32], imm32 (memory version)
unsigned char or_m32_i32_return_flags(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "orl $0x00000002, (%2);" // OR [memory] with immediate 0x00000002
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"                // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_m32_i32_CF(uint32_t x) {
    unsigned char flags = or_m32_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_m32_i32_SF(int32_t x) {
    int32_t result = x | 0x00000002;
    unsigned char flags = or_m32_i32_return_flags((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_m32_i32_ZF(int32_t x) {
    int32_t result = x | 0x00000002;
    unsigned char flags = or_m32_i32_return_flags((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_m32_i32_PF(uint32_t x) {
    unsigned char flags = or_m32_i32_return_flags(x);
    uint32_t result = x | 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0); 
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_m32_i32_return_OF(uint32_t x) {
    unsigned char of;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "orl $0x00000002, (%2);" // OR [memory] with immediate 0x00000002
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :                      // no clobbered registers
    );

    return of;
}

bool test_or_m32_i32_OF(uint32_t x) {
    return or_m32_i32_return_OF(x) == 0;  // Expect OF = 0
}

//***********************************************************
// r64,i64

// Return full flags (from AH) after OR rcx, imm32
unsigned char or_R64_i32_return_flags(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rcx;"       // Load x into rcx
        "orq $0x00000002, %%rcx;" // OR rcx with 32-bit immediate 0x00000002
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%rcx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_R64_i32_CF(uint64_t x) {
    unsigned char flags = or_R64_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_R64_i32_SF(int64_t x) {
    int64_t result = x | 0x00000002;
    unsigned char flags = or_R64_i32_return_flags((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_R64_i32_ZF(int64_t x) {
    int64_t result = x | 0x00000002;
    unsigned char flags = or_R64_i32_return_flags((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_R64_i32_PF(uint64_t x) {
    unsigned char flags = or_R64_i32_return_flags(x);
    uint64_t result = x | 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
     return ((flags & 0x04) != 0) == (result_parity != 0);  
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_R64_i32_return_OF(uint64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rcx;"
        "orq $0x00000002, %%rcx;"
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%rcx"
    );

    return of;
}

bool test_or_R64_i32_OF(uint64_t x) {
    return or_R64_i32_return_OF(x) == 0;  // Expect OF = 0
}

//**********************************************************
// m64,i32 

// Return full flags (from AH) after OR [mem64], imm32 (memory version)
unsigned char or_m64_i32_return_flags(uint64_t x) {
    unsigned char ah;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location (64-bit)
        "orq $0x00000002, (%2);" // OR [memory] with 32-bit immediate (sign-extended to 64-bit)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"                // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_m64_i32_CF(uint64_t x) {
    unsigned char flags = or_m64_i32_return_flags(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_m64_i32_SF(int64_t x) {
    int64_t result = x | 0x00000002;
    unsigned char flags = or_m64_i32_return_flags((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_m64_i32_ZF(int64_t x) {
    int64_t result = x | 0x00000002;
    unsigned char flags = or_m64_i32_return_flags((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_m64_i32_PF(uint64_t x) {
    unsigned char flags = or_m64_i32_return_flags(x);
    uint64_t result = x | 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0); 
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_m64_i32_return_OF(uint64_t x) {
    unsigned char of;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location (64-bit)
        "orq $0x00000002, (%2);" // OR [memory] with 32-bit immediate (sign-extended to 64-bit)
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :                      // no clobbered registers
    );

    return of;
}

bool test_or_m64_i32_OF(uint64_t x) {
    return or_m64_i32_return_OF(x) == 0;  // Expect OF = 0
}

//*************************************************************8
// r16,i8 

// Return full flags (from AH) after OR AX, imm8 (register version - 83/1 ib for 16-bit)
unsigned char or_r16_i8_return_flags_reg(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "orw $0x02, %%ax;"     // 83/1 ib: OR AX with sign-extended 8-bit immediate
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%ax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_r16_i8_CF_reg(uint16_t x) {
    unsigned char flags = or_r16_i8_return_flags_reg(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_r16_i8_SF_reg(int16_t x) {
    int16_t result = x | 0x0002;  // 0x02 sign-extended to 16-bit
    unsigned char flags = or_r16_i8_return_flags_reg((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_r16_i8_ZF_reg(int16_t x) {
    int16_t result = x | 0x0002;  // 0x02 sign-extended to 16-bit
    unsigned char flags = or_r16_i8_return_flags_reg((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_r16_i8_PF_reg(uint16_t x) {
    unsigned char flags = or_r16_i8_return_flags_reg(x);
    uint16_t result = x | 0x0002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_r16_i8_return_OF_reg(uint16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"
        "orw $0x02, %%ax;"     
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%ax"
    );

    return of;
}

bool test_or_r16_i8_OF_reg(uint16_t x) {
    return or_r16_i8_return_OF_reg(x) == 0;  // Expect OF = 0
}

//******************************************************
// m16,i8 

// Return full flags (from AH) after OR [mem16], imm8 (memory version - 83/1 ib for 16-bit)
unsigned char or_m16_i8_return_flags_mem(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "orw $0x02, (%2);"     // 83/1 ib: OR [memory] with sign-extended 8-bit immediate
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"                // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_m16_i8_CF_mem(uint16_t x) {
    unsigned char flags = or_m16_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_m16_i8_SF_mem(int16_t x) {
    int16_t result = x | 0x0002;  // 0x02 sign-extended to 16-bit
    unsigned char flags = or_m16_i8_return_flags_mem((uint16_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_m16_i8_ZF_mem(int16_t x) {
    int16_t result = x | 0x0002;  // 0x02 sign-extended to 16-bit
    unsigned char flags = or_m16_i8_return_flags_mem((uint16_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_m16_i8_PF_mem(uint16_t x) {
    unsigned char flags = or_m16_i8_return_flags_mem(x);
    uint16_t result = x | 0x0002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_m16_i8_return_OF_mem(uint16_t x) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "orw $0x02, (%2);"     // 83/1 ib: OR [memory] with sign-extended 8-bit immediate
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :                      // no clobbered registers
    );

    return of;
}

bool test_or_m16_i8_OF_mem(uint16_t x) {
    return or_m16_i8_return_OF_mem(x) == 0;  // Expect OF = 0
}


//*************************************************************
// r32,i8 

unsigned char or_r32_i8_return_flags_reg(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%ecx;"      // Load x into ECX
        "orl $0x02, %%ecx;"    // 83/1 ib: OR ECX with sign-extended 8-bit immediate
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%ecx", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_r32_i8_CF_reg(uint32_t x) {
    unsigned char flags = or_r32_i8_return_flags_reg(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_r32_i8_SF_reg(int32_t x) {
    int32_t result = x | 0x00000002;  // 0x02 sign-extended to 32-bit
    unsigned char flags = or_r32_i8_return_flags_reg((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_r32_i8_ZF_reg(int32_t x) {
    int32_t result = x | 0x00000002;  // 0x02 sign-extended to 32-bit
    unsigned char flags = or_r32_i8_return_flags_reg((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_r32_i8_PF_reg(uint32_t x) {
    unsigned char flags = or_r32_i8_return_flags_reg(x);
    uint32_t result = x | 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_r32_i8_return_OF_reg(uint32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%ecx;"
        "orl $0x02, %%ecx;"    // OR ECX with sign-extended 8-bit immediate
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%ecx"
    );

    return of;
}

bool test_or_r32_i8_OF_reg(uint32_t x) {
    return or_r32_i8_return_OF_reg(x) == 0;  // Expect OF = 0
}

//***********************************************************
// m32,i8 

// Return full flags (from AH) after OR [mem32], imm8 (memory version - 83/1 ib)
unsigned char or_m32_i8_return_flags_mem(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "orl $0x02, (%2);"     // 83/1 ib: OR [memory] with sign-extended 8-bit immediate
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"                // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_m32_i8_CF_mem(uint32_t x) {
    unsigned char flags = or_m32_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_m32_i8_SF_mem(int32_t x) {
    int32_t result = x | 0x00000002;  // 0x02 sign-extended to 32-bit
    unsigned char flags = or_m32_i8_return_flags_mem((uint32_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_m32_i8_ZF_mem(int32_t x) {
    int32_t result = x | 0x00000002;  // 0x02 sign-extended to 32-bit
    unsigned char flags = or_m32_i8_return_flags_mem((uint32_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_m32_i8_PF_mem(uint32_t x) {
    unsigned char flags = or_m32_i8_return_flags_mem(x);
    uint32_t result = x | 0x00000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_m32_i8_return_OF_mem(uint32_t x) {
    unsigned char of;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "orl $0x02, (%2);"     // 83/1 ib: OR [memory] with sign-extended 8-bit immediate
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :                      // no clobbered registers
    );

    return of;
}

bool test_or_m32_i8_OF_mem(uint32_t x) {
    return or_m32_i8_return_OF_mem(x) == 0;  // Expect OF = 0
}

//*************************************************************
// r64,i8 
// Return full flags (from AH) after OR RAX, imm8 (register version - REX.W + 83/1 ib)
unsigned char or_r64_i8_return_flags_reg(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // Load x into RAX
        "orq $0x02, %%rax;"    // REX.W + 83/1 ib: OR RAX with sign-extended 8-bit immediate
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x)
        : "%rax", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_r64_i8_CF_reg(uint64_t x) {
    unsigned char flags = or_r64_i8_return_flags_reg(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_r64_i8_SF_reg(int64_t x) {
    int64_t result = x | 0x0000000000000002;  // 0x02 sign-extended to 64-bit
    unsigned char flags = or_r64_i8_return_flags_reg((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_r64_i8_ZF_reg(int64_t x) {
    int64_t result = x | 0x0000000000000002;  // 0x02 sign-extended to 64-bit
    unsigned char flags = or_r64_i8_return_flags_reg((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_r64_i8_PF_reg(uint64_t x) {
    unsigned char flags = or_r64_i8_return_flags_reg(x);
    uint64_t result = x | 0x0000000000000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_r64_i8_return_OF_reg(uint64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"
        "orq $0x02, %%rax;"   
        "seto %0;"
        : "=r"(of)
        : "r"(x)
        : "%rax"
    );

    return of;
}

bool test_or_r64_i8_OF_reg(uint64_t x) {
    return or_r64_i8_return_OF_reg(x) == 0;  // Expect OF = 0
}

//*********************************************************************
// m64,i8 
unsigned char or_m64_i8_return_flags_mem(uint64_t x) {
    unsigned char ah;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "orq $0x02, (%2);"     // REX.W + 83/1 ib: OR [memory] with sign-extended 8-bit immediate
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"                // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_m64_i8_CF_mem(uint64_t x) {
    unsigned char flags = or_m64_i8_return_flags_mem(x);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_m64_i8_SF_mem(int64_t x) {
    int64_t result = x | 0x0000000000000002;  // 0x02 sign-extended to 64-bit
    unsigned char flags = or_m64_i8_return_flags_mem((uint64_t)x);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_m64_i8_ZF_mem(int64_t x) {
    int64_t result = x | 0x0000000000000002;  // 0x02 sign-extended to 64-bit
    unsigned char flags = or_m64_i8_return_flags_mem((uint64_t)x);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_m64_i8_PF_mem(uint64_t x) {
    unsigned char flags = or_m64_i8_return_flags_mem(x);
    uint64_t result = x | 0x0000000000000002;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_m64_i8_return_OF_mem(uint64_t x) {
    unsigned char of;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "orq $0x02, (%2);"     // REX.W + 83/1 ib: OR [memory] with sign-extended 8-bit immediate
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(&val)    // inputs: x, memory address
        :                      // no clobbered registers
    );

    return of;
}

bool test_or_m64_i8_OF_mem(uint64_t x) {
    return or_m64_i8_return_OF_mem(x) == 0;  // Expect OF = 0
}

//***********************************************************
// r8,r8 


unsigned char or_r8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // Load x into AL
        "movb %2, %%bl;"       // Load y into BL
        "orb %%bl, %%al;"      // 08/r: OR AL with BL
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%al", "%bl", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_r8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = or_r8_r8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_r8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = or_r8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_r8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = or_r8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2
bool test_or_r8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = or_r8_r8_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_r8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%al;"
        "movb %2, %%bl;"
        "orb %%bl, %%al;"      // 08/r: OR AL with BL
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%al", "%bl"
    );

    return of;
}

bool test_or_r8_r8_OF(uint8_t x, uint8_t y) {
    return or_r8_r8_return_OF(x, y) == 0;  // Expect OF = 0
}

//***************************************************
// m8,r8 

// Return full flags (from AH) after OR [mem8], r8 (memory to register version)
unsigned char or_m8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%bl;"       // load y into BL
        "orb %%bl, (%3);"      // 08/r: OR [memory] with BL
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%bl", "%ah"         // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_m8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = or_m8_r8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_m8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = or_m8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_m8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = or_m8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2
bool test_or_m8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = or_m8_r8_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_m8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%bl;"       // load y into BL
        "orb %%bl, (%3);"      // 08/r: OR [memory] with BL
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%bl"                // clobbered registers
    );

    return of;
}

bool test_or_m8_r8_OF(uint8_t x, uint8_t y) {
    return or_m8_r8_return_OF(x, y) == 0;  // Expect OF = 0
}

//*********************************************************
// REX R8,R8 

// Return full flags (from AH) after REX + OR R8B, R9B (register to register version)
unsigned char rex_or_r8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r8b;"      // Load x into R8B (extended register)
        "movb %2, %%r9b;"      // Load y into R9B (extended register)
        "orb %%r9b, %%r8b;"    // REX + 08/r: OR R8B with R9B
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%r8", "%r9", "%ah"
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_rex_or_r8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_or_r8_r8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_rex_or_r8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = rex_or_r8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_rex_or_r8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = rex_or_r8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2
bool test_rex_or_r8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_or_r8_r8_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char rex_or_r8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%r8b;"
        "movb %2, %%r9b;"
        "orb %%r9b, %%r8b;"    // REX + 08/r: OR R8B with R9B
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%r8", "%r9"
    );

    return of;
}

bool test_rex_or_r8_r8_OF(uint8_t x, uint8_t y) {
    return rex_or_r8_r8_return_OF(x, y) == 0;  // Expect OF = 0
}

//************************************************************
// REX M8,R8 

// Return full flags (from AH) after REX + OR [mem8], r8 (memory to extended register version)
unsigned char rex_or_m8_r8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%r9b;"      // load y into R9B (extended register)
        "orb %%r9b, (%3);"     // REX + 08/r: OR [memory] with R9B
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%r9", "%ah"         // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_rex_or_m8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_or_m8_r8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_rex_or_m8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = rex_or_m8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_rex_or_m8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = rex_or_m8_r8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2
bool test_rex_or_m8_r8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_or_m8_r8_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char rex_or_m8_r8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%r9b;"      // load y into R9B (extended register)
        "orb %%r9b, (%3);"     // REX + 08/r: OR [memory] with R9B
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%r9"                // clobbered registers
    );

    return of;
}

bool test_rex_or_m8_r8_OF(uint8_t x, uint8_t y) {
    return rex_or_m8_r8_return_OF(x, y) == 0;  // Expect OF = 0
}

//******************************************************
// R16,R16 

unsigned char or_r16_r16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "movw %2, %%bx;"       // Load y into BX
        "orw %%bx, %%ax;"      // OR AX with BX (0x09 /r)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%ax", "%bx", "%ah"
    );

    return ah;
}
bool test_or_r16_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = or_r16_r16_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

bool test_or_r16_r16_SF(int16_t x, int16_t y) {
    int16_t result = x | y;
    unsigned char flags = or_r16_r16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_r16_r16_ZF(int16_t x, int16_t y) {
    int16_t result = x | y;
    unsigned char flags = or_r16_r16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

bool test_or_r16_r16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = or_r16_r16_return_flags(x, y);
  uint16_t result = x | y;
    uint8_t result_parity = calculate_parity((uint8_t)result); 
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

unsigned char or_r16_r16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"
        "movw %2, %%bx;"
        "orw %%bx, %%ax;"   // 0x09 /r: OR r/m16, r16
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%ax", "%bx"
    );

    return of;
}

bool test_or_r16_r16_OF(uint16_t x, uint16_t y) {
    return or_r16_r16_return_OF(x, y) == 0;  // OF should be cleared
}

//****************************************************
// M16,R16 

unsigned char or_m16_r16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%3);"       // store x in memory location
        "movw %2, %%bx;"       // load y into BX
        "orw %%bx, (%3);"      // 08/r: OR [memory] with BX
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%bx", "%ah"         // clobbered registers
    );

    return ah;
}

bool test_or_m16_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = or_m16_r16_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

bool test_or_m16_r16_SF(int16_t x, int16_t y) {
    int16_t result = x | y;
    unsigned char flags = or_m16_r16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_m16_r16_ZF(int16_t x, int16_t y) {
    int16_t result = x | y;
    unsigned char flags = or_m16_r16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


bool test_or_m16_r16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = or_m16_r16_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

unsigned char or_m16_r16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%3);"       // store x in memory location
        "movw %2, %%bx;"       // load y into Bx
        "orw %%bx, (%3);"      // 08/r: OR [memory] with Bx
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%bx"                // clobbered registers
    );

    return of;
}

bool test_or_m16_r16_OF(uint16_t x, uint16_t y) {
    return or_m16_r16_return_OF(x, y) == 0;  // Expect OF = 0
}
//**************************************************************
// r32,r32 

unsigned char or_r32_r32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // Load x into EAX
        "movl %2, %%ebx;"      // Load y into EBX
        "orl %%ebx, %%eax;"    // OR EAX with EBX
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%eax", "%ebx", "%ah"
    );

    return ah;
}

bool test_or_r32_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = or_r32_r32_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

bool test_or_r32_r32_SF(int32_t x, int32_t y) {
    int32_t result = x | y;
    unsigned char flags = or_r32_r32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_r32_r32_ZF(int32_t x, int32_t y) {
    int32_t result = x | y;
    unsigned char flags = or_r32_r32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


bool test_or_r32_r32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = or_r32_r32_return_flags(x, y);
    uint8_t result = x | y;  
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

unsigned char or_r32_r32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"
        "movl %2, %%ebx;"
        "orl %%ebx, %%eax;"   // OR EAX, EBX
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%eax", "%ebx"
    );

    return of;
}

bool test_or_r32_r32_OF(uint32_t x, uint32_t y) {
    return or_r32_r32_return_OF(x, y) == 0;  // OF should be cleared
}

//********************************************************
// m32,r32 

unsigned char or_m32_r32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%3);"       // store x in memory location
        "movl %2, %%ebx;"       // load y into EBX
        "orl %%ebx, (%3);"      // 08/r: OR [memory] with EBX
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%ebx", "%ah"         // clobbered registers
    );

    return ah;
}

bool test_or_m32_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = or_m32_r32_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

bool test_or_m32_r32_SF(int32_t x, int32_t y) {
    int32_t result = x | y;
    unsigned char flags = or_m32_r32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_m32_r32_ZF(int32_t x, int32_t y) {
    int32_t result = x | y;
    unsigned char flags = or_m32_r32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


bool test_or_m32_r32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = or_m32_r32_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

unsigned char or_m32_r32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
    uint32_t val;
__asm__ volatile (
        "movl %1, (%3);"       // store x in memory location
        "movl %2, %%ebx;"       // load y into Bx
        "orl %%ebx, (%3);"      // 08/r: OR [memory] with Bx
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%ebx"                // clobbered registers
    );

    return of;
}

bool test_or_m32_r32_OF(uint32_t x, uint32_t y) {
    return or_m32_r32_return_OF(x, y) == 0;  // OF should be 0
}

//*****************************************************
// r64,r64 

unsigned char or_r64_r64_return_flags(uint64_t x, uint64_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"       // Load x into RAX
        "movq %2, %%rbx;"       // Load y into RBX
        "orq %%rbx, %%rax;"     // OR RAX with RBX
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "%rax", "%rbx", "%ah"
    );

    return ah;
}

bool test_or_r64_r64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = or_r64_r64_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

bool test_or_r64_r64_SF(int64_t x, int64_t y) {
    int64_t result = x | y;
    unsigned char flags = or_r64_r64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_r64_r64_ZF(int64_t x, int64_t y) {
    int64_t result = x | y;
    unsigned char flags = or_r64_r64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


bool test_or_r64_r64_PF(uint64_t x, uint64_t y) {
    unsigned char flags = or_r64_r64_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

unsigned char or_r64_r64_return_OF(uint64_t x, uint64_t y) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"
        "movq %2, %%rbx;"
        "orq %%rbx, %%rax;"   // OR RAX, RBX
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "%rax", "%rbx"
    );

    return of;
}

bool test_or_r64_r64_OF(uint64_t x, uint64_t y) {
    return or_r64_r64_return_OF(x, y) == 0;  // OF should be 0
}

//***************************************************************
// m64,r64 

unsigned char or_m64_r64_return_flags(uint64_t x, uint64_t y) {
    unsigned char ah;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%3);"       // store x in memory location
        "movq %2, %%rbx;"       // load y into RBX
        "orq %%rbx, (%3);"      // 08/r: OR [memory] with RBX
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%rbx", "%ah"         // clobbered registers
    );

    return ah;
}
       bool test_or_m64_r64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = or_m64_r64_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

bool test_or_m64_r64_SF(int64_t x, int64_t y) {
    int64_t result = x | y;
    unsigned char flags = or_m64_r64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_m64_r64_ZF(int64_t x, int64_t y) {
    int64_t result = x | y;
    unsigned char flags = or_m64_r64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

bool test_or_m64_r64_PF(uint64_t x, uint64_t y) {
    unsigned char flags = or_m64_r64_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

unsigned char or_m64_r64_return_OF(uint64_t x, uint64_t y) {
    unsigned char of;
    uint64_t val;
    __asm__ volatile (
        "movq %1, (%3);"       // store x in memory location
        "movq %2, %%rbx;"       // load y into RBx
        "orq %%rbx, (%3);"      
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%rbx"                // clobbered registers
    );

    return of;
}
 
bool test_or_m64_r64_OF(uint64_t x, uint64_t y) {
    return or_m64_r64_return_OF(x, y) == 0;  // OF should be 0
}

//***********************************************************
// R8,M8 

// Return full flags (from AH) after OR AL, [mem8] (register from memory version)
unsigned char or_r8_m8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location (source)
        "movb %1, %%al;"       // load x into AL (destination)
        "orb (%3), %%al;"      // 0A/r: OR AL with [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%al", "%ah"         // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_r8_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = or_r8_m8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_r8_m8_SF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = or_r8_m8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_r8_m8_ZF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = or_r8_m8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

// Parity Flag (PF) is bit 2
bool test_or_r8_m8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = or_r8_m8_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_r8_m8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location (source)
        "movb %1, %%al;"       // load x into AL (destination)
        "orb (%3), %%al;"      // 0A/r: OR AL with [memory]
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%al"                // clobbered registers
    );

    return of;
}

bool test_or_r8_m8_OF(uint8_t x, uint8_t y) {
    return or_r8_m8_return_OF(x, y) == 0;  // Expect OF = 0
}

//****************************************************
// REX R8,M8 

// Return full flags (from AH) after REX + OR R8B, [mem8] (extended register from memory version)
unsigned char rex_or_r8_m8_return_flags(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location (source)
        "movb %1, %%r8b;"      // load x into R8B (extended register destination)
        "orb (%3), %%r8b;"     // REX + 0A/r: OR R8B with [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%r8", "%ah"         // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_rex_or_r8_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_or_r8_m8_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_rex_or_r8_m8_SF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = rex_or_r8_m8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_rex_or_r8_m8_ZF(int8_t x, int8_t y) {
    int8_t result = x | y;
    unsigned char flags = rex_or_r8_m8_return_flags((uint8_t)x, (uint8_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


// Parity Flag (PF) is bit 2
bool test_rex_or_r8_m8_PF(uint8_t x, uint8_t y) {
    unsigned char flags = rex_or_r8_m8_return_flags(x, y);
    uint8_t result = x | y;
    uint8_t result_parity = calculate_parity(result);
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char rex_or_r8_m8_return_OF(uint8_t x, uint8_t y) {
    unsigned char of;
    uint8_t val;

    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location (source)
        "movb %1, %%r8b;"      // load x into R8B (extended register destination)
        "orb (%3), %%r8b;"     // REX + 0A/r: OR R8B with [memory]
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%r8"                // clobbered registers
    );

    return of;
}

bool test_rex_or_r8_m8_OF(uint8_t x, uint8_t y) {
    return rex_or_r8_m8_return_OF(x, y) == 0;  // Expect OF = 0
}

//************************************************888
// R16,M16

// Return full flags (from AH) after OR AX, [mem16] (16-bit register from memory version)
unsigned char or_r16_m16_return_flags(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %2, (%3);"       // store y in memory location (source)
        "movw %1, %%ax;"       // load x into AX (destination)
        "orw (%3), %%ax;"      // 0B/r: OR AX with [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

// Carry Flag (CF) is bit 0. OR always clears CF.
bool test_or_r16_m16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = or_r16_m16_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

// Sign Flag (SF) is bit 7
bool test_or_r16_m16_SF(int16_t x, int16_t y) {
    int16_t result = x | y;
    unsigned char flags = or_r16_m16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

// Zero Flag (ZF) is bit 6
bool test_or_r16_m16_ZF(int16_t x, int16_t y) {
    int16_t result = x | y;
    unsigned char flags = or_r16_m16_return_flags((uint16_t)x, (uint16_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}



// Parity Flag (PF) is bit 2 - only considers lower 8 bits
bool test_or_r16_m16_PF(uint16_t x, uint16_t y) {
    unsigned char flags = or_r16_m16_return_flags(x, y);
    uint16_t result = x | y;
    uint8_t result_parity = calculate_parity((uint8_t)result);  // PF only looks at lower 8 bits
    
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

// Overflow Flag (OF) – OR always clears OF
unsigned char or_r16_m16_return_OF(uint16_t x, uint16_t y) {
    unsigned char of;
    uint16_t val;

    __asm__ volatile (
        "movw %2, (%3);"       // store y in memory location (source)
        "movw %1, %%ax;"       // load x into AX (destination)
        "orw (%3), %%ax;"      // 0B/r: OR AX with [memory]
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%ax"                // clobbered registers
    );

    return of;
}

bool test_or_r16_m16_OF(uint16_t x, uint16_t y) {
    return or_r16_m16_return_OF(x, y) == 0;  // Expect OF = 0
}

//************************************************************
// R32,M32

unsigned char or_r32_m32_return_flags(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;  

      __asm__ volatile (
        "movl %2, (%3);"       // store y in memory location (source)
        "movl %1, %%eax;"       // load x into EAX (destination)
        "orl (%3), %%eax;"      
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%eax", "%ah"         // clobbered registers
    );

    return ah;
}

bool test_or_r32_m32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = or_r32_m32_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

bool test_or_r32_m32_SF(int32_t x, int32_t y) {
    int32_t result = x | y;
    unsigned char flags = or_r32_m32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_r32_m32_ZF(int32_t x, int32_t y) {
    int32_t result = x | y;
    unsigned char flags = or_r32_m32_return_flags((uint32_t)x, (uint32_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}


bool test_or_r32_m32_PF(uint32_t x, uint32_t y) {
    unsigned char flags = or_r32_m32_return_flags(x, y);
    uint8_t result = x | y;  // PF is based on low byte
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

unsigned char or_r32_m32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
     uint32_t val;

    __asm__ volatile (
        "movl %2, (%3);"       // store y in memory location (source)
        "movl %1, %%eax;"       // load x into EAX (destination)
        "orl (%3), %%eax;"      
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%eax"                // clobbered registers
    );

    return of;
}

bool test_or_r32_m32_OF(uint32_t x, uint32_t y) {
    return or_r32_m32_return_OF(x, y) == 0;  // OF should be 0
}

//**********************************************************
// R64,M64 

unsigned char or_r64_m64_return_flags(uint64_t x, uint64_t y) {
    unsigned char ah;
       uint64_t val;  

      __asm__ volatile (
        "movq %2, (%3);"       // store y in memory location (source)
        "movq %1, %%rax;"       // load x into RAX (destination)
        "orq (%3), %%rax;"      
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%rax", "%ah"         // clobbered registers
    );
    return ah;
}

bool test_or_r64_m64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = or_r64_m64_return_flags(x, y);
    return ((flags & 0x01) == 0x00);  // CF should be 0
}

bool test_or_r64_m64_SF(int64_t x, int64_t y) {
    int64_t result = x | y;
    unsigned char flags = or_r64_m64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result < 0) == ((flags & 0x80) != 0));
}

bool test_or_r64_m64_ZF(int64_t x, int64_t y) {
    int64_t result = x | y;
    unsigned char flags = or_r64_m64_return_flags((uint64_t)x, (uint64_t)y);
    return ((result == 0) == ((flags & 0x40) != 0));
}

bool test_or_r64_m64_PF(uint64_t x, uint64_t y) {
    unsigned char flags = or_r64_m64_return_flags(x, y);
    uint8_t result = (uint8_t)((x | y) & 0xFF);  // PF checks low byte only
    uint8_t result_parity = calculate_parity(result);
    return ((flags & 0x04) != 0) == (result_parity != 0);
}

unsigned char or_r64_m64_return_OF(uint64_t x, uint64_t y) {
    unsigned char of;
     uint64_t val;

    __asm__ volatile (
        "movq %2, (%3);"       // store y in memory location (source)
        "movq %1, %%rax;"       // load x into RAX (destination)
        "orq (%3), %%rax;"      
        "seto %0;"             // set OF flag into 'of'
        : "=r"(of)             // output
        : "r"(x), "r"(y), "r"(&val)  // inputs: x, y, memory address
        : "%rax"                // clobbered registers
    );

    return of;
}

bool test_or_r64_m64_OF(uint64_t x, uint64_t y) {
    return or_r64_m64_return_OF(x, y) == 0;  // OF should be 0
}

// dummy main function, to allow us to link the executable
int main () { return 0;}