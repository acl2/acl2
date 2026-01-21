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




//**********************************************************
// CMP al, i8
unsigned char cmp_AL_i8_return_CF(uint8_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movb %1, %%al;"       // al = x
        "cmpb $0x02, %%al;"       // al -= imm (immediate)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x)                 // inputs
        : "%al", "%ah"         // clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_cmp_AL_i8_CF (uint8_t  x) {
 
    unsigned char flags = cmp_AL_i8_return_CF(x);

    if (0x02 > x) {
        // Expect CF = 1 (borrow occurred)
        return ((flags & 0x01) == 0x01);
    } else {
        // Expect CF = 0 (no borrow)
        return ((flags & 0x01) == 0x00);
    }
}


unsigned char cmp_AL_i8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"      // al = x 
        "cmpb $0x02, %%al;"      // al -= imm 
        "lahf;"               // load flags into AH
        "movb %%ah, %0;"      // store AH in output variable
        : "=r" (ah)           // output
        : "r" (x)            // inputs
        : "%al", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_AL_i8_SF (int8_t x) {
  
  int8_t diff = x-0x02;  
    unsigned char flags = cmp_AL_i8_return_flags(x);

    if (diff<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_AL_i8_ZF (int8_t x) {
    int8_t diff = x - 0x02;
    unsigned char flags = cmp_AL_i8_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_AL_i8_AF (int8_t x) {
    int8_t x_lsb = x & 0xF;  // Get lower 4 bits of x
    int8_t imm_lsb = 0x02 & 0xF;  // Get lower 4 bits of y
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_AL_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}


//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_cmp_AL_i8_PF (int8_t x) {
   
    unsigned char flags = cmp_AL_i8_return_flags(x);

    int8_t result = x - 0x02;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}



unsigned char cmp_AL_i8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%al;"      // Load x into AL (8-bit)
        "cmpb $0x02, %%al;"      // Cmptract immediate from AL
        "seto %0;"            // Set OF flag into 'of'
        : "=r"(of)            // Output operand
        : "r"(x)               // input
        : "%al"               // Clobbered register
    );

    return of;
}

//check property for OF

bool test_cmp_AL_i8_OF (int8_t x) {
    int8_t  diff = x - 0x02;
    unsigned char of = cmp_AL_i8_return_OF (x);
  if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//**********************************************************
// CMP AX, i16

unsigned char cmp_AX_i16_return_CF(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "cmpw $0x0002, %%ax;"       // Cmptract immediate value from AX
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output variable
        : "=r" (ah)            // output: store AH flags in 'ah'
        : "r" (x)              // inputs: x = register, imm = immediate
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah
bool test_cmp_AX_i16_CF (uint16_t  x) {
    
    unsigned char flags = cmp_AX_i16_return_CF(x);

    if (0x0002 > x) {
        // Expect CF = 1 (borrow occurred)
        return ((flags & 0x01) == 0x01);
    } else {
        // Expect CF = 0 (no borrow)
        return ((flags & 0x01) == 0x00);
    }
       
}


unsigned char cmp_AX_i16_return_flags(int16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"      // Load x into AX
        "cmpw $0x0002, %%ax;"      // Cmptract immediate from AX
        "lahf;"               // Load flags into AH
        "movb %%ah, %0;"      // Move AH to output variable
        : "=r" (ah)           // output
        : "r" (x)             // inputs
        : "%ax", "%ah"        // clobbered registers
    );

    return ah;
}


//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_cmp_AX_i16_SF (int16_t x) {
  
  int16_t diff = x- 0x0002;  
    unsigned char flags = cmp_AX_i16_return_flags(x);

    if (diff<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    return false; 

    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_cmp_AX_i16_ZF (int16_t x) {
    int16_t diff = x - 0x0002;
    unsigned char flags = cmp_AX_i16_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_cmp_AX_i16_AF (int16_t x) {

    int16_t x_lsb = x & 0x000F;  // Get lower 4 bits of x
    int16_t imm_lsb = 0x0002 & 0x000F;  // Get lower 4 bits of y
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_AX_i16_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}




//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_cmp_AX_i16_PF (int16_t x) {
   
    unsigned char flags = cmp_AX_i16_return_flags(x);

    int16_t result = x - 0x0002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}




unsigned char cmp_AX_i16_return_OF(int16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"     // Load x into AX
        "cmpw $0x0002, %%ax;"     // Cmptract immediate value from AX
        "seto %0;"           // Set OF flag into 'of'
        : "=r"(of)           // Output operand
        : "r"(x)              // Inputs: x in register, imm as immediate
        : "%ax"              // Clobbered register
    );

    return of;
}


//check property for OF
bool test_cmp_AX_i16_OF (int16_t x) {
     int16_t diff = x - 0x0002;
    unsigned char of = cmp_AX_i16_return_OF (x);
     if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//**********************************************************
// CMP EAX, i32

unsigned char cmp_EAX_i32_return_CF(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x 
        "cmpl $0x00000002, %%eax;"      // eax -= imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output
        : "=r" (ah)            // output
        : "r" (x)       // inputs: register and immediate
        : "%eax", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah

bool test_cmp_EAX_i32_CF (uint32_t  x) {
    
    unsigned char flags = cmp_EAX_i32_return_CF(x);

    if (0x00000002 > x) {
        // Expect CF = 1 (borrow occurred)
        return ((flags & 0x01) == 0x01);
    } else {
        // Expect CF = 0 (no borrow)
        return ((flags & 0x01) == 0x00);
    }      

}


unsigned char cmp_EAX_i32_return_flags(int32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"       // eax = x (32-bit)
        "cmpl $0x00000002, %%eax;"       // eax -= imm (immediate)
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output
        : "=r" (ah)
        : "r" (x)
        : "%eax", "%ah"
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_cmp_EAX_i32_SF (int32_t x) {
  
  int32_t  diff = x- 0x00000002;  
    unsigned char flags = cmp_EAX_i32_return_flags(x);

    if (diff<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    return false; 
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_cmp_EAX_i32_ZF (int32_t x) {
    int32_t diff = x - 0x00000002;
    unsigned char flags = cmp_EAX_i32_return_flags(x);

    if (diff == 0) {   
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_EAX_i32_AF (int32_t x) {
     int32_t x_lsb = x & 0X0000000F;  // Get lower 4 bits of x
     int32_t imm_lsb = 0x00000002 & 0X0000000F;  // Get lower 4 bits of y
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_EAX_i32_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_cmp_EAX_i32_PF (int32_t x) {
   
    unsigned char flags = cmp_EAX_i32_return_flags(x);

    int32_t result = x - 0x00000002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}


unsigned char cmp_EAX_i32_return_OF(int32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"     // Load x into EAX (32-bit register)
        "cmpl $0x00000002, %%eax;"     // Cmptract immediate value from EAX
        "seto %0;"            // Set OF flag into 'of'
        : "=r"(of)            // Output
        : "r"(x)                   // Inputs: register and immediate
        : "%eax"              // Clobbered register
    );

    return of;
}


//check property for OF

bool test_cmp_EAX_i32_OF (int32_t x) {
    int32_t diff = x - 0x00000002;
    unsigned char of = cmp_EAX_i32_return_OF (x);
 if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//**********************************************************
// CMP RAX,i32


uint64_t cmp_RAX_i32_return_CF(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"           // Load x into RAX
        "cmpq $0x00000002, %%rax;"  // Cmptract immediate value from RAX
        "lahf;"                     // Load flags into AH
        "movb %%ah, %0;"            // Move AH to output variable
        : "=r" (ah)                 // output: store AH flags in 'ah'
        : "r" (x)                   // inputs: x = register
        : "%rax", "%ah"             // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah

bool test_cmp_RAX_i32_CF (uint64_t x) {
     
    unsigned char flags = cmp_RAX_i32_return_CF(x);

    if (0x000000002 > x) {
        // Expect CF = 1 (borrow occurred)
        return ((flags & 0x01) == 0x01);
    } else {
        // Expect CF = 0 (no borrow)
        return ((flags & 0x01) == 0x00);
    }
       
}
unsigned char cmp_RAX_i32_return_flags(int64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"           // Load x into RAX
        "cmpq $0x00000002, %%rax;"  // Cmptract immediate from RAX
        "lahf;"                     // Load flags into AH
        "movb %%ah, %0;"            // Move AH to output variable
        : "=r" (ah)                 // output
        : "r" (x)                   // inputs
        : "%rax", "%ah"             // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_RAX_i32_SF (int64_t x) {
    int64_t diff = x - 0x00000002;  
    unsigned char flags = cmp_RAX_i32_return_flags(x);

    if (diff < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}
    
//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_RAX_i32_ZF (int64_t x) {
    int64_t diff = x - 0x00000002;
    unsigned char flags = cmp_RAX_i32_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_RAX_i32_AF (int64_t x) {
    int64_t x_lsb = x & 0x0000000F;               // Get lower 4 bits of x
    int64_t imm_lsb = 0x00000002 & 0x0000000F;    
    
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_RAX_i32_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}


 bool test_cmp_RAX_i32_PF (int64_t x) {
   
    unsigned char flags = cmp_RAX_i32_return_flags(x);

    int64_t result = x - 0x00000002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}


unsigned char cmp_RAX_i32_return_OF(int64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"           // Load x into RAX
        "cmpq $0x00000002, %%rax;"  // Cmptract immediate value from RAX
        "seto %0;"                  // Set OF flag into 'of'
        : "=r"(of)                  // Output operand
        : "r"(x)                    // Inputs: x in register
        : "%rax"                    // Clobbered register
    );

    return of;
}

//check property for OF
bool test_cmp_RAX_i32_OF (int64_t x) {
    int64_t diff = x - 0x00000002;
    unsigned char of = cmp_RAX_i32_return_OF(x);

    if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//**********************************************************
// CMP r8, i8
unsigned char cmp_r8_i8_return_CF(uint8_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movb %1, %%cl;"       // cl = x
        "cmpb $0x02, %%cl;"       // cl -= imm (immediate)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x)                 // inputs
        : "%cl", "%ah"         // clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_cmp_r8_i8_CF (uint8_t  x) {
 
unsigned char flags = cmp_r8_i8_return_CF(x);

if (0x02 > x) {
    // Expect CF = 1 (borrow occurred)
    return ((flags & 0x01) == 0x01);
} else {
    // Expect CF = 0 (no borrow)
    return ((flags & 0x01) == 0x00);
}
}

unsigned char cmp_r8_i8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%cl;"      // cl = x 
        "cmpb $0x02, %%cl;"      // cl -= imm 
        "lahf;"               // load flags into AH
        "movb %%ah, %0;"      // store AH in output variable
        : "=r" (ah)           // output
        : "r" (x)            // inputs
        : "%cl", "%ah"        // clobbered registers
    );

    return ah;
}


//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_r8_i8_SF (int8_t x) {
  
  int8_t diff = x-0x02;  
    unsigned char flags = cmp_r8_i8_return_flags(x);

    if (diff<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    return false; 

    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_r8_i8_ZF (int8_t x) {
    int8_t diff = x - 0x02;
    unsigned char flags = cmp_r8_i8_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_r8_i8_AF (int8_t x) {
    int8_t x_lsb = x & 0xF;  // Get lower 4 bits of x
    int8_t imm_lsb = 0x02 & 0xF;  // Get lower 4 bits of y
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_r8_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}



//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_cmp_r8_i8_PF (int8_t x) {
   
    unsigned char flags = cmp_r8_i8_return_flags(x);

    int8_t result = x - 0x02;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}



unsigned char cmp_r8_i8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%cl;"      // Load x into cl (8-bit)
        "cmpb $0x02, %%cl;"      // Cmptract immediate from cl
        "seto %0;"            // Set OF flag into 'of'
        : "=r"(of)            // Output operand
        : "r"(x)               // input
        : "%cl"               // Clobbered register
    );

    return of;
}

//check property for OF

bool test_cmp_r8_i8_OF (int8_t x) {
    int8_t  diff = x - 0x02;
    unsigned char of = cmp_r8_i8_return_OF (x);

   if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//******************************************************************
// Cmp m8, i8 


unsigned char cmp_M8_i8_return_CF(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "cmpb $0x02, (%2);"    // 80/5 ib: [memory] = [memory] - imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"         // clobbered registers
    );

    return ah;
}


// Check property for CF
// CF is bit 0 in ah
bool test_cmp_M8_i8_CF(uint8_t x) {
    unsigned char flags = cmp_M8_i8_return_CF(x);

    if (x < 2) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

//  CMP m8, imm8 (memory form) - signed version
unsigned char cmp_M8_i8_return_flags(int8_t x) {
    unsigned char ah;
    int8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "cmpb $0x02, (%2);"    // 80/5 ib: [memory] = [memory] - imm8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_M8_i8_SF(int8_t x) {
    int8_t result = x - 2;  
    unsigned char flags = cmp_M8_i8_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_M8_i8_ZF(int8_t x) {
    int8_t result = x - 2;  
    unsigned char flags = cmp_M8_i8_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_M8_i8_AF(int8_t x) {

    int16_t x_lsb = x & 0x000F;  // Get lower 4 bits of x
    int16_t imm_lsb = 0x0002 & 0x000F;  // Get lower 4 bits of y
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_M8_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_M8_i8_PF(int8_t x) {
    unsigned char flags = cmp_M8_i8_return_flags(x);
    
    int8_t result = x - 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// overflow flag version
unsigned char cmp_M8_i8_return_OF(int8_t x) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "cmpb $0x02, (%2);"    // [memory] = [memory] - imm8
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        :
        "cc"
    );

    return of;
}

// Check property for OF
bool test_cmp_M8_i8_OF(int8_t x) {
    int8_t result = x - 2;
    unsigned char of = cmp_M8_i8_return_OF(x);
    if ((x < 0) && (2 >= 0) && (result >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}
//******************************************************************* */
// CMP REX.r8, i8
unsigned char cmp_REX1_r8_i8_return_CF(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r8b;"       // R8B = x (forces REX prefix)
        "cmpb $0x02, %%r8b;"    // REX + 80 /5 ib: CMP r8, imm8
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r"(ah)              // output
        : "r"(x)                // inputs: x
        : "%r8", "%ah"   // clobbered registers
    );

    return ah;
}

// Check property for CF (REX immediate form)
bool test_cmp_REX1_r8_i8_CF(uint8_t x) {
    unsigned char flags = cmp_REX1_r8_i8_return_CF(x);
    const uint8_t imm = 0x02;

    if (imm > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// REX + 80 /5 ib: CMP r8, imm8 (immediate form) - signed version
unsigned char cmp_REX1_r8_i8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r9b;"       // R9B = x (forces REX prefix)
        "cmpb $0x02, %%r9b;"    // REX + 80 /5 ib: CMP r8, imm8
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r"(ah)              // output
        : "r"(x)                // inputs: x
        : "%r9", "%ah"   // clobbered registers
    );

    return ah;
}

// Check property for SF (REX immediate form)
bool test_cmp_REX1_r8_i8_SF(int8_t x) {
    const int8_t imm = 0x02;
    int8_t result = x - imm;
    unsigned char flags = cmp_REX1_r8_i8_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (REX immediate form)
bool test_cmp_REX1_r8_i8_ZF(int8_t x) {
    const int8_t imm = 0x02;
    int8_t result = x - imm;
    unsigned char flags = cmp_REX1_r8_i8_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (REX immediate form)
bool test_cmp_REX1_r8_i8_AF(int8_t x) {
    const uint8_t imm = 0x02;
    uint8_t x_lsb = x & 0x0F;
    uint8_t imm_lsb = imm & 0x0F;
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_REX1_r8_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (REX immediate form)
bool test_cmp_REX1_r8_i8_PF(int8_t x) {
    const int8_t imm = 0x02;
    unsigned char flags = cmp_REX1_r8_i8_return_flags(x);
    
    int8_t result = x - imm;
    uint8_t expected_parity = calculate_parity((uint8_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (REX immediate form)
unsigned char cmp_REX1_r8_i8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%r10b;"      // R10B = x (forces REX prefix)
        "cmpb $0x02, %%r10b;"   // REX + 80 /5 ib: CMP r8, imm8
        "seto %0;"              // Set 'of' to 1 if overflow occurred
        : "=r"(of)              // Output operand (OF flag)
        : "r"(x)                // Input operands: x
        : "%r10"                // clobbered registers
    );

    return of;
}

// Check property for OF (REX immediate form)
bool test_cmp_REX1_r8_i8_OF(int8_t x) {
    const int8_t imm = 0x02;
    int8_t result = x - imm;
    unsigned char of = cmp_REX1_r8_i8_return_OF(x);
    
    // For x - imm, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (imm < 0) && (result < 0)) ||
        ((x < 0) && (imm >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//**********************************************************
//  rex m8,i8 */




// REX + 80 /5 ib: CMP r/m8, imm8 (memory form with REX) - unsigned version
unsigned char cmp_REX1_m8_i8_return_CF(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, %%al;"        // AL = x (temporary storage)
        "movq %2, %%r8;"        // R8 = memory address (forces REX prefix)
        "movb %%al, (%%r8);"
        "cmpb $0x02, (%%r8);"   // REX + 80 /5 ib: CMP [R8], imm8
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r"(ah)              // output
        : "r"(x), "r"(&val)     // inputs: x, memory address
        : "%r8", "al", "%ah" // clobbered registers
    );

    return ah;
}

// Check property for CF (REX memory immediate form)
bool test_cmp_REX1_m8_i8_CF(uint8_t x) {
    unsigned char flags = cmp_REX1_m8_i8_return_CF(x);
    const uint8_t imm = 0x02;

    if (imm > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// REX + 80 /5 ib: CMP r/m8, imm8 (memory form with REX) - signed version
unsigned char cmp_REX1_m8_i8_return_flags(int8_t x) {
    unsigned char ah;
    int8_t val;

    __asm__ volatile (
        "movb %1, %%al;"        // AL = x (temporary storage)
        "movq %2, %%r9;"        // R9 = memory address (forces REX prefix)
        "movb %%al, (%%r9);"    // store x in memory location via R9
        "cmpb $0x02, (%%r9);"   // REX + 80 /5 ib: CMP [R9], imm8
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Store AH in output
        : "=r"(ah)              // output
        : "r"(x), "r"(&val)     // inputs: x, memory address
        : "%r9","al", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF (REX memory immediate form)
bool test_cmp_REX1_m8_i8_SF(int8_t x) {
    const int8_t imm = 0x02;
    int8_t result = x - imm;
    unsigned char flags = cmp_REX1_m8_i8_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (REX memory immediate form)
bool test_cmp_REX1_m8_i8_ZF(int8_t x) {
    const int8_t imm = 0x02;
    int8_t result = x - imm;
    unsigned char flags = cmp_REX1_m8_i8_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (REX memory immediate form)
bool test_cmp_REX1_m8_i8_AF(int8_t x) {
    const uint8_t imm = 0x02;
    uint8_t x_lsb = x & 0x0F;
    uint8_t imm_lsb = imm & 0x0F;
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_REX1_m8_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (REX memory immediate form)
bool test_cmp_REX1_m8_i8_PF(int8_t x) {
    const int8_t imm = 0x02;
    unsigned char flags = cmp_REX1_m8_i8_return_flags(x);
    
    int8_t result = x - imm;
    uint8_t expected_parity = calculate_parity((uint8_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (REX memory immediate form)
unsigned char cmp_REX1_m8_i8_return_OF(int8_t x) {
    unsigned char of;
    int8_t val;

    __asm__ volatile (
        "movb %1, %%al;"        // AL = x (temporary storage)
        "movq %2, %%r10;"       // R10 = memory address (forces REX prefix)
        "movb %%al, (%%r10);"   // store x in memory location via R10
        "cmpb $0x02, (%%r10);"  // REX + 80 /5 ib: CMP [R10], imm8
        "seto %0;"              // Set 'of' to 1 if overflow occurred
        : "=r"(of)              // Output operand (OF flag)
        : "r"(x), "r"(&val)     // Input operands: x, memory address
        : "%r10", "%al"         // clobbered registers
    );

    return of;
}

// Check property for OF (REX memory immediate form)
bool test_cmp_REX1_m8_i8_OF(int8_t x) {
    const int8_t imm = 0x02;
    int8_t result = x - imm;
    unsigned char of = cmp_REX1_m8_i8_return_OF(x);
    
    // For x - imm, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (imm < 0) && (result < 0)) ||
        ((x < 0) && (imm >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//**********************************************************
// CMP r16,i16

unsigned char cmp_r16_i16_return_CF(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%cx;"       // Load x into cx
        "cmpw $0x0002, %%cx;"       // Cmptract immediate value from cx
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output variable
        : "=r" (ah)            // output: store AH flags in 'ah'
        : "r" (x)              // inputs: x = register, imm = immediate
        : "%cx", "%ah"         // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah
bool test_cmp_r16_i16_CF (uint16_t  x) {
  unsigned char flags = cmp_r16_i16_return_CF(x);

if (0x02 > x) {
    // Expect CF = 1 (borrow occurred)
    return ((flags & 0x01) == 0x01);
} else {
    // Expect CF = 0 (no borrow)
    return ((flags & 0x01) == 0x00);
}

}

unsigned char cmp_r16_i16_return_flags(int16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%cx;"      // Load x into cx
        "cmpw $0x0002, %%cx;"      // Cmptract immediate from cx
        "lahf;"               // Load flags into AH
        "movb %%ah, %0;"      // Move AH to output variable
        : "=r" (ah)           // output
        : "r" (x)             // inputs
        : "%cx", "%ah"        // clobbered registers
    );

    return ah;
}


//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_cmp_r16_i16_SF (int16_t x) {
  
  int16_t diff = x- 0x0002;  
    unsigned char flags = cmp_r16_i16_return_flags(x);

    if (diff<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    return false; 

    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_cmp_r16_i16_ZF (int16_t x) {
    int16_t diff = x - 0x0002;
    unsigned char flags = cmp_r16_i16_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_cmp_r16_i16_AF (int16_t x) {

    int16_t x_lsb = x & 0x000F;  // Get lower 4 bits of x
    int16_t imm_lsb = 0x0002 & 0x000F;  // Get lower 4 bits of y
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_r16_i16_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}


//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_cmp_r16_i16_PF (int16_t x) {
   
    unsigned char flags = cmp_r16_i16_return_flags(x);

    int16_t result = x - 0x0002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}


unsigned char cmp_r16_i16_return_OF(int16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%cx;"     // Load x into cx
        "cmpw $0x0002, %%cx;"     // Cmptract immediate value from cx
        "seto %0;"           // Set OF flag into 'of'
        : "=r"(of)           // Output operand
        : "r"(x)              // Inputs: x in register, imm as immediate
        : "%cx"              // Clobbered register
    );

    return of;
}


//check property for OF
bool test_cmp_r16_i16_OF (int16_t x) {
     int16_t diff = x - 0x0002;
    unsigned char of = cmp_r16_i16_return_OF (x);
  if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
} 

//*************************************************
// Cmp m16,i16 

unsigned char cmp_M16_i16_return_CF(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "cmpw $0x0002, (%2);"  // 81/5 iw: [memory] = [memory] - imm16
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_M16_i16_CF(uint16_t x) {
    unsigned char flags = cmp_M16_i16_return_CF(x);

    if (x < 2) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 81/5 iw: CMP r/m16, imm16 (memory form) - signed version
unsigned char cmp_M16_i16_return_flags(int16_t x) {
    unsigned char ah;
    int16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "cmpw $0x0002, (%2);"  // 81/5 iw: [memory] = [memory] - imm16
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_M16_i16_SF(int16_t x) {
    int16_t result = x - 2;  
    unsigned char flags = cmp_M16_i16_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_M16_i16_ZF(int16_t x) {
    int16_t result = x - 2;  
    unsigned char flags = cmp_M16_i16_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_M16_i16_AF(int16_t x) {
    
     int16_t x_lsb = x & 0x000F;  // Get lower 4 bits of x
    int16_t imm_lsb = 0x0002 & 0x000F;  // Get lower 4 bits of y
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_M16_i16_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_M16_i16_PF(int16_t x) {
    unsigned char flags = cmp_M16_i16_return_flags(x);
    
    int16_t result = x - 0x0002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// overflow flag version
unsigned char cmp_M16_i16_return_OF(int16_t x) {
    unsigned char of;
    int16_t val;
    
    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "cmpw $0x0002, (%2);"  // [memory] = [memory] - imm16
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        :
        "cc"
    );

    return of;
}

// Check property for OF
bool test_cmp_M16_i16_OF(int16_t x) {
    int16_t result = x - 2;
    unsigned char of = cmp_M16_i16_return_OF(x);
     if ((x < 0) && (2 >= 0) && (result >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//**************************************************
// r32,i32

unsigned char cmp_r32_i32_return_CF(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%ecx;"      // ecx = x 
        "cmpl $0x00000002, %%ecx;"      // ecx -= imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output
        : "=r" (ah)            // output
        : "r" (x)       // inputs: register and immediate
        : "%ecx", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah

bool test_cmp_r32_i32_CF (uint32_t  x) {
    unsigned char flags = cmp_r32_i32_return_CF(x);

    if (0x02 > x) {
        // Expect CF = 1 (borrow occurred)
        return ((flags & 0x01) == 0x01);
    } else {
        // Expect CF = 0 (no borrow)
        return ((flags & 0x01) == 0x00);
    }
    
}


unsigned char cmp_r32_i32_return_flags(int32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%ecx;"       // ecx = x (32-bit)
        "cmpl $0x00000002, %%ecx;"       // ecx -= imm (immediate)
        "lahf;"                 // load flags into AH
        "movb %%ah, %0;"        // move AH to output
        : "=r" (ah)
        : "r" (x)
        : "%ecx", "%ah"
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_cmp_r32_i32_SF (int32_t x) {
  
  int32_t  diff = x- 0x00000002;  
    unsigned char flags = cmp_r32_i32_return_flags(x);

    if (diff<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    return false; 
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_cmp_r32_i32_ZF (int32_t x) {
    int32_t diff = x - 0x00000002;
    unsigned char flags = cmp_r32_i32_return_flags(x);

    if (diff == 0) {   
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_r32_i32_AF (int32_t x) {
     int32_t x_lsb = x & 0X0000000F;  // Get lower 4 bits of x
     int32_t imm_lsb = 0x00000002 & 0X0000000F;  // Get lower 4 bits of y
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_r32_i32_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_cmp_r32_i32_PF (int32_t x) {
   
    unsigned char flags = cmp_r32_i32_return_flags(x);

    int32_t result = x - 0x00000002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}



unsigned char cmp_r32_i32_return_OF(int32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%ecx;"     // Load x into ecx (32-bit register)
        "cmpl $0x00000002, %%ecx;"     // Cmptract immediate value from ecx
        "seto %0;"            // Set OF flag into 'of'
        : "=r"(of)            // Output
        : "r"(x)                   // Inputs: register and immediate
        : "%ecx"              // Clobbered register
    );

    return of;
}


//check property for OF

bool test_cmp_r32_i32_OF (int32_t x) {
    int32_t diff = x - 0x00000002;
    unsigned char of = cmp_r32_i32_return_OF (x);

      if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//*********************************************
// m32,i32 

unsigned char cmp_M32_i32_return_CF(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "cmpl $0x00000002, (%2);"  // 81/5 id: [memory] = [memory] - imm32
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_M32_i32_CF(uint32_t x) {
    unsigned char flags = cmp_M32_i32_return_CF(x);

    if (x < 2) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char cmp_M32_i32_return_flags(int32_t x) {
    unsigned char ah;
    int32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "cmpl $0x00000002, (%2);"  // 81/5 id: [memory] = [memory] - imm32
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"       // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_M32_i32_SF(int32_t x) {
    int32_t result = x - 2;  
    unsigned char flags = cmp_M32_i32_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_M32_i32_ZF(int32_t x) {
    int32_t result = x - 2;  
    unsigned char flags = cmp_M32_i32_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_M32_i32_AF(int32_t x) {
    int32_t x_lsb = x & 0x0000000F;  // Get lower 4 bits of x
    int32_t imm_lsb = 0x00000002 & 0x0000000F;  // Get lower 4 bits of immediate
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_M32_i32_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_M32_i32_PF(int32_t x) {
    unsigned char flags = cmp_M32_i32_return_flags(x);
    
    int32_t result = x - 0x00000002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// overflow flag version
unsigned char cmp_M32_i32_return_OF(int32_t x) {
    unsigned char of;
    int32_t val;
    
    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "cmpl $0x00000002, (%2);"  // [memory] = [memory] - imm32
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        :
        "cc"
    );

    return of;
}

// Check property for OF
bool test_cmp_M32_i32_OF(int32_t x) {
    int32_t result = x - 2;
    unsigned char of = cmp_M32_i32_return_OF(x);
     if ((x < 0) && (2 >= 0) && (result >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//*******************************************************
// r64,i32

unsigned char cmp_r64_i32_return_CF(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rcx;"           // Load x into rcx
        "cmpq $0x00000002, %%rcx;"  // Cmptract immediate value from rcx
        "lahf;"                     // Load flags into AH
        "movb %%ah, %0;"            // Move AH to output variable
        : "=r" (ah)                 // output: store AH flags in 'ah'
        : "r" (x)                   // inputs: x = register
        : "%rcx", "%ah"             // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah

   bool test_cmp_r64_i32_CF (uint64_t x) {
    unsigned char flags = cmp_r64_i32_return_CF(x);

    if (0x02 > x) {
        // Expect CF = 1 (borrow occurred)
        return ((flags & 0x01) == 0x01);
    } else {
        // Expect CF = 0 (no borrow)
        return ((flags & 0x01) == 0x00);
    }
       
}


unsigned char cmp_r64_i32_return_flags(int64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rcx;"           // Load x into rcx
        "cmpq $0x00000002, %%rcx;"  // Cmptract immediate from rcx
        "lahf;"                     // Load flags into AH
        "movb %%ah, %0;"            // Move AH to output variable
        : "=r" (ah)                 // output
        : "r" (x)                   // inputs
        : "%rcx", "%ah"             // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_r64_i32_SF (int64_t x) {
    int64_t diff = x - 0x00000002;  
    unsigned char flags = cmp_r64_i32_return_flags(x);

    if (diff < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}
    
//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_r64_i32_ZF (int64_t x) {
    int64_t diff = x - 0x00000002;
    unsigned char flags = cmp_r64_i32_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_r64_i32_AF (int64_t x) {
    int64_t x_lsb = x & 0x0000000F;               // Get lower 4 bits of x
    int64_t imm_lsb = 0x00000002 & 0x0000000F;    
    
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_r64_i32_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}


 bool test_cmp_r64_i32_PF (int64_t x) {
   
    unsigned char flags = cmp_r64_i32_return_flags(x);

    int64_t result = x - 0x00000002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}


unsigned char cmp_r64_i32_return_OF(int64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rcx;"           // Load x into rcx
        "cmpq $0x00000002, %%rcx;"  // Cmptract immediate value from rcx
        "seto %0;"                  // Set OF flag into 'of'
        : "=r"(of)                  // Output operand
        : "r"(x)                    // Inputs: x in register
        : "%rcx"                    // Clobbered register
    );

    return of;
}

//check property for OF
bool test_cmp_r64_i32_OF (int64_t x) {
    int64_t diff = x - 0x00000002;
    unsigned char of = cmp_r64_i32_return_OF(x);
 if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//*******************************************************
// m64,i32

unsigned char cmp_M64_i32_return_CF(uint64_t x) {
    unsigned char ah;
    uint64_t val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "cmpq $0x00000002, (%2);"  // REX.W + 81/5 id: [memory] = [memory] - imm32
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_M64_i32_CF(uint64_t x) {
    unsigned char flags = cmp_M64_i32_return_CF(x);

    if (x < 2) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// REX.W + 81/5 id: CMP r/m64, imm32 (memory form) - signed version
unsigned char cmp_M64_i32_return_flags(int64_t x) {
    unsigned char ah;
    int64_t val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "cmpq $0x00000002, (%2);"  // REX.W + 81/5 id: [memory] = [memory] - imm32
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"       // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_M64_i32_SF(int64_t x) {
    int64_t result = x - 2;  
    unsigned char flags = cmp_M64_i32_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_M64_i32_ZF(int64_t x) {
    int64_t result = x - 2;  
    unsigned char flags = cmp_M64_i32_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_M64_i32_AF(int64_t x) {
    int64_t x_lsb = x & 0x000000000000000FLL;  // Get lower 4 bits of x
    int64_t imm_lsb = 0x00000002 & 0x000000000000000FLL;  // Get lower 4 bits of immediate
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_M64_i32_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_M64_i32_PF(int64_t x) {
    unsigned char flags = cmp_M64_i32_return_flags(x);
    
    int64_t result = x - 0x00000002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// overflow flag version
unsigned char cmp_M64_i32_return_OF(int64_t x) {
    unsigned char of;
    int64_t val;
    
    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "cmpq $0x00000002, (%2);"  // [memory] = [memory] - imm32
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        :
        "cc"
    );

    return of;
}

// Check property for OF
bool test_cmp_M64_i32_OF(int64_t x) {
    int64_t result = x - 2;
    unsigned char of = cmp_M64_i32_return_OF(x);

  if ((x < 0) && (2 >= 0) && (result >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//**********************************************************
// CMP r16/i8

unsigned char cmp_R16_i8_return_CF(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "cmpw $0x02, %%ax;"    // Cmptract 8-bit immediate value from AX
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output variable
        : "=r" (ah)            // output: store AH flags in 'ah'
        : "r" (x)              // inputs: x = register
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah
bool test_cmp_R16_i8_CF (uint16_t x) {
    unsigned char flags = cmp_R16_i8_return_CF(x);

    if (0x02 > x) {
        // Expect CF = 1 (borrow occurred)
        return ((flags & 0x01) == 0x01);
    } else {
        // Expect CF = 0 (no borrow)
        return ((flags & 0x01) == 0x00);
    }
       
}

unsigned char cmp_R16_i8_return_flags(int16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "cmpw $0x02, %%ax;"    // Cmptract 8-bit immediate from AX
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_R16_i8_SF (int16_t x) {
    int16_t diff = x - 0x02;  
    unsigned char flags = cmp_R16_i8_return_flags(x);

    if (diff < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_R16_i8_ZF (int16_t x) {
    int16_t diff = x - 0x02;
    unsigned char flags = cmp_R16_i8_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_R16_i8_AF (int16_t x) {
    int16_t x_lsb = x & 0x0F;               // Get lower 4 bits of x
    int16_t imm_lsb = 0x02 & 0x0F;          // Get lower 4 bits of immediate (=2)
    
    // For cmptraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_R16_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  // Check if AF bit is set
    
    return expected_af == actual_af;
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04


 bool test_cmp_R16_i8_PF (int16_t x) {
   
    unsigned char flags = cmp_R16_i8_return_flags(x);

    int16_t result = x - 0x02;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}

unsigned char cmp_R16_i8_return_OF(int16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "cmpw $0x02, %%ax;"    // Cmptract 8-bit immediate value from AX
        "seto %0;"             // Set OF flag into 'of'
        : "=r"(of)             // Output operand
        : "r"(x)               // Inputs: x in register
        : "%ax"                // Clobbered register
    );

    return of;
}

//check property for OF
bool test_cmp_R16_i8_OF (int16_t x) {
    int16_t diff = x - 0x02;
    unsigned char of = cmp_R16_i8_return_OF(x);
 if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//****************************************************************
// m16,i8 

unsigned char cmp_M16_i8_return_CF(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "cmpw $0x02, (%2);"    // 83/5 ib: [memory] = [memory] - imm8 (sign-extended)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        :  "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_M16_i8_CF(uint16_t x) {
    unsigned char flags = cmp_M16_i8_return_CF(x);

    if (x < 2) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char cmp_M16_i8_return_flags(int16_t x) {
    unsigned char ah;
    int16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "cmpw $0x02, (%2);"    // 83/5 ib: [memory] = [memory] - imm8 (sign-extended)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        :  "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_M16_i8_SF(int16_t x) {
    int16_t result = x - 2;  
    unsigned char flags = cmp_M16_i8_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_M16_i8_ZF(int16_t x) {
    int16_t result = x - 2;  
    unsigned char flags = cmp_M16_i8_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_M16_i8_AF(int16_t x) {
   
    uint16_t x_lsb = x & 0x0F;
    uint16_t imm_lsb = 0x02 & 0x0F;  // 8-bit immediate, only low nibble matters
     bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_M16_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  // Check if AF bit is set
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_M16_i8_PF(int16_t x) {
    unsigned char flags = cmp_M16_i8_return_flags(x);
    
    int16_t result = x - 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// overflow flag version
unsigned char cmp_M16_i8_return_OF(int16_t x) {
    unsigned char of;
    int16_t val;
    
    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "cmpw $0x02, (%2);"    // [memory] = [memory] - imm8 (sign-extended)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        : "cc"                // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_cmp_M16_i8_OF(int16_t x) {
    int16_t result = x - 2;
    unsigned char of = cmp_M16_i8_return_OF(x);
    if ((x < 0) && (2 >= 0) && (result >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//**********************************************************
// CMP r32,i8
unsigned char cmp_R32_i8_return_CF(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // Load x into EAX
        "cmpl $0x02, %%eax;"   // Cmptract 8-bit immediate value from EAX
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output variable
        : "=r" (ah)            // output: store AH flags in 'ah'
        : "r" (x)              // inputs: x = register
        : "%eax", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah
bool test_cmp_R32_i8_CF (uint32_t x) {
    unsigned char flags = cmp_R32_i8_return_CF(x);

    if (0x02 > x) {
        // Expect CF = 1 (borrow occurred)
        return ((flags & 0x01) == 0x01);
    } else {
        // Expect CF = 0 (no borrow)
        return ((flags & 0x01) == 0x00);
    }
}

unsigned char cmp_R32_i8_return_flags(int32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // Load x into EAX
        "cmpl $0x02, %%eax;"   // Cmptract 8-bit immediate from EAX
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%eax", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_R32_i8_SF (int32_t x) {
    int32_t diff = x - 0x02;  
    unsigned char flags = cmp_R32_i8_return_flags(x);

    if (diff < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_R32_i8_ZF (int32_t x) {
    int32_t diff = x - 0x02;
    unsigned char flags = cmp_R32_i8_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_R32_i8_AF (int32_t x) {
    int32_t x_lsb = x & 0x0F;               // Get lower 4 bits of x
    int32_t imm_lsb = 0x02 & 0x0F;          // Get lower 4 bits of immediate (=2)
    
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_R32_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  // Check if AF bit is set
    
    return expected_af == actual_af;
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_cmp_R32_i8_PF (int32_t x) {
   
    unsigned char flags = cmp_R32_i8_return_flags(x);

    int32_t result = x - 0x02;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}


unsigned char cmp_R32_i8_return_OF(int32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"      // Load x into EAX
        "cmpl $0x02, %%eax;"   // Cmptract 8-bit immediate value from EAX
        "seto %0;"             // Set OF flag into 'of'
        : "=r"(of)             // Output operand
        : "r"(x)               // Inputs: x in register
        : "%eax"               // Clobbered register
    );

    return of;
}

//check property for OF
bool test_cmp_R32_i8_OF (int32_t x) {
    int32_t diff = x - 0x02;
    unsigned char of = cmp_R32_i8_return_OF(x);
      if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//**********************************************
// m32,i8 

unsigned char cmp_M32_i8_return_CF(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "cmpl $0x02, (%2);"    // 83/5 ib: [memory] = [memory] - imm8 (sign-extended)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        :  "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_M32_i8_CF(uint32_t x) {
    unsigned char flags = cmp_M32_i8_return_CF(x);

    if (x < 2) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char cmp_M32_i8_return_flags(int32_t x) {
    unsigned char ah;
    int32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "cmpl $0x02, (%2);"    // 83/5 ib: [memory] = [memory] - imm8 (sign-extended)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        :  "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_M32_i8_SF(int32_t x) {
    int32_t result = x - 2;  
    unsigned char flags = cmp_M32_i8_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_M32_i8_ZF(int32_t x) {
    int32_t result = x - 2;  
    unsigned char flags = cmp_M32_i8_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_M32_i8_AF(int32_t x) {
    // For CMP: AF=1 when there's a borrow from bit 4 (low nibble underflow)
    uint32_t x_lsb = x & 0x0F;
    uint32_t imm_lsb = 0x02 & 0x0F;  // 8-bit immediate, only low nibble matters
    bool borrow_needed = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_M32_i8_return_flags(x);

    if (borrow_needed) {
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_M32_i8_PF(int32_t x) {
    unsigned char flags = cmp_M32_i8_return_flags(x);
    
    int32_t result = x - 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// overflow flag version
unsigned char cmp_M32_i8_return_OF(int32_t x) {
    unsigned char of;
    int32_t val;
    
    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "cmpl $0x02, (%2);"    // [memory] = [memory] - imm8 (sign-extended)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        : "cc"               // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_cmp_M32_i8_OF(int32_t x) {
    int32_t result = x - 2;
    unsigned char of = cmp_M32_i8_return_OF(x);
    // x < 0, imm >= 0, result >= 0: overflow (negative - positive = positive)
    if ((x < 0) && (2 >= 0) && (result >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//**********************************************************
// CMP r64/i8


unsigned char cmp_R64_i8_return_CF(uint64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // Load x into RAX
        "cmpq $0x02, %%rax;"   // Cmptract 8-bit immediate value from RAX
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output variable
        : "=r" (ah)            // output: store AH flags in 'ah'
        : "r" (x)              // inputs: x = register
        : "%rax", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah
bool test_cmp_R64_i8_CF (uint64_t x) {
    unsigned char flags = cmp_R64_i8_return_CF(x);

    if (0x02 > x) {
      
        return ((flags & 0x01) == 0x01);
    } else {
        
        return ((flags & 0x01) == 0x00);
    }
}

unsigned char cmp_R64_i8_return_flags(int64_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // Load x into RAX
        "cmpq $0x02, %%rax;"   // Cmptract 8-bit immediate from RAX
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%rax", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_R64_i8_SF (int64_t x) {
    int64_t diff = x - 0x02;  
    unsigned char flags = cmp_R64_i8_return_flags(x);

    if (diff < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_R64_i8_ZF (int64_t x) {
    int64_t diff = x - 0x02;
    unsigned char flags = cmp_R64_i8_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_R64_i8_AF (int64_t x) {
    int64_t x_lsb = x & 0x0F;               // Get lower 4 bits of x
    int64_t imm_lsb = 0x02 & 0x0F;          // Get lower 4 bits of immediate (=2)
    
   
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_R64_i8_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  // Check if AF bit is set
    
    return expected_af == actual_af;
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_cmp_R64_i8_PF (int64_t x) {
   
    unsigned char flags = cmp_R64_i8_return_flags(x);

    int64_t result = x - 0x02;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}



unsigned char cmp_R64_i8_return_OF(int64_t x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"      // Load x into RAX
        "cmpq $0x02, %%rax;"   // Cmptract 8-bit immediate value from RAX
        "seto %0;"             // Set OF flag into 'of'
        : "=r"(of)             // Output operand
        : "r"(x)               // Inputs: x in register
        : "%rax"               // Clobbered register
    );

    return of;
}

//check property for OF
bool test_cmp_R64_i8_OF (int64_t x) {
    int64_t diff = x - 0x02;
    unsigned char of = cmp_R64_i8_return_OF(x);
   if ((x < 0) && (diff >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}
//*************************************************************
// m64,i8

unsigned char cmp_M64_i8_return_CF(uint64_t x) {
    unsigned char ah;
    uint64_t val;  

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "cmpq $0x02, (%2);"    // REX.W + 83/5 ib: [memory] = [memory] - imm8 (sign-extended)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
// Filter to extract CF is: 0000 0001=0x01
bool test_cmp_M64_i8_CF(uint64_t x) {  
    unsigned char flags = cmp_M64_i8_return_CF(x);
    

    if (x < 2) {
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char cmp_M64_i8_return_flags(int64_t x) {
    unsigned char ah;
    int64_t val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "cmpq $0x02, (%2);"    // REX.W + 83/5 ib: [memory] = [memory] - imm8 (sign-extended)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        :  "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_M64_i8_SF(int64_t x) {
    int64_t result = x - 2;  
    unsigned char flags = cmp_M64_i8_return_flags(x);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_M64_i8_ZF(int64_t x) {
    int64_t result = x - 2;  
    unsigned char flags = cmp_M64_i8_return_flags(x);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_M64_i8_AF(int64_t x) {
    // For CMP: AF=1 when there's a borrow from bit 4 (low nibble underflow)
    uint64_t x_lsb = x & 0x0F;
    uint64_t imm_lsb = 0x02 & 0x0F;  // 8-bit immediate, only low nibble matters
    bool borrow_needed = (x_lsb < imm_lsb);
    
    unsigned char flags = cmp_M64_i8_return_flags(x);

    if (borrow_needed) {
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_M64_i8_PF(int64_t x) {
    unsigned char flags = cmp_M64_i8_return_flags(x);
    
    int64_t result = x - 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// overflow flag version
unsigned char cmp_M64_i8_return_OF(int64_t x) {
    unsigned char of;
    int64_t val;
    
    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "cmpq $0x02, (%2);"    // [memory] = [memory] - imm8 (sign-extended)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        : "cc"               // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_cmp_M64_i8_OF(int64_t x) {
    int64_t result = x - 2;
    unsigned char of = cmp_M64_i8_return_OF(x);
    
    if ((x < 0) && (2 >= 0) && (result >= 0)) {
        return of == 1;
    } else {
        return of == 0;
    }
}
//***********************************************************8
// CMP r8, r8 

unsigned char cmp_R8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movb %1, %%al;"       // al = x (destination)
        "movb %2, %%bl;"       // bl = y (source)
        "cmpb %%bl, %%al;"     // 28 /r: al = al - bl
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%al", "%bl", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_R8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = cmp_R8_r8_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char cmp_R8_r8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movb %1, %%al;"       // al = x (destination)
        "movb %2, %%bl;"       // bl = y (source)
        "cmpb %%bl, %%al;"     // 28 /r: al = al - bl
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%al", "%bl", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_R8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_R8_r8_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_R8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_R8_r8_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_R8_r8_AF(int8_t x, int8_t y) {
    uint8_t x_lsb = x & 0x0F;
    uint8_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_R8_r8_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_R8_r8_PF(int8_t x, int8_t y) {
    unsigned char flags = cmp_R8_r8_return_flags(x, y);
    
    int8_t result = x - y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version
unsigned char cmp_R8_r8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    
    __asm__ volatile (
        "movb %1, %%al;"       // al = x (destination)
        "movb %2, %%bl;"       // bl = y (source)
        "cmpb %%bl, %%al;"     // 28 /r: al = al - bl
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "%al", "%bl"         // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_cmp_R8_r8_OF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char of = cmp_R8_r8_return_OF(x, y);
    
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//**************************************************
// CMP m8, r8 */

unsigned char cmp_M8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    
    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%bl;"       // bl = y (source register)
        "cmpb %%bl, (%3);"     // 28 /r: [memory] = [memory] - bl
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%bl", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for CF (memory form)
bool test_cmp_M8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = cmp_M8_r8_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char cmp_M8_r8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    int8_t val;
    
    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%bl;"       // bl = y (source register)
        "cmpb %%bl, (%3);"     // 28 /r: [memory] = [memory] - bl
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        :  "%bl", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF (memory form)
bool test_cmp_M8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_M8_r8_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (memory form)
bool test_cmp_M8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_M8_r8_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (memory form)
bool test_cmp_M8_r8_AF(int8_t x, int8_t y) {
    uint8_t x_lsb = x & 0x0F;
    uint8_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_M8_r8_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (memory form)
bool test_cmp_M8_r8_PF(int8_t x, int8_t y) {
    unsigned char flags = cmp_M8_r8_return_flags(x, y);
    
    int8_t result = x - y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (memory form)
unsigned char cmp_M8_r8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%bl;"       // bl = y (source register)
        "cmpb %%bl, (%3);"     // 28 /r: [memory] = [memory] - bl
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%bl"                // clobbered registers
    );

    return of;
}

// Check property for OF (memory form)
bool test_cmp_M8_r8_OF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char of = cmp_M8_r8_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//*************************************************************** */
// REX + 28 /r: CMP r8, r8 (register form

unsigned char cmp_REX_r8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movb %1, %%r10b;"       // AL (destination register)
        "movb %2, %%r11b;"     // R11B requires REX prefix (source)
        "cmpb %%r11b, %%r10b;"   // REX + 28 /r: AL = AL - R11B
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%r10", "%r11", "%ah" // clobbered registers (REX required)
    );

    return ah;
}

// Check property for CF (register form - REX)
bool test_cmp_REX_r8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = cmp_REX_r8_r8_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char cmp_REX_r8_r8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r10b;"       // R10B = x
        "movb %2, %%r11b;"       // R11B = y
        "cmpb %%r11b, %%r10b;"   // R10B = R10B - R11B
        "lahf;"                  // Load flags into AH
        "movb %%ah, %0;"         // Store AH into output
        : "=r"(ah)
        : "r"(x), "r"(y)
        : "%r10", "%r11", "%ah"
    );

    return ah;
}


// Check property for SF (register form - REX)
// SF is bit 7 in ah - Filter: 1000 0000 = 0x80
bool test_cmp_REX_r8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_REX_r8_r8_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (register form - REX)
// ZF is bit 6 in ah - Filter: 0100 0000 = 0x40
bool test_cmp_REX_r8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_REX_r8_r8_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (register form - REX)
// AF is bit 4 in ah - Filter: 0001 0000 = 0x10
bool test_cmp_REX_r8_r8_AF(int8_t x, int8_t y) {
    uint8_t x_lsb = x & 0x0F;
    uint8_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_REX_r8_r8_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (register form - REX)
// PF is bit 2 in ah - Filter: 0000 0100 = 0x04
bool test_cmp_REX_r8_r8_PF(int8_t x, int8_t y) {
    unsigned char flags = cmp_REX_r8_r8_return_flags(x, y);
    
    int8_t result = x - y;
    uint8_t expected_parity = calculate_parity((uint8_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (register form - REX)
unsigned char cmp_REX_r8_r8_return_OF(int8_t x, int8_t y) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%r10b;"       // R10B = x (destination)
        "movb %2, %%r11b;"       // R11B = y (source)
        "cmpb %%r11b, %%r10b;"   // R10B = R10B - R11B
        "seto %0;"               // Set OF = 1 if overflow
        : "=r"(of)               // Output
        : "r"(x), "r"(y)         // Inputs
        : "%r10", "%r11"         // Clobbered extended registers
    );

    return of;
}


// Check property for OF (REX register form)
bool test_cmp_REX_r8_r8_OF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char of = cmp_REX_r8_r8_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//*************************************************************
// CMP m8, REX.r8 

unsigned char cmp_REX_M8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    
    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%r8b;"      // R8B requires REX prefix (source register)
        "cmpb %%r8b, (%3);"    // REX + 28 /r: [memory] = [memory] - R8
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%r8","%ah"  // clobbered registers (CORRECTED)
    );

    return ah;
}

// Check property for CF (memory form - REX)
bool test_cmp_REX_M8_r8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = cmp_REX_M8_r8_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char cmp_REX_M8_r8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    int8_t val;
    
    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%r9b;"      // R9B requires REX prefix (source register)
        "cmpb %%r9b, (%3);"    // REX + 28 /r: [memory] = [memory] - R9B
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%r9", "%ah" // clobbered registers (REX required)
    );

    return ah;
}

// Check property for SF (memory form - REX)
// SF is bit 7 in ah - Filter: 1000 0000 = 0x80
bool test_cmp_REX_M8_r8_SF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_REX_M8_r8_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (memory form - REX)
// ZF is bit 6 in ah - Filter: 0100 0000 = 0x40
bool test_cmp_REX_M8_r8_ZF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_REX_M8_r8_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (memory form - REX)
// AF is bit 4 in ah - Filter: 0001 0000 = 0x10
bool test_cmp_REX_M8_r8_AF(int8_t x, int8_t y) {
    uint8_t x_lsb = x & 0x0F;
    uint8_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_REX_M8_r8_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (memory form - REX)
// PF is bit 2 in ah - Filter: 0000 0100 = 0x04
bool test_cmp_REX_M8_r8_PF(int8_t x, int8_t y) {
    unsigned char flags = cmp_REX_M8_r8_return_flags(x, y);
    
    int8_t result = x - y;
    uint8_t expected_parity = calculate_parity((uint8_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (memory form - REX)
unsigned char cmp_REX_M8_r8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movb %1, (%3);"       // store x in memory location
        "movb %2, %%r10b;"     // R10B requires REX prefix (source register)
        "cmpb %%r10b, (%3);"   // REX + 28 /r: [memory] = [memory] - R10B
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%r10"              // clobbered registers (REX required)
    );

    return of;
}

// Check property for OF (memory form - REX)
bool test_cmp_REX_M8_r8_OF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char of = cmp_REX_M8_r8_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//********************************************************
// r16,r16 */

unsigned char cmp_R16_r16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x (destination)
        "movw %2, %%bx;"       // bx = y (source)
        "cmpw %%bx, %%ax;"     // 29 /r: ax = ax - bx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%ax", "%bx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_R16_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = cmp_R16_r16_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 29 /r: CMP r/m16, r16 (register form) - signed version
unsigned char cmp_R16_r16_return_flags(int16_t x, int16_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x (destination)
        "movw %2, %%bx;"       // bx = y (source)
        "cmpw %%bx, %%ax;"     // 29 /r: ax = ax - bx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%ax", "%bx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_R16_r16_SF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char flags = cmp_R16_r16_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_R16_r16_ZF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char flags = cmp_R16_r16_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_R16_r16_AF(int16_t x, int16_t y) {
    uint16_t x_lsb = x & 0x0F;
    uint16_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_R16_r16_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_R16_r16_PF(int16_t x, int16_t y) {
    unsigned char flags = cmp_R16_r16_return_flags(x, y);
    
    int16_t result = x - y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version
unsigned char cmp_R16_r16_return_OF(int16_t x, int16_t y) {
    unsigned char of;
    
    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x (destination)
        "movw %2, %%bx;"       // bx = y (source)
        "cmpw %%bx, %%ax;"     // 29 /r: ax = ax - bx
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "%ax", "%bx"         // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_cmp_R16_r16_OF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char of = cmp_R16_r16_return_OF(x, y);
    
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//********************************************************************
// m16,r16 */

unsigned char cmp_M16_r16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;
    
    __asm__ volatile (
        "movw %1, (%3);"       // store x in memory location
        "movw %2, %%bx;"       // bx = y (source register)
        "cmpw %%bx, (%3);"     // 29 /r: [memory] = [memory] - bx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%bx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for CF (memory form)
bool test_cmp_M16_r16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = cmp_M16_r16_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 29 /r: CMP r/m16, r16 (memory form) - signed version
unsigned char cmp_M16_r16_return_flags(int16_t x, int16_t y) {
    unsigned char ah;
    int16_t val;
    
    __asm__ volatile (
        "movw %1, (%3);"       // store x in memory location
        "movw %2, %%bx;"       // bx = y (source register)
        "cmpw %%bx, (%3);"     // 29 /r: [memory] = [memory] - bx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        :  "%bx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF (memory form)
bool test_cmp_M16_r16_SF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char flags = cmp_M16_r16_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (memory form)
bool test_cmp_M16_r16_ZF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char flags = cmp_M16_r16_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (memory form)
bool test_cmp_M16_r16_AF(int16_t x, int16_t y) {
    uint16_t x_lsb = x & 0x0F;
    uint16_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_M16_r16_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (memory form)
bool test_cmp_M16_r16_PF(int16_t x, int16_t y) {
    unsigned char flags = cmp_M16_r16_return_flags(x, y);
    
    int16_t result = x - y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (memory form)
unsigned char cmp_M16_r16_return_OF(int16_t x, int16_t y) {
    unsigned char of;
    int16_t val;
    
    __asm__ volatile (
        "movw %1, (%3);"       // store x in memory location
        "movw %2, %%bx;"       // bx = y (source register)
        "cmpw %%bx, (%3);"     // 29 /r: [memory] = [memory] - bx
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%bx"                // clobbered registers
    );

    return of;
}

// Check property for OF (memory form)
bool test_cmp_M16_r16_OF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char of = cmp_M16_r16_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//********************************************
// r32,r32 */

unsigned char cmp_R32_r32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x (destination)
        "movl %2, %%ebx;"      // ebx = y (source)
        "cmpl %%ebx, %%eax;"   // 2B /r: eax = eax - ebx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%eax", "%ebx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_R32_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = cmp_R32_r32_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 2B /r: CMP r/m32, r32 (register form) - signed version
unsigned char cmp_R32_r32_return_flags(int32_t x, int32_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x (destination)
        "movl %2, %%ebx;"      // ebx = y (source)
        "cmpl %%ebx, %%eax;"   // 2B /r: eax = eax - ebx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%eax", "%ebx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_R32_r32_SF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char flags = cmp_R32_r32_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_R32_r32_ZF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char flags = cmp_R32_r32_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_R32_r32_AF(int32_t x, int32_t y) {
    uint32_t x_lsb = x & 0x0F;
    uint32_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_R32_r32_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_R32_r32_PF(int32_t x, int32_t y) {
    unsigned char flags = cmp_R32_r32_return_flags(x, y);
    
    int32_t result = x - y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version
unsigned char cmp_R32_r32_return_OF(int32_t x, int32_t y) {
    unsigned char of;
    
    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x (destination)
        "movl %2, %%ebx;"      // ebx = y (source)
        "cmpl %%ebx, %%eax;"   // 2B /r: eax = eax - ebx
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "%eax", "%ebx"       // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_cmp_R32_r32_OF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char of = cmp_R32_r32_return_OF(x, y);
    
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//******************************************************
// m32,r32 */

unsigned char cmp_M32_r32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;
    
    __asm__ volatile (
        "movl %1, (%3);"       // store x in memory location
        "movl %2, %%ebx;"      // ebx = y (source register)
        "cmpl %%ebx, (%3);"    // 2B /r: [memory] = [memory] - ebx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        :  "%ebx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for CF (memory form)
bool test_cmp_M32_r32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = cmp_M32_r32_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 2B /r: CMP r/m32, r32 (memory form) - signed version
unsigned char cmp_M32_r32_return_flags(int32_t x, int32_t y) {
    unsigned char ah;
    int32_t val;
    
    __asm__ volatile (
        "movl %1, (%3);"       // store x in memory location
        "movl %2, %%ebx;"      // ebx = y (source register)
        "cmpl %%ebx, (%3);"    // 2B /r: [memory] = [memory] - ebx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        :  "%ebx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF (memory form)
bool test_cmp_M32_r32_SF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char flags = cmp_M32_r32_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (memory form)
bool test_cmp_M32_r32_ZF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char flags = cmp_M32_r32_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (memory form)
bool test_cmp_M32_r32_AF(int32_t x, int32_t y) {
    uint32_t x_lsb = x & 0x0F;
    uint32_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_M32_r32_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (memory form)
bool test_cmp_M32_r32_PF(int32_t x, int32_t y) {
    unsigned char flags = cmp_M32_r32_return_flags(x, y);
    
    int32_t result = x - y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (memory form)
unsigned char cmp_M32_r32_return_OF(int32_t x, int32_t y) {
    unsigned char of;
    int32_t val;
    
    __asm__ volatile (
        "movl %1, (%3);"       // store x in memory location
        "movl %2, %%ebx;"      // ebx = y (source register)
        "cmpl %%ebx, (%3);"    // 2B /r: [memory] = [memory] - ebx
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%ebx"               // clobbered registers
    );

    return of;
}

// Check property for OF (memory form)
bool test_cmp_M32_r32_OF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char of = cmp_M32_r32_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//********************************************************
// r64,r64 

unsigned char cmp_R64_r64_return_CF(uint64_t x, uint64_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x (destination)
        "movq %2, %%rbx;"      // rbx = y (source)
        "cmpq %%rbx, %%rax;"   // REX.W + 2B /r: rax = rax - rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%rax", "%rbx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_cmp_R64_r64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = cmp_R64_r64_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// REX.W + 2B /r: CMP r/m64, r64 (register form) - signed version
unsigned char cmp_R64_r64_return_flags(int64_t x, int64_t y) {
    unsigned char ah;
    
    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x (destination)
        "movq %2, %%rbx;"      // rbx = y (source)
        "cmpq %%rbx, %%rax;"   // REX.W + 2B /r: rax = rax - rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs: x, y
        : "%rax", "%rbx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_cmp_R64_r64_SF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char flags = cmp_R64_r64_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_cmp_R64_r64_ZF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char flags = cmp_R64_r64_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_cmp_R64_r64_AF(int64_t x, int64_t y) {
    uint64_t x_lsb = x & 0x0F;
    uint64_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_R64_r64_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_cmp_R64_r64_PF(int64_t x, int64_t y) {
    unsigned char flags = cmp_R64_r64_return_flags(x, y);
    
    int64_t result = x - y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version
unsigned char cmp_R64_r64_return_OF(int64_t x, int64_t y) {
    unsigned char of;
    
    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x (destination)
        "movq %2, %%rbx;"      // rbx = y (source)
        "cmpq %%rbx, %%rax;"   // REX.W + 2B /r: rax = rax - rbx
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "%rax", "%rbx"       // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_cmp_R64_r64_OF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char of = cmp_R64_r64_return_OF(x, y);
    
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//************************************************************* */
// M64,R64

unsigned char cmp_M64_r64_return_CF(uint64_t x, uint64_t y) {
    unsigned char ah;
    uint64_t val;
    
    __asm__ volatile (
        "movq %1, (%3);"       // store x in memory location
        "movq %2, %%rbx;"      // rbx = y (source register)
        "cmpq %%rbx, (%3);"    // REX.W + 2B /r: [memory] = [memory] - rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        :  "%rbx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for CF (memory form)
bool test_cmp_M64_r64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = cmp_M64_r64_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// REX.W + 2B /r: CMP r/m64, r64 (memory form) - signed version
unsigned char cmp_M64_r64_return_flags(int64_t x, int64_t y) {
    unsigned char ah;
    int64_t val;
    
    __asm__ volatile (
        "movq %1, (%3);"       // store x in memory location
        "movq %2, %%rbx;"      // rbx = y (source register)
        "cmpq %%rbx, (%3);"    // REX.W + 2B /r: [memory] = [memory] - rbx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        :  "%rbx", "%ah"  // clobbered registers
    );

    return ah;
}

// Check property for SF (memory form)
bool test_cmp_M64_r64_SF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char flags = cmp_M64_r64_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (memory form)
bool test_cmp_M64_r64_ZF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char flags = cmp_M64_r64_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (memory form)
bool test_cmp_M64_r64_AF(int64_t x, int64_t y) {
    uint64_t x_lsb = x & 0x0F;
    uint64_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_M64_r64_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (memory form)
bool test_cmp_M64_r64_PF(int64_t x, int64_t y) {
    unsigned char flags = cmp_M64_r64_return_flags(x, y);
    
    int64_t result = x - y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (memory form)
unsigned char cmp_M64_r64_return_OF(int64_t x, int64_t y) {
    unsigned char of;
    int64_t val;
    
    __asm__ volatile (
        "movq %1, (%3);"       // store x in memory location
        "movq %2, %%rbx;"      // rbx = y (source register)
        "cmpq %%rbx, (%3);"    // REX.W + 2B /r: [memory] = [memory] - rbx
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%rbx"               // clobbered registers
    );

    return of;
}

// Check property for OF (memory form)
bool test_cmp_M64_r64_OF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char of = cmp_M64_r64_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//****************************************************************** */
//  CMP r8, m8  
unsigned char cmp_r8_m8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    
    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location
        "movb %1, %%al;"       // al = x (destination register)
        "cmpb (%3), %%al;"     // 2A /r: al = al - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%al", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF 
bool test_cmp_r8_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = cmp_r8_m8_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 2A /r: CMP r8, r/m8 (register form) - signed version
unsigned char cmp_r8_m8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    int8_t val;
    
    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location
        "movb %1, %%al;"       // al = x (destination register)
        "cmpb (%3), %%al;"     // 2A /r: al = al - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%al", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF (register form)
bool test_cmp_r8_m8_SF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_r8_m8_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (register form)
bool test_cmp_r8_m8_ZF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_r8_m8_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (register form)
bool test_cmp_r8_m8_AF(int8_t x, int8_t y) {
    uint8_t x_lsb = x & 0x0F;
    uint8_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_r8_m8_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (register form)
bool test_cmp_r8_m8_PF(int8_t x, int8_t y) {
    unsigned char flags = cmp_r8_m8_return_flags(x, y);
    
    int8_t result = x - y;
    uint8_t expected_parity = calculate_parity((uint8_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (register form)
unsigned char cmp_r8_m8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location
        "movb %1, %%al;"       // al = x (destination register)
        "cmpb (%3), %%al;"     // 2A /r: al = al - [memory]
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%al"                // clobbered registers
    );

    return of;
}

// Check property for OF (register form)
bool test_cmp_r8_m8_OF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char of = cmp_r8_m8_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}





//********************************************************** */
// R8,M8
unsigned char cmp_REX_r8_m8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;
    
    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location
        "movb %1, %%r8b;"      // R8B = x (forces REX prefix)
        "cmpb (%3), %%r8b;"    // REX + 2A /r: R8B = R8B - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%r8", "%ah" // clobbered registers
    );

    return ah;
}

// Check property for CF (REX memory form)
bool test_cmp_REX_r8_m8_CF(uint8_t x, uint8_t y) {
    unsigned char flags = cmp_REX_r8_m8_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char cmp_REX_r8_m8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    int8_t val;
    
    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location
        "movb %1, %%r9b;"      // R9B = x (forces REX prefix)
        "cmpb (%3), %%r9b;"    // REX + 2A /r: R9B = R9B - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%r9", "%ah" // clobbered registers
    );

    return ah;
}

// Check property for SF (REX memory form)
bool test_cmp_REX_r8_m8_SF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_REX_r8_m8_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (REX memory form)
bool test_cmp_REX_r8_m8_ZF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char flags = cmp_REX_r8_m8_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (REX memory form)
bool test_cmp_REX_r8_m8_AF(int8_t x, int8_t y) {
    uint8_t x_lsb = x & 0x0F;
    uint8_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_REX_r8_m8_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (REX memory form)
bool test_cmp_REX_r8_m8_PF(int8_t x, int8_t y) {
    unsigned char flags = cmp_REX_r8_m8_return_flags(x, y);
    
    int8_t result = x - y;
    uint8_t expected_parity = calculate_parity((uint8_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (REX memory form) - CORRECT implementation
unsigned char cmp_REX_r8_m8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movb %2, (%3);"       // store y in memory location
        "movb %1, %%r10b;"     // R10B = x (forces REX prefix)
        "cmpb (%3), %%r10b;"   // REX + 2A /r: R10B = R10B - [memory]
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%r10"              // clobbered registers
    );

    return of;
}

// Check property for OF (REX memory form)
bool test_cmp_REX_r8_m8_OF(int8_t x, int8_t y) {
    int8_t result = x - y;
    unsigned char of = cmp_REX_r8_m8_return_OF(x, y);
    
    // For x - y, overflow occurs when:

    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//************************************************************* */
// r16,m16
unsigned char cmp_r16_m16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;
    
    __asm__ volatile (
        "movw %2, (%3);"       // store y in memory location
        "movw %1, %%ax;"       // ax = x (destination register)
        "cmpw (%3), %%ax;"     // 2B /r: ax = ax - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF (register form)
bool test_cmp_r16_m16_CF(uint16_t x, uint16_t y) {
    unsigned char flags = cmp_r16_m16_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 2B /r: CMP r16, r/m16 (register form) - signed version
unsigned char cmp_r16_m16_return_flags(int16_t x, int16_t y) {
    unsigned char ah;
    int16_t val;
    
    __asm__ volatile (
        "movw %2, (%3);"       // store y in memory location
        "movw %1, %%ax;"       // ax = x (destination register)
        "cmpw (%3), %%ax;"     // 2B /r: ax = ax - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF (register form)
bool test_cmp_r16_m16_SF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char flags = cmp_r16_m16_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (register form)
bool test_cmp_r16_m16_ZF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char flags = cmp_r16_m16_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (register form)
bool test_cmp_r16_m16_AF(int16_t x, int16_t y) {
    uint16_t x_lsb = x & 0x0F;
    uint16_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_r16_m16_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (register form)
bool test_cmp_r16_m16_PF(int16_t x, int16_t y) {
    unsigned char flags = cmp_r16_m16_return_flags(x, y);
    
    int16_t result = x - y;
    uint8_t expected_parity = calculate_parity((uint16_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (register form)
unsigned char cmp_r16_m16_return_OF(int16_t x, int16_t y) {
    unsigned char of;
    int16_t val;
    
    __asm__ volatile (
        "movw %2, (%3);"       // store y in memory location
        "movw %1, %%ax;"       // ax = x (destination register)
        "cmpw (%3), %%ax;"     // 2B /r: ax = ax - [memory]
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%ax"                // clobbered registers
    );

    return of;
}

// Check property for OF (register form)
bool test_cmp_r16_m16_OF(int16_t x, int16_t y) {
    int16_t result = x - y;
    unsigned char of = cmp_r16_m16_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//*********************************************************
// r32,m32 
unsigned char cmp_r32_m32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;
    
    __asm__ volatile (
        "movl %2, (%3);"       // store y in memory location
        "movl %1, %%eax;"      // eax = x (destination register)
        "cmpl (%3), %%eax;"    // 2B /r: eax = eax - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%eax", "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF 
bool test_cmp_r32_m32_CF(uint32_t x, uint32_t y) {
    unsigned char flags = cmp_r32_m32_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 2B /r: CMP r32, r/m32 (register form) - signed version
unsigned char cmp_r32_m32_return_flags(int32_t x, int32_t y) {
    unsigned char ah;
    int32_t val;
    
    __asm__ volatile (
        "movl %2, (%3);"       // store y in memory location
        "movl %1, %%eax;"      // eax = x (destination register)
        "cmpl (%3), %%eax;"    // 2B /r: eax = eax - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%eax", "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for SF (register form)
bool test_cmp_r32_m32_SF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char flags = cmp_r32_m32_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (register form)
bool test_cmp_r32_m32_ZF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char flags = cmp_r32_m32_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (register form)
bool test_cmp_r32_m32_AF(int32_t x, int32_t y) {
    uint32_t x_lsb = x & 0x0F;
    uint32_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_r32_m32_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (register form)
bool test_cmp_r32_m32_PF(int32_t x, int32_t y) {
    unsigned char flags = cmp_r32_m32_return_flags(x, y);
    
    int32_t result = x - y;
    uint8_t expected_parity = calculate_parity((uint32_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (register form)
unsigned char cmp_r32_m32_return_OF(int32_t x, int32_t y) {
    unsigned char of;
    int32_t val;
    
    __asm__ volatile (
        "movl %2, (%3);"       // store y in memory location
        "movl %1, %%eax;"      // eax = x (destination register)
        "cmpl (%3), %%eax;"    // 2B /r: eax = eax - [memory]
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%eax"               // clobbered registers
    );

    return of;
}

// Check property for OF (register form)
bool test_cmp_r32_m32_OF(int32_t x, int32_t y) {
    int32_t result = x - y;
    unsigned char of = cmp_r32_m32_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//***************************************8
// r64,m64 */
unsigned char cmp_r64_m64_return_CF(uint64_t x, uint64_t y) {
    unsigned char ah;
    uint64_t val;
    
    __asm__ volatile (
        "movq %2, (%3);"       // store y in memory location
        "movq %1, %%rax;"      // rax = x (destination register)
        "cmpq (%3), %%rax;"    // REX.W + 2B /r: rax = rax - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%rax", "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF (register form)
bool test_cmp_r64_m64_CF(uint64_t x, uint64_t y) {
    unsigned char flags = cmp_r64_m64_return_CF(x, y);

    if (y > x) {  // Underflow occurred (borrowing needed)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {      // No underflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// REX.W + 2B /r: CMP r64, r/m64 (register form) - signed version
unsigned char cmp_r64_m64_return_flags(int64_t x, int64_t y) {
    unsigned char ah;
    int64_t val;
    
    __asm__ volatile (
        "movq %2, (%3);"       // store y in memory location
        "movq %1, %%rax;"      // rax = x (destination register)
        "cmpq (%3), %%rax;"    // REX.W + 2B /r: rax = rax - [memory]
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // store AH in output
        : "=r" (ah)            // output
        : "r" (x), "r" (y), "r" (&val)  // inputs: x, y, memory address
        : "%rax", "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for SF (register form)
bool test_cmp_r64_m64_SF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char flags = cmp_r64_m64_return_flags(x, y);

    if (result < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}

// Check property for ZF (register form)
bool test_cmp_r64_m64_ZF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char flags = cmp_r64_m64_return_flags(x, y);

    if (result == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF (register form)
bool test_cmp_r64_m64_AF(int64_t x, int64_t y) {
    uint64_t x_lsb = x & 0x0F;
    uint64_t y_lsb = y & 0x0F;
    bool expected_af = (x_lsb < y_lsb);
    
    unsigned char flags = cmp_r64_m64_return_flags(x, y);
    bool actual_af = ((flags & 0x10) != 0);
    
    return expected_af == actual_af;
}

// Check property for PF (register form)
bool test_cmp_r64_m64_PF(int64_t x, int64_t y) {
    unsigned char flags = cmp_r64_m64_return_flags(x, y);
    
    int64_t result = x - y;
    uint8_t expected_parity = calculate_parity((uint64_t)result);
    
    return (flags & 0x04) == expected_parity;
}

// Overflow flag version (register form)
unsigned char cmp_r64_m64_return_OF(int64_t x, int64_t y) {
    unsigned char of;
    int64_t val;
    
    __asm__ volatile (
        "movq %2, (%3);"       // store y in memory location
        "movq %1, %%rax;"      // rax = x (destination register)
        "cmpq (%3), %%rax;"    // REX.W + 2B /r: rax = rax - [memory]
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%rax"               // clobbered registers
    );

    return of;
}

// Check property for OF (register form)
bool test_cmp_r64_m64_OF(int64_t x, int64_t y) {
    int64_t result = x - y;
    unsigned char of = cmp_r64_m64_return_OF(x, y);
    
    // For x - y, overflow occurs when:
    // (positive - negative = negative) OR (negative - positive = positive)
    if (((x >= 0) && (y < 0) && (result < 0)) ||
        ((x < 0) && (y >= 0) && (result >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


// dummy main function, to allow us to link the executable
int main () { return 0;}


