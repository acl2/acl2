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
// ADD al, i8

unsigned char add_AL_i8_return_CF (uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // al = x 
        "addb $0x02, %%al;"       // al += imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)     // inputs
        : "%al", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah

bool test_add_AL_i8_CF (uint8_t x) {
    uint8_t  sum = x + 2;
    unsigned char flags = add_AL_i8_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_AL_i8_return_flags (int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // al = x 
        "addb $0x02, %%al;"       // al += imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)                 // inputs
        : "%al", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_AL_i8_SF (int8_t x) {
  
    int8_t sum = x+2;  
    unsigned char flags = add_AL_i8_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	} 
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_AL_i8_ZF (int8_t x) {
  
  int8_t sum = x+2;  
    unsigned char flags = add_AL_i8_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
      
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_AL_i8_AF (int8_t x) {

  int8_t sum_lsb = (x & 0x0F) + (0x02 & 0x0F); // Only add least 4 bits, zero out all other bits
  int8_t AF_value = sum_lsb & 0x10; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_AL_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
    }
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add_AL_i8_PF(int8_t x) {
    unsigned char flags = add_AL_i8_return_flags(x);
    
    int8_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_AL_i8_return_OF (int8_t x) {
    unsigned char of;
    __asm__ volatile (
        "movb %1, %%al;"      // Load x into AL
        "addb $0x02, %%al;"      // al += imm 
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)             // Input operands
        : "%al"              // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_AL_i8_OF (int8_t x) {
    int8_t sum = x + 2;
    unsigned char of = add_AL_i8_return_OF(x);
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}




//**********************************************************
// ADD ax, i16

unsigned char add_ax_i16_return_CF (uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x 
        "addw $0x0002, %%ax;"       // ax += imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)                // inputs
        : "%ax", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah

bool test_add_ax_i16_CF (uint16_t  x) {
    uint16_t  sum = x + 0x0002;
       unsigned char flags = add_ax_i16_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_ax_i16_return_flags (int16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x (16-bit)
        "addw $0x0002, %%ax;"       // ax += imm (16-bit)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)            // inputs
        : "%ax", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_ax_i16_SF (int16_t x) {
  
  int16_t sum = x+ 0x0002;  
    unsigned char flags = add_ax_i16_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_ax_i16_ZF (int16_t x) {
  
  int16_t sum = x+0x0002;  
    unsigned char flags = add_ax_i16_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_ax_i16_AF (int16_t x) {

  int16_t sum_lsb = (x & 0x000F) + (0x0002 & 0x000F); // Only add least 4 bits, zero out all other bits
  int16_t AF_value = sum_lsb & 0x0010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_ax_i16_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04


bool test_add_ax_i16_PF (int16_t x) {
   unsigned char flags = add_ax_i16_return_flags(x);
    
    int16_t result = x + 0x0002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}



 unsigned char add_ax_i16_return_OF (int16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"      // Load x into ax 
        "addw $0x0002, %%ax;"      // ax += imm 
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)      // Input operands
        : "%ax"              // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_ax_i16_OF (int16_t x) {
    int16_t sum = x + 0x0002;
    unsigned char of = add_ax_i16_return_OF(x);
      if (((x >= 0) && (0x0002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x0002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//**********************************************************
// ADD eax, i32

unsigned char add_eax_i32_return_CF (uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x
        "addl $0x00000002, %%eax;"   // eax += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)    // inputs
        : "%eax", "%ah"// clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_add_eax_i32_CF (uint32_t  x) {
    uint32_t  sum = x + 0x00000002;
  
    unsigned char flags = add_eax_i32_return_CF(x);

    if (sum < x) {  // Overflow occurred in unsigned addition
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_eax_i32_return_flags (int32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x
        "addl $0x00000002, %%eax;"   // eax += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%eax", "%ah"// clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_eax_i32_SF (int32_t x) {
  
  int32_t sum = x+ 0x00000002;  
    unsigned char flags = add_eax_i32_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_eax_i32_ZF (int32_t x) {
  
  int32_t sum = x+ 0x00000002;  
    unsigned char flags = add_eax_i32_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}

    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_eax_i32_AF (int32_t x) {

  int32_t sum_lsb = (x & 0x0000000F) + (0x00000002 & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x00000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_eax_i32_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_eax_i32_PF (int32_t x) {
    unsigned char flags = add_eax_i32_return_flags(x);
    
    int32_t result = x + 0x00000002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_eax_i32_return_OF (int32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"     // Load x into EAX
	"addl $0x00000002, %%eax;"   // eax += imm
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)       // Input operands
	: "%eax"      // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_eax_i32_OF (int32_t x) {
    int32_t sum = x + 0x00000002;
    unsigned char of = add_eax_i32_return_OF(x);
     if (((x >= 0) && (0x00000002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x00000002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//**********************************************************
// ADD rax, i32

unsigned char add_RAX_i32_return_CF (unsigned long long x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "addq $0x00000002, %%rax;"   // rax += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)     // inputs
        : "%rax", "%ah"// clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_add_RAX_i32_CF (unsigned long long x) {
    unsigned long long sum = x + 0x00000002;
  
    unsigned char flags = add_RAX_i32_return_CF(x);

    if (sum < x) {  // Overflow occurred in unsigned addition
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_RAX_i32_return_flags (long long x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "addq $0x00000002, %%rax;"   // rax += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)     // inputs
        : "%rax", "%ah"// clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_RAX_i32_SF (long long x) {
  
  long long sum = x+0x00000002;  
    unsigned char flags = add_RAX_i32_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	} 

    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_RAX_i32_ZF (long long x) {
  
  long long sum = x+0x00000002;  
    unsigned char flags = add_RAX_i32_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}

    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_RAX_i32_AF (long long x) {

  long long sum_lsb = (x & 0x000000000000000F) + (0x00000002 & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  int AF_value = sum_lsb & 0x0000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_RAX_i32_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_RAX_i32_PF(long long x) {
   unsigned char flags = add_RAX_i32_return_flags(x);
    
    long long result = x + 0x00000002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_RAX_i32_return_OF (long long x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"     // Load x into RAX
	"addq $0x00000002, %%rax;"   // rax += imm
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)      // Input operands
	: "%rax"     // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_RAX_i32_OF (long long x) {
  long long  sum = x + 0x00000002;
    unsigned char of = add_RAX_i32_return_OF(x);
     if (((x >= 0) && (0x00000002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x00000002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}
//***************************************************
// ADD r8, i8 

unsigned char add_R8_i8_return_CF (uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%cl;"       // al = x 
        "addb $0x02, %%cl;"       // cl += imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)     // inputs
        : "%cl", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah

bool test_add_R8_i8_CF (uint8_t x) {
    uint8_t  sum = x + 2;
    unsigned char flags = add_R8_i8_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_R8_i8_return_flags (int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%cl;"       // cl = x 
        "addb $0x02, %%cl;"       // cl += imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)                 // inputs
        : "%cl", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_R8_i8_SF (int8_t x) {
  
    int8_t sum = x+2;  
    unsigned char flags = add_R8_i8_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	} 
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_R8_i8_ZF (int8_t x) {
  
  int8_t sum = x+2;  
    unsigned char flags = add_R8_i8_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
      
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_R8_i8_AF (int8_t x) {

  int8_t sum_lsb = (x & 0x0F) + (0x02 & 0x0F); // Only add least 4 bits, zero out all other bits
  int8_t AF_value = sum_lsb & 0x10; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_R8_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
    }
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add_R8_i8_PF(int8_t x) {
    unsigned char flags = add_R8_i8_return_flags(x);
    
    int8_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_R8_i8_return_OF (int8_t x) {
    unsigned char of;
    __asm__ volatile (
        "movb %1, %%cl;"      // Load x into cl
        "addb $0x02, %%cl;"      // cl += imm 
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)             // Input operands
        : "%cl"              // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_R8_i8_OF (int8_t x) {
    int8_t sum = x + 2;
    unsigned char of = add_R8_i8_return_OF(x);
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//*****************************************************
// ADD m8, i8 


unsigned char add_M8_i8_return_CF(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "addb $0x02, (%2);"    // 80/0 ib: [memory] = [memory] + imm8
        "movb (%2), %%al;"     // load result from memory to AL for LAHF
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%al", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_M8_i8_CF(uint8_t x) {
    uint8_t sum = x + 2;
    unsigned char flags = add_M8_i8_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 80/0 ib: ADD r/m8, imm8 (memory form) - signed version
unsigned char add_M8_i8_return_flags(int8_t x) {
    unsigned char ah;
    int8_t val;

    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "addb $0x02, (%2);"    // 80/0 ib: [memory] = [memory] + imm8
        "movb (%2), %%al;"     // load result from memory to AL for LAHF
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%al", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_M8_i8_SF(int8_t x) {
    int8_t sum = x + 2;  
    unsigned char flags = add_M8_i8_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_M8_i8_ZF(int8_t x) {
    int8_t sum = x + 2;  
    unsigned char flags = add_M8_i8_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_M8_i8_AF(int8_t x) {
    int8_t sum_lsb = (x & 0x0F) + (0x02 & 0x0F); // Only add least 4 bits, zero out all other bits
    int8_t AF_value = sum_lsb & 0x10; // extract bit 4, should represent AF flag value
    
    unsigned char flags = add_M8_i8_return_flags(x);

    if (AF_value == 16) {
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_M8_i8_PF(int8_t x) {
    unsigned char flags = add_M8_i8_return_flags(x);
    
    int8_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// overflow flag version
unsigned char add_M8_i8_return_OF(int8_t x) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movb %1, (%2);"       // store x in memory location
        "addb $0x02, (%2);"    // [memory] = [memory] + imm8
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        : "%al"                // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_M8_i8_OF(int8_t x) {
    int8_t sum = x + 2;
    unsigned char of = add_M8_i8_return_OF(x);
    
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


// ============================================================================
// ADD REX_r8, i8 

unsigned char add_REX_register8_imm8_return_CF(uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r8b;"      // Use %b1 to force 8-bit access
        "addb $0x02, %%r8b;"    // REX + 80/0 ib: R8B = R8B + imm8
        "movb %%r8b, %%al;"     // Move result to AL for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x)               // Input: x
        : "r8", "al", "ah"      // Clobbered registers 
    );

    return ah;
}
// Check property for CF
// CF is bit 0 in ah
bool test_add_REX_register8_imm8_CF(uint8_t x) {
    uint8_t sum = x + 2;
    unsigned char flags = add_REX_register8_imm8_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_REX_register8_imm8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r9b;"       // Load x into R9B (extended register)
        "addb $0x02, %%r9b;"    // REX + 80/0 ib: R9B = R9B + imm8 (register form)
        "movb %%r9b, %%al;"     // Move result to AL for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x)               // Input: x
        : "%r9", "%al", "%ah"   // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_REX_register8_imm8_SF(int8_t x) {
    int8_t sum = x + 2;  
    unsigned char flags = add_REX_register8_imm8_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_REX_register8_imm8_ZF(int8_t x) {
    int8_t sum = x + 2;  
    unsigned char flags = add_REX_register8_imm8_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_REX_register8_imm8_AF(int8_t x) {
    int8_t sum_lsb = (x & 0x0F) + (0x02 & 0x0F); // Only add least 4 bits, zero out all other bits
    int8_t AF_value = sum_lsb & 0x10; // extract bit 4, should represent AF flag value
    
    unsigned char flags = add_REX_register8_imm8_return_flags(x);

    if (AF_value == 16) {
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_REX_register8_imm8_PF(int8_t x) {
    unsigned char flags = add_REX_register8_imm8_return_flags(x);
    
    int8_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_REX_register8_imm8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%r10b;"      // Load x into R10B (extended register)
        "addb $0x02, %%r10b;"   // REX + 80/0 ib: R10B = R10B + imm8 (register form)
        "seto %0;"              // Set 'of' to 1 if overflow occurred
        : "=r"(of)              // Output operand (OF flag)
        : "r"(x)                // Input operand: x
        : "%r10"                // Clobbered register
    );

    return of;
}

// Check property for OF
bool test_add_REX_register8_imm8_OF(int8_t x) {
    int8_t sum = x + 2;
    unsigned char of = add_REX_register8_imm8_return_OF(x);
    
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


// ============================================================================
//  ADD REX_m8, i8 

unsigned char add_REX_memory8_imm8_return_CF(uint8_t x) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movq %2, %%r8;"        // Load memory address into R8 (extended register)
        "movb %1, (%%r8);"      // Store x in memory using R8 addressing
        "addb $0x02, (%%r8);"   // REX + 80/0 ib: [R8] = [R8] + imm8 (memory form)
        "movb (%%r8), %%al;"    // Load result from memory to AL for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x), "r" (&val)   // Inputs: x, memory address
        : "%r8", "%al", "%ah"   // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_REX_memory8_imm8_CF(uint8_t x) {
    uint16_t sum = (uint16_t)x + 2;
    unsigned char flags = add_REX_memory8_imm8_return_CF(x);

    if (sum > 255) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {          // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_REX_memory8_imm8_return_flags(int8_t x) {
    unsigned char ah;
    int8_t val;

    __asm__ volatile (
        "movq %2, %%r9;"        // Load memory address into R9 (extended register)
        "movb %1, (%%r9);"      // Store x in memory using R9 addressing
        "addb $0x02, (%%r9);"   // REX + 80/0 ib: [R9] = [R9] + imm8 (memory form)
        "movb (%%r9), %%al;"    // Load result from memory to AL for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x), "r" (&val)   // Inputs: x, memory address
        : "%r9", "%al", "%ah"   // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_REX_memory8_imm8_SF(int8_t x) {
    int8_t sum = x + 2;  
    unsigned char flags = add_REX_memory8_imm8_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_REX_memory8_imm8_ZF(int8_t x) {
    int8_t sum = x + 2;  
    unsigned char flags = add_REX_memory8_imm8_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_REX_memory8_imm8_AF(int8_t x) {
    int8_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int8_t imm_lsb = 0x02 & 0x0F; // Get lower 4 bits of immediate (0x02)
    
    unsigned char flags = add_REX_memory8_imm8_return_flags(x);

    if ((x_lsb + imm_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_REX_memory8_imm8_PF(int8_t x) {
    unsigned char flags = add_REX_memory8_imm8_return_flags(x);
    
    int8_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_REX_memory8_imm8_return_OF(int8_t x) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movq %2, %%r10;"       // Load memory address into R10 (extended register)
        "movb %1, (%%r10);"     // Store x in memory using R10 addressing
        "addb $0x02, (%%r10);"  // REX + 80/0 ib: [R10] = [R10] + imm8 (memory form)
        "seto %0;"              // Set 'of' to 1 if overflow occurred
        : "=r"(of)              // Output operand (OF flag)
        : "r"(x), "r" (&val)    // Input operands: x, memory address
        : "%r10"                // Clobbered register
    );

    return of;
}

// Check property for OF
bool test_add_REX_memory8_imm8_OF(int8_t x) {
    int8_t sum = x + 2;
    unsigned char of = add_REX_memory8_imm8_return_OF(x);
    
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}




//*********************************************************
// Add r16, i16 

unsigned char add_R16_i16_return_CF (uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%cx;"       // cx = x 
        "addw $0x0002, %%cx;"       // cx += imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)                // inputs
        : "%cx", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for CF
//CF is bit 0 in ah

bool test_add_R16_i16_CF (uint16_t  x) {
    uint16_t  sum = x + 0x0002;
       unsigned char flags = add_R16_i16_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_R16_i16_return_flags (int16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%cx;"       // cx = x (16-bit)
        "addw $0x0002, %%cx;"       // cx += imm (16-bit)
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)            // inputs
        : "%cx", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_R16_i16_SF (int16_t x) {
  
  int16_t sum = x+ 0x0002;  
    unsigned char flags = add_R16_i16_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_R16_i16_ZF (int16_t x) {
  
  int16_t sum = x+0x0002;  
    unsigned char flags = add_R16_i16_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_R16_i16_AF (int16_t x) {

  int16_t sum_lsb = (x & 0x000F) + (0x0002 & 0x000F); // Only add least 4 bits, zero out all other bits
  int16_t AF_value = sum_lsb & 0x0010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_R16_i16_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04


bool test_add_R16_i16_PF (int16_t x) {
   unsigned char flags = add_R16_i16_return_flags(x);
    
    int16_t result = x + 0x0002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}



 unsigned char add_R16_i16_return_OF (int16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%cx;"      // Load x into cx 
        "addw $0x0002, %%cx;"      // cx += imm 
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)      // Input operands
        : "%cx"              // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_R16_i16_OF (int16_t x) {
    int16_t sum = x + 0x0002;
    unsigned char of = add_R16_i16_return_OF(x);
      if (((x >= 0) && (0x0002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x0002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//********************************************************************* */
// ADD m16, i16
unsigned char add_M16_i16_return_CF(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "addw $0x0002, (%2);"  // 81/0 iw: [memory] = [memory] + imm16
        "movw (%2), %%ax;"     // load result from memory to AX for LAHF
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_M16_i16_CF(uint16_t x) {
    uint16_t sum = x + 2;
    unsigned char flags = add_M16_i16_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_M16_i16_return_flags(int16_t x) {
    unsigned char ah;
    int16_t val;

    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "addw $0x0002, (%2);"  // 81/0 iw: [memory] = [memory] + imm16
        "movw (%2), %%ax;"     // load result from memory to AX for LAHF
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%ax", "%ah"         // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_M16_i16_SF(int16_t x) {
    int16_t sum = x + 2;  
    unsigned char flags = add_M16_i16_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_M16_i16_ZF(int16_t x) {
    int16_t sum = x + 2;  
    unsigned char flags = add_M16_i16_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_M16_i16_AF(int16_t x) {
    int16_t sum_lsb = (x & 0x0F) + (0x0002 & 0x0F); // Only add least 4 bits, zero out all other bits
    int16_t AF_value = sum_lsb & 0x10; // extract bit 4, should represent AF flag value
    
    unsigned char flags = add_M16_i16_return_flags(x);

    if (AF_value == 16) {
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_M16_i16_PF(int16_t x) {
    unsigned char flags = add_M16_i16_return_flags(x);
    
    int16_t result = x + 0x0002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}
// overflow flag version
unsigned char add_M16_i16_return_OF(int16_t x) {
    unsigned char of;
    int16_t val;
    
    __asm__ volatile (
        "movw %1, (%2);"       // store x in memory location
        "addw $0x0002, (%2);"  // 81/0 iw: [memory] = [memory] + imm16
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        : "%ax"                // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_M16_i16_OF(int16_t x) {
    int16_t sum = x + 2;
    unsigned char of = add_M16_i16_return_OF(x);
    
    if (((x >= 0) && (0x0002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x0002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//**********************************************************
// ADD r32, i32

unsigned char add_R32_i32_return_CF (uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%ecx;"      // ecx = x
        "addl $0x00000002, %%ecx;"   // ecx += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)    // inputs
        : "%ecx", "%ah"// clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_add_R32_i32_CF (uint32_t  x) {
    uint32_t  sum = x + 0x00000002;
  
    unsigned char flags = add_R32_i32_return_CF(x);

    if (sum < x) {  // Overflow occurred in unsigned addition
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_R32_i32_return_flags (int32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%ecx;"      // ecx = x
        "addl $0x00000002, %%ecx;"   // ecx += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%ecx", "%ah"// clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_R32_i32_SF (int32_t x) {
  
  int32_t sum = x+ 0x00000002;  
    unsigned char flags = add_R32_i32_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_R32_i32_ZF (int32_t x) {
  
  int32_t sum = x+ 0x00000002;  
    unsigned char flags = add_R32_i32_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}

    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_R32_i32_AF (int32_t x) {

  int32_t sum_lsb = (x & 0x0000000F) + (0x00000002 & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x00000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_R32_i32_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_R32_i32_PF (int32_t x) {
    unsigned char flags = add_R32_i32_return_flags(x);
    
    int32_t result = x + 0x00000002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_R32_i32_return_OF (int32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%ecx;"     // Load x into ecx
	"addl $0x00000002, %%ecx;"   // ecx += imm
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)       // Input operands
	: "%ecx"      // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_R32_i32_OF (int32_t x) {
    int32_t sum = x + 0x00000002;
    unsigned char of = add_R32_i32_return_OF(x);
     if (((x >= 0) && (0x00000002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x00000002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//***********************************************************88 */
// ADD m32, i32
unsigned char add_M32_i32_return_CF(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "addl $0x00000002, (%2);"  // 81/0 id: [memory] = [memory] + imm32
        "movl (%2), %%eax;"    // load result from memory to EAX for LAHF
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%eax", "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_M32_i32_CF(uint32_t x) {
    uint32_t sum = x + 2;
    unsigned char flags = add_M32_i32_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// 81/0 id: ADD r/m32, imm32 (memory form) - signed version
unsigned char add_M32_i32_return_flags(int32_t x) {
    unsigned char ah;
    int32_t val;

    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "addl $0x00000002, (%2);"  // 81/0 id: [memory] = [memory] + imm32
        "movl (%2), %%eax;"    // load result from memory to EAX for LAHF
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%eax", "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_M32_i32_SF(int32_t x) {
    int32_t sum = x + 2;  
    unsigned char flags = add_M32_i32_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_M32_i32_ZF(int32_t x) {
    int32_t sum = x + 2;  
    unsigned char flags = add_M32_i32_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_M32_i32_AF(int32_t x) {
    int32_t sum_lsb = (x & 0x0F) + (0x00000002 & 0x0F); // Only add least 4 bits, zero out all other bits
    int32_t AF_value = sum_lsb & 0x10; // extract bit 4, should represent AF flag value
    
    unsigned char flags = add_M32_i32_return_flags(x);

    if (AF_value == 16) {
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_M32_i32_PF(int32_t x) {
    unsigned char flags = add_M32_i32_return_flags(x);
    
    int32_t result = x + 0x00000002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}
// overflow flag version
unsigned char add_M32_i32_return_OF(int32_t x) {
    unsigned char of;
    int32_t val;
    
    __asm__ volatile (
        "movl %1, (%2);"       // store x in memory location
        "addl $0x00000002, (%2);"  // 81/0 id: [memory] = [memory] + imm32
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        : "%eax"               // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_M32_i32_OF(int32_t x) {
    int32_t sum = x + 2;
    unsigned char of = add_M32_i32_return_OF(x);
    
    if (((x >= 0) && (0x00000002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x00000002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//***************************************************
// ADD r64, i32

unsigned char add_R64_i32_return_CF (unsigned long long x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rcx;"      // rcx = x
        "addq $0x00000002, %%rcx;"   // rcx += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)     // inputs
        : "%rcx", "%ah"// clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_add_R64_i32_CF (unsigned long long x) {
    unsigned long long sum = x + 0x00000002;
  
    unsigned char flags = add_R64_i32_return_CF(x);

    if (sum < x) {  // Overflow occurred in unsigned addition
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_R64_i32_return_flags (long long x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rcx;"      // rcx = x
        "addq $0x00000002, %%rcx;"   // rcx += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)     // inputs
        : "%rcx", "%ah"// clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_R64_i32_SF (long long x) {
  
  long long sum = x+0x00000002;  
    unsigned char flags = add_R64_i32_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	} 

    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_R64_i32_ZF (long long x) {
  
  long long sum = x+0x00000002;  
    unsigned char flags = add_R64_i32_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}

    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_R64_i32_AF (long long x) {

  long long sum_lsb = (x & 0x000000000000000F) + (0x00000002 & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  long long AF_value = sum_lsb & 0x0000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_R64_i32_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_R64_i32_PF(long long  x) {
   unsigned char flags = add_R64_i32_return_flags(x);
    
    long long result = x + 0x00000002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_R64_i32_return_OF (long long x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rcx;"     // Load x into rcx
	"addq $0x00000002, %%rcx;"   // rcx += imm
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)      // Input operands
	: "%rcx"     // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_R64_i32_OF (long long x) {
  long long sum = x + 0x00000002;
    unsigned char of = add_R64_i32_return_OF(x);
     if (((x >= 0) && (0x00000002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x00000002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}



// ============================================================================
// ADD m64, i32
// ============================================================================

unsigned char add_M64_i32_return_CF(unsigned long long x) {
    unsigned char ah;
    unsigned long long val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "addq $0x00000002, (%2);"  // REX.W + 81/0 id: [memory] = [memory] + imm32 (sign-extended to 64-bit)
        "movq (%2), %%rax;"    // load result from memory to RAX for LAHF
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%rax", "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_M64_i32_CF(unsigned long long x) {
    unsigned long long sum = x + 2;
    unsigned char flags = add_M64_i32_return_CF(x);

    if (sum < x) {  // Overflow occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

// REX.W + 81/0 id: ADD r/m64, imm32 (memory form) - signed version
unsigned char add_M64_i32_return_flags(long long x) {
    unsigned char ah;
    long long val;

    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "addq $0x00000002, (%2);"  // REX.W + 81/0 id: [memory] = [memory] + imm32 (sign-extended to 64-bit)
        "movq (%2), %%rax;"    // load result from memory to RAX for LAHF
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (&val)  // inputs: x, memory address
        : "%rax", "%ah"        // clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_M64_i32_SF(long long x) {
    long long sum = x + 2;  
    unsigned char flags = add_M64_i32_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_M64_i32_ZF(long long x) {
    long long sum = x + 2;  
    unsigned char flags = add_M64_i32_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_M64_i32_AF(long long x) {
    long long sum_lsb = (x & 0x0F) + (0x00000002 & 0x0F); // Only add least 4 bits, zero out all other bits
    int AF_value = sum_lsb & 0x10; // extract bit 4, should represent AF flag value
    
    unsigned char flags = add_M64_i32_return_flags(x);

    if (AF_value == 16) {
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_M64_i32_PF(long long x) {
    unsigned char flags = add_M64_i32_return_flags(x);
    
    long long result = x + 0x00000002;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

// REX.W + 81/0 id: ADD r/m64, imm32 (memory form) - overflow flag version
unsigned char add_M64_i32_return_OF(long long x) {
    unsigned char of;
    long long val;
    
    __asm__ volatile (
        "movq %1, (%2);"       // store x in memory location
        "addq $0x00000002, (%2);"  // REX.W + 81/0 id: [memory] = [memory] + imm32 (sign-extended to 64-bit)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r" (&val)   // Input operands: x, memory address
        : "%rax"               // clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_M64_i32_OF( long long x) {
    long long sum = x + 2;
    unsigned char of = add_M64_i32_return_OF(x);
    
    if (((x >= 0) && (0x00000002 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x00000002 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


 

//**********************************************************
//  ADD r16/i8

unsigned char OP83_r16_i8_return_CF(uint16_t x) {
    unsigned char ah;

  __asm__ volatile (
        "movw %1, %%ax;"           // Load x into AX  
        "addw $0x02, %%ax;"           // ADD AX
        "lahf;"                     // Load flags into AH
        "movb %%ah, %0;"            // Move AH to output
        : "=r" (ah)                 // Output
        : "r" (x)      // Inputs: x and immediate constant
        : "%ax", "%ah"             // Clobbered registers
    );
    
    return ah;
}


//check property for CF
//CF is bit 0 in ah
bool test_OP83_r16_i8_CF(uint16_t x) {
    uint16_t sum = x + 2;
    unsigned char flags = OP83_r16_i8_return_CF(x);  

    if (sum < x) {  
        return ((flags & 0x01) == 0x01);  
    } else {       
        return ((flags & 0x01) == 0x00);  
    }
}



unsigned char OP83_r16_i8_return_flags(int16_t x) {
    unsigned char ah;
    
    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x (16-bit)
        "addw $0x02, %%ax;"       // ax += imm 
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)               // inputs
        : "%ax", "%ah"        // clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_OP83_r16_i8_SF (int16_t x) {
  
  int16_t sum = x+2;  
    unsigned char flags = OP83_r16_i8_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
     

    
}



//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_OP83_r16_i8_ZF (int16_t x) {
  
  int16_t sum = x+2;  
    unsigned char flags = OP83_r16_i8_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	} 

    
}



//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_OP83_r16_i8_AF (int16_t x) {

  int16_t sum_lsb = (x & 0x000F) + (2 & 0x000F); // Only add least 4 bits, zero out all other bits
  int16_t AF_value = sum_lsb & 0x0010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = OP83_r16_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    

    
}



//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
    bool test_OP83_r16_i8_PF(int16_t x) {
    unsigned char flags = OP83_r16_i8_return_flags(x);
    
    int16_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char OP83_r16_i8_return_OF (int16_t x) {
    unsigned char of;
     __asm__ volatile (
        "movw %1, %%ax;"      // Load x into AX 
        "addw $2, %%ax;"      // ax += imm 
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)      // Input operands
        : "%ax"             // clobbered registers
    );

    return of;
}
//check property for OF

bool test_OP83_r16_i8_OF (int16_t x) {
    int16_t sum = x + 0x02;
    unsigned char of = OP83_r16_i8_return_OF(x);
     if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}



// ============================================================================
// ADD m16, i8 (sign-extended)


unsigned char OP83_memory16_imm8_return_CF(uint16_t x) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%2);"        // Store x in memory location
        "addw $0x02, (%2);"     // OP83/0 ib: [memory] = [memory] + imm8 (sign-extended to 16-bit)
        "movw (%2), %%ax;"      // Load result from memory to AX for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x), "r" (&val)   // Inputs: x, memory address
        : "%ax", "%ah"          // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_OP83_memory16_imm8_CF(uint16_t x) {
    uint32_t sum = (uint32_t)x + 2;
    unsigned char flags = OP83_memory16_imm8_return_CF(x);

    if (sum > 65535) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {            // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char OP83_memory16_imm8_return_flags(int16_t x) {
    unsigned char ah;
    int16_t val;

    __asm__ volatile (
        "movw %1, (%2);"        // Store x in memory location
        "addw $0x02, (%2);"     // OP83/0 ib: [memory] = [memory] + imm8 (sign-extended to 16-bit)
        "movw (%2), %%ax;"      // Load result from memory to AX for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x), "r" (&val)   // Inputs: x, memory address
        : "%ax", "%ah"          // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_OP83_memory16_imm8_SF(int16_t x) {
    int16_t sum = x + 2;  
    unsigned char flags = OP83_memory16_imm8_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_OP83_memory16_imm8_ZF(int16_t x) {
    int16_t sum = x + 2;  
    unsigned char flags = OP83_memory16_imm8_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_OP83_memory16_imm8_AF(int16_t x) {
    int16_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int16_t imm_lsb = 0x02 & 0x0F; // Get lower 4 bits of immediate (0x02)
    
    unsigned char flags = OP83_memory16_imm8_return_flags(x);

    if ((x_lsb + imm_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_OP83_memory16_imm8_PF(int16_t x) {
    unsigned char flags = OP83_memory16_imm8_return_flags(x);
    
    int16_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char OP83_memory16_imm8_return_OF(int16_t x) {
    unsigned char of;
    int16_t val;
    
    __asm__ volatile (
        "movw %1, (%2);"        // Store x in memory location
        "addw $0x02, (%2);"     // OP83/0 ib: [memory] = [memory] + imm8 (sign-extended to 16-bit)
        "seto %0;"              // Set 'of' to 1 if overflow occurred
        : "=r"(of)              // Output operand (OF flag)
        : "r"(x), "r" (&val)    // Input operands: x, memory address
        : "%ax"                 // Clobbered register
    );

    return of;
}

// Check property for OF
bool test_OP83_memory16_imm8_OF(int16_t x) {
    int16_t sum = x + 2;
    unsigned char of = OP83_memory16_imm8_return_OF(x);
    
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//**********************************************************
// ADD r32, i8

unsigned char OP83_r32_i8_return_CF(uint32_t x) {
    unsigned char ah;

     __asm__ volatile (
        "movl %1, %%eax;"      // eax = x
        "addl $0x02, %%eax;"   // eax += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%eax", "%ah"        // clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah
  
bool test_OP83_r32_i8_CF (uint32_t x) {
    uint32_t sum = x + 0x02;
    unsigned char flags = OP83_r32_i8_return_CF(x);
    
    if (sum < x) {  
        return ((flags & 0x01) == 0x01);  
    } else {        
        return ((flags & 0x01) == 0x00); 
    }
}


unsigned char OP83_r32_i8_return_flags(int32_t x) {
    unsigned char ah;
    
     __asm__ volatile (
        "movl %1, %%eax;"      // eax = x
        "addl $0x02, %%eax;"   // eax += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%eax", "%ah"// clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_OP83_r32_i8_SF (int32_t x) {
  
  int32_t sum = x+0x02;  
    unsigned char flags = OP83_r32_i8_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_OP83_r32_i8_ZF (int32_t x) {
  
  int32_t sum = x+0x02;  
    unsigned char flags = OP83_r32_i8_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
    

    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_OP83_r32_i8_AF ( int32_t x) {

  int32_t sum_lsb = (x & 0x0000000F) + (0x02 & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x00000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = OP83_r32_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

  
   bool test_OP83_r32_i8_PF(int32_t x) {
    unsigned char flags = OP83_r32_i8_return_flags(x);
    
    int32_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}
  

  unsigned char OP83_r32_i8_return_OF(int32_t x) {
    unsigned char of;
    
     __asm__ volatile (
        "movl %1, %%eax;"     // Load x into EAX
	      "addl $0x02, %%eax;"   // eax += imm
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)              // Input operands
	       : "%eax"              // clobbered registers
    );

    return of;
}
//check property for OF

bool test_OP83_r32_i8_OF (int32_t x) {
  
    int32_t sum = x + 2;
    unsigned char of = OP83_r32_i8_return_OF(x);
     if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


// ============================================================================
// ADD m32, i8 (sign-extended)


unsigned char OP83_memory32_imm8_return_CF(uint32_t x) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%2);"        // Store x in memory location
        "addl $0x02, (%2);"     // OP83/0 ib: [memory] = [memory] + imm8 (sign-extended to 32-bit)
        "movl (%2), %%eax;"     // Load result from memory to EAX for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x), "r" (&val)   // Inputs: x, memory address
        : "%eax", "%ah"         // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_OP83_memory32_imm8_CF(uint32_t x) {
    uint64_t sum = (uint64_t)x + 2;
    unsigned char flags = OP83_memory32_imm8_return_CF(x);

    if (sum > 4294967295UL) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {                   // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char OP83_memory32_imm8_return_flags(int32_t x) {
    unsigned char ah;
    int32_t val;

    __asm__ volatile (
        "movl %1, (%2);"        // Store x in memory location
        "addl $0x02, (%2);"     // OP83/0 ib: [memory] = [memory] + imm8 (sign-extended to 32-bit)
        "movl (%2), %%eax;"     // Load result from memory to EAX for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x), "r" (&val)   // Inputs: x, memory address
        : "%eax", "%ah"         // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_OP83_memory32_imm8_SF(int32_t x) {
    int32_t sum = x + 2;  
    unsigned char flags = OP83_memory32_imm8_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_OP83_memory32_imm8_ZF(int32_t x) {
    int32_t sum = x + 2;  
    unsigned char flags = OP83_memory32_imm8_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_OP83_memory32_imm8_AF(int32_t x) {
    int32_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int32_t imm_lsb = 0x02 & 0x0F; // Get lower 4 bits of immediate (0x02)
    
    unsigned char flags = OP83_memory32_imm8_return_flags(x);

    if ((x_lsb + imm_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_OP83_memory32_imm8_PF(int32_t x) {
    unsigned char flags = OP83_memory32_imm8_return_flags(x);
    
    int32_t result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char OP83_memory32_imm8_return_OF(int32_t x) {
    unsigned char of;
    int32_t val;
    
    __asm__ volatile (
        "movl %1, (%2);"        // Store x in memory location
        "addl $0x02, (%2);"     // OP83/0 ib: [memory] = [memory] + imm8 (sign-extended to 32-bit)
        "seto %0;"              // Set 'of' to 1 if overflow occurred
        : "=r"(of)              // Output operand (OF flag)
        : "r"(x), "r" (&val)    // Input operands: x, memory address
        : "%eax"                // Clobbered register
    );

    return of;
}

// Check property for OF
bool test_OP83_memory32_imm8_OF(int32_t x) {
    int32_t sum = x + 2;
    unsigned char of = OP83_memory32_imm8_return_OF(x);
    
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//**********************************************************
// ADD r64, i8

unsigned char REXW_r64_i8_return_CF(unsigned long long x) {
    unsigned char ah;

   __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "addq $0x02, %%rax;"   // rax += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%rax", "%ah"// clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_REXW_r64_i8_CF(unsigned long long x) {
    unsigned long long sum = x + 0x02;
    unsigned char flags = REXW_r64_i8_return_CF(x);
    
    if (sum < x) {  
        return ((flags & 0x01) == 0x01); 
    } else {        
        return ((flags & 0x01) == 0x00); 
    }
}
    

unsigned char REXW_r64_i8_return_flags(unsigned long long x) {
    unsigned char ah;


    __asm__ volatile (
        "movq %1, %%rax;"      // rax = x
        "addq $0x02, %%rax;"   // rax += imm
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x)              // inputs
        : "%rax", "%ah"// clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_REXW_r64_i8_SF (long long x) {
  
  long long sum = x+0x02;  
    unsigned char flags = REXW_r64_i8_return_flags(x);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_REXW_r64_i8_ZF (long long x) {
  
  long long sum = x+0x02;  
    unsigned char flags = REXW_r64_i8_return_flags(x);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
    

    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_REXW_r64_i8_AF (long long x) {

  long long sum_lsb = (x & 0x000000000000000F) + (0x02 & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  int AF_value = sum_lsb & 0x0000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = REXW_r64_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
     
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_REXW_r64_i8_PF(long long x) {
    unsigned char flags = REXW_r64_i8_return_flags(x);
    
    long long result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

  unsigned char REXW_r64_i8_return_OF(long long x) {
    unsigned char of;
    
     __asm__ volatile (
        "movq %1, %%rax;"     // Load x into RAX
	      "addq $0x02, %%rax;"   // rax += imm
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)           // Input operands
	: "%rax"              // clobbered registers
    );

    return of;
}
//check property for OF

bool test_REXW_r64_i8_OF (long long x) {
    long long sum = x + 0x02;
    unsigned char of = REXW_r64_i8_return_OF(x);
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


// ============================================================================
// ADD m64, i8 (sign-extended)
// ============================================================================

unsigned char REXW_memory64_imm8_return_CF(unsigned long long x) {
    unsigned char ah;
    unsigned long long val;

    __asm__ volatile (
        "movq %1, (%2);"        // Store x in memory location
        "addq $0x02, (%2);"     // REX.W + 83/0 ib: [memory] = [memory] + imm8 (sign-extended to 64-bit)
        "movq (%2), %%rax;"     // Load result from memory to RAX for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x), "r" (&val)   // Inputs: x, memory address
        : "%rax", "%ah"         // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_REXW_memory64_imm8_CF(unsigned long long x) {
    unsigned long long sum = x + 2;
    unsigned char flags = REXW_memory64_imm8_return_CF(x);

    if (sum < x) {  // Overflow occurred (wraparound)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No overflow
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char REXW_memory64_imm8_return_flags(long long x) {
    unsigned char ah;
    long long val;

    __asm__ volatile (
        "movq %1, (%2);"        // Store x in memory location
        "addq $0x02, (%2);"     // REX.W + 83/0 ib: [memory] = [memory] + imm8 (sign-extended to 64-bit)
        "movq (%2), %%rax;"     // Load result from memory to RAX for LAHF
        "lahf;"                 // Load flags into AH
        "movb %%ah, %0;"        // Move AH to output
        : "=r" (ah)             // Output
        : "r" (x), "r" (&val)   // Inputs: x, memory address
        : "%rax", "%ah"         // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_REXW_memory64_imm8_SF(long long x) {
    long long sum = x + 2;  
    unsigned char flags = REXW_memory64_imm8_return_flags(x);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_REXW_memory64_imm8_ZF(long long x) {
    long long sum = x + 2;  
    unsigned char flags = REXW_memory64_imm8_return_flags(x);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_REXW_memory64_imm8_AF(long long x) {
    long long x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int imm_lsb = 0x02 & 0x0F; // Get lower 4 bits of immediate (0x02)
    
    unsigned char flags = REXW_memory64_imm8_return_flags(x);

    if ((x_lsb + imm_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_REXW_memory64_imm8_PF(long long x) {
    unsigned char flags = REXW_memory64_imm8_return_flags(x);
    
    long long result = x + 0x02;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char REXW_memory64_imm8_return_OF(long long x) {
    unsigned char of;
    long long val;
    
    __asm__ volatile (
        "movq %1, (%2);"        // Store x in memory location
        "addq $0x02, (%2);"     // REX.W + 83/0 ib: [memory] = [memory] + imm8 (sign-extended to 64-bit)
        "seto %0;"              // Set 'of' to 1 if overflow occurred
        : "=r"(of)              // Output operand (OF flag)
        : "r"(x), "r" (&val)    // Input operands: x, memory address
        : "%rax"                // Clobbered register
    );

    return of;
}

// Check property for OF
bool test_REXW_memory64_imm8_OF(long long x) {
    long long sum = x + 2;
    unsigned char of = REXW_memory64_imm8_return_OF(x);
    
    if (((x >= 0) && (0x02 >= 0) && (sum < 0)) ||
        ((x < 0) && (0x02 < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

//**********************************************************
// ADD r8, r8 
unsigned char OP00_r8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // AL = x (destination register)
        "movb %2, %%bl;"       // BL = y (source register)
        "addb %%bl, %%al;"     // OP00: AL = AL + BL (ADD r/m8, r8 - register form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y
        : "%al", "%bl", "%ah"  // Clobbered registers (only AL, BL, AH)
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_OP00_r8_r8_CF (uint8_t  x, uint8_t  y) {
    uint8_t  sum = x + y;
    unsigned char flags = OP00_r8_r8_return_CF(x, y);

     if (sum < x) {  
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {       
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char OP00_r8_r8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"       // AL = x (destination register)
        "movb %2, %%bl;"       // BL = y (source register)  
        "addb %%bl, %%al;"     // OP00: AL = AL + BL (ADD r/m8, r8 - register form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y
        : "%al", "%bl", "%ah"  // Clobbered registers (only AL, BL, AH)
    );

    return ah;
}


//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1OP000 OP00OP00=0x80
bool test_OP00_r8_r8_SF (int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = OP00_r8_r8_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    }
    else {
        return ((flags & 0x80) == 0x00);
    }
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 01OP00 OP00OP00=0x40
bool test_OP00_r8_r8_ZF (int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = OP00_r8_r8_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    }
    else {
        return ((flags & 0x40) == 0x00);
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: OP0001 OP00OP00=0x10
bool test_OP00_r8_r8_AF (int8_t x, int8_t y) {
    // AF is set when there's a carry from bit 3 to bit 4
    int sum_lsb = (x & 0x0F) + (y & 0x0F);
    bool should_have_af = (sum_lsb > 0x0F);
    
    unsigned char flags = OP00_r8_r8_return_flags(x, y);

    if (should_have_af) {
        return ((flags & 0x10) == 0x10);
    }
    else {
        return ((flags & 0x10) == 0x00);
    }
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: OP00OP00 01OP00=0x04
bool test_OP00_r8_r8_PF(int8_t x, int8_t y) {
      unsigned char flags = OP00_r8_r8_return_flags(x, y);
    
    int8_t result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char OP00_r8_r8_return_OF(int8_t x, int8_t y) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%al;"       // AL = x (destination register)
        "movb %2, %%bl;"       // BL = y (source register)
        "addb %%bl, %%al;"     // OP00: AL = AL + BL (ADD r/m8, r8 - register form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "%al", "%bl"         // Clobbered registers (only AL, BL)
    );

    return of;
}

//check property for OF
bool test_OP00_r8_r8_OF (int8_t x, int8_t y) {
    int8_t sum = x + y;
    unsigned char of = OP00_r8_r8_return_OF(x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    }
    else { 
        return of == 0;
    }
}


// ============================================================================
// ADD m8, r8 (ADD r/m8, r8 - memory form)
// ============================================================================

unsigned char OP00_m8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, (%3);"       // Store x in memory location (destination)
        "movb %2, %%bl;"       // BL = y (source register)
        "addb %%bl, (%3);"     // OP00: [memory] = [memory] + BL (ADD r/m8, r8 - memory form)
        "movb (%3), %%al;"     // Load result from memory to AL for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%al", "%bl", "%ah"  // Clobbered registers (only AL, BL, AH)
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_OP00_m8_r8_CF(uint8_t x, uint8_t y) {
    uint16_t sum = (uint16_t)x + (uint16_t)y;
    unsigned char flags = OP00_m8_r8_return_CF(x, y);

    if (sum > 255) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {          // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char OP00_m8_r8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    int8_t val;

    __asm__ volatile (
        "movb %1, (%3);"       // Store x in memory location (destination)
        "movb %2, %%bl;"       // BL = y (source register)
        "addb %%bl, (%3);"     // OP00: [memory] = [memory] + BL (ADD r/m8, r8 - memory form)
        "movb (%3), %%al;"     // Load result from memory to AL for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%al", "%bl", "%ah"  // Clobbered registers (only AL, BL, AH)
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1OP000 OP00OP00=0x80
bool test_OP00_m8_r8_SF(int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = OP00_m8_r8_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 01OP00 OP00OP00=0x40
bool test_OP00_m8_r8_ZF(int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = OP00_m8_r8_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: OP0001 OP00OP00=0x10
bool test_OP00_m8_r8_AF(int8_t x, int8_t y) {
    int8_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int8_t y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = OP00_m8_r8_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: OP00OP00 01OP00=0x04
bool test_OP00_m8_r8_PF(int8_t x, int8_t y) {
    unsigned char flags = OP00_m8_r8_return_flags(x, y);
    
    int8_t result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char OP00_m8_r8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movb %1, (%3);"       // Store x in memory location (destination)
        "movb %2, %%bl;"       // BL = y (source register)
        "addb %%bl, (%3);"     // OP00: [memory] = [memory] + BL (ADD r/m8, r8 - memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%bl"                // Clobbered registers (only BL)
    );

    return of;
}

// Check property for OF
bool test_OP00_m8_r8_OF(int8_t x, int8_t y) {
    int8_t sum = x + y;
    unsigned char of = OP00_m8_r8_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}



//  ADD REX_r8, REX_r8
// ============================================================================

unsigned char add_REX_r8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r8b;"      // R8B = x (destination extended register)
        "movb %2, %%r9b;"      // R9B = y (source extended register)
        "addb %%r9b, %%r8b;"   // REX + 00/r: R8B = R8B + R9B (extended register form)
        "movb %%r8b, %%al;"    // Move result to AL for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y
        : "%r8", "%r9", "%al", "%ah"  // Clobbered extended registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_add_REX_r8_r8_CF (uint8_t  x, uint8_t  y) {
    uint8_t  sum = x + y;
    unsigned char flags = add_REX_r8_r8_return_CF(x, y);

     if (sum < x) {  
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {       
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_REX_r8_r8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%r10b;"     // R10B = x (destination extended register)
        "movb %2, %%r11b;"     // R11B = y (source extended register)  
        "addb %%r11b, %%r10b;" // REX + 00/r: R10B = R10B + R11B (extended register form)
        "movb %%r10b, %%al;"   // Move result to AL for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y
        : "%r10", "%r11", "%al", "%ah"  // Clobbered extended registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_REX_r8_r8_SF (int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = add_REX_r8_r8_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    }
    else {
        return ((flags & 0x80) == 0x00);
    }
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_REX_r8_r8_ZF (int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = add_REX_r8_r8_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    }
    else {
        return ((flags & 0x40) == 0x00);
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_REX_r8_r8_AF (int8_t x, int8_t y) {
    // AF is set when there's a carry from bit 3 to bit 4
    int sum_lsb = (x & 0x0F) + (y & 0x0F);
    bool should_have_af = (sum_lsb > 0x0F);
    
    unsigned char flags = add_REX_r8_r8_return_flags(x, y);

    if (should_have_af) {
        return ((flags & 0x10) == 0x10);
    }
    else {
        return ((flags & 0x10) == 0x00);
    }
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_REX_r8_r8_PF(int8_t x, int8_t y) {
      unsigned char flags = add_REX_r8_r8_return_flags(x, y);
    
    int8_t result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_REX_r8_r8_return_OF(int8_t x, int8_t y) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%r12b;"     // R12B = x (destination extended register)
        "movb %2, %%r13b;"     // R13B = y (source extended register)
        "addb %%r13b, %%r12b;" // REX + 00/r: R12B = R12B + R13B (extended register form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "%r12", "%r13"       // Clobbered extended registers
    );

    return of;
}

//check property for OF
bool test_add_REX_r8_r8_OF (int8_t x, int8_t y) {
    int8_t sum = x + y;
    unsigned char of = add_REX_r8_r8_return_OF(x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    }
    else { 
        return of == 0;
    }
}


// ============================================================================
// ADD REX_m8, REX_r8
// ============================================================================

unsigned char add_REX_m8_r8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movq %3, %%r8;"       // Load memory address into R8 (extended register)
        "movb %1, (%%r8);"     // Store x in memory using R8 addressing (destination)
        "movb %2, %%r9b;"      // R9B = y (source extended register)
        "addb %%r9b, (%%r8);"  // REX + 00/r: [R8] = [R8] + R9B (extended memory form)
        "movb (%%r8), %%al;"   // Load result from memory to AL for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%r8", "%r9", "%al", "%ah"  // Clobbered extended registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_REX_m8_r8_CF(uint8_t x, uint8_t y) {
    uint16_t sum = (uint16_t)x + (uint16_t)y;
    unsigned char flags = add_REX_m8_r8_return_CF(x, y);

    if (sum > 255) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {          // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_REX_m8_r8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    int8_t val;

    __asm__ volatile (
        "movq %3, %%r10;"      // Load memory address into R10 (extended register)
        "movb %1, (%%r10);"    // Store x in memory using R10 addressing (destination)
        "movb %2, %%r11b;"     // R11B = y (source extended register)
        "addb %%r11b, (%%r10);" // REX + 00/r: [R10] = [R10] + R11B (extended memory form)
        "movb (%%r10), %%al;"  // Load result from memory to AL for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%r10", "%r11", "%al", "%ah"  // Clobbered extended registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_REX_m8_r8_SF(int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = add_REX_m8_r8_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_REX_m8_r8_ZF(int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = add_REX_m8_r8_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_REX_m8_r8_AF(int8_t x, int8_t y) {
    int8_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int8_t y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_REX_m8_r8_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_REX_m8_r8_PF(int8_t x, int8_t y) {
    unsigned char flags = add_REX_m8_r8_return_flags(x, y);
    
    int8_t result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_REX_m8_r8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movq %3, %%r12;"      // Load memory address into R12 (extended register)
        "movb %1, (%%r12);"    // Store x in memory using R12 addressing (destination)
        "movb %2, %%r13b;"     // R13B = y (source extended register)
        "addb %%r13b, (%%r12);" // REX + 00/r: [R12] = [R12] + R13B (extended memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%r12", "%r13"       // Clobbered extended registers
    );

    return of;
}

// Check property for OF
bool test_add_REX_m8_r8_OF(int8_t x, int8_t y) {
    int8_t sum = x + y;
    unsigned char of = add_REX_m8_r8_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


// ============================================================================
// ADD r16, r16 (16-bit register to register)
// ============================================================================

unsigned char add_OP01_r16_r16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // AX = x (destination register)
        "movw %2, %%bx;"       // BX = y (source register)
        "addw %%bx, %%ax;"     // OP01: AX = AX + BX (ADD r/m16, r16 - register form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y
        : "%ax", "%bx", "%ah"  // Clobbered registers (only AX, BX, AH)
    );

    return ah;
}



//check property for CF
//CF is bit 0 in ah

bool test_add_OP01_r16_r16_CF (uint16_t  x, uint16_t  y) {
    uint16_t  sum = x + y;
    unsigned char flags = add_OP01_r16_r16_return_CF(x, y);
   if (sum < x) {  
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {       
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_OP01_r16_r16_return_flags(int16_t x, int16_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // AX = x (destination register)
        "movw %2, %%bx;"       // BX = y (source register)  
        "addw %%bx, %%ax;"     // OP01: AX = AX + BX (ADD r/m16, r16 - register form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y
        : "%ax", "%bx", "%ah"  // Clobbered registers (only AX, BX, AH)
    );

    return ah;
}


//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_OP01_r16_r16_SF (int16_t x, int16_t y) {
  
  int16_t sum = x+y;  
    unsigned char flags = add_OP01_r16_r16_return_flags(x, y);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	} return false; 
   
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: OP0100 0000=0x40

bool test_add_OP01_r16_r16_ZF (int16_t x, int16_t y) {
  
  int16_t sum = x+y;  
    unsigned char flags = add_OP01_r16_r16_return_flags(x, y);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	} 
 return false; 
    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 00OP01 0000=0x10

bool test_add_OP01_r16_r16_AF (int16_t x, int16_t y) {

  int16_t sum_lsb = (x & 0x000F) + (y & 0x000F); // Only add least 4 bits, zero out all other bits
  int16_t AF_value = sum_lsb & 0x010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_OP01_r16_r16_return_flags(x, y);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	} 
 
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 OP0100=0x04

    bool test_add_OP01_r16_r16_PF(int16_t x, int16_t y) {
    unsigned char flags = add_OP01_r16_r16_return_flags(x, y);
    
    int16_t result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_OP01_r16_r16_return_OF(int16_t x, int16_t y) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"       // AX = x (destination register)
        "movw %2, %%bx;"       // BX = y (source register)
        "addw %%bx, %%ax;"     // OP01: AX = AX + BX (ADD r/m16, r16 - register form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "%ax", "%bx"         // Clobbered registers (only AX, BX)
    );

    return of;
}
//check property for OF

bool test_add_OP01_r16_r16_OF (int16_t x, int16_t y) {
    int16_t sum = x + y;
    unsigned char of = add_OP01_r16_r16_return_OF (x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
      
}


// ============================================================================
// ADD m16, r16 (ADD r/m16, r16 - memory form)
// ============================================================================

unsigned char add_OP01_m16_r16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, (%3);"       // Store x in memory location (destination)
        "movw %2, %%bx;"       // BX = y (source register)
        "addw %%bx, (%3);"     // OP01: [memory] = [memory] + BX (ADD r/m16, r16 - memory form)
        "movw (%3), %%ax;"     // Load result from memory to AX for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%ax", "%bx", "%ah"  // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_OP01_m16_r16_CF(uint16_t x, uint16_t y) {
    uint32_t sum = (uint32_t)x + (uint32_t)y;
    unsigned char flags = add_OP01_m16_r16_return_CF(x, y);

    if (sum > 65535) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {            // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_OP01_m16_r16_return_flags(int16_t x, int16_t y) {
    unsigned char ah;
    int16_t val;

    __asm__ volatile (
        "movw %1, (%3);"       // Store x in memory location (destination)
        "movw %2, %%bx;"       // BX = y (source register)
        "addw %%bx, (%3);"     // OP01: [memory] = [memory] + BX (ADD r/m16, r16 - memory form)
        "movw (%3), %%ax;"     // Load result from memory to AX for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%ax", "%bx", "%ah"  // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_OP01_m16_r16_SF(int16_t x, int16_t y) {
    int16_t sum = x + y;  
    unsigned char flags = add_OP01_m16_r16_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: OP0100 0000=0x40
bool test_add_OP01_m16_r16_ZF(int16_t x, int16_t y) {
    int16_t sum = x + y;  
    unsigned char flags = add_OP01_m16_r16_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 00OP01 0000=0x10
bool test_add_OP01_m16_r16_AF(int16_t x, int16_t y) {
    int16_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int16_t y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_OP01_m16_r16_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 OP0100=0x04
bool test_add_OP01_m16_r16_PF(int16_t x, int16_t y) {
    unsigned char flags = add_OP01_m16_r16_return_flags(x, y);
    
    int16_t result = x + y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_OP01_m16_r16_return_OF(int16_t x, int16_t y) {
    unsigned char of;
    int16_t val;
    
    __asm__ volatile (
        "movw %1, (%3);"       // Store x in memory location (destination)
        "movw %2, %%bx;"       // DX = y (source register)
        "addw %%bx, (%3);"     // OP01: [memory] = [memory] + DX (ADD r/m16, r16 - memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%bx"                // Clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_OP01_m16_r16_OF(int16_t x, int16_t y) {
    int16_t sum = x + y;
    unsigned char of = add_OP01_m16_r16_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


// ============================================================================
// ADD r32, r32 
// ============================================================================

unsigned char add_OP01_r32_r32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // EAX = x (destination register)
        "movl %2, %%ebx;"      // EBX = y (source register)
        "addl %%ebx, %%eax;"   // OP01: EAX = EAX + EBX (ADD r/m32, r32 - register form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y
        : "%eax", "%ebx", "%ah"  // Clobbered registers (only EAX, EBX, AH)
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_add_OP01_r32_r32_CF (uint32_t  x, uint32_t  y) {
    uint32_t  sum = x + y;
    unsigned char flags = add_OP01_r32_r32_return_CF(x, y);

     if (sum < x) {  
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {       
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
      
}

unsigned char add_OP01_r32_r32_return_flags(int32_t x, int32_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // EAX = x (destination register)
        "movl %2, %%ebx;"      // EBX = y (source register)  
        "addl %%ebx, %%eax;"   // OP01: EAX = EAX + EBX (ADD r/m32, r32 - register form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y
        : "%eax", "%ebx", "%ah"  // Clobbered registers (only EAX, EBX, AH)
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_OP01_r32_r32_SF (int32_t x, int32_t y) {
  
  int32_t sum = x+y;  
    unsigned char flags = add_OP01_r32_r32_return_flags(x, y);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: OP0100 0000=0x40

bool test_add_OP01_r32_r32_ZF (int32_t x, int32_t y) {
  
  int32_t sum = x+y;  
    unsigned char flags = add_OP01_r32_r32_return_flags(x, y);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 00OP01 0000=0x10

bool test_add_OP01_r32_r32_AF (int32_t x, int32_t y) {

  int32_t sum_lsb = (x & 0x0000000F) + (y & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x0000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_OP01_r32_r32_return_flags(x, y);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
      
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 OP0100=0x04

bool test_add_OP01_r32_r32_PF(int32_t x, int32_t y) {
    unsigned char flags = add_OP01_r32_r32_return_flags(x, y);
    
    int32_t result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_OP01_r32_r32_return_OF(int32_t x, int32_t y) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"      // EAX = x (destination register)
        "movl %2, %%ebx;"      // EBX = y (source register)
        "addl %%ebx, %%eax;"   // OP01: EAX = EAX + EBX (ADD r/m32, r32 - register form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y
        : "%eax", "%ebx"       // Clobbered registers (only EAX, EBX)
    );

    return of;
}

//check property for OF

bool test_add_OP01_r32_r32_OF (int32_t x, int32_t y) {
    int32_t sum = x + y;
    unsigned char of = add_OP01_r32_r32_return_OF (x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
     
    
}


// ============================================================================
// ADD m32, r32 (ADD r/m32, r32 - memory form)
// ============================================================================

unsigned char add_OP01_m32_r32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, (%3);"       // Store x in memory location (destination)
        "movl %2, %%ebx;"      // EBX = y (source register)
        "addl %%ebx, (%3);"    // OP01: [memory] = [memory] + EBX (ADD r/m32, r32 - memory form)
        "movl (%3), %%eax;"    // Load result from memory to EAX for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%eax", "%ebx", "%ah"  // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_OP01_m32_r32_CF(uint32_t x, uint32_t y) {
    uint64_t sum = (uint64_t)x + (uint64_t)y;
    unsigned char flags = add_OP01_m32_r32_return_CF(x, y);

    if (sum > 4294967295UL) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {                   // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_OP01_m32_r32_return_flags(int32_t x, int32_t y) {
    unsigned char ah;
    int32_t val;

    __asm__ volatile (
        "movl %1, (%3);"       // Store x in memory location (destination)
        "movl %2, %%ebx;"      // EBX = y (source register)
        "addl %%ebx, (%3);"    // OP01: [memory] = [memory] + EBX (ADD r/m32, r32 - memory form)
        "movl (%3), %%eax;"    // Load result from memory to EAX for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%eax", "%ebx", "%ah"  // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_OP01_m32_r32_SF(int32_t x, int32_t y) {
    int32_t sum = x + y;  
    unsigned char flags = add_OP01_m32_r32_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: OP0100 0000=0x40
bool test_add_OP01_m32_r32_ZF(int32_t x, int32_t y) {
    int32_t sum = x + y;  
    unsigned char flags = add_OP01_m32_r32_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 00OP01 0000=0x10
bool test_add_OP01_m32_r32_AF(int32_t x, int32_t y) {
    int32_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int32_t y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_OP01_m32_r32_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 OP0100=0x04
bool test_add_OP01_m32_r32_PF(int32_t x, int32_t y) {
    unsigned char flags = add_OP01_m32_r32_return_flags(x, y);
    
    int32_t result = x + y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_OP01_m32_r32_return_OF(int32_t x, int32_t y) {
    unsigned char of;
    int32_t val;
    
    __asm__ volatile (
        "movl %1, (%3);"       // Store x in memory location (destination)
        "movl %2, %%ebx;"      // EBX = y (source register)
        "addl %%ebx, (%3);"    // OP01: [memory] = [memory] + EBX (ADD r/m32, r32 - memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%ebx"               // Clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_OP01_m32_r32_OF(int32_t x, int32_t y) {
    int32_t sum = x + y;
    unsigned char of = add_OP01_m32_r32_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


//**********************************************************
// ADD r64, r64


unsigned char add_OP01_r64_r64_return_CF (unsigned long long x,  unsigned long long y) {
    unsigned char ah;

      __asm__ volatile (
        "movq %1, %%rax;"      // RAX = x (destination 64-bit register)
        "movq %2, %%rbx;"      // RBX = y (source 64-bit register)
        "addq %%rbx, %%rax;"   // REX.W + OP01/r: RAX = RAX + RBX (ADD r/m64, r64 - register form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y (64-bit values)
        : "%rax", "%rbx", "%ah"  // Clobbered 64-bit registers (only RAX, RBX, AH)
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_add_OP01_r64_r64_CF (unsigned long long x,  unsigned long long y) {
    unsigned long long sum = x + y;
    unsigned char flags = add_OP01_r64_r64_return_CF(x, y);
    if (sum < x) {  
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {       
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_OP01_r64_r64_return_flags (long long x, long long y) {
    unsigned char ah;
__asm__ volatile (
        "movq %1, %%rax;"      // RAX = x (destination 64-bit register)
        "movq %2, %%rbx;"      // RBX = y (source 64-bit register)  
        "addq %%rbx, %%rax;"   // REX.W + OP01/r: RAX = RAX + RBX (ADD r/m64, r64 - register form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y)     // Inputs: x, y (64-bit values)
        : "%rax", "%rbx", "%ah"  // Clobbered 64-bit registers (only RAX, RBX, AH)
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_OP01_r64_r64_SF (long long x, long long y) {
  
  long long sum = x+y;  
    unsigned char flags = add_OP01_r64_r64_return_flags(x, y);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
       
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: OP0100 0000=0x40

bool test_add_OP01_r64_r64_ZF (long long x, long long y) {
  
  long long sum = x+y;  
    unsigned char flags = add_OP01_r64_r64_return_flags(x, y);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
     
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 00OP01 0000=0x10

bool test_add_OP01_r64_r64_AF (long long x, long long y) {

  long long sum_lsb = (x & 0x000000000000000F) + (y & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  int AF_value = sum_lsb & 0x000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_OP01_r64_r64_return_flags(x, y);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 OP0100=0x04
  
   bool test_add_OP01_r64_r64_PF(long long x, long long y) {
    unsigned char flags = add_OP01_r64_r64_return_flags(x, y);
    
    long long result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_OP01_r64_r64_return_OF (long long x, long long y) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"      // RAX = x (destination 64-bit register)
        "movq %2, %%rbx;"      // RBX = y (source 64-bit register)
        "addq %%rbx, %%rax;"   // REX.W + OP01/r: RAX = RAX + RBX (ADD r/m64, r64 - register form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y)       // Input operands: x, y (64-bit values)
        : "%rax", "%rbx"       // Clobbered 64-bit registers (only RAX, RBX)
    );

    return of;
}

//check property for OF

bool test_add_OP01_r64_r64_OF (long long x, long long y) {
    long long sum = x + y;
    unsigned char of = add_OP01_r64_r64_return_OF (x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
}



// ============================================================================
// ADD m64, r64 (ADD r/m64, r64 - memory form)
// ============================================================================

unsigned char add_OP01_m64_r64_return_CF(unsigned long long x, unsigned long long y) {
    unsigned char ah;
    unsigned long long val;

    __asm__ volatile (
        "movq %1, (%3);"       // Store x in memory location (destination)
        "movq %2, %%rbx;"      // RBX = y (source register)
        "addq %%rbx, (%3);"    // REX.W + OP01/r: [memory] = [memory] + RBX (ADD r/m64, r64 - memory form)
        "movq (%3), %%rax;"    // Load result from memory to RAX for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%rax", "%rbx", "%ah"  // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_OP01_m64_r64_CF(unsigned long long x, unsigned long long y) {
    unsigned long long sum = x + y;
    unsigned char flags = add_OP01_m64_r64_return_CF(x, y);

    if (sum < x) {  // Carry occurred (overflow in unsigned addition)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_OP01_m64_r64_return_flags(long long x, long long y) {
    unsigned char ah;
    long long val;

    __asm__ volatile (
        "movq %1, (%3);"       // Store x in memory location (destination)
        "movq %2, %%rbx;"      // RBX = y (source register)
        "addq %%rbx, (%3);"    // REX.W + OP01/r: [memory] = [memory] + RBX (ADD r/m64, r64 - memory form)
        "movq (%3), %%rax;"    // Load result from memory to RAX for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%rax", "%rbx", "%ah"  // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_OP01_m64_r64_SF(long long x, long long y) {
    long long sum = x + y;  
    unsigned char flags = add_OP01_m64_r64_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: OP0100 0000=0x40
bool test_add_OP01_m64_r64_ZF(long long x, long long y) {
    long long sum = x + y;  
    unsigned char flags = add_OP01_m64_r64_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 00OP01 0000=0x10
bool test_add_OP01_m64_r64_AF(long long x, long long y) {
    long long x_lsb = x & 0x0F;     // Get lower 4 bits of x
    long long y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_OP01_m64_r64_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 OP0100=0x04
bool test_add_OP01_m64_r64_PF(long long x, long long y) {
    unsigned char flags = add_OP01_m64_r64_return_flags(x, y);
    
    long long result = x + y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_OP01_m64_r64_return_OF(long long x, long long y) {
    unsigned char of;
    long long val;
    
    __asm__ volatile (
        "movq %1, (%3);"       // Store x in memory location (destination)
        "movq %2, %%rbx;"      // RBX = y (source register)
        "addq %%rbx, (%3);"    // REX.W + OP01/r: [memory] = [memory] + RBX (ADD r/m64, r64 - memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%rbx"               // Clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_OP01_m64_r64_OF(long long x, long long y) {
    long long sum = x + y;
    unsigned char of = add_OP01_m64_r64_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}


// ============================================================================
// ADD r8, m8 
// ============================================================================

unsigned char add_OP02_r8_m8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movb %1, %%al;"       // AL = x (destination register)
        "movb %2, (%3);"       // Store y in memory location (source)
        "addb (%3), %%al;"     // OP02: AL = AL + [memory] (ADD r8, r/m8 - memory form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%al", "%ah"         // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_OP02_r8_m8_CF(uint8_t x, uint8_t y) {
    uint16_t sum = (uint16_t)x + (uint16_t)y;
    unsigned char flags = add_OP02_r8_m8_return_CF(x, y);

    if (sum > 255) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {          // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_OP02_r8_m8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    int8_t val;

    __asm__ volatile (
        "movb %1, %%al;"       // AL = x (destination register)
        "movb %2, (%3);"       // Store y in memory location (source)
        "addb (%3), %%al;"     // OP02: AL = AL + [memory] (ADD r8, r/m8 - memory form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%al", "%ah"         // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_OP02_r8_m8_SF(int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = add_OP02_r8_m8_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_OP02_r8_m8_ZF(int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = add_OP02_r8_m8_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_OP02_r8_m8_AF(int8_t x, int8_t y) {
    int8_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int8_t y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_OP02_r8_m8_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_OP02_r8_m8_PF(int8_t x, int8_t y) {
    unsigned char flags = add_OP02_r8_m8_return_flags(x, y);
    
    int8_t result = x + y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Check all 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_OP02_r8_m8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movb %1, %%al;"       // AL = x (destination register)
        "movb %2, (%3);"       // Store y in memory location (source)
        "addb (%3), %%al;"     // OP02: AL = AL + [memory] (ADD r8, r/m8 - memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%al"                // Clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_OP02_r8_m8_OF(int8_t x, int8_t y) {
    int8_t sum = x + y;
    unsigned char of = add_OP02_r8_m8_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}




// ============================================================================
// ADD REX_r8, REX_m8
// ============================================================================

unsigned char add_REX02_r8_m8_return_CF(uint8_t x, uint8_t y) {
    unsigned char ah;
    uint8_t val;

    __asm__ volatile (
        "movq %3, %%r8;"       // Load memory address into R8 (extended register for addressing)
        "movb %1, %%r9b;"      // R9B = x (destination extended register)
        "movb %2, (%%r8);"     // Store y in memory using R8 addressing (source)
        "addb (%%r8), %%r9b;"  // REX + 02/r: R9B = R9B + [R8] (ADD r8, r/m8 - extended memory form)
        "movb %%r9b, %%al;"    // Move result to AL for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%r8", "%r9", "%al", "%ah"  // Clobbered extended registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_REX02_r8_m8_CF(uint8_t x, uint8_t y) {
    uint16_t sum = (uint16_t)x + (uint16_t)y;
    unsigned char flags = add_REX02_r8_m8_return_CF(x, y);

    if (sum > 255) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {          // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_REX02_r8_m8_return_flags(int8_t x, int8_t y) {
    unsigned char ah;
    int8_t val;

    __asm__ volatile (
        "movq %3, %%r10;"      // Load memory address into R10 (extended register for addressing)
        "movb %1, %%r11b;"     // R11B = x (destination extended register)
        "movb %2, (%%r10);"    // Store y in memory using R10 addressing (source)
        "addb (%%r10), %%r11b;" // REX + 02/r: R11B = R11B + [R10] (ADD r8, r/m8 - extended memory form)
        "movb %%r11b, %%al;"   // Move result to AL for LAHF
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%r10", "%r11", "%al", "%ah"  // Clobbered extended registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_REX02_r8_m8_SF(int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = add_REX02_r8_m8_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_REX02_r8_m8_ZF(int8_t x, int8_t y) {
    int8_t sum = x + y;  
    unsigned char flags = add_REX02_r8_m8_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_REX02_r8_m8_AF(int8_t x, int8_t y) {
    int8_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int8_t y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_REX02_r8_m8_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_REX02_r8_m8_PF(int8_t x, int8_t y) {
    unsigned char flags = add_REX02_r8_m8_return_flags(x, y);
    
    int8_t result = x + y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Check all 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_REX02_r8_m8_return_OF(int8_t x, int8_t y) {
    unsigned char of;
    int8_t val;
    
    __asm__ volatile (
        "movq %3, %%r12;"      // Load memory address into R12 (extended register for addressing)
        "movb %1, %%r13b;"     // R13B = x (destination extended register)
        "movb %2, (%%r12);"    // Store y in memory using R12 addressing (source)
        "addb (%%r12), %%r13b;" // REX + 02/r: R13B = R13B + [R12] (ADD r8, r/m8 - extended memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%r12", "%r13"       // Clobbered extended registers
    );

    return of;
}

// Check property for OF
bool test_add_REX02_r8_m8_OF(int8_t x, int8_t y) {
    int8_t sum = x + y;
    unsigned char of = add_REX02_r8_m8_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}




// ============================================================================
// ADD r16, m16 
// ============================================================================

unsigned char add_OP03_r16_m16_return_CF(uint16_t x, uint16_t y) {
    unsigned char ah;
    uint16_t val;

    __asm__ volatile (
        "movw %1, %%ax;"       // AX = x (destination register)
        "movw %2, (%3);"       // Store y in memory location (source)
        "addw (%3), %%ax;"     // OP03: AX = AX + [memory] (ADD r16, r/m16 - memory form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%ax", "%ah"         // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_OP03_r16_m16_CF(uint16_t x, uint16_t y) {
    uint32_t sum = (uint32_t)x + (uint32_t)y;
    unsigned char flags = add_OP03_r16_m16_return_CF(x, y);

    if (sum > 65535) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {            // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_OP03_r16_m16_return_flags(int16_t x, int16_t y) {
    unsigned char ah;
    int16_t val;

    __asm__ volatile (
        "movw %1, %%ax;"       // AX = x (destination register)
        "movw %2, (%3);"       // Store y in memory location (source)
        "addw (%3), %%ax;"     // OP03: AX = AX + [memory] (ADD r16, r/m16 - memory form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%ax", "%ah"         // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_OP03_r16_m16_SF(int16_t x, int16_t y) {
    int16_t sum = x + y;  
    unsigned char flags = add_OP03_r16_m16_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_OP03_r16_m16_ZF(int16_t x, int16_t y) {
    int16_t sum = x + y;  
    unsigned char flags = add_OP03_r16_m16_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_OP03_r16_m16_AF(int16_t x, int16_t y) {
    int16_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int16_t y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_OP03_r16_m16_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_OP03_r16_m16_PF(int16_t x, int16_t y) {
    unsigned char flags = add_OP03_r16_m16_return_flags(x, y);
    
    int16_t result = x + y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_OP03_r16_m16_return_OF(int16_t x, int16_t y) {
    unsigned char of;
    int16_t val;
    
    __asm__ volatile (
        "movw %1, %%ax;"       // AX = x (destination register)
        "movw %2, (%3);"       // Store y in memory location (source)
        "addw (%3), %%ax;"     // OP03: AX = AX + [memory] (ADD r16, r/m16 - memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%ax"                // Clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_OP03_r16_m16_OF(int16_t x, int16_t y) {
    int16_t sum = x + y;
    unsigned char of = add_OP03_r16_m16_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}
// ============================================================================
// ADD r32, r32 
// ============================================================================

unsigned char add_OP03_r32_r32_return_CF (uint32_t x, uint32_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x
        "movl %2, %%ebx;"      // ebx = y
        "addl %%ebx, %%eax;"   // eax += ebx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs
        : "%eax", "%ebx", "%ah"// clobbered registers
    );

    return ah;
}


//check property for CF
//CF is bit 0 in ah

bool test_add_OP03_r32_r32_CF (uint32_t  x, uint32_t  y) {
    uint32_t  sum = x + y;
    unsigned char flags = add_OP03_r32_r32_return_CF(x, y);

     if (sum < x) {  
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {       
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
      
}


unsigned char add_OP03_r32_r32_return_flags (int32_t x, int32_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x
        "movl %2, %%ebx;"      // ebx = y
        "addl %%ebx, %%eax;"   // eax += ebx
        "lahf;"                // load flags into AH
        "movb %%ah, %0;"       // move AH to output variable
        : "=r" (ah)            // output
        : "r" (x), "r" (y)     // inputs
        : "%eax", "%ebx", "%ah"// clobbered registers
    );

    return ah;
}

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_OP03_r32_r32_SF (int32_t x, int32_t y) {
  
  int32_t sum = x+y;  
    unsigned char flags = add_OP03_r32_r32_return_flags(x, y);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
    
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_OP03_r32_r32_ZF (int32_t x, int32_t y) {
  
  int32_t sum = x+y;  
    unsigned char flags = add_OP03_r32_r32_return_flags(x, y);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
    
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_OP03_r32_r32_AF (int32_t x, int32_t y) {

  int32_t sum_lsb = (x & 0x0000000F) + (y & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x00000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_OP03_r32_r32_return_flags(x, y);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
      
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add_OP03_r32_r32_PF(int32_t x, int32_t y) {
    unsigned char flags = add_OP03_r32_r32_return_flags(x, y);
    
    int32_t result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_OP03_r32_r32_return_OF (int32_t x, int32_t y) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"     // Load x into EAX
	"movl %2, %%ebx;"      // ebx = y
	"addl %%ebx, %%eax;"   // eax += ebx
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x), "r"(y)      // Input operands
	: "%eax", "%ebx"      // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_OP03_r32_r32_OF (int32_t x, int32_t y) {
    int32_t sum = x + y;
    unsigned char of = add_OP03_r32_r32_return_OF (x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
     
    
}


// ============================================================================
// ADD r32, m32
// ============================================================================

unsigned char add_OP03_r32_m32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;
    uint32_t val;

    __asm__ volatile (
        "movl %1, %%eax;"      // EAX = x (destination register)
        "movl %2, (%3);"       // Store y in memory location (source)
        "addl (%3), %%eax;"    // OP03: EAX = EAX + [memory] (ADD r32, r/m32 - memory form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%eax", "%ah"        // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_OP03_r32_m32_CF(uint32_t x, uint32_t y) {
    uint64_t sum = (uint64_t)x + (uint64_t)y;
    unsigned char flags = add_OP03_r32_m32_return_CF(x, y);

    if (sum > 4294967295UL) {  // Carry occurred
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {                   // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_OP03_r32_m32_return_flags(int32_t x, int32_t y) {
    unsigned char ah;
    int32_t val;

    __asm__ volatile (
        "movl %1, %%eax;"      // EAX = x (destination register)
        "movl %2, (%3);"       // Store y in memory location (source)
        "addl (%3), %%eax;"    // OP03: EAX = EAX + [memory] (ADD r32, r/m32 - memory form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%eax", "%ah"        // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_OP03_r32_m32_SF(int32_t x, int32_t y) {
    int32_t sum = x + y;  
    unsigned char flags = add_OP03_r32_m32_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_OP03_r32_m32_ZF(int32_t x, int32_t y) {
    int32_t sum = x + y;  
    unsigned char flags = add_OP03_r32_m32_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_OP03_r32_m32_AF(int32_t x, int32_t y) {
    int32_t x_lsb = x & 0x0F;     // Get lower 4 bits of x
    int32_t y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_OP03_r32_m32_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_OP03_r32_m32_PF(int32_t x, int32_t y) {
    unsigned char flags = add_OP03_r32_m32_return_flags(x, y);
    
    int32_t result = x + y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_OP03_r32_m32_return_OF(int32_t x, int32_t y) {
    unsigned char of;
    int32_t val;
    
    __asm__ volatile (
        "movl %1, %%eax;"      // EAX = x (destination register)
        "movl %2, (%3);"       // Store y in memory location (source)
        "addl (%3), %%eax;"    // OP03: EAX = EAX + [memory] (ADD r32, r/m32 - memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%eax"               // Clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_OP03_r32_m32_OF(int32_t x, int32_t y) {
    int32_t sum = x + y;
    unsigned char of = add_OP03_r32_m32_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

// ============================================================================
// ADD r64, r64
// ===========================================================================

unsigned char add_REXW03__r64_r64_return_CF (unsigned long long  x , unsigned long long y) {
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


//check property for CF
//CF is bit 0 in ah

bool test_add_REXW03__r64_r64_CF (unsigned long long x, unsigned long long y) {
    unsigned long long sum = x + y;
    unsigned char flags = add_REXW03__r64_r64_return_CF(x, y);
    if (sum < x) {  
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {       
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}


unsigned char add_REXW03__r64_r64_return_flags (long long x, long long y) {
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

//check property for SF
//SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80

bool test_add_REXW03__r64_r64_SF (long long x, long long y) {
  
  long long sum = x+y;  
    unsigned char flags = add_REXW03__r64_r64_return_flags(x, y);

    if (sum<0) {
      return ((flags & 0x80)==0x80);
      }
    else {
      return ((flags & 0x80)==0x00);
	}
       
}

//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40

bool test_add_REXW03__r64_r64_ZF (long long x, long long y) {
  
  long long sum = x+y;  
    unsigned char flags = add_REXW03__r64_r64_return_flags(x, y);

    if (sum==0) {
      return ((flags & 0x40)==0x40);
      }
    else {
      return ((flags & 0x40)==0x00);
	}
     
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_add_REXW03__r64_r64_AF (long long x, long long y) {

  long long  sum_lsb = (x & 0x000000000000000F) + (y & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  int AF_value = sum_lsb & 0x0000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_REXW03__r64_r64_return_flags(x, y);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
  
   bool test_add_REXW03__r64_r64_PF(long long x, long long y) {
    unsigned char flags = add_REXW03__r64_r64_return_flags(x, y);
    
    long long result = x + y;
    uint8_t expected_parity = calculate_parity(result);
    
    return (flags & 0x04) == expected_parity;
}


unsigned char add_REXW03__r64_r64_return_OF (long long x, long long y) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"     // Load x into RAX
	"movq %2, %%rbx;"      // rbx = y
	"addq %%rbx, %%rax;"   // rax += rbx
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x), "r"(y)      // Input operands
	: "%rax", "%rbx"      // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_REXW03__r64_r64_OF (long long x, long long y) {
    long long sum = x + y;
    unsigned char of = add_REXW03__r64_r64_return_OF (x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
}



// ============================================================================
// ADD r64, m64 
// ============================================================================

unsigned char add_REXW03__r64_m64_return_CF (unsigned long long x, unsigned long long y) {
    unsigned char ah;
    unsigned long long val;

    __asm__ volatile (
        "movq %1, %%rax;"      // RAX = x (destination register)
        "movq %2, (%3);"       // Store y in memory location (source)
        "addq (%3), %%rax;"    // REX.W + 03/r: RAX = RAX + [memory] (ADD r64, r/m64 - memory form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%rax", "%ah"        // Clobbered registers
    );

    return ah;
}

// Check property for CF
// CF is bit 0 in ah
bool test_add_REXW03__r64_m64_CF(unsigned long long x, unsigned long long y) {
    unsigned long long  sum = x + y;
    unsigned char flags = add_REXW03__r64_m64_return_CF(x, y);

    if (sum < x) {  // Carry occurred (overflow in unsigned addition)
        return ((flags & 0x01) == 0x01);  // Expect CF = 1
    } else {        // No carry
        return ((flags & 0x01) == 0x00);  // Expect CF = 0
    }
}

unsigned char add_REXW03__r64_m64_return_flags(long long x, long long y) {
    unsigned char ah;
    long long val;

    __asm__ volatile (
        "movq %1, %%rax;"      // RAX = x (destination register)
        "movq %2, (%3);"       // Store y in memory location (source)
        "addq (%3), %%rax;"    // REX.W + 03/r: RAX = RAX + [memory] (ADD r64, r/m64 - memory form)
        "lahf;"                // Load flags into AH
        "movb %%ah, %0;"       // Move AH to output
        : "=r" (ah)            // Output
        : "r" (x), "r" (y), "r" (&val)  // Inputs: x, y, memory address
        : "%rax", "%ah"        // Clobbered registers
    );

    return ah;
}

// Check property for SF
// SF is bit 7 in ah
// Filter to extract SF is: 1000 0000=0x80
bool test_add_REXW03__r64_m64_SF(long long x, long long y) {
    long long  sum = x + y;  
    unsigned char flags = add_REXW03__r64_m64_return_flags(x, y);

    if (sum < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    } 
}

// Check property for ZF
// ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_add_REXW03__r64_m64_ZF(long long x, long long y) {
    long long sum = x + y;  
    unsigned char flags = add_REXW03__r64_m64_return_flags(x, y);

    if (sum == 0) {
        return ((flags & 0x40) == 0x40);
    } else {
        return ((flags & 0x40) == 0x00);
    }
}

// Check property for AF
// AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_add_REXW03__r64_m64_AF (long long x, long long y) {
    long long  x_lsb = x & 0x0F;     // Get lower 4 bits of x
    long long y_lsb = y & 0x0F;     // Get lower 4 bits of y
    
    unsigned char flags = add_REXW03__r64_m64_return_flags(x, y);

    if ((x_lsb + y_lsb) > 0x0F) {  // Carry from bit 3 to bit 4
        return ((flags & 0x10) == 0x10);
    } else {
        return ((flags & 0x10) == 0x00);
    }
}

// Check property for PF
// PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04
bool test_add_REXW03__r64_m64_PF(long long x, long long y) {
    unsigned char flags = add_REXW03__r64_m64_return_flags(x, y);
    
    long long  result = x + y;
    uint8_t expected_parity = calculate_parity(result & 0xFF);  // Only check lower 8 bits for parity
    
    return (flags & 0x04) == expected_parity;
}

unsigned char add_REXW03__r64_m64_return_OF (long long x, long long y) {
    unsigned char of;
    long long val;
    
    __asm__ volatile (
        "movq %1, %%rax;"      // RAX = x (destination register)
        "movq %2, (%3);"       // Store y in memory location (source)
        "addq (%3), %%rax;"    // REX.W + 03/r: RAX = RAX + [memory] (ADD r64, r/m64 - memory form)
        "seto %0;"             // Set 'of' to 1 if overflow occurred
        : "=r"(of)             // Output operand (OF flag)
        : "r"(x), "r"(y), "r" (&val)  // Input operands: x, y, memory address
        : "%rax"               // Clobbered registers
    );

    return of;
}

// Check property for OF
bool test_add_REXW03__r64_m64_OF(long long x, long long y) {
    long long sum = x + y;
    unsigned char of = add_REXW03__r64_m64_return_OF(x, y);
    
    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
        ((x < 0) && (y < 0) && (sum >= 0))) {
        return of == 1;
    } else {
        return of == 0;
    }
}

// dummy main function, to allow us to link the executable

#include <stdio.h>

int main() {
    return 0;
}
