#include <stdbool.h>
#include <stdint.h>


uint8_t calculate_parity (int8_t x) {
    uint8_t v = (uint8_t)x;

    // XOR folding to compute parity
    v ^= v >> 4;
    v ^= v >> 2;
    v ^= v >> 1;

    // Check the lowest bit (parity)
    // If even number of 1's → return 0x04
    // Else (odd parity)      → return 0x00
    return (~v & 1) ? 0x04 : 0x00;
}







//**********************************************************
// SUB r8/i8
unsigned char sub_AL_i8_return_CF(uint8_t x) {
    unsigned char ah;
    __asm__ volatile (
        "movb %1, %%al;"       // al = x
        "subb $0x02, %%al;"       // al -= imm (immediate)
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

bool test_sub_AL_i8_CF (uint8_t  x) {
    uint8_t diff = x - 0x02;
    unsigned char flags = sub_AL_i8_return_CF(x);

    if ((0x02 > x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}



unsigned char sub_AL_i8_return_flags(int8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%al;"      // al = x 
        "subb $0x02, %%al;"      // al -= imm 
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
bool test_sub_AL_i8_SF (int8_t x) {
  
  int8_t diff = x-0x02;  
    unsigned char flags = sub_AL_i8_return_flags(x);

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
bool test_sub_AL_i8_ZF (int8_t x) {
    int8_t diff = x - 0x02;
    unsigned char flags = sub_AL_i8_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_sub_AL_i8_AF (int8_t x) {
    int8_t x_lsb = x & 0xF;  // Get lower 4 bits of x
    int8_t imm_lsb = 0x02 & 0xF;  // Get lower 4 bits of y
    
    // For subtraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = sub_AL_i8_return_flags(x);
    bool actual_af = (flags & 0x10);
    
    return expected_af == actual_af;
}










//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_sub_AL_i8_PF (int8_t x) {
   
    unsigned char flags = sub_AL_i8_return_flags(x);

    int8_t result = x - 0x02;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}



unsigned char sub_AL_i8_return_OF(int8_t x) {
    unsigned char of;

    __asm__ volatile (
        "movb %1, %%al;"      // Load x into AL (8-bit)
        "subb $0x02, %%al;"      // Subtract immediate from AL
        "seto %0;"            // Set OF flag into 'of'
        : "=r"(of)            // Output operand
        : "r"(x)               // input
        : "%al"               // Clobbered register
    );

    return of;
}

//check property for OF

bool test_sub_AL_i8_OF (int8_t x) {
    int8_t  diff = x - 0x02;
    unsigned char of = sub_AL_i8_return_OF (x);

     if ((x < 0) && (diff >= 0)) {
        return (of == 1);
    } else {
        return (of == 0);
    }
       return false; 
}



//**********************************************************
// SUB r16/i16

unsigned char sub_AX_i16_return_CF(uint16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // Load x into AX
        "subw $0x0002, %%ax;"       // Subtract immediate value from AX
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
bool test_sub_AX_i16_CF (uint16_t  x) {
    uint16_t diff = x - 0x0002;
    unsigned char flags = sub_AX_i16_return_CF(x);

    if ((0x0002 > x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char sub_AX_i16_return_flags(int16_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"      // Load x into AX
        "subw $0x0002, %%ax;"      // Subtract immediate from AX
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

bool test_sub_AX_i16_SF (int16_t x) {
  
  int16_t diff = x- 0x0002;  
    unsigned char flags = sub_AX_i16_return_flags(x);

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

bool test_sub_AX_i16_ZF (int16_t x) {
    int16_t diff = x - 0x0002;
    unsigned char flags = sub_AX_i16_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10

bool test_sub_AX_i16_AF (int16_t x) {

    int16_t x_lsb = x & 0x000F;  // Get lower 4 bits of x
    int16_t imm_lsb = 0x0002 & 0x000F;  // Get lower 4 bits of y
    
    // For subtraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = sub_AX_i16_return_flags(x);
    bool actual_af = (flags & 0x10);
    
    return expected_af == actual_af;
}




//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_sub_AX_i16_PF (int16_t x) {
   
    unsigned char flags = sub_AX_i16_return_flags(x);

    int16_t result = x - 0x0002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}




unsigned char sub_AX_i16_return_OF(int16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"     // Load x into AX
        "subw $0x0002, %%ax;"     // Subtract immediate value from AX
        "seto %0;"           // Set OF flag into 'of'
        : "=r"(of)           // Output operand
        : "r"(x)              // Inputs: x in register, imm as immediate
        : "%ax"              // Clobbered register
    );

    return of;
}


//check property for OF
bool test_sub_AX_i16_OF (int16_t x) {
     int16_t diff = x - 0x0002;
    unsigned char of = sub_AX_i16_return_OF (x);

  if ((x < 0) && (diff >= 0)) {
        return (of == 1);
    } else {
        return (of == 0);
    }
       return false; 
} 



//**********************************************************
// SUB r32/i32

unsigned char sub_EAX_i32_return_CF(uint32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"      // eax = x 
        "subl $0x00000002, %%eax;"      // eax -= imm 
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

bool test_sub_EAX_i32_CF (uint32_t  x) {
     uint32_t diff = x - 0x00000002;
    unsigned char flags = sub_EAX_i32_return_CF (x);

    if ((0x00000002 > x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char sub_EAX_i32_return_flags(int32_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"       // eax = x (32-bit)
        "subl $0x00000002, %%eax;"       // eax -= imm (immediate)
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

bool test_sub_EAX_i32_SF (int32_t x) {
  
  int32_t  diff = x- 0x00000002;  
    unsigned char flags = sub_EAX_i32_return_flags(x);

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

bool test_sub_EAX_i32_ZF (int32_t x) {
    int32_t diff = x - 0x00000002;
    unsigned char flags = sub_EAX_i32_return_flags(x);

    if (diff == 0) {   
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_sub_EAX_i32_AF (int32_t x) {
     int32_t x_lsb = x & 0X0000000F;  // Get lower 4 bits of x
     int32_t imm_lsb = 0x00000002 & 0X0000000F;  // Get lower 4 bits of y
    
    // For subtraction, AF is set when there's a borrow from bit 4 to bit 3
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = sub_EAX_i32_return_flags(x);
    bool actual_af = (flags & 0x10);
    
    return expected_af == actual_af;
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_sub_EAX_i32_PF (int32_t x) {
   
    unsigned char flags = sub_EAX_i32_return_flags(x);

    int32_t result = x - 0x00000002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}





unsigned char sub_EAX_i32_return_OF(int32_t x) {
    unsigned char of;

    __asm__ volatile (
        "movl %1, %%eax;"     // Load x into EAX (32-bit register)
        "subl $0x00000002, %%eax;"     // Subtract immediate value from EAX
        "seto %0;"            // Set OF flag into 'of'
        : "=r"(of)            // Output
        : "r"(x)                   // Inputs: register and immediate
        : "%eax"              // Clobbered register
    );

    return of;
}


//check property for OF

bool test_sub_EAX_i32_OF (int32_t x) {
    int32_t diff = x - 0x00000002;
    unsigned char of = sub_EAX_i32_return_OF (x);

        if ((x < 0) && (diff >= 0)) {
        return (of == 1);
    } else {
        return (of == 0);
    }
       return false; 
}



//**********************************************************
// SUB r64/i32


unsigned char sub_RAX_i32_return_CF(unsigned long x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"           // Load x into RAX
        "subq $0x00000002, %%rax;"  // Subtract immediate value from RAX
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

bool test_sub_RAX_i32_CF (uint32_t  x) {
     long diff = x - 0x00000002;
    unsigned char flags = sub_RAX_i32_return_CF (x);

    if ((0x00000002 > x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}

unsigned char sub_RAX_i32_return_flags(long x) {
    unsigned char ah;

    __asm__ volatile (
        "movq %1, %%rax;"           // Load x into RAX
        "subq $0x00000002, %%rax;"  // Subtract immediate from RAX
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
bool test_sub_RAX_i32_SF (long x) {
    long diff = x - 0x00000002;  
    unsigned char flags = sub_RAX_i32_return_flags(x);

    if (diff < 0) {
        return ((flags & 0x80) == 0x80);
    } else {
        return ((flags & 0x80) == 0x00);
    }
}
    
//check property for ZF
//ZF is bit 6 in ah
// Filter to extract ZF is: 0100 0000=0x40
bool test_sub_RAX_i32_ZF (long x) {
    long diff = x - 0x00000002;
    unsigned char flags = sub_RAX_i32_return_flags(x);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//check property for AF
//AF is bit 4 in ah
// Filter to extract AF is: 0001 0000=0x10
bool test_sub_RAX_i32_AF (long x) {
    long x_lsb = x & 0x0000000F;               // Get lower 4 bits of x
    long imm_lsb = 0x00000002 & 0x0000000F;    
    
    bool expected_af = (x_lsb < imm_lsb);
    
    unsigned char flags = sub_RAX_i32_return_flags(x);
    bool actual_af = ((flags & 0x10) != 0);  
    
    return expected_af == actual_af;
}


 bool test_sub_RAX_i32_PF (long x) {
   
    unsigned char flags = sub_RAX_i32_return_flags(x);

    long result = x - 0x00000002;
    uint8_t result_lsb = result & 0xFF;
    uint8_t result_parity = calculate_parity(result); 
    
    return (flags & 0x04) == result_parity; 
}


unsigned char sub_RAX_i32_return_OF(long x) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"           // Load x into RAX
        "subq $0x00000002, %%rax;"  // Subtract immediate value from RAX
        "seto %0;"                  // Set OF flag into 'of'
        : "=r"(of)                  // Output operand
        : "r"(x)                    // Inputs: x in register
        : "%rax"                    // Clobbered register
    );

    return of;
}

//check property for OF
bool test_sub_RAX_i32_OF (long x) {
    long diff = x - 0x00000002;
    unsigned char of = sub_RAX_i32_return_OF(x);

    if ((x < 0) && (diff >= 0)) {
        return (of == 1);
    } else {
        return (of == 0);
    }
}



// dummy main function, to allow us to link the executable
int main () 
{ return 0;}
