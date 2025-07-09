#include <stdbool.h>
#include <stdint.h>


//**********************************************************
// ADD AL/i8

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

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
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
    return false; 
    
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
    return false; 

    
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
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add_AL_i8_PF_0 () {
    unsigned char flags = add_AL_i8_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add_AL_i8_PF_1 () {   
    unsigned char flags = add_AL_i8_return_flags(1);  
    return ((flags & 0x04) == 0x04);
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
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}



//**********************************************************
// ADD AX/i16

unsigned char add_AX_i16_return_CF (uint16_t x) {
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

bool test_add_AX_i16_CF (uint16_t  x) {
    uint16_t  sum = x + 0x0002;
    unsigned char flags = add_AX_i16_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_AX_i16_return_flags (int16_t x) {
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

bool test_add_AX_i16_SF (int16_t x) {
  
  int16_t sum = x+ 0x0002;  
    unsigned char flags = add_AX_i16_return_flags(x);

    if (sum<0) {
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

bool test_add_AX_i16_ZF (int16_t x) {
  
  int16_t sum = x+0x0002;  
    unsigned char flags = add_AX_i16_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add_AX_i16_AF (int16_t x) {

  int16_t sum_lsb = (x & 0x000F) + (0x0002 & 0x000F); // Only add least 4 bits, zero out all other bits
  int16_t AF_value = sum_lsb & 0x0010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_AX_i16_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04


bool test_add_AX_i16_PF_0 () {
    unsigned char flags = add_AX_i16_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add_AX_i16_PF_1 () {   
    unsigned char flags = add_AX_i16_return_flags(1);  
    return ((flags & 0x04) == 0x04);
}


 unsigned char add_AX_i16_return_OF (int16_t x) {
    unsigned char of;

    __asm__ volatile (
        "movw %1, %%ax;"      // Load x into AX 
        "addw $0x0002, %%ax;"      // ax += imm 
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)      // Input operands
        : "%ax"              // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_AX_i16_OF (int16_t x) {
    int16_t sum = x + 0x0002;
    unsigned char of = add_AX_i16_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}


//**********************************************************
// ADD EAX/i32


unsigned char add_EAX_i32_return_CF (uint32_t x) {
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

bool test_add_EAX_i32_CF (uint32_t  x) {
    uint32_t  sum = x + 0x00000002;
    unsigned char flags = add_EAX_i32_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_EAX_i32_return_flags (int32_t x) {
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

bool test_add_EAX_i32_SF (int32_t x) {
  
  int32_t sum = x+ 0x00000002;  
    unsigned char flags = add_EAX_i32_return_flags(x);

    if (sum<0) {
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

bool test_add_EAX_i32_ZF (int32_t x) {
  
  int32_t sum = x+ 0x00000002;  
    unsigned char flags = add_EAX_i32_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add_EAX_i32_AF (int32_t x) {

  int32_t sum_lsb = (x & 0x0000000F) + (0x00000002 & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x00000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_EAX_i32_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add_EAX_i32_PF_0 () {
    unsigned char flags = add_EAX_i32_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add_EAX_i32_PF_1 () {   
    unsigned char flags = add_EAX_i32_return_flags(1);  
    return ((flags & 0x04) == 0x04);
}



unsigned char add_EAX_i32_return_OF (int32_t x) {
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

bool test_add_EAX_i32_OF (int32_t x) {
    int32_t sum = x + 0x00000002;
    unsigned char of = add_EAX_i32_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}


//**********************************************************
// ADD RAX/i32


unsigned char add_RAX_i32_return_CF (unsigned long x) {
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

bool test_add_RAX_i32_CF (unsigned long x) {
    unsigned long sum = x + 0x00000002;
    unsigned char flags = add_RAX_i32_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_RAX_i32_return_flags (long x) {
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

bool test_add_RAX_i32_SF (long x) {
  
  long sum = x+0x00000002;  
    unsigned char flags = add_RAX_i32_return_flags(x);

    if (sum<0) {
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

bool test_add_RAX_i32_ZF (long x) {
  
  long sum = x+0x00000002;  
    unsigned char flags = add_RAX_i32_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add_RAX_i32_AF (long x) {

  long sum_lsb = (x & 0x000000000000000F) + (0x00000002 & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  long AF_value = sum_lsb & 0x0000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_RAX_i32_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add_RAX_i32_PF_0 () {
    unsigned char flags = add_RAX_i32_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add_RAX_i32_PF_1 () {   
    unsigned char flags = add_RAX_i32_return_flags(1);  
    return ((flags & 0x04) == 0x04);
}



unsigned char add_RAX_i32_return_OF (long x) {
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

bool test_add_RAX_i32_OF (long x) {
  long sum = x + 0x00000002;
    unsigned char of = add_RAX_i32_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
} 


//**********************************************************
// ADD r8/i8 

unsigned char add__r8_i8_return_CF (uint8_t x) {
    unsigned char ah;

    __asm__ volatile (
        "movb %1, %%cl;"       // cl = x 
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

bool test_add__r8_i8_CF (uint8_t  x) {
    uint8_t  sum = x + 2;
    unsigned char flags = add__r8_i8_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}

unsigned char add__r8_i8_return_flags (int8_t x) {
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

bool test_add__r8_i8_SF (int8_t x) {
  
    int8_t sum = x+2;  
    unsigned char flags = add__r8_i8_return_flags(x);

    if (sum<0) {
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

bool test_add__r8_i8_ZF (int8_t x) {
  
  int8_t sum = x+2;  
    unsigned char flags = add__r8_i8_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add__r8_i8_AF (int8_t x) {

  int8_t sum_lsb = (x & 0x0F) + (0x02 & 0x0F); // Only add least 4 bits, zero out cll other bits
  int8_t AF_value = sum_lsb & 0x10; // extract bit 4, should represent AF flag vclue
  
  
    unsigned char flags = add__r8_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add__r8_i8_PF_0 () {
    unsigned char flags = add__r8_i8_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add__r8_i8_PF_1 () {   
    unsigned char flags = add__r8_i8_return_flags(1);  
    return ((flags & 0x04) == 0x04);
}

unsigned char add__r8_i8_return_OF (int8_t x) {
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

bool test_add__r8_i8_OF (int8_t x) {
    int8_t sum = x + 2;
    unsigned char of = add__r8_i8_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}



//**********************************************************
// ADD r16/i16
unsigned char add__r16_i16_return_CF (uint16_t x) {
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

bool test_add__r16_i16_CF (uint16_t  x) {
    uint16_t  sum = x + 0x0002;
    unsigned char flags = add__r16_i16_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add__r16_i16_return_flags (int16_t x) {
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

bool test_add__r16_i16_SF (int16_t x) {
  
  int16_t sum = x+ 0x0002;  
    unsigned char flags = add__r16_i16_return_flags(x);

    if (sum<0) {
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

bool test_add__r16_i16_ZF (int16_t x) {
  
  int16_t sum = x+0x0002;  
    unsigned char flags = add__r16_i16_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add__r16_i16_AF (int16_t x) {

  int16_t sum_lsb = (x & 0x000F) + (0x0002 & 0x000F); // Only add least 4 bits, zero out all other bits
  int16_t AF_value = sum_lsb & 0x0010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add__r16_i16_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04


bool test_add__r16_i16_PF_0 () {
    unsigned char flags = add__r16_i16_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add__r16_i16_PF_1 () {   
    unsigned char flags = add__r16_i16_return_flags(1);  
    return ((flags & 0x04) == 0x04);
}


 unsigned char add__r16_i16_return_OF (int16_t x) {
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

bool test_add__r16_i16_OF (int16_t x) {
    int16_t sum = x + 0x0002;
    unsigned char of = add__r16_i16_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}


//**********************************************************
// ADD r32/i32
unsigned char add__r32_i32_return_CF (uint32_t x) {
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

bool test_add__r32_i32_CF (uint32_t  x) {
    uint32_t  sum = x + 0x00000002;
    unsigned char flags = add__r32_i32_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add__r32_i32_return_flags (int32_t x) {
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

bool test_add__r32_i32_SF (int32_t x) {
  
  int32_t sum = x+ 0x00000002;  
    unsigned char flags = add__r32_i32_return_flags(x);

    if (sum<0) {
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

bool test_add__r32_i32_ZF (int32_t x) {
  
  int32_t sum = x+ 0x00000002;  
    unsigned char flags = add__r32_i32_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add__r32_i32_AF (int32_t x) {

  int32_t sum_lsb = (x & 0x0000000F) + (0x00000002 & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x00000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add__r32_i32_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add__r32_i32_PF_0 () {
    unsigned char flags = add__r32_i32_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add__r32_i32_PF_1 () {   
    unsigned char flags = add__r32_i32_return_flags(1);  
    return ((flags & 0x04) == 0x04);
}



unsigned char add__r32_i32_return_OF (int32_t x) {
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

bool test_add__r32_i32_OF (int32_t x) {
    int32_t sum = x + 0x00000002;
    unsigned char of = add__r32_i32_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}


//**********************************************************
// ADD r64/i32



unsigned char add__r64_i32_return_CF (unsigned long x) {
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

bool test_add__r64_i32_CF (unsigned long x) {
    unsigned long sum = x + 0x00000002;
    unsigned char flags = add__r64_i32_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add__r64_i32_return_flags (long x) {
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

bool test_add__r64_i32_SF (long x) {
  
  long sum = x+0x00000002;  
    unsigned char flags = add__r64_i32_return_flags(x);

    if (sum<0) {
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

bool test_add__r64_i32_ZF (long x) {
  
  long sum = x+0x00000002;  
    unsigned char flags = add__r64_i32_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add__r64_i32_AF (long x) {

  long sum_lsb = (x & 0x000000000000000F) + (0x00000002 & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  long AF_value = sum_lsb & 0x0000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add__r64_i32_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add__r64_i32_PF_0 () {
    unsigned char flags = add__r64_i32_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add__r64_i32_PF_1 () {   
    unsigned char flags = add__r64_i32_return_flags(1);  
    return ((flags & 0x04) == 0x04);
}



unsigned char add__r64_i32_return_OF (long x) {
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

bool test_add__r64_i32_OF (long x) {
  long sum = x + 0x00000002;
    unsigned char of = add__r64_i32_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}




//**********************************************************
// ADD r16/i8

unsigned char add_r16_i8_return_CF(uint16_t x) {
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

bool test_add_r16_i8_CF (uint16_t x) {
    uint16_t sum = x + 2;
    unsigned char flags = add_r16_i8_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_r16_i8_return_flags(int16_t x) {
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

bool test_add_r16_i8_SF (int16_t x) {
  
  int16_t sum = x+2;  
    unsigned char flags = add_r16_i8_return_flags(x);

    if (sum<0) {
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

bool test_add_r16_i8_ZF (int16_t x) {
  
  int16_t sum = x+2;  
    unsigned char flags = add_r16_i8_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add_r16_i8_AF (int16_t x) {

  int16_t sum_lsb = (x & 0x000F) + (2 & 0x000F); // Only add least 4 bits, zero out all other bits
  int16_t AF_value = sum_lsb & 0x0010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_r16_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04


bool test_add_r16_i8_PF_0 () {
    unsigned char flags = add_r16_i8_return_flags(2);
    return ((flags & 0x04) == 0x00);
}

bool test_add_r16_i8_PF_1 () {   
    unsigned char flags = add_r16_i8_return_flags(1);  
    return ((flags & 0x04) == 0x04);
}

unsigned char add_r16_i8_return_OF (int16_t x) {
    unsigned char of;
     __asm__ volatile (
        "movw %1, %%ax;"      // Load x into AX 
        "addw $0x02, %%ax;"      // ax += imm 
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)      // Input operands
        : "%ax", "%ah"             // clobbered registers
    );

    return of;
}
//check property for OF

bool test_add_r16_i8_OF (int16_t x) {
    int16_t sum = x + 2;
    unsigned char of = add_r16_i8_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}


//**********************************************************
// ADD r32/i8

unsigned char add_r32_i8_return_CF(uint32_t x) {
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

bool test_add_r32_i8_CF (uint32_t x) {
    uint32_t sum = x + 0x02;
    unsigned char flags = add_r32_i8_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_r32_i8_return_flags(int32_t x) {
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

bool test_add_r32_i8_SF (int32_t x) {
  
  int32_t sum = x+0x02;  
    unsigned char flags = add_r32_i8_return_flags(x);

    if (sum<0) {
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

bool test_add_r32_i8_ZF (int32_t x) {
  
  int32_t sum = x+0x02;  
    unsigned char flags = add_r32_i8_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add_r32_i8_AF ( int32_t x) {

  int32_t sum_lsb = (x & 0x0000000F) + (0x02 & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x00000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_r32_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add_r32_i8_PF_0 () {
  
   
    unsigned char flags = add_r32_i8_return_flags(2);

   
      return ((flags & 0x04)==0x00);
    

    
}


bool test_add_r32_i8_PF_1 () {   
  unsigned char flags = add_r32_i8_return_flags(1);
  return ((flags & 0x04)==0x04);}

  unsigned char add_r32_i8_return_OF(int32_t x) {
    unsigned char of;
    
     __asm__ volatile (
        "movl %1, %%eax;"     // Load x into EAX
	"addl $0x02, %%eax;"   // eax += imm
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)              // Input operands
	       : "%eax","%ah"               // clobbered registers
    );

    return of;
}
//check property for OF

bool test_add_r32_i8_OF (int32_t x) {
  
    int32_t sum = x + 2;
    unsigned char of = add_r32_i8_return_OF(x);
    if ((x >= 0) && (sum < 0)) {  
        return of == 1; 
    }
    else { 
        return of == 0;
    }
    return false; 
}


//**********************************************************
// ADD r64/i8

unsigned char add_r64_i8_return_CF(unsigned long x) {
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

bool test_add_r64_i8_CF (unsigned long x) {
    unsigned long sum = x + 0x02;
    unsigned char flags = add_r64_i8_return_CF(x);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_r64_i8_return_flags(long x) {
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

bool test_add_r64_i8_SF (unsigned long x) {
  
  long sum = x+0x02;  
    unsigned char flags = add_r64_i8_return_flags(x);

    if (sum<0) {
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

bool test_add_r64_i8_ZF (long x) {
  
  long sum = x+0x02;  
    unsigned char flags = add_r64_i8_return_flags(x);

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
// Filter to extract AF is: 0001 0000=0x10

bool test_add_r64_i8_AF (long x) {

  long sum_lsb = (x & 0x000000000000000F) + (0x02 & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  long AF_value = sum_lsb & 0x0000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_r64_i8_return_flags(x);

    if (AF_value==16) {
      return ((flags & 0x10)==0x10);
      }
    else {
      return ((flags & 0x10)==0x00);
	}
    return false; 

    
}

//check property for PF
//PF is bit 2 in ah
// Filter to extract PF is: 0000 0100=0x04

bool test_add_r64_i8_PF_0 () {
  
   
    unsigned char flags = add_r64_i8_return_flags(2);

   
      return ((flags & 0x04)==0x00);
    

    
}


bool test_add_r64_i8_PF_1 () {   
  unsigned char flags = add_r64_i8_return_flags(1);
  return ((flags & 0x04)==0x04);}

  unsigned char add_r64_i8_return_OF(long x) {
    unsigned char of;
    
     __asm__ volatile (
        "movq %1, %%rax;"     // Load x into RAX
	"addq $0x02, %%rax;"   // rax += imm
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x)           // Input operands
	: "%rax","%ah"     // clobbered registers
    );

    return of;
}
//check property for OF

bool test_add_r64_i8_OF (long x) {
    long sum = x + 0x02;
    unsigned char of = add_r64_i8_return_OF (x);

    if ((x >= 0) && (sum < 0))
	 {
      return of==1; }
    else { return of==0;}
    return false; 
    
}



// dummy main function, to allow us to link the executable
int main () { return 0;}
