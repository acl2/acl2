#include <stdbool.h>
#include <stdint.h>

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
        "addw $2, %%ax;"      // ax += imm 
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



int main() {
    
    return 0;
}
