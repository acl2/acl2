#include <stdbool.h>
#include <stdint.h>


//**********************************************************
// ADD r16/r16

unsigned char add_r16_r16_return_CF (uint16_t x, uint16_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x 
        "movw %2, %%bx;"       // bx = y 
        "addw %%bx, %%ax;"     // ax += bx 
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

bool test_add_r16_r16_CF (uint16_t  x, uint16_t  y) {
    uint16_t  sum = x + y;
    unsigned char flags = add_r16_r16_return_CF(x, y);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_r16_r16_return_flags (int16_t x, int16_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movw %1, %%ax;"       // ax = x
        "movw %2, %%bx;"       // bx = y 
        "addw %%bx, %%ax;"     // ax += bx 
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

bool test_add_r16_r16_SF (int16_t x, int16_t y) {
  
  int16_t sum = x+y;  
    unsigned char flags = add_r16_r16_return_flags(x, y);

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

bool test_add_r16_r16_ZF (int16_t x, int16_t y) {
  
  int16_t sum = x+y;  
    unsigned char flags = add_r16_r16_return_flags(x, y);

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

bool test_add_r16_r16_AF (int16_t x, int16_t y) {

  int16_t sum_lsb = (x & 0x000F) + (y & 0x000F); // Only add least 4 bits, zero out all other bits
  int16_t AF_value = sum_lsb & 0x0010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_r16_r16_return_flags(x, y);

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

bool test_add_r16_r16_PF_0 () {
  
   
    unsigned char flags = add_r16_r16_return_flags(1, 1);

   
      return ((flags & 0x04)==0x00);
    

    
}


bool test_add_r16_r16_PF_1 () {   
  unsigned char flags = add_r16_r16_return_flags(1, 2);
  return ((flags & 0x04)==0x04);}



unsigned char add_r16_r16_return_OF (int16_t x, int16_t y) {
    unsigned char of;
    
    __asm__ volatile (
        "movw %1, %%ax;"      // Load x into AX 
        "movw %2, %%bx;"      // bx = y 
        "addw %%bx, %%ax;"    // ax += bx 
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x), "r"(y)      // Input operands
        : "%eax", "%ebx"      // clobbered registers
    );

    return of;
}

//check property for OF

bool test_add_r16_r16_OF (int16_t x, int16_t y) {
    int16_t sum = x + y;
    unsigned char of = add_r16_r16_return_OF (x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
    return false; 
	
       

    
}


//**********************************************************
// ADD r32/r32


unsigned char add_r32_r32_return_CF (uint32_t x, uint32_t y) {
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

bool test_add_r32_r32_CF (uint32_t  x, uint32_t  y) {
    uint32_t  sum = x + y;
    unsigned char flags = add_r32_r32_return_CF(x, y);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_r32_r32_return_flags (int32_t x, int32_t y) {
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

bool test_add_r32_r32_SF (int32_t x, int32_t y) {
  
  int32_t sum = x+y;  
    unsigned char flags = add_r32_r32_return_flags(x, y);

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

bool test_add_r32_r32_ZF (int32_t x, int32_t y) {
  
  int32_t sum = x+y;  
    unsigned char flags = add_r32_r32_return_flags(x, y);

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

bool test_add_r32_r32_AF (int32_t x, int32_t y) {

  int32_t sum_lsb = (x & 0x0000000F) + (y & 0x0000000F); // Only add least 4 bits, zero out all other bits
  int32_t AF_value = sum_lsb & 0x00000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_r32_r32_return_flags(x, y);

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

bool test_add_r32_r32_PF_0 () {
  
   
    unsigned char flags = add_r32_r32_return_flags(1, 1);

   
      return ((flags & 0x04)==0x00);
    

    
}


bool test_add_r32_r32_PF_1 () {   
  unsigned char flags = add_r32_r32_return_flags(1, 2);
  return ((flags & 0x04)==0x04);}



unsigned char add_r32_r32_return_OF (int32_t x, int32_t y) {
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

bool test_add_r32_r32_OF (int32_t x, int32_t y) {
    int32_t sum = x + y;
    unsigned char of = add_r32_r32_return_OF (x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
    return false; 
	
       

    
}

//**********************************************************
// ADD r64/r64


unsigned char add_r64_r64_return_CF (unsigned long x, unsigned long y) {
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

bool test_add_r64_r64_CF (unsigned long x, unsigned long y) {
    unsigned long sum = x + y;
    unsigned char flags = add_r64_r64_return_CF(x, y);

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }
    return false;
}


unsigned char add_r64_r64_return_flags (long x, long y) {
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

bool test_add_r64_r64_SF (long x, long y) {
  
  long sum = x+y;  
    unsigned char flags = add_r64_r64_return_flags(x, y);

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

bool test_add_r64_r64_ZF (long x, long y) {
  
  long sum = x+y;  
    unsigned char flags = add_r64_r64_return_flags(x, y);

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

bool test_add_r64_r64_AF (long x, long y) {

  long sum_lsb = (x & 0x000000000000000F) + (y & 0x000000000000000F); // Only add least 4 bits, zero out all other bits
  long AF_value = sum_lsb & 0x0000000000000010; // extract bit 4, should represent AF flag value
  
  
    unsigned char flags = add_r64_r64_return_flags(x, y);

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

bool test_add_r64_r64_PF_0 () {
  
   
    unsigned char flags = add_r64_r64_return_flags(1, 1);

   
      return ((flags & 0x04)==0x00);
    

    
}


bool test_add_r64_r64_PF_1 () {   
  unsigned char flags = add_r64_r64_return_flags(1, 2);
  return ((flags & 0x04)==0x04);}



unsigned char add_r64_r64_return_OF (long x, long y) {
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

bool test_add_r64_r64_OF (long x, long y) {
    long sum = x + y;
    unsigned char of = add_r64_r64_return_OF (x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
    return false; 
	
       

    
}

// dummy main function, to allow us to link the executable
int main () { return 0;}
