#include <stdbool.h>

// Following function subs two values and returns OF flag value using seto instruction

#include <stdio.h>

unsigned char get_overflow_flag(long x, long y) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"     // Load x into RAX
        "subq %2, %%rax;"     // Sub y from RAX (this may set OF)
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x), "r"(y)      // Input operands
        : "%rax"              // Clobbered register
    );

    return of;
}



//check property for OF

bool test_long_sub_OF (long x, long y) {
    long diff = x - y;
    unsigned char of = get_overflow_flag(x, y);

    if (((x <  0) && (y > 0) && (diff > 0)) ||
	((x > 0) && (y < 0) && (diff <  0))) {
      return of==1; }
    else { return of==0;}
    return false; 
	
       

    
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
