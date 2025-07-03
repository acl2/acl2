#include <stdbool.h>

// Following function adds two values and returns OF flag value using seto instruction

#include <stdio.h>

unsigned char get_overflow_flag(long x, long y) {
    unsigned char of;

    __asm__ volatile (
        "movq %1, %%rax;"     // Load x into RAX
        "addq %2, %%rax;"     // Add y to RAX (this may set OF)
        "seto %0;"            // Set 'of' to 1 if overflow occurred
        : "=r"(of)            // Output operand (OF flag)
        : "r"(x), "r"(y)      // Input operands
        : "%rax"              // Clobbered register
    );

    return of;
}



//check property for OF

bool test_long_add_OF (long x, long y) {
    long sum = x + y;
    unsigned char of = get_overflow_flag(x, y);

    if (((x >= 0) && (y >= 0) && (sum < 0)) ||
	((x < 0) && (y < 0) && (sum >= 0))) {
      return of==1; }
    else { return of==0;}
    return false; 
	
       

    
}




// dummy main function, to allow us to link the executable
int main () { return 0;}
