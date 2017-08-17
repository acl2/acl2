// Shilpi Goel
// gcc push.c -o push.o

// A little program to see what the default operand sizes are of the
// PUSH instructions in 64-bit mode

#include <stdio.h>
#include <stdint.h>

// See pre-defined macros supported by your GCC using:
// gcc -dM -E - < /dev/null

uint64_t push (void) {

  uint64_t out;
  uint16_t x = 12;  
  uint16_t *v = &x;
  
  __asm__ volatile
    (
     "movq   $0xFFFFFFFF, %%rax\n\t"
     
     "pushw  %[v]\n\t"
     "pushq  %[v]\n\t"
     "pushw  %%ax\n\t"
     "pushq  %%rax\n\t"

     "popw  %0\n\t"
     "popq  %0\n\t"
     "popw  %0\n\t"
     "popq  %0\n\t"

     :  // output list
	"=g"(out)
	
     :  // input list
	[v] "rm" (*v)
	
     : "cc", "memory");
  
  return (0);
}

int main () {

  push();

  return 0;

}
