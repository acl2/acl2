// Shilpi Goel

// gcc xchg.c -o xchg.o

#include <stdio.h>
#include <stdint.h>

// See pre-defined macros supported by your GCC using:
// gcc -dM -E - < /dev/null

uint64_t xchg (void) {

  uint64_t n,m;
  __asm__ volatile
    (
     "mov  $0x1,        %%rax\n\t"
     "mov  $0xFFFFFFFF, %%r8\n\t"
     "xchg %%ax,       %%r8w\n\t"
     "mov  %%r8,        %1\n\t"
     : "=a"(n),"=g"(m)  // output list
	 
     :  // input list

     : "cc", "memory");

  printf("\nValue in rax: 0x%llx\n", n);
  printf("\nValue in r8:  0x%llx\n", m);

  return (0);
}

int main () {

  xchg();

  return 0;

}
