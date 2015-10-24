// Shilpi Goel

// This program reads input from stdin and computes the number of
// lines, words, and characters in it till a # character is
// encountered.

// gcc wc-input.c -o wc-input.o

#include <stdio.h>
#include <stdint.h>

// See pre-defined macros supported by your GCC using:
// gcc -dM -E - < /dev/null

#ifdef __linux__
static int sysread_num = 0;
#endif
#ifdef __MACH__  // Apple machines
static int sysread_num = 0x2000003;
#endif

int gc(void) {

  char buf[1];
  uint64_t n;

  // printf("\nAddress where the read contents will be stored: %p\n", buf);

  __asm__ volatile
    (
     "mov %1, %%rax\n\t"
     "xor %%rdi, %%rdi\n\t"
     "mov %2, %%rsi\n\t"
     "mov $0x1, %%rdx\n\t"

     "syscall"

     : "+a"(n)  // output list
                // If I use =a (write-only modifier) here instead
                // of +a, bad things happen; rax is being used
                // as both an input and output register, and as such,
                // should be constrained by + rather than =.

     : "g"((uint64_t)sysread_num), "g"((uint64_t)buf) // input list

     : "cc", "memory", "%rdi", "%rsi", "%rdx");

  // printf("\nSyscall returns?: %d\n", n);
  // printf("\nCharacter read in: %c\n", buf[0]);

  return (unsigned char) buf[0];

}

#define IN 1   /* inside a word  */
#define OUT 0  /* outside a word */

/* count lines, words, and characters in input from stdin till # is encountered */
int main () {

  int c, nl, nw, nc, state;

  state = OUT;

  nl = nw = nc = 0;

  while ((c = gc()) != '#') {
    ++nc;
    if (c == '\n')
      ++nl;
    if (c == ' ' || c == '\n' || c == '\t')
      state = OUT;
    else if (state == OUT) {
      state = IN;
      ++nw;
    }
  }

  //  printf("nc: %d nw: %d nl: %d\n", nc, nw, nl);

  return 0;

}

/*
void _start() {
    main();
    asm (
     "mov $60, %rax;"
     "xor %rdi, %rdi;"
     "syscall");
}
*/
