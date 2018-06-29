// X86ISA Library
//
// Note: The license below is based on the template at:
// http://opensource.org/licenses/BSD-3-Clause
//
// Copyright (C) 2015, Regents of the University of Texas
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// o Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.
//
// o Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the distribution.
//
// o Neither the name of the copyright holders nor the names of its
//   contributors may be used to endorse or promote products derived
//   from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// Original Author(s):
// Shilpi Goel         <shigoel@cs.utexas.edu>

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
