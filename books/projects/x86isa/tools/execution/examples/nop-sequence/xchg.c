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
