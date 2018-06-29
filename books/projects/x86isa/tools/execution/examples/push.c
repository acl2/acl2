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
