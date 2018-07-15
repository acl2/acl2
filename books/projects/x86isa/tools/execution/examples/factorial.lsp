; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "../top" :ttags :all)

;; ======================================================================i

#||

// Source program (in C):

#include <stdio.h>
#include <stdlib.h>

// From Rosetta Code article on factorial

int factorial_recursive (int n)
{
  return n == 0 ? 1 : n * factorial_recursive(n - 1);
}

int factorial_iterative (int n)
{
  int result = 1, i;
  for (i = 1; i <= n; ++i)
    result *= i;
  return result;
}

// Safe with some compilers (for example: GCC with -O2, LLVM's clang)
int fac_aux(int n, int acc)
{
  return n < 1 ? acc : fac_aux(n - 1, acc * n);
}

int factorial_tail_recursive (int n)
{
  return fac_aux(n, 1);
}

int main (int argc, char *argv[], char *env[])
{
  if (argc != 3)
    {
      printf("Error: Need two arg.\n");
      exit(1);
    }
  int n = atoi(argv[1]);
  int v = atoi(argv[2]); // 0: recursive, 1: iterative, others: tail recursive
  switch (v)
    {
    case 0:
      printf("fact_recursive(%d) = %d\n", n, factorial_recursive(n));
      break;
    case 1:
      printf("fact_iterative(%d) = %d\n", n, factorial_iterative(n));
      break;
    default:
      printf("fact_tail_recursive(%d) = %d\n", n, factorial_tail_recursive(n));
    }
}

||#

(defun fact (n)
  ;; Specification Function in ACL2
  (declare (xargs :measure (nfix n)))
  (if (or (< n 2) (not (integerp n)))
      1
    (* n (fact (- n 1)))))

;; The following ACL2 representation of the factorial binary (with the
;; assembly instructions preserved as comments) was obtained from the
;; factorial machine-code program using the -O2 option of GCC.

(defconst *factorial-binary*
  (list

   ;; Section: <.interp>:


   (cons #x400238 #x2f) ;; (bad)
   (cons #x400239 #x6c) ;; insb (%dx),%es:(%rdi)
   (cons #x40023a #x69) ;; imul $0x646c2f34,0x36(%rdx),%esp
   (cons #x40023b #x62) ;;
   (cons #x40023c #x36) ;;
   (cons #x40023d #x34) ;;
   (cons #x40023e #x2f) ;;
   (cons #x40023f #x6c) ;;
   (cons #x400240 #x64) ;;
   (cons #x400241 #x2d) ;; sub $0x756e696c,%eax
   (cons #x400242 #x6c) ;;
   (cons #x400243 #x69) ;;
   (cons #x400244 #x6e) ;;
   (cons #x400245 #x75) ;;
   (cons #x400246 #x78) ;; js 400275 <_init-0x21b>
   (cons #x400247 #x2d) ;;
   (cons #x400248 #x78) ;; js 400282 <_init-0x20e>
   (cons #x400249 #x38) ;;
   (cons #x40024a #x36) ;; ss
   (cons #x40024b #x2d) ;; sub $0x732e3436,%eax
   (cons #x40024c #x36) ;;
   (cons #x40024d #x34) ;;
   (cons #x40024e #x2e) ;;
   (cons #x40024f #x73) ;;
   (cons #x400250 #x6f) ;; outsl %ds:(%rsi),(%dx)
   (cons #x400251 #x2e) ;; xor %cs:(%rax),%al
   (cons #x400252 #x32) ;;
   (cons #x400253 #x00) ;;

   ;; Section: <.note.ABI-tag>:


   (cons #x400254 #x04) ;; add $0x0,%al
   (cons #x400255 #x00) ;;
   (cons #x400256 #x00) ;; add %al,(%rax)
   (cons #x400257 #x00) ;;
   (cons #x400258 #x10) ;; adc %al,(%rax)
   (cons #x400259 #x00) ;;
   (cons #x40025a #x00) ;; add %al,(%rax)
   (cons #x40025b #x00) ;;
   (cons #x40025c #x01) ;; add %eax,(%rax)
   (cons #x40025d #x00) ;;
   (cons #x40025e #x00) ;; add %al,(%rax)
   (cons #x40025f #x00) ;;
   (cons #x400260 #x47) ;; rex.RXB
   (cons #x400261 #x4e) ;; rex.WRX push %rbp
   (cons #x400262 #x55) ;;
   (cons #x400263 #x00) ;; add %al,(%rax)
   (cons #x400264 #x00) ;;
   (cons #x400265 #x00) ;; add %al,(%rax)
   (cons #x400266 #x00) ;;
   (cons #x400267 #x00) ;; add %al,(%rdx)
   (cons #x400268 #x02) ;;
   (cons #x400269 #x00) ;; add %al,(%rax)
   (cons #x40026a #x00) ;;
   (cons #x40026b #x00) ;; add %al,(%rsi)
   (cons #x40026c #x06) ;;
   (cons #x40026d #x00) ;; add %al,(%rax)
   (cons #x40026e #x00) ;;
   (cons #x40026f #x00) ;; add %cl,(%rdi)
   (cons #x400270 #x0f) ;;
   (cons #x400271 #x00) ;; add %al,(%rax)
   (cons #x400272 #x00) ;;

   ;; Section: <.note.gnu.build-id>:


   (cons #x400274 #x04) ;; add $0x0,%al
   (cons #x400275 #x00) ;;
   (cons #x400276 #x00) ;; add %al,(%rax)
   (cons #x400277 #x00) ;;
   (cons #x400278 #x14) ;; adc $0x0,%al
   (cons #x400279 #x00) ;;
   (cons #x40027a #x00) ;; add %al,(%rax)
   (cons #x40027b #x00) ;;
   (cons #x40027c #x03) ;; add (%rax),%eax
   (cons #x40027d #x00) ;;
   (cons #x40027e #x00) ;; add %al,(%rax)
   (cons #x40027f #x00) ;;
   (cons #x400280 #x47) ;; rex.RXB
   (cons #x400281 #x4e) ;; rex.WRX push %rbp
   (cons #x400282 #x55) ;;
   (cons #x400283 #x00) ;; add %bh,(%rdx)
   (cons #x400284 #x3a) ;;
   (cons #x400285 #xc2) ;; retq $0x1e3d
   (cons #x400286 #x3d) ;;
   (cons #x400287 #x1e) ;;
   (cons #x400288 #x3f) ;; (bad)
   (cons #x400289 #x7a) ;; jp 4002d8 <_init-0x1b8>
   (cons #x40028a #x4d) ;;
   (cons #x40028b #x9e) ;; sahf
   (cons #x40028c #xd3) ;; shll %cl,(%rbx)
   (cons #x40028d #x23) ;;
   (cons #x40028e #x70) ;; jo 40022c <_init-0x264>
   (cons #x40028f #x9c) ;;
   (cons #x400290 #x7b) ;; jnp 400287 <_init-0x209>
   (cons #x400291 #xf5) ;;
   (cons #x400292 #xc6) ;; (bad)
   (cons #x400293 #x31) ;; .byte 0x31
   (cons #x400294 #xae) ;; scas %es:(%rdi),%al
   (cons #x400295 #x07) ;; (bad)
   (cons #x400296 #x5f) ;; pop %rdi
   (cons #x400297 #x8d) ;; .byte 0x8d

   ;; Section: <.hash>:


   (cons #x400298 #x03) ;; add (%rax),%eax
   (cons #x400299 #x00) ;;
   (cons #x40029a #x00) ;; add %al,(%rax)
   (cons #x40029b #x00) ;;
   (cons #x40029c #x06) ;; (bad)
   (cons #x40029d #x00) ;; add %al,(%rax)
   (cons #x40029e #x00) ;;
   (cons #x40029f #x00) ;; add %al,(%rcx)
   (cons #x4002a0 #x01) ;;
   (cons #x4002a1 #x00) ;; add %al,(%rax)
   (cons #x4002a2 #x00) ;;
   (cons #x4002a3 #x00) ;; add %al,(%rax,%rax,1)
   (cons #x4002a4 #x04) ;;
   (cons #x4002a5 #x00) ;;
   (cons #x4002a6 #x00) ;; add %al,(%rax)
   (cons #x4002a7 #x00) ;;
   (cons #x4002a8 #x05) ;; add $0x0,%eax
   (cons #x4002a9 #x00) ;;
   (cons #x4002aa #x00) ;;
   (cons #x4002ab #x00) ;;
   (cons #x4002ac #x00) ;;

   ;; Section: <.gnu.hash>:


   (cons #x4002c8 #x01) ;; add %eax,(%rax)
   (cons #x4002c9 #x00) ;;
   (cons #x4002ca #x00) ;; add %al,(%rax)
   (cons #x4002cb #x00) ;;
   (cons #x4002cc #x01) ;; add %eax,(%rax)
   (cons #x4002cd #x00) ;;
   (cons #x4002ce #x00) ;; add %al,(%rax)
   (cons #x4002cf #x00) ;;
   (cons #x4002d0 #x01) ;; add %eax,(%rax)
   (cons #x4002d1 #x00) ;;

   ;; Section: <.dynsym>:



   ;; Section: <.dynstr>:


   (cons #x400378 #x00) ;; add %bl,0x5f(%rdi)
   (cons #x400379 #x5f) ;;
   (cons #x40037a #x5f) ;;
   (cons #x40037b #x67) ;; addr32 insl (%dx),%es:(%edi)
   (cons #x40037c #x6d) ;;
   (cons #x40037d #x6f) ;; outsl %ds:(%rsi),(%dx)
   (cons #x40037e #x6e) ;; outsb %ds:(%rsi),(%dx)
   (cons #x40037f #x5f) ;; pop %rdi
   (cons #x400380 #x73) ;; jae 4003f6 <_init-0x9a>
   (cons #x400381 #x74) ;;
   (cons #x400382 #x61) ;; (bad)
   (cons #x400383 #x72) ;; jb 4003f9 <_init-0x97>
   (cons #x400384 #x74) ;;
   (cons #x400385 #x5f) ;; pop %rdi
   (cons #x400386 #x5f) ;; pop %rdi
   (cons #x400387 #x00) ;; add %ch,0x62(%rcx,%rbp,2)
   (cons #x400388 #x6c) ;;
   (cons #x400389 #x69) ;;
   (cons #x40038a #x62) ;;
   (cons #x40038b #x63) ;; movslq (%rsi),%ebp
   (cons #x40038c #x2e) ;;
   (cons #x40038d #x73) ;; jae 4003fe <_init-0x92>
   (cons #x40038e #x6f) ;;
   (cons #x40038f #x2e) ;; add %bl,%cs:%ss:0x5f(%rdi)
   (cons #x400390 #x36) ;;
   (cons #x400391 #x00) ;;
   (cons #x400392 #x5f) ;;
   (cons #x400393 #x5f) ;;
   (cons #x400394 #x70) ;; jo 400408 <_init-0x88>
   (cons #x400395 #x72) ;;
   (cons #x400396 #x69) ;; imul $0x68635f66,0x74(%rsi),%ebp
   (cons #x400397 #x6e) ;;
   (cons #x400398 #x74) ;;
   (cons #x400399 #x66) ;;
   (cons #x40039a #x5f) ;;
   (cons #x40039b #x63) ;;
   (cons #x40039c #x68) ;;
   (cons #x40039d #x6b) ;; imul $0x65,(%rax),%eax
   (cons #x40039e #x00) ;;
   (cons #x40039f #x65) ;;
   (cons #x4003a0 #x78) ;; js 40040b <_init-0x85>
   (cons #x4003a1 #x69) ;;
   (cons #x4003a2 #x74) ;; je 4003a4 <_init-0xec>
   (cons #x4003a3 #x00) ;;
   (cons #x4003a4 #x73) ;; jae 40041a <_init-0x76>
   (cons #x4003a5 #x74) ;;
   (cons #x4003a6 #x72) ;; jb 40041c <_init-0x74>
   (cons #x4003a7 #x74) ;;
   (cons #x4003a8 #x6f) ;; outsl %ds:(%rsi),(%dx)
   (cons #x4003a9 #x6c) ;; insb (%dx),%es:(%rdi)
   (cons #x4003aa #x00) ;; add %bl,0x5f(%rdi)
   (cons #x4003ab #x5f) ;;
   (cons #x4003ac #x5f) ;;
   (cons #x4003ad #x6c) ;; insb (%dx),%es:(%rdi)
   (cons #x4003ae #x69) ;; imul $0x6174735f,0x63(%rdx),%esp
   (cons #x4003af #x62) ;;
   (cons #x4003b0 #x63) ;;
   (cons #x4003b1 #x5f) ;;
   (cons #x4003b2 #x73) ;;
   (cons #x4003b3 #x74) ;;
   (cons #x4003b4 #x61) ;;
   (cons #x4003b5 #x72) ;; jb 40042b <_init-0x65>
   (cons #x4003b6 #x74) ;;
   (cons #x4003b7 #x5f) ;; pop %rdi
   (cons #x4003b8 #x6d) ;; insl (%dx),%es:(%rdi)
   (cons #x4003b9 #x61) ;; (bad)
   (cons #x4003ba #x69) ;; imul $0x42494c47,0x0(%rsi),%ebp
   (cons #x4003bb #x6e) ;;
   (cons #x4003bc #x00) ;;
   (cons #x4003bd #x47) ;;
   (cons #x4003be #x4c) ;;
   (cons #x4003bf #x49) ;;
   (cons #x4003c0 #x42) ;;
   (cons #x4003c1 #x43) ;; rex.XB pop %r15
   (cons #x4003c2 #x5f) ;;
   (cons #x4003c3 #x32) ;; xor (%rsi),%ch
   (cons #x4003c4 #x2e) ;;
   (cons #x4003c5 #x33) ;; xor (%rsi),%ebp
   (cons #x4003c6 #x2e) ;;
   (cons #x4003c7 #x34) ;; xor $0x0,%al
   (cons #x4003c8 #x00) ;;
   (cons #x4003c9 #x47) ;; rex.RXB
   (cons #x4003ca #x4c) ;; rex.WR
   (cons #x4003cb #x49) ;; rex.WB
   (cons #x4003cc #x42) ;; rex.X
   (cons #x4003cd #x43) ;; rex.XB pop %r15
   (cons #x4003ce #x5f) ;;
   (cons #x4003cf #x32) ;; xor (%rsi),%ch
   (cons #x4003d0 #x2e) ;;
   (cons #x4003d1 #x32) ;; xor (%rsi),%ch
   (cons #x4003d2 #x2e) ;;
   (cons #x4003d3 #x35) ;; .byte 0x35

   ;; Section: <.gnu.version>:


   (cons #x4003d6 #x00) ;; add %al,(%rax)
   (cons #x4003d7 #x00) ;;
   (cons #x4003d8 #x00) ;; add %al,(%rax)
   (cons #x4003d9 #x00) ;;
   (cons #x4003da #x02) ;; add (%rax),%al
   (cons #x4003db #x00) ;;
   (cons #x4003dc #x03) ;; add (%rax),%eax
   (cons #x4003dd #x00) ;;
   (cons #x4003de #x02) ;; add (%rax),%al
   (cons #x4003df #x00) ;;
   (cons #x4003e0 #x02) ;; add (%rax),%al
   (cons #x4003e1 #x00) ;;

   ;; Section: <.gnu.version_r>:


   (cons #x4003e8 #x01) ;; add %eax,(%rax)
   (cons #x4003e9 #x00) ;;
   (cons #x4003ea #x02) ;; add (%rax),%al
   (cons #x4003eb #x00) ;;
   (cons #x4003ec #x10) ;; adc %al,(%rax)
   (cons #x4003ed #x00) ;;
   (cons #x4003ee #x00) ;; add %al,(%rax)
   (cons #x4003ef #x00) ;;
   (cons #x4003f0 #x10) ;; adc %al,(%rax)
   (cons #x4003f1 #x00) ;;
   (cons #x4003f2 #x00) ;; add %al,(%rax)
   (cons #x4003f3 #x00) ;;
   (cons #x4003f4 #x00) ;; add %al,(%rax)
   (cons #x4003f5 #x00) ;;
   (cons #x4003f6 #x00) ;; add %al,(%rax)
   (cons #x4003f7 #x00) ;;
   (cons #x4003f8 #x74) ;; je 400413 <_init-0x7d>
   (cons #x4003f9 #x19) ;;
   (cons #x4003fa #x69) ;; imul $0x30000,(%rcx),%ecx
   (cons #x4003fb #x09) ;;
   (cons #x4003fc #x00) ;;
   (cons #x4003fd #x00) ;;
   (cons #x4003fe #x03) ;;
   (cons #x4003ff #x00) ;;
   (cons #x400400 #x45) ;; add %r8b,(%r8)
   (cons #x400401 #x00) ;;
   (cons #x400402 #x00) ;;
   (cons #x400403 #x00) ;; add %dl,(%rax)
   (cons #x400404 #x10) ;;
   (cons #x400405 #x00) ;; add %al,(%rax)
   (cons #x400406 #x00) ;;
   (cons #x400407 #x00) ;; add %dh,0x1a(%rbp)
   (cons #x400408 #x75) ;;
   (cons #x400409 #x1a) ;;
   (cons #x40040a #x69) ;; imul $0x20000,(%rcx),%ecx
   (cons #x40040b #x09) ;;
   (cons #x40040c #x00) ;;
   (cons #x40040d #x00) ;;
   (cons #x40040e #x02) ;;
   (cons #x40040f #x00) ;;
   (cons #x400410 #x51) ;; push %rcx
   (cons #x400411 #x00) ;; add %al,(%rax)
   (cons #x400412 #x00) ;;
   (cons #x400413 #x00) ;; add %al,(%rax)
   (cons #x400414 #x00) ;;
   (cons #x400415 #x00) ;; add %al,(%rax)
   (cons #x400416 #x00) ;;

   ;; Section: <.rela.dyn>:


   (cons #x400418 #xe0) ;; loopne 400429 <_init-0x67>
   (cons #x400419 #x0f) ;;
   (cons #x40041a #x60) ;; (bad)
   (cons #x40041b #x00) ;; add %al,(%rax)
   (cons #x40041c #x00) ;;
   (cons #x40041d #x00) ;; add %al,(%rax)
   (cons #x40041e #x00) ;;
   (cons #x40041f #x00) ;; add %al,(%rsi)
   (cons #x400420 #x06) ;;
   (cons #x400421 #x00) ;; add %al,(%rax)
   (cons #x400422 #x00) ;;
   (cons #x400423 #x00) ;; add %al,(%rcx)
   (cons #x400424 #x01) ;;

   ;; Section: <.rela.plt>:


   (cons #x400430 #x00) ;; add %dl,(%rax)
   (cons #x400431 #x10) ;;
   (cons #x400432 #x60) ;; (bad)
   (cons #x400433 #x00) ;; add %al,(%rax)
   (cons #x400434 #x00) ;;
   (cons #x400435 #x00) ;; add %al,(%rax)
   (cons #x400436 #x00) ;;
   (cons #x400437 #x00) ;; add %al,(%rdi)
   (cons #x400438 #x07) ;;
   (cons #x400439 #x00) ;; add %al,(%rax)
   (cons #x40043a #x00) ;;
   (cons #x40043b #x00) ;; add %al,(%rdx)
   (cons #x40043c #x02) ;;

   ;; Section: <_init>:


   (cons #x400490 #x48) ;; sub $0x8,%rsp
   (cons #x400491 #x83) ;;
   (cons #x400492 #xec) ;;
   (cons #x400493 #x08) ;;
   (cons #x400494 #xe8) ;; callq 40052c <call_gmon_start>
   (cons #x400495 #x93) ;;
   (cons #x400496 #x00) ;;
   (cons #x400497 #x00) ;;
   (cons #x400498 #x00) ;;
   (cons #x400499 #xe8) ;; callq 4005c0 <frame_dummy>
   (cons #x40049a #x22) ;;
   (cons #x40049b #x01) ;;
   (cons #x40049c #x00) ;;
   (cons #x40049d #x00) ;;
   (cons #x40049e #xe8) ;; callq 400830 <__do_global_ctors_aux>
   (cons #x40049f #x8d) ;;
   (cons #x4004a0 #x03) ;;
   (cons #x4004a1 #x00) ;;
   (cons #x4004a2 #x00) ;;
   (cons #x4004a3 #x48) ;; add $0x8,%rsp
   (cons #x4004a4 #x83) ;;
   (cons #x4004a5 #xc4) ;;
   (cons #x4004a6 #x08) ;;
   (cons #x4004a7 #xc3) ;; retq

   ;; Section: <exit@plt-0x10>:


   (cons #x4004a8 #xff) ;; pushq 0x200b42(%rip) # 600ff0 <_GLOBAL_OFFSET_TABLE_+0x8>
   (cons #x4004a9 #x35) ;;
   (cons #x4004aa #x42) ;;
   (cons #x4004ab #x0b) ;;
   (cons #x4004ac #x20) ;;
   (cons #x4004ad #x00) ;;
   (cons #x4004ae #xff) ;; jmpq *0x200b44(%rip) # 600ff8 <_GLOBAL_OFFSET_TABLE_+0x10>
   (cons #x4004af #x25) ;;
   (cons #x4004b0 #x44) ;;
   (cons #x4004b1 #x0b) ;;
   (cons #x4004b2 #x20) ;;
   (cons #x4004b3 #x00) ;;
   (cons #x4004b4 #x0f) ;; nopl 0x0(%rax)
   (cons #x4004b5 #x1f) ;;
   (cons #x4004b6 #x40) ;;
   (cons #x4004b7 #x00) ;;

   ;; Section: <_start>:


   (cons #x400500 #x31) ;; xor %ebp,%ebp
   (cons #x400501 #xed) ;;
   (cons #x400502 #x49) ;; mov %rdx,%r9
   (cons #x400503 #x89) ;;
   (cons #x400504 #xd1) ;;
   (cons #x400505 #x5e) ;; pop %rsi
   (cons #x400506 #x48) ;; mov %rsp,%rdx
   (cons #x400507 #x89) ;;
   (cons #x400508 #xe2) ;;
   (cons #x400509 #x48) ;; and $0xfffffffffffffff0,%rsp
   (cons #x40050a #x83) ;;
   (cons #x40050b #xe4) ;;
   (cons #x40050c #xf0) ;;
   (cons #x40050d #x50) ;; push %rax
   (cons #x40050e #x54) ;; push %rsp
   (cons #x40050f #x49) ;; mov $0x400790,%r8
   (cons #x400510 #xc7) ;;
   (cons #x400511 #xc0) ;;
   (cons #x400512 #x90) ;;
   (cons #x400513 #x07) ;;
   (cons #x400514 #x40) ;;
   (cons #x400515 #x00) ;;
   (cons #x400516 #x48) ;; mov $0x4007a0,%rcx
   (cons #x400517 #xc7) ;;
   (cons #x400518 #xc1) ;;
   (cons #x400519 #xa0) ;;
   (cons #x40051a #x07) ;;
   (cons #x40051b #x40) ;;
   (cons #x40051c #x00) ;;
   (cons #x40051d #x48) ;; mov $0x400670,%rdi
   (cons #x40051e #xc7) ;;
   (cons #x40051f #xc7) ;;
   (cons #x400520 #x70) ;;
   (cons #x400521 #x06) ;;
   (cons #x400522 #x40) ;;
   (cons #x400523 #x00) ;;
   (cons #x400524 #xe8) ;; callq 4004d8 <__libc_start_main@plt>
   (cons #x400525 #xaf) ;;
   (cons #x400526 #xff) ;;
   (cons #x400527 #xff) ;;
   (cons #x400528 #xff) ;;
   (cons #x400529 #xf4) ;; hlt
   (cons #x40052a #x90) ;; nop
   (cons #x40052b #x90) ;; nop

   ;; Section: <call_gmon_start>:


   (cons #x40052c #x48) ;; sub $0x8,%rsp
   (cons #x40052d #x83) ;;
   (cons #x40052e #xec) ;;
   (cons #x40052f #x08) ;;
   (cons #x400530 #x48) ;; mov 0x200aa9(%rip),%rax # 600fe0 <_DYNAMIC+0x1a0>
   (cons #x400531 #x8b) ;;
   (cons #x400532 #x05) ;;
   (cons #x400533 #xa9) ;;
   (cons #x400534 #x0a) ;;
   (cons #x400535 #x20) ;;
   (cons #x400536 #x00) ;;
   (cons #x400537 #x48) ;; test %rax,%rax
   (cons #x400538 #x85) ;;
   (cons #x400539 #xc0) ;;
   (cons #x40053a #x74) ;; je 40053e <call_gmon_start+0x12>
   (cons #x40053b #x02) ;;
   (cons #x40053c #xff) ;; callq *%rax
   (cons #x40053d #xd0) ;;
   (cons #x40053e #x48) ;; add $0x8,%rsp
   (cons #x40053f #x83) ;;
   (cons #x400540 #xc4) ;;
   (cons #x400541 #x08) ;;
   (cons #x400542 #xc3) ;; retq
   (cons #x400543 #x90) ;; nop
   (cons #x400544 #x90) ;; nop
   (cons #x400545 #x90) ;; nop
   (cons #x400546 #x90) ;; nop
   (cons #x400547 #x90) ;; nop
   (cons #x400548 #x90) ;; nop
   (cons #x400549 #x90) ;; nop
   (cons #x40054a #x90) ;; nop
   (cons #x40054b #x90) ;; nop
   (cons #x40054c #x90) ;; nop
   (cons #x40054d #x90) ;; nop
   (cons #x40054e #x90) ;; nop
   (cons #x40054f #x90) ;; nop

   ;; Section: <__do_global_dtors_aux>:


   (cons #x400550 #x55) ;; push %rbp
   (cons #x400551 #x48) ;; mov %rsp,%rbp
   (cons #x400552 #x89) ;;
   (cons #x400553 #xe5) ;;
   (cons #x400554 #x53) ;; push %rbx
   (cons #x400555 #x48) ;; sub $0x8,%rsp
   (cons #x400556 #x83) ;;
   (cons #x400557 #xec) ;;
   (cons #x400558 #x08) ;;
   (cons #x400559 #x80) ;; cmpb $0x0,0x200ad0(%rip) # 601030 <__bss_start>
   (cons #x40055a #x3d) ;;
   (cons #x40055b #xd0) ;;
   (cons #x40055c #x0a) ;;
   (cons #x40055d #x20) ;;
   (cons #x40055e #x00) ;;
   (cons #x40055f #x00) ;;
   (cons #x400560 #x75) ;; jne 4005ad <__do_global_dtors_aux+0x5d>
   (cons #x400561 #x4b) ;;
   (cons #x400562 #xbb) ;; mov $0x600e30,%ebx
   (cons #x400563 #x30) ;;
   (cons #x400564 #x0e) ;;
   (cons #x400565 #x60) ;;
   (cons #x400566 #x00) ;;
   (cons #x400567 #x48) ;; mov 0x200aca(%rip),%rax # 601038 <dtor_idx.7384>
   (cons #x400568 #x8b) ;;
   (cons #x400569 #x05) ;;
   (cons #x40056a #xca) ;;
   (cons #x40056b #x0a) ;;
   (cons #x40056c #x20) ;;
   (cons #x40056d #x00) ;;
   (cons #x40056e #x48) ;; sub $0x600e28,%rbx
   (cons #x40056f #x81) ;;
   (cons #x400570 #xeb) ;;
   (cons #x400571 #x28) ;;
   (cons #x400572 #x0e) ;;
   (cons #x400573 #x60) ;;
   (cons #x400574 #x00) ;;
   (cons #x400575 #x48) ;; sar $0x3,%rbx
   (cons #x400576 #xc1) ;;
   (cons #x400577 #xfb) ;;
   (cons #x400578 #x03) ;;
   (cons #x400579 #x48) ;; sub $0x1,%rbx
   (cons #x40057a #x83) ;;
   (cons #x40057b #xeb) ;;
   (cons #x40057c #x01) ;;
   (cons #x40057d #x48) ;; cmp %rbx,%rax
   (cons #x40057e #x39) ;;
   (cons #x40057f #xd8) ;;
   (cons #x400580 #x73) ;; jae 4005a6 <__do_global_dtors_aux+0x56>
   (cons #x400581 #x24) ;;
   (cons #x400582 #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x400583 #x0f) ;;
   (cons #x400584 #x1f) ;;
   (cons #x400585 #x44) ;;
   (cons #x400586 #x00) ;;
   (cons #x400587 #x00) ;;
   (cons #x400588 #x48) ;; add $0x1,%rax
   (cons #x400589 #x83) ;;
   (cons #x40058a #xc0) ;;
   (cons #x40058b #x01) ;;
   (cons #x40058c #x48) ;; mov %rax,0x200aa5(%rip) # 601038 <dtor_idx.7384>
   (cons #x40058d #x89) ;;
   (cons #x40058e #x05) ;;
   (cons #x40058f #xa5) ;;
   (cons #x400590 #x0a) ;;
   (cons #x400591 #x20) ;;
   (cons #x400592 #x00) ;;
   (cons #x400593 #xff) ;; callq *0x600e28(,%rax,8)
   (cons #x400594 #x14) ;;
   (cons #x400595 #xc5) ;;
   (cons #x400596 #x28) ;;
   (cons #x400597 #x0e) ;;
   (cons #x400598 #x60) ;;
   (cons #x400599 #x00) ;;
   (cons #x40059a #x48) ;; mov 0x200a97(%rip),%rax # 601038 <dtor_idx.7384>
   (cons #x40059b #x8b) ;;
   (cons #x40059c #x05) ;;
   (cons #x40059d #x97) ;;
   (cons #x40059e #x0a) ;;
   (cons #x40059f #x20) ;;
   (cons #x4005a0 #x00) ;;
   (cons #x4005a1 #x48) ;; cmp %rbx,%rax
   (cons #x4005a2 #x39) ;;
   (cons #x4005a3 #xd8) ;;
   (cons #x4005a4 #x72) ;; jb 400588 <__do_global_dtors_aux+0x38>
   (cons #x4005a5 #xe2) ;;
   (cons #x4005a6 #xc6) ;; movb $0x1,0x200a83(%rip) # 601030 <__bss_start>
   (cons #x4005a7 #x05) ;;
   (cons #x4005a8 #x83) ;;
   (cons #x4005a9 #x0a) ;;
   (cons #x4005aa #x20) ;;
   (cons #x4005ab #x00) ;;
   (cons #x4005ac #x01) ;;
   (cons #x4005ad #x48) ;; add $0x8,%rsp
   (cons #x4005ae #x83) ;;
   (cons #x4005af #xc4) ;;
   (cons #x4005b0 #x08) ;;
   (cons #x4005b1 #x5b) ;; pop %rbx
   (cons #x4005b2 #xc9) ;; leaveq
   (cons #x4005b3 #xc3) ;; retq
   (cons #x4005b4 #x66) ;; nopw %cs:0x0(%rax,%rax,1)
   (cons #x4005b5 #x66) ;;
   (cons #x4005b6 #x66) ;;
   (cons #x4005b7 #x2e) ;;
   (cons #x4005b8 #x0f) ;;
   (cons #x4005b9 #x1f) ;;
   (cons #x4005ba #x84) ;;
   (cons #x4005bb #x00) ;;
   (cons #x4005bc #x00) ;;
   (cons #x4005bd #x00) ;;
   (cons #x4005be #x00) ;;
   (cons #x4005bf #x00) ;;

   ;; Section: <frame_dummy>:


   (cons #x4005c0 #x55) ;; push %rbp
   (cons #x4005c1 #x48) ;; cmpq $0x0,0x20086f(%rip) # 600e38 <__JCR_END__>
   (cons #x4005c2 #x83) ;;
   (cons #x4005c3 #x3d) ;;
   (cons #x4005c4 #x6f) ;;
   (cons #x4005c5 #x08) ;;
   (cons #x4005c6 #x20) ;;
   (cons #x4005c7 #x00) ;;
   (cons #x4005c8 #x00) ;;
   (cons #x4005c9 #x48) ;; mov %rsp,%rbp
   (cons #x4005ca #x89) ;;
   (cons #x4005cb #xe5) ;;
   (cons #x4005cc #x74) ;; je 4005e0 <frame_dummy+0x20>
   (cons #x4005cd #x12) ;;
   (cons #x4005ce #xb8) ;; mov $0x0,%eax
   (cons #x4005cf #x00) ;;
   (cons #x4005d0 #x00) ;;
   (cons #x4005d1 #x00) ;;
   (cons #x4005d2 #x00) ;;
   (cons #x4005d3 #x48) ;; test %rax,%rax
   (cons #x4005d4 #x85) ;;
   (cons #x4005d5 #xc0) ;;
   (cons #x4005d6 #x74) ;; je 4005e0 <frame_dummy+0x20>
   (cons #x4005d7 #x08) ;;
   (cons #x4005d8 #xbf) ;; mov $0x600e38,%edi
   (cons #x4005d9 #x38) ;;
   (cons #x4005da #x0e) ;;
   (cons #x4005db #x60) ;;
   (cons #x4005dc #x00) ;;
   (cons #x4005dd #xc9) ;; leaveq
   (cons #x4005de #xff) ;; jmpq *%rax
   (cons #x4005df #xe0) ;;
   (cons #x4005e0 #xc9) ;; leaveq
   (cons #x4005e1 #xc3) ;; retq
   (cons #x4005e2 #x90) ;; nop
   (cons #x4005e3 #x90) ;; nop
   (cons #x4005e4 #x90) ;; nop
   (cons #x4005e5 #x90) ;; nop
   (cons #x4005e6 #x90) ;; nop
   (cons #x4005e7 #x90) ;; nop
   (cons #x4005e8 #x90) ;; nop
   (cons #x4005e9 #x90) ;; nop
   (cons #x4005ea #x90) ;; nop
   (cons #x4005eb #x90) ;; nop
   (cons #x4005ec #x90) ;; nop
   (cons #x4005ed #x90) ;; nop
   (cons #x4005ee #x90) ;; nop
   (cons #x4005ef #x90) ;; nop

   ;; Section: <factorial_recursive>:


   (cons #x4005f0 #x85) ;; test %edi,%edi
   (cons #x4005f1 #xff) ;;
   (cons #x4005f2 #xb8) ;; mov $0x1,%eax
   (cons #x4005f3 #x01) ;;
   (cons #x4005f4 #x00) ;;
   (cons #x4005f5 #x00) ;;
   (cons #x4005f6 #x00) ;;
   (cons #x4005f7 #x74) ;; je 400608 <factorial_recursive+0x18>
   (cons #x4005f8 #x0f) ;;
   (cons #x4005f9 #x0f) ;; nopl 0x0(%rax)
   (cons #x4005fa #x1f) ;;
   (cons #x4005fb #x80) ;;
   (cons #x4005fc #x00) ;;
   (cons #x4005fd #x00) ;;
   (cons #x4005fe #x00) ;;
   (cons #x4005ff #x00) ;;
   (cons #x400600 #x0f) ;; imul %edi,%eax
   (cons #x400601 #xaf) ;;
   (cons #x400602 #xc7) ;;
   (cons #x400603 #x83) ;; sub $0x1,%edi
   (cons #x400604 #xef) ;;
   (cons #x400605 #x01) ;;
   (cons #x400606 #x75) ;; jne 400600 <factorial_recursive+0x10>
   (cons #x400607 #xf8) ;;
   (cons #x400608 #xf3) ;; repz retq
   (cons #x400609 #xc3) ;;
   (cons #x40060a #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x40060b #x0f) ;;
   (cons #x40060c #x1f) ;;
   (cons #x40060d #x44) ;;
   (cons #x40060e #x00) ;;
   (cons #x40060f #x00) ;;

   ;; Section: <factorial_iterative>:


   (cons #x400610 #x85) ;; test %edi,%edi
   (cons #x400611 #xff) ;;
   (cons #x400612 #xba) ;; mov $0x1,%edx
   (cons #x400613 #x01) ;;
   (cons #x400614 #x00) ;;
   (cons #x400615 #x00) ;;
   (cons #x400616 #x00) ;;
   (cons #x400617 #xb8) ;; mov $0x1,%eax
   (cons #x400618 #x01) ;;
   (cons #x400619 #x00) ;;
   (cons #x40061a #x00) ;;
   (cons #x40061b #x00) ;;
   (cons #x40061c #x7e) ;; jle 40062a <factorial_iterative+0x1a>
   (cons #x40061d #x0c) ;;
   (cons #x40061e #x66) ;; xchg %ax,%ax
   (cons #x40061f #x90) ;;
   (cons #x400620 #x0f) ;; imul %edx,%eax
   (cons #x400621 #xaf) ;;
   (cons #x400622 #xc2) ;;
   (cons #x400623 #x83) ;; add $0x1,%edx
   (cons #x400624 #xc2) ;;
   (cons #x400625 #x01) ;;
   (cons #x400626 #x39) ;; cmp %edx,%edi
   (cons #x400627 #xd7) ;;
   (cons #x400628 #x7d) ;; jge 400620 <factorial_iterative+0x10>
   (cons #x400629 #xf6) ;;
   (cons #x40062a #xf3) ;; repz retq
   (cons #x40062b #xc3) ;;
   (cons #x40062c #x0f) ;; nopl 0x0(%rax)
   (cons #x40062d #x1f) ;;
   (cons #x40062e #x40) ;;
   (cons #x40062f #x00) ;;

   ;; Section: <fac_aux>:


   (cons #x400630 #x85) ;; test %edi,%edi
   (cons #x400631 #xff) ;;
   (cons #x400632 #x89) ;; mov %esi,%eax
   (cons #x400633 #xf0) ;;
   (cons #x400634 #x7e) ;; jle 400648 <fac_aux+0x18>
   (cons #x400635 #x12) ;;
   (cons #x400636 #x66) ;; nopw %cs:0x0(%rax,%rax,1)
   (cons #x400637 #x2e) ;;
   (cons #x400638 #x0f) ;;
   (cons #x400639 #x1f) ;;
   (cons #x40063a #x84) ;;
   (cons #x40063b #x00) ;;
   (cons #x40063c #x00) ;;
   (cons #x40063d #x00) ;;
   (cons #x40063e #x00) ;;
   (cons #x40063f #x00) ;;
   (cons #x400640 #x0f) ;; imul %edi,%eax
   (cons #x400641 #xaf) ;;
   (cons #x400642 #xc7) ;;
   (cons #x400643 #x83) ;; sub $0x1,%edi
   (cons #x400644 #xef) ;;
   (cons #x400645 #x01) ;;
   (cons #x400646 #x75) ;; jne 400640 <fac_aux+0x10>
   (cons #x400647 #xf8) ;;
   (cons #x400648 #xf3) ;; repz retq
   (cons #x400649 #xc3) ;;
   (cons #x40064a #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x40064b #x0f) ;;
   (cons #x40064c #x1f) ;;
   (cons #x40064d #x44) ;;
   (cons #x40064e #x00) ;;
   (cons #x40064f #x00) ;;

   ;; Section: <factorial_tail_recursive>:


   (cons #x400650 #x85) ;; test %edi,%edi
   (cons #x400651 #xff) ;;
   (cons #x400652 #xb8) ;; mov $0x1,%eax
   (cons #x400653 #x01) ;;
   (cons #x400654 #x00) ;;
   (cons #x400655 #x00) ;;
   (cons #x400656 #x00) ;;
   (cons #x400657 #x7e) ;; jle 400668 <factorial_tail_recursive+0x18>
   (cons #x400658 #x0f) ;;
   (cons #x400659 #x0f) ;; nopl 0x0(%rax)
   (cons #x40065a #x1f) ;;
   (cons #x40065b #x80) ;;
   (cons #x40065c #x00) ;;
   (cons #x40065d #x00) ;;
   (cons #x40065e #x00) ;;
   (cons #x40065f #x00) ;;
   (cons #x400660 #x0f) ;; imul %edi,%eax
   (cons #x400661 #xaf) ;;
   (cons #x400662 #xc7) ;;
   (cons #x400663 #x83) ;; sub $0x1,%edi
   (cons #x400664 #xef) ;;
   (cons #x400665 #x01) ;;
   (cons #x400666 #x75) ;; jne 400660 <factorial_tail_recursive+0x10>
   (cons #x400667 #xf8) ;;
   (cons #x400668 #xf3) ;; repz retq
   (cons #x400669 #xc3) ;;
   (cons #x40066a #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x40066b #x0f) ;;
   (cons #x40066c #x1f) ;;
   (cons #x40066d #x44) ;;
   (cons #x40066e #x00) ;;
   (cons #x40066f #x00) ;;

   ;; Section: <main>:


   (cons #x400670 #x41) ;; push %r12
   (cons #x400671 #x54) ;;
   (cons #x400672 #x83) ;; cmp $0x3,%edi
   (cons #x400673 #xff) ;;
   (cons #x400674 #x03) ;;
   (cons #x400675 #x55) ;; push %rbp
   (cons #x400676 #x48) ;; mov %rsi,%rbp
   (cons #x400677 #x89) ;;
   (cons #x400678 #xf5) ;;
   (cons #x400679 #x53) ;; push %rbx
   (cons #x40067a #x0f) ;; jne 400771 <main+0x101>
   (cons #x40067b #x85) ;;
   (cons #x40067c #xf1) ;;
   (cons #x40067d #x00) ;;
   (cons #x40067e #x00) ;;
   (cons #x40067f #x00) ;;
   (cons #x400680 #x48) ;; mov 0x8(%rsi),%rdi
   (cons #x400681 #x8b) ;;
   (cons #x400682 #x7e) ;;
   (cons #x400683 #x08) ;;
   (cons #x400684 #xba) ;; mov $0xa,%edx
   (cons #x400685 #x0a) ;;
   (cons #x400686 #x00) ;;
   (cons #x400687 #x00) ;;
   (cons #x400688 #x00) ;;
   (cons #x400689 #x31) ;; xor %esi,%esi
   (cons #x40068a #xf6) ;;
   (cons #x40068b #xe8) ;; callq 4004e8 <strtol@plt>
   (cons #x40068c #x58) ;;
   (cons #x40068d #xfe) ;;
   (cons #x40068e #xff) ;;
   (cons #x40068f #xff) ;;
   (cons #x400690 #x48) ;; mov 0x10(%rbp),%rdi
   (cons #x400691 #x8b) ;;
   (cons #x400692 #x7d) ;;
   (cons #x400693 #x10) ;;
   (cons #x400694 #x31) ;; xor %esi,%esi
   (cons #x400695 #xf6) ;;
   (cons #x400696 #xba) ;; mov $0xa,%edx
   (cons #x400697 #x0a) ;;
   (cons #x400698 #x00) ;;
   (cons #x400699 #x00) ;;
   (cons #x40069a #x00) ;;
   (cons #x40069b #x49) ;; mov %rax,%r12
   (cons #x40069c #x89) ;;
   (cons #x40069d #xc4) ;;
   (cons #x40069e #x89) ;; mov %eax,%ebx
   (cons #x40069f #xc3) ;;
   (cons #x4006a0 #xe8) ;; callq 4004e8 <strtol@plt>
   (cons #x4006a1 #x43) ;;
   (cons #x4006a2 #xfe) ;;
   (cons #x4006a3 #xff) ;;
   (cons #x4006a4 #xff) ;;
   (cons #x4006a5 #x85) ;; test %eax,%eax
   (cons #x4006a6 #xc0) ;;
   (cons #x4006a7 #x75) ;; jne 4006f0 <main+0x80>
   (cons #x4006a8 #x47) ;;
   (cons #x4006a9 #x45) ;; test %r12d,%r12d
   (cons #x4006aa #x85) ;;
   (cons #x4006ab #xe4) ;;
   (cons #x4006ac #xb9) ;; mov $0x1,%ecx
   (cons #x4006ad #x01) ;;
   (cons #x4006ae #x00) ;;
   (cons #x4006af #x00) ;;
   (cons #x4006b0 #x00) ;;
   (cons #x4006b1 #x74) ;; je 4006d0 <main+0x60>
   (cons #x4006b2 #x1d) ;;
   (cons #x4006b3 #x31) ;; xor %eax,%eax
   (cons #x4006b4 #xc0) ;;
   (cons #x4006b5 #xb9) ;; mov $0x1,%ecx
   (cons #x4006b6 #x01) ;;
   (cons #x4006b7 #x00) ;;
   (cons #x4006b8 #x00) ;;
   (cons #x4006b9 #x00) ;;
   (cons #x4006ba #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x4006bb #x0f) ;;
   (cons #x4006bc #x1f) ;;
   (cons #x4006bd #x44) ;;
   (cons #x4006be #x00) ;;
   (cons #x4006bf #x00) ;;
   (cons #x4006c0 #x44) ;; mov %r12d,%edx
   (cons #x4006c1 #x89) ;;
   (cons #x4006c2 #xe2) ;;
   (cons #x4006c3 #x29) ;; sub %eax,%edx
   (cons #x4006c4 #xc2) ;;
   (cons #x4006c5 #x83) ;; add $0x1,%eax
   (cons #x4006c6 #xc0) ;;
   (cons #x4006c7 #x01) ;;
   (cons #x4006c8 #x0f) ;; imul %edx,%ecx
   (cons #x4006c9 #xaf) ;;
   (cons #x4006ca #xca) ;;
   (cons #x4006cb #x44) ;; cmp %r12d,%eax
   (cons #x4006cc #x39) ;;
   (cons #x4006cd #xe0) ;;
   (cons #x4006ce #x75) ;; jne 4006c0 <main+0x50>
   (cons #x4006cf #xf0) ;;
   (cons #x4006d0 #x89) ;; mov %ebx,%edx
   (cons #x4006d1 #xda) ;;
   (cons #x4006d2 #xbe) ;; mov $0x400892,%esi
   (cons #x4006d3 #x92) ;;
   (cons #x4006d4 #x08) ;;
   (cons #x4006d5 #x40) ;;
   (cons #x4006d6 #x00) ;;
   (cons #x4006d7 #xbf) ;; mov $0x1,%edi
   (cons #x4006d8 #x01) ;;
   (cons #x4006d9 #x00) ;;
   (cons #x4006da #x00) ;;
   (cons #x4006db #x00) ;;
   (cons #x4006dc #x5b) ;; pop %rbx
   (cons #x4006dd #x5d) ;; pop %rbp
   (cons #x4006de #x41) ;; pop %r12
   (cons #x4006df #x5c) ;;
   (cons #x4006e0 #x31) ;; xor %eax,%eax
   (cons #x4006e1 #xc0) ;;
   (cons #x4006e2 #xe9) ;; jmpq 4004c8 <__printf_chk@plt>
   (cons #x4006e3 #xe1) ;;
   (cons #x4006e4 #xfd) ;;
   (cons #x4006e5 #xff) ;;
   (cons #x4006e6 #xff) ;;
   (cons #x4006e7 #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x4006e8 #x0f) ;;
   (cons #x4006e9 #x1f) ;;
   (cons #x4006ea #x84) ;;
   (cons #x4006eb #x00) ;;
   (cons #x4006ec #x00) ;;
   (cons #x4006ed #x00) ;;
   (cons #x4006ee #x00) ;;
   (cons #x4006ef #x00) ;;
   (cons #x4006f0 #x83) ;; cmp $0x1,%eax
   (cons #x4006f1 #xf8) ;;
   (cons #x4006f2 #x01) ;;
   (cons #x4006f3 #x74) ;; je 400740 <main+0xd0>
   (cons #x4006f4 #x4b) ;;
   (cons #x4006f5 #x45) ;; test %r12d,%r12d
   (cons #x4006f6 #x85) ;;
   (cons #x4006f7 #xe4) ;;
   (cons #x4006f8 #xb9) ;; mov $0x1,%ecx
   (cons #x4006f9 #x01) ;;
   (cons #x4006fa #x00) ;;
   (cons #x4006fb #x00) ;;
   (cons #x4006fc #x00) ;;
   (cons #x4006fd #x7e) ;; jle 400720 <main+0xb0>
   (cons #x4006fe #x21) ;;
   (cons #x4006ff #x31) ;; xor %eax,%eax
   (cons #x400700 #xc0) ;;
   (cons #x400701 #xb9) ;; mov $0x1,%ecx
   (cons #x400702 #x01) ;;
   (cons #x400703 #x00) ;;
   (cons #x400704 #x00) ;;
   (cons #x400705 #x00) ;;
   (cons #x400706 #x66) ;; nopw %cs:0x0(%rax,%rax,1)
   (cons #x400707 #x2e) ;;
   (cons #x400708 #x0f) ;;
   (cons #x400709 #x1f) ;;
   (cons #x40070a #x84) ;;
   (cons #x40070b #x00) ;;
   (cons #x40070c #x00) ;;
   (cons #x40070d #x00) ;;
   (cons #x40070e #x00) ;;
   (cons #x40070f #x00) ;;
   (cons #x400710 #x44) ;; mov %r12d,%edx
   (cons #x400711 #x89) ;;
   (cons #x400712 #xe2) ;;
   (cons #x400713 #x29) ;; sub %eax,%edx
   (cons #x400714 #xc2) ;;
   (cons #x400715 #x83) ;; add $0x1,%eax
   (cons #x400716 #xc0) ;;
   (cons #x400717 #x01) ;;
   (cons #x400718 #x0f) ;; imul %edx,%ecx
   (cons #x400719 #xaf) ;;
   (cons #x40071a #xca) ;;
   (cons #x40071b #x44) ;; cmp %r12d,%eax
   (cons #x40071c #x39) ;;
   (cons #x40071d #xe0) ;;
   (cons #x40071e #x75) ;; jne 400710 <main+0xa0>
   (cons #x40071f #xf0) ;;
   (cons #x400720 #x89) ;; mov %ebx,%edx
   (cons #x400721 #xda) ;;
   (cons #x400722 #xbe) ;; mov $0x4008c3,%esi
   (cons #x400723 #xc3) ;;
   (cons #x400724 #x08) ;;
   (cons #x400725 #x40) ;;
   (cons #x400726 #x00) ;;
   (cons #x400727 #xbf) ;; mov $0x1,%edi
   (cons #x400728 #x01) ;;
   (cons #x400729 #x00) ;;
   (cons #x40072a #x00) ;;
   (cons #x40072b #x00) ;;
   (cons #x40072c #x5b) ;; pop %rbx
   (cons #x40072d #x5d) ;; pop %rbp
   (cons #x40072e #x41) ;; pop %r12
   (cons #x40072f #x5c) ;;
   (cons #x400730 #x31) ;; xor %eax,%eax
   (cons #x400731 #xc0) ;;
   (cons #x400732 #xe9) ;; jmpq 4004c8 <__printf_chk@plt>
   (cons #x400733 #x91) ;;
   (cons #x400734 #xfd) ;;
   (cons #x400735 #xff) ;;
   (cons #x400736 #xff) ;;
   (cons #x400737 #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x400738 #x0f) ;;
   (cons #x400739 #x1f) ;;
   (cons #x40073a #x84) ;;
   (cons #x40073b #x00) ;;
   (cons #x40073c #x00) ;;
   (cons #x40073d #x00) ;;
   (cons #x40073e #x00) ;;
   (cons #x40073f #x00) ;;
   (cons #x400740 #x45) ;; test %r12d,%r12d
   (cons #x400741 #x85) ;;
   (cons #x400742 #xe4) ;;
   (cons #x400743 #xb9) ;; mov $0x1,%ecx
   (cons #x400744 #x01) ;;
   (cons #x400745 #x00) ;;
   (cons #x400746 #x00) ;;
   (cons #x400747 #x00) ;;
   (cons #x400748 #x7e) ;; jle 40075a <main+0xea>
   (cons #x400749 #x10) ;;
   (cons #x40074a #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x40074b #x0f) ;;
   (cons #x40074c #x1f) ;;
   (cons #x40074d #x44) ;;
   (cons #x40074e #x00) ;;
   (cons #x40074f #x00) ;;
   (cons #x400750 #x0f) ;; imul %eax,%ecx
   (cons #x400751 #xaf) ;;
   (cons #x400752 #xc8) ;;
   (cons #x400753 #x83) ;; add $0x1,%eax
   (cons #x400754 #xc0) ;;
   (cons #x400755 #x01) ;;
   (cons #x400756 #x39) ;; cmp %eax,%ebx
   (cons #x400757 #xc3) ;;
   (cons #x400758 #x7d) ;; jge 400750 <main+0xe0>
   (cons #x400759 #xf6) ;;
   (cons #x40075a #x89) ;; mov %ebx,%edx
   (cons #x40075b #xda) ;;
   (cons #x40075c #xbe) ;; mov $0x4008ab,%esi
   (cons #x40075d #xab) ;;
   (cons #x40075e #x08) ;;
   (cons #x40075f #x40) ;;
   (cons #x400760 #x00) ;;
   (cons #x400761 #xbf) ;; mov $0x1,%edi
   (cons #x400762 #x01) ;;
   (cons #x400763 #x00) ;;
   (cons #x400764 #x00) ;;
   (cons #x400765 #x00) ;;
   (cons #x400766 #x5b) ;; pop %rbx
   (cons #x400767 #x5d) ;; pop %rbp
   (cons #x400768 #x41) ;; pop %r12
   (cons #x400769 #x5c) ;;
   (cons #x40076a #x31) ;; xor %eax,%eax
   (cons #x40076b #xc0) ;;
   (cons #x40076c #xe9) ;; jmpq 4004c8 <__printf_chk@plt>
   (cons #x40076d #x57) ;;
   (cons #x40076e #xfd) ;;
   (cons #x40076f #xff) ;;
   (cons #x400770 #xff) ;;
   (cons #x400771 #xbf) ;; mov $0x1,%edi
   (cons #x400772 #x01) ;;
   (cons #x400773 #x00) ;;
   (cons #x400774 #x00) ;;
   (cons #x400775 #x00) ;;
   (cons #x400776 #xbe) ;; mov $0x40087c,%esi
   (cons #x400777 #x7c) ;;
   (cons #x400778 #x08) ;;
   (cons #x400779 #x40) ;;
   (cons #x40077a #x00) ;;
   (cons #x40077b #x31) ;; xor %eax,%eax
   (cons #x40077c #xc0) ;;
   (cons #x40077d #xe8) ;; callq 4004c8 <__printf_chk@plt>
   (cons #x40077e #x46) ;;
   (cons #x40077f #xfd) ;;
   (cons #x400780 #xff) ;;
   (cons #x400781 #xff) ;;
   (cons #x400782 #xbf) ;; mov $0x1,%edi
   (cons #x400783 #x01) ;;
   (cons #x400784 #x00) ;;
   (cons #x400785 #x00) ;;
   (cons #x400786 #x00) ;;
   (cons #x400787 #xe8) ;; callq 4004b8 <exit@plt>
   (cons #x400788 #x2c) ;;
   (cons #x400789 #xfd) ;;
   (cons #x40078a #xff) ;;
   (cons #x40078b #xff) ;;
   (cons #x40078c #x90) ;; nop
   (cons #x40078d #x90) ;; nop
   (cons #x40078e #x90) ;; nop
   (cons #x40078f #x90) ;; nop

   ;; Section: <__libc_csu_fini>:


   (cons #x400790 #xf3) ;; repz retq
   (cons #x400791 #xc3) ;;
   (cons #x400792 #x66) ;; nopw %cs:0x0(%rax,%rax,1)
   (cons #x400793 #x66) ;;
   (cons #x400794 #x66) ;;
   (cons #x400795 #x66) ;;
   (cons #x400796 #x66) ;;
   (cons #x400797 #x2e) ;;
   (cons #x400798 #x0f) ;;
   (cons #x400799 #x1f) ;;
   (cons #x40079a #x84) ;;
   (cons #x40079b #x00) ;;
   (cons #x40079c #x00) ;;
   (cons #x40079d #x00) ;;
   (cons #x40079e #x00) ;;
   (cons #x40079f #x00) ;;

   ;; Section: <__libc_csu_init>:


   (cons #x4007a0 #x48) ;; mov %rbp,-0x28(%rsp)
   (cons #x4007a1 #x89) ;;
   (cons #x4007a2 #x6c) ;;
   (cons #x4007a3 #x24) ;;
   (cons #x4007a4 #xd8) ;;
   (cons #x4007a5 #x4c) ;; mov %r12,-0x20(%rsp)
   (cons #x4007a6 #x89) ;;
   (cons #x4007a7 #x64) ;;
   (cons #x4007a8 #x24) ;;
   (cons #x4007a9 #xe0) ;;
   (cons #x4007aa #x48) ;; lea 0x200663(%rip),%rbp # 600e14 <__init_array_end>
   (cons #x4007ab #x8d) ;;
   (cons #x4007ac #x2d) ;;
   (cons #x4007ad #x63) ;;
   (cons #x4007ae #x06) ;;
   (cons #x4007af #x20) ;;
   (cons #x4007b0 #x00) ;;
   (cons #x4007b1 #x4c) ;; lea 0x20065c(%rip),%r12 # 600e14 <__init_array_end>
   (cons #x4007b2 #x8d) ;;
   (cons #x4007b3 #x25) ;;
   (cons #x4007b4 #x5c) ;;
   (cons #x4007b5 #x06) ;;
   (cons #x4007b6 #x20) ;;
   (cons #x4007b7 #x00) ;;
   (cons #x4007b8 #x4c) ;; mov %r13,-0x18(%rsp)
   (cons #x4007b9 #x89) ;;
   (cons #x4007ba #x6c) ;;
   (cons #x4007bb #x24) ;;
   (cons #x4007bc #xe8) ;;
   (cons #x4007bd #x4c) ;; mov %r14,-0x10(%rsp)
   (cons #x4007be #x89) ;;
   (cons #x4007bf #x74) ;;
   (cons #x4007c0 #x24) ;;
   (cons #x4007c1 #xf0) ;;
   (cons #x4007c2 #x4c) ;; mov %r15,-0x8(%rsp)
   (cons #x4007c3 #x89) ;;
   (cons #x4007c4 #x7c) ;;
   (cons #x4007c5 #x24) ;;
   (cons #x4007c6 #xf8) ;;
   (cons #x4007c7 #x48) ;; mov %rbx,-0x30(%rsp)
   (cons #x4007c8 #x89) ;;
   (cons #x4007c9 #x5c) ;;
   (cons #x4007ca #x24) ;;
   (cons #x4007cb #xd0) ;;
   (cons #x4007cc #x48) ;; sub $0x38,%rsp
   (cons #x4007cd #x83) ;;
   (cons #x4007ce #xec) ;;
   (cons #x4007cf #x38) ;;
   (cons #x4007d0 #x4c) ;; sub %r12,%rbp
   (cons #x4007d1 #x29) ;;
   (cons #x4007d2 #xe5) ;;
   (cons #x4007d3 #x41) ;; mov %edi,%r13d
   (cons #x4007d4 #x89) ;;
   (cons #x4007d5 #xfd) ;;
   (cons #x4007d6 #x49) ;; mov %rsi,%r14
   (cons #x4007d7 #x89) ;;
   (cons #x4007d8 #xf6) ;;
   (cons #x4007d9 #x48) ;; sar $0x3,%rbp
   (cons #x4007da #xc1) ;;
   (cons #x4007db #xfd) ;;
   (cons #x4007dc #x03) ;;
   (cons #x4007dd #x49) ;; mov %rdx,%r15
   (cons #x4007de #x89) ;;
   (cons #x4007df #xd7) ;;
   (cons #x4007e0 #xe8) ;; callq 400490 <_init>
   (cons #x4007e1 #xab) ;;
   (cons #x4007e2 #xfc) ;;
   (cons #x4007e3 #xff) ;;
   (cons #x4007e4 #xff) ;;
   (cons #x4007e5 #x48) ;; test %rbp,%rbp
   (cons #x4007e6 #x85) ;;
   (cons #x4007e7 #xed) ;;
   (cons #x4007e8 #x74) ;; je 400806 <__libc_csu_init+0x66>
   (cons #x4007e9 #x1c) ;;
   (cons #x4007ea #x31) ;; xor %ebx,%ebx
   (cons #x4007eb #xdb) ;;
   (cons #x4007ec #x0f) ;; nopl 0x0(%rax)
   (cons #x4007ed #x1f) ;;
   (cons #x4007ee #x40) ;;
   (cons #x4007ef #x00) ;;
   (cons #x4007f0 #x4c) ;; mov %r15,%rdx
   (cons #x4007f1 #x89) ;;
   (cons #x4007f2 #xfa) ;;
   (cons #x4007f3 #x4c) ;; mov %r14,%rsi
   (cons #x4007f4 #x89) ;;
   (cons #x4007f5 #xf6) ;;
   (cons #x4007f6 #x44) ;; mov %r13d,%edi
   (cons #x4007f7 #x89) ;;
   (cons #x4007f8 #xef) ;;
   (cons #x4007f9 #x41) ;; callq *(%r12,%rbx,8)
   (cons #x4007fa #xff) ;;
   (cons #x4007fb #x14) ;;
   (cons #x4007fc #xdc) ;;
   (cons #x4007fd #x48) ;; add $0x1,%rbx
   (cons #x4007fe #x83) ;;
   (cons #x4007ff #xc3) ;;
   (cons #x400800 #x01) ;;
   (cons #x400801 #x48) ;; cmp %rbp,%rbx
   (cons #x400802 #x39) ;;
   (cons #x400803 #xeb) ;;
   (cons #x400804 #x72) ;; jb 4007f0 <__libc_csu_init+0x50>
   (cons #x400805 #xea) ;;
   (cons #x400806 #x48) ;; mov 0x8(%rsp),%rbx
   (cons #x400807 #x8b) ;;
   (cons #x400808 #x5c) ;;
   (cons #x400809 #x24) ;;
   (cons #x40080a #x08) ;;
   (cons #x40080b #x48) ;; mov 0x10(%rsp),%rbp
   (cons #x40080c #x8b) ;;
   (cons #x40080d #x6c) ;;
   (cons #x40080e #x24) ;;
   (cons #x40080f #x10) ;;
   (cons #x400810 #x4c) ;; mov 0x18(%rsp),%r12
   (cons #x400811 #x8b) ;;
   (cons #x400812 #x64) ;;
   (cons #x400813 #x24) ;;
   (cons #x400814 #x18) ;;
   (cons #x400815 #x4c) ;; mov 0x20(%rsp),%r13
   (cons #x400816 #x8b) ;;
   (cons #x400817 #x6c) ;;
   (cons #x400818 #x24) ;;
   (cons #x400819 #x20) ;;
   (cons #x40081a #x4c) ;; mov 0x28(%rsp),%r14
   (cons #x40081b #x8b) ;;
   (cons #x40081c #x74) ;;
   (cons #x40081d #x24) ;;
   (cons #x40081e #x28) ;;
   (cons #x40081f #x4c) ;; mov 0x30(%rsp),%r15
   (cons #x400820 #x8b) ;;
   (cons #x400821 #x7c) ;;
   (cons #x400822 #x24) ;;
   (cons #x400823 #x30) ;;
   (cons #x400824 #x48) ;; add $0x38,%rsp
   (cons #x400825 #x83) ;;
   (cons #x400826 #xc4) ;;
   (cons #x400827 #x38) ;;
   (cons #x400828 #xc3) ;; retq
   (cons #x400829 #x90) ;; nop
   (cons #x40082a #x90) ;; nop
   (cons #x40082b #x90) ;; nop
   (cons #x40082c #x90) ;; nop
   (cons #x40082d #x90) ;; nop
   (cons #x40082e #x90) ;; nop
   (cons #x40082f #x90) ;; nop

   ;; Section: <__do_global_ctors_aux>:


   (cons #x400830 #x55) ;; push %rbp
   (cons #x400831 #x48) ;; mov %rsp,%rbp
   (cons #x400832 #x89) ;;
   (cons #x400833 #xe5) ;;
   (cons #x400834 #x53) ;; push %rbx
   (cons #x400835 #x48) ;; sub $0x8,%rsp
   (cons #x400836 #x83) ;;
   (cons #x400837 #xec) ;;
   (cons #x400838 #x08) ;;
   (cons #x400839 #x48) ;; mov 0x2005d8(%rip),%rax # 600e18 <__CTOR_LIST__>
   (cons #x40083a #x8b) ;;
   (cons #x40083b #x05) ;;
   (cons #x40083c #xd8) ;;
   (cons #x40083d #x05) ;;
   (cons #x40083e #x20) ;;
   (cons #x40083f #x00) ;;
   (cons #x400840 #x48) ;; cmp $0xffffffffffffffff,%rax
   (cons #x400841 #x83) ;;
   (cons #x400842 #xf8) ;;
   (cons #x400843 #xff) ;;
   (cons #x400844 #x74) ;; je 40085f <__do_global_ctors_aux+0x2f>
   (cons #x400845 #x19) ;;
   (cons #x400846 #xbb) ;; mov $0x600e18,%ebx
   (cons #x400847 #x18) ;;
   (cons #x400848 #x0e) ;;
   (cons #x400849 #x60) ;;
   (cons #x40084a #x00) ;;
   (cons #x40084b #x0f) ;; nopl 0x0(%rax,%rax,1)
   (cons #x40084c #x1f) ;;
   (cons #x40084d #x44) ;;
   (cons #x40084e #x00) ;;
   (cons #x40084f #x00) ;;
   (cons #x400850 #x48) ;; sub $0x8,%rbx
   (cons #x400851 #x83) ;;
   (cons #x400852 #xeb) ;;
   (cons #x400853 #x08) ;;
   (cons #x400854 #xff) ;; callq *%rax
   (cons #x400855 #xd0) ;;
   (cons #x400856 #x48) ;; mov (%rbx),%rax
   (cons #x400857 #x8b) ;;
   (cons #x400858 #x03) ;;
   (cons #x400859 #x48) ;; cmp $0xffffffffffffffff,%rax
   (cons #x40085a #x83) ;;
   (cons #x40085b #xf8) ;;
   (cons #x40085c #xff) ;;
   (cons #x40085d #x75) ;; jne 400850 <__do_global_ctors_aux+0x20>
   (cons #x40085e #xf1) ;;
   (cons #x40085f #x48) ;; add $0x8,%rsp
   (cons #x400860 #x83) ;;
   (cons #x400861 #xc4) ;;
   (cons #x400862 #x08) ;;
   (cons #x400863 #x5b) ;; pop %rbx
   (cons #x400864 #xc9) ;; leaveq
   (cons #x400865 #xc3) ;; retq
   (cons #x400866 #x90) ;; nop
   (cons #x400867 #x90) ;; nop

   ;; Section: <_fini>:


   (cons #x400868 #x48) ;; sub $0x8,%rsp
   (cons #x400869 #x83) ;;
   (cons #x40086a #xec) ;;
   (cons #x40086b #x08) ;;
   (cons #x40086c #xe8) ;; callq 400550 <__do_global_dtors_aux>
   (cons #x40086d #xdf) ;;
   (cons #x40086e #xfc) ;;
   (cons #x40086f #xff) ;;
   (cons #x400870 #xff) ;;
   (cons #x400871 #x48) ;; add $0x8,%rsp
   (cons #x400872 #x83) ;;
   (cons #x400873 #xc4) ;;
   (cons #x400874 #x08) ;;
   (cons #x400875 #xc3) ;; retq

   ;; Section: <_IO_stdin_used>:


   (cons #x400878 #x01) ;; add %eax,(%rax)
   (cons #x400879 #x00) ;;
   (cons #x40087a #x02) ;; add (%rax),%al
   (cons #x40087b #x00) ;;
   (cons #x40087c #x45) ;; rex.RB jb 4008f1 <_IO_stdin_used+0x79>
   (cons #x40087d #x72) ;;
   (cons #x40087e #x72) ;;
   (cons #x40087f #x6f) ;; outsl %ds:(%rsi),(%dx)
   (cons #x400880 #x72) ;; jb 4008bc <_IO_stdin_used+0x44>
   (cons #x400881 #x3a) ;;
   (cons #x400882 #x20) ;; and %cl,0x65(%rsi)
   (cons #x400883 #x4e) ;;
   (cons #x400884 #x65) ;;
   (cons #x400885 #x65) ;; and %dh,%fs:%gs:0x6f(%rdi,%rsi,2)
   (cons #x400886 #x64) ;;
   (cons #x400887 #x20) ;;
   (cons #x400888 #x74) ;;
   (cons #x400889 #x77) ;;
   (cons #x40088a #x6f) ;;
   (cons #x40088b #x20) ;; and %ah,0x72(%rcx)
   (cons #x40088c #x61) ;;
   (cons #x40088d #x72) ;;
   (cons #x40088e #x67) ;; addr32 or %cs:(%eax),%al
   (cons #x40088f #x2e) ;;
   (cons #x400890 #x0a) ;;
   (cons #x400891 #x00) ;;
   (cons #x400892 #x66) ;; data16
   (cons #x400893 #x61) ;; (bad)
   (cons #x400894 #x63) ;; movslq 0x72(%rdi,%rbx,2),%esi
   (cons #x400895 #x74) ;;
   (cons #x400896 #x5f) ;;
   (cons #x400897 #x72) ;;
   (cons #x400898 #x65) ;; movslq %gs:0x72(%rbp),%esi
   (cons #x400899 #x63) ;;
   (cons #x40089a #x75) ;;
   (cons #x40089b #x72) ;;
   (cons #x40089c #x73) ;; jae 400907 <_IO_stdin_used+0x8f>
   (cons #x40089d #x69) ;;
   (cons #x40089e #x76) ;; jbe 400905 <_IO_stdin_used+0x8d>
   (cons #x40089f #x65) ;;
   (cons #x4008a0 #x28) ;; sub %ah,0x3d202964(%rip) # 3d60320a <_end+0x3d0021ca>
   (cons #x4008a1 #x25) ;;
   (cons #x4008a2 #x64) ;;
   (cons #x4008a3 #x29) ;;
   (cons #x4008a4 #x20) ;;
   (cons #x4008a5 #x3d) ;;
   (cons #x4008a6 #x20) ;; and %ah,0x66000a64(%rip) # 66401310 <_end+0x65e002d0>
   (cons #x4008a7 #x25) ;;
   (cons #x4008a8 #x64) ;;
   (cons #x4008a9 #x0a) ;;
   (cons #x4008aa #x00) ;;
   (cons #x4008ab #x66) ;;
   (cons #x4008ac #x61) ;; (bad)
   (cons #x4008ad #x63) ;; movslq 0x74(%rcx,%rbp,2),%esi
   (cons #x4008ae #x74) ;;
   (cons #x4008af #x69) ;;
   (cons #x4008b0 #x74) ;;
   (cons #x4008b1 #x65) ;; gs
   (cons #x4008b2 #x72) ;; jb 400915 <_IO_stdin_used+0x9d>
   (cons #x4008b3 #x61) ;;
   (cons #x4008b4 #x74) ;; je 40091f <_IO_stdin_used+0xa7>
   (cons #x4008b5 #x69) ;;
   (cons #x4008b6 #x76) ;; jbe 40091d <_IO_stdin_used+0xa5>
   (cons #x4008b7 #x65) ;;
   (cons #x4008b8 #x28) ;; sub %ah,0x3d202964(%rip) # 3d603222 <_end+0x3d0021e2>
   (cons #x4008b9 #x25) ;;
   (cons #x4008ba #x64) ;;
   (cons #x4008bb #x29) ;;
   (cons #x4008bc #x20) ;;
   (cons #x4008bd #x3d) ;;
   (cons #x4008be #x20) ;; and %ah,0x66000a64(%rip) # 66401328 <_end+0x65e002e8>
   (cons #x4008bf #x25) ;;
   (cons #x4008c0 #x64) ;;
   (cons #x4008c1 #x0a) ;;
   (cons #x4008c2 #x00) ;;
   (cons #x4008c3 #x66) ;;
   (cons #x4008c4 #x61) ;; (bad)
   (cons #x4008c5 #x63) ;; movslq 0x74(%rdi,%rbx,2),%esi
   (cons #x4008c6 #x74) ;;
   (cons #x4008c7 #x5f) ;;
   (cons #x4008c8 #x74) ;;
   (cons #x4008c9 #x61) ;; (bad)
   (cons #x4008ca #x69) ;; imul $0x72756365,0x72(%rdi,%rbx,2),%ebp
   (cons #x4008cb #x6c) ;;
   (cons #x4008cc #x5f) ;;
   (cons #x4008cd #x72) ;;
   (cons #x4008ce #x65) ;;
   (cons #x4008cf #x63) ;;
   (cons #x4008d0 #x75) ;;
   (cons #x4008d1 #x72) ;;
   (cons #x4008d2 #x73) ;; jae 40093d <_IO_stdin_used+0xc5>
   (cons #x4008d3 #x69) ;;
   (cons #x4008d4 #x76) ;; jbe 40093b <_IO_stdin_used+0xc3>
   (cons #x4008d5 #x65) ;;
   (cons #x4008d6 #x28) ;; sub %ah,0x3d202964(%rip) # 3d603240 <_end+0x3d002200>
   (cons #x4008d7 #x25) ;;
   (cons #x4008d8 #x64) ;;
   (cons #x4008d9 #x29) ;;
   (cons #x4008da #x20) ;;
   (cons #x4008db #x3d) ;;
   (cons #x4008dc #x20) ;; .byte 0x20
   (cons #x4008dd #x25) ;; .byte 0x25
   (cons #x4008de #x64) ;; or %fs:(%rax),%al
   (cons #x4008df #x0a) ;;
   (cons #x4008e0 #x00) ;;

   ;; Section: <.eh_frame_hdr>:


   (cons #x4008e4 #x01) ;; add %ebx,(%rbx)
   (cons #x4008e5 #x1b) ;;
   (cons #x4008e6 #x03) ;; add (%rbx),%edi
   (cons #x4008e7 #x3b) ;;
   (cons #x4008e8 #x40) ;; add %al,(%rax)
   (cons #x4008e9 #x00) ;;
   (cons #x4008ea #x00) ;;
   (cons #x4008eb #x00) ;; add %al,(%rdi)
   (cons #x4008ec #x07) ;;
   (cons #x4008ed #x00) ;; add %al,(%rax)
   (cons #x4008ee #x00) ;;
   (cons #x4008ef #x00) ;; add %cl,0x5cffff(,%rdi,8)
   (cons #x4008f0 #x0c) ;;
   (cons #x4008f1 #xfd) ;;
   (cons #x4008f2 #xff) ;;
   (cons #x4008f3 #xff) ;;
   (cons #x4008f4 #x5c) ;;
   (cons #x4008f5 #x00) ;;
   (cons #x4008f6 #x00) ;; add %al,(%rax)
   (cons #x4008f7 #x00) ;;
   (cons #x4008f8 #x2c) ;; sub $0xfd,%al
   (cons #x4008f9 #xfd) ;;
   (cons #x4008fa #xff) ;; (bad)
   (cons #x4008fb #xff) ;; pushq 0x0(%rax,%rax,1)
   (cons #x4008fc #x74) ;;
   (cons #x4008fd #x00) ;;
   (cons #x4008fe #x00) ;;
   (cons #x4008ff #x00) ;; add %cl,-0x1(%rbp,%rdi,8)
   (cons #x400900 #x4c) ;;
   (cons #x400901 #xfd) ;;
   (cons #x400902 #xff) ;;
   (cons #x400903 #xff) ;; decl -0x2940000(%rax,%rax,1)
   (cons #x400904 #x8c) ;;
   (cons #x400905 #x00) ;;
   (cons #x400906 #x00) ;;
   (cons #x400907 #x00) ;;
   (cons #x400908 #x6c) ;;
   (cons #x400909 #xfd) ;;
   (cons #x40090a #xff) ;; (bad)
   (cons #x40090b #xff) ;; jmpq *-0x2740000(%rax,%rax,1)
   (cons #x40090c #xa4) ;;
   (cons #x40090d #x00) ;;
   (cons #x40090e #x00) ;;
   (cons #x40090f #x00) ;;
   (cons #x400910 #x8c) ;;
   (cons #x400911 #xfd) ;;
   (cons #x400912 #xff) ;; (bad)
   (cons #x400913 #xff) ;; (bad)
   (cons #x400914 #xbc) ;; mov $0xac000000,%esp
   (cons #x400915 #x00) ;;
   (cons #x400916 #x00) ;;
   (cons #x400917 #x00) ;;
   (cons #x400918 #xac) ;;
   (cons #x400919 #xfe) ;; (bad)
   (cons #x40091a #xff) ;; (bad)
   (cons #x40091b #xff) ;; jmpq *%rsp
   (cons #x40091c #xe4) ;;
   (cons #x40091d #x00) ;; add %al,(%rax)
   (cons #x40091e #x00) ;;
   (cons #x40091f #x00) ;; add %bh,0xfcffff(%rsi,%rdi,8)
   (cons #x400920 #xbc) ;;
   (cons #x400921 #xfe) ;;
   (cons #x400922 #xff) ;;
   (cons #x400923 #xff) ;;
   (cons #x400924 #xfc) ;;
   (cons #x400925 #x00) ;;

   ;; Section: <__FRAME_END__-0xe0>:


   (cons #x400928 #x14) ;; adc $0x0,%al
   (cons #x400929 #x00) ;;
   (cons #x40092a #x00) ;; add %al,(%rax)
   (cons #x40092b #x00) ;;
   (cons #x40092c #x00) ;; add %al,(%rax)
   (cons #x40092d #x00) ;;
   (cons #x40092e #x00) ;; add %al,(%rax)
   (cons #x40092f #x00) ;;
   (cons #x400930 #x01) ;; add %edi,0x52(%rdx)
   (cons #x400931 #x7a) ;;
   (cons #x400932 #x52) ;;
   (cons #x400933 #x00) ;; add %al,(%rcx)
   (cons #x400934 #x01) ;;
   (cons #x400935 #x78) ;; js 400947 <_IO_stdin_used+0xcf>
   (cons #x400936 #x10) ;;
   (cons #x400937 #x01) ;; add %ebx,(%rbx)
   (cons #x400938 #x1b) ;;
   (cons #x400939 #x0c) ;; or $0x7,%al
   (cons #x40093a #x07) ;;
   (cons #x40093b #x08) ;; or %dl,0x14000001(%rax)
   (cons #x40093c #x90) ;;
   (cons #x40093d #x01) ;;
   (cons #x40093e #x00) ;;
   (cons #x40093f #x00) ;;
   (cons #x400940 #x14) ;;
   (cons #x400941 #x00) ;; add %al,(%rax)
   (cons #x400942 #x00) ;;
   (cons #x400943 #x00) ;; add %bl,(%rax,%rax,1)
   (cons #x400944 #x1c) ;;
   (cons #x400945 #x00) ;;
   (cons #x400946 #x00) ;; add %al,(%rax)
   (cons #x400947 #x00) ;;
   (cons #x400948 #xa8) ;; test $0xfc,%al
   (cons #x400949 #xfc) ;;
   (cons #x40094a #xff) ;; (bad)
   (cons #x40094b #xff) ;; lcallq *(%rdx)
   (cons #x40094c #x1a) ;;

   ;; Section: <__FRAME_END__>:


   (cons #x400a08 #x00) ;; add %al,(%rax)
   (cons #x400a09 #x00) ;;

   ;; Section: <__CTOR_LIST__>:


   (cons #x600e18 #xff) ;; (bad)
   (cons #x600e19 #xff) ;; (bad)
   (cons #x600e1a #xff) ;; (bad)
   (cons #x600e1b #xff) ;; (bad)
   (cons #x600e1c #xff) ;; (bad)
   (cons #x600e1d #xff) ;; (bad)
   (cons #x600e1e #xff) ;; (bad)
   (cons #x600e1f #xff) ;; incl (%rax)
   (cons #x600e20 #x00) ;;

   ;; Section: <__CTOR_END__>:



   ;; Section: <__DTOR_LIST__>:


   (cons #x600e28 #xff) ;; (bad)
   (cons #x600e29 #xff) ;; (bad)
   (cons #x600e2a #xff) ;; (bad)
   (cons #x600e2b #xff) ;; (bad)
   (cons #x600e2c #xff) ;; (bad)
   (cons #x600e2d #xff) ;; (bad)
   (cons #x600e2e #xff) ;; (bad)
   (cons #x600e2f #xff) ;; incl (%rax)
   (cons #x600e30 #x00) ;;

   ;; Section: <__JCR_END__>:



   ;; Section: <_DYNAMIC>:


   (cons #x600e40 #x01) ;; add %eax,(%rax)
   (cons #x600e41 #x00) ;;
   (cons #x600e42 #x00) ;; add %al,(%rax)
   (cons #x600e43 #x00) ;;
   (cons #x600e44 #x00) ;; add %al,(%rax)
   (cons #x600e45 #x00) ;;
   (cons #x600e46 #x00) ;; add %al,(%rax)
   (cons #x600e47 #x00) ;;
   (cons #x600e48 #x10) ;; adc %al,(%rax)
   (cons #x600e49 #x00) ;;
   (cons #x600e4a #x00) ;; add %al,(%rax)
   (cons #x600e4b #x00) ;;
   (cons #x600e4c #x00) ;; add %al,(%rax)
   (cons #x600e4d #x00) ;;
   (cons #x600e4e #x00) ;; add %al,(%rax)
   (cons #x600e4f #x00) ;;
   (cons #x600e50 #x0c) ;; or $0x0,%al
   (cons #x600e51 #x00) ;;
   (cons #x600e52 #x00) ;; add %al,(%rax)
   (cons #x600e53 #x00) ;;
   (cons #x600e54 #x00) ;; add %al,(%rax)
   (cons #x600e55 #x00) ;;
   (cons #x600e56 #x00) ;; add %al,(%rax)
   (cons #x600e57 #x00) ;;
   (cons #x600e58 #x90) ;; nop
   (cons #x600e59 #x04) ;; add $0x40,%al
   (cons #x600e5a #x40) ;;
   (cons #x600e5b #x00) ;; add %al,(%rax)
   (cons #x600e5c #x00) ;;
   (cons #x600e5d #x00) ;; add %al,(%rax)
   (cons #x600e5e #x00) ;;
   (cons #x600e5f #x00) ;; add %cl,0x0(%rip) # 600e65 <_DYNAMIC+0x25>
   (cons #x600e60 #x0d) ;;
   (cons #x600e61 #x00) ;;
   (cons #x600e62 #x00) ;;
   (cons #x600e63 #x00) ;;
   (cons #x600e64 #x00) ;;
   (cons #x600e65 #x00) ;; add %al,(%rax)
   (cons #x600e66 #x00) ;;
   (cons #x600e67 #x00) ;; add %ch,0x8(%rax)
   (cons #x600e68 #x68) ;;
   (cons #x600e69 #x08) ;;
   (cons #x600e6a #x40) ;; add %al,(%rax)
   (cons #x600e6b #x00) ;;
   (cons #x600e6c #x00) ;;
   (cons #x600e6d #x00) ;; add %al,(%rax)
   (cons #x600e6e #x00) ;;
   (cons #x600e6f #x00) ;; add %al,(%rax,%rax,1)
   (cons #x600e70 #x04) ;;
   (cons #x600e71 #x00) ;;
   (cons #x600e72 #x00) ;; add %al,(%rax)
   (cons #x600e73 #x00) ;;
   (cons #x600e74 #x00) ;; add %al,(%rax)
   (cons #x600e75 #x00) ;;
   (cons #x600e76 #x00) ;; add %al,(%rax)
   (cons #x600e77 #x00) ;;
   (cons #x600e78 #x98) ;; cwtl
   (cons #x600e79 #x02) ;; add 0x0(%rax),%al
   (cons #x600e7a #x40) ;;
   (cons #x600e7b #x00) ;;
   (cons #x600e7c #x00) ;; add %al,(%rax)
   (cons #x600e7d #x00) ;;
   (cons #x600e7e #x00) ;; add %al,(%rax)
   (cons #x600e7f #x00) ;;
   (cons #x600e80 #xf5) ;; cmc
   (cons #x600e81 #xfe) ;; (bad)
   (cons #x600e82 #xff) ;; ljmpq *0x0(%rdi)
   (cons #x600e83 #x6f) ;;
   (cons #x600e84 #x00) ;;
   (cons #x600e85 #x00) ;; add %al,(%rax)
   (cons #x600e86 #x00) ;;
   (cons #x600e87 #x00) ;; add %cl,%al
   (cons #x600e88 #xc8) ;;
   (cons #x600e89 #x02) ;; add 0x0(%rax),%al
   (cons #x600e8a #x40) ;;
   (cons #x600e8b #x00) ;;
   (cons #x600e8c #x00) ;; add %al,(%rax)
   (cons #x600e8d #x00) ;;
   (cons #x600e8e #x00) ;; add %al,(%rax)
   (cons #x600e8f #x00) ;;
   (cons #x600e90 #x05) ;; add $0x0,%eax
   (cons #x600e91 #x00) ;;
   (cons #x600e92 #x00) ;;
   (cons #x600e93 #x00) ;;
   (cons #x600e94 #x00) ;;
   (cons #x600e95 #x00) ;; add %al,(%rax)
   (cons #x600e96 #x00) ;;
   (cons #x600e97 #x00) ;; add %bh,0x3(%rax)
   (cons #x600e98 #x78) ;;
   (cons #x600e99 #x03) ;;
   (cons #x600e9a #x40) ;; add %al,(%rax)
   (cons #x600e9b #x00) ;;
   (cons #x600e9c #x00) ;;
   (cons #x600e9d #x00) ;; add %al,(%rax)
   (cons #x600e9e #x00) ;;
   (cons #x600e9f #x00) ;; add %al,(%rsi)
   (cons #x600ea0 #x06) ;;
   (cons #x600ea1 #x00) ;; add %al,(%rax)
   (cons #x600ea2 #x00) ;;
   (cons #x600ea3 #x00) ;; add %al,(%rax)
   (cons #x600ea4 #x00) ;;
   (cons #x600ea5 #x00) ;; add %al,(%rax)
   (cons #x600ea6 #x00) ;;
   (cons #x600ea7 #x00) ;; add %ch,%al
   (cons #x600ea8 #xe8) ;;
   (cons #x600ea9 #x02) ;; add 0x0(%rax),%al
   (cons #x600eaa #x40) ;;
   (cons #x600eab #x00) ;;
   (cons #x600eac #x00) ;; add %al,(%rax)
   (cons #x600ead #x00) ;;
   (cons #x600eae #x00) ;; add %al,(%rax)
   (cons #x600eaf #x00) ;;
   (cons #x600eb0 #x0a) ;; or (%rax),%al
   (cons #x600eb1 #x00) ;;
   (cons #x600eb2 #x00) ;; add %al,(%rax)
   (cons #x600eb3 #x00) ;;
   (cons #x600eb4 #x00) ;; add %al,(%rax)
   (cons #x600eb5 #x00) ;;
   (cons #x600eb6 #x00) ;; add %al,(%rax)
   (cons #x600eb7 #x00) ;;
   (cons #x600eb8 #x5d) ;; pop %rbp
   (cons #x600eb9 #x00) ;; add %al,(%rax)
   (cons #x600eba #x00) ;;
   (cons #x600ebb #x00) ;; add %al,(%rax)
   (cons #x600ebc #x00) ;;
   (cons #x600ebd #x00) ;; add %al,(%rax)
   (cons #x600ebe #x00) ;;
   (cons #x600ebf #x00) ;; add %cl,(%rbx)
   (cons #x600ec0 #x0b) ;;
   (cons #x600ec1 #x00) ;; add %al,(%rax)
   (cons #x600ec2 #x00) ;;
   (cons #x600ec3 #x00) ;; add %al,(%rax)
   (cons #x600ec4 #x00) ;;
   (cons #x600ec5 #x00) ;; add %al,(%rax)
   (cons #x600ec6 #x00) ;;
   (cons #x600ec7 #x00) ;; add %bl,(%rax)
   (cons #x600ec8 #x18) ;;
   (cons #x600ec9 #x00) ;; add %al,(%rax)
   (cons #x600eca #x00) ;;
   (cons #x600ecb #x00) ;; add %al,(%rax)
   (cons #x600ecc #x00) ;;
   (cons #x600ecd #x00) ;; add %al,(%rax)
   (cons #x600ece #x00) ;;
   (cons #x600ecf #x00) ;; add %dl,0x0(%rip) # 600ed5 <_DYNAMIC+0x95>
   (cons #x600ed0 #x15) ;;
   (cons #x600ed1 #x00) ;;
   (cons #x600ed2 #x00) ;;
   (cons #x600ed3 #x00) ;;
   (cons #x600ed4 #x00) ;;

   ;; Section: <.got>:



   ;; Section: <_GLOBAL_OFFSET_TABLE_>:


   (cons #x600fe8 #x40) ;; rex (bad)
   (cons #x600fe9 #x0e) ;;
   (cons #x600fea #x60) ;; (bad)

   ;; Section: <__data_start>:



   ;; Section: <completed.7382>:



   ;; Section: <dtor_idx.7384>:



   ;; Section: <.comment>:


   (cons #x0 #x47)  ;; rex.RXB
   (cons #x1 #x43)  ;; rex.XB
   (cons #x2 #x43)  ;; rex.XB cmp (%r8),%spl
   (cons #x3 #x3a)  ;;
   (cons #x4 #x20)  ;;
   (cons #x5 #x28)  ;; sub %dl,0x62(%rbp)
   (cons #x6 #x55)  ;;
   (cons #x7 #x62)  ;;
   (cons #x8 #x75)  ;; jne 78 <_init-0x400418>
   (cons #x9 #x6e)  ;;
   (cons #xa #x74)  ;; je 81 <_init-0x40040f>
   (cons #xb #x75)  ;;
   (cons #xc #x20)  ;; and %dh,(%rsi,%rbp,1)
   (cons #xd #x34)  ;;
   (cons #xe #x2e)  ;;
   (cons #xf #x34)  ;; xor $0x2e,%al
   (cons #x10 #x2e) ;;
   (cons #x11 #x33) ;; xor 0x75627534(%rip),%ebp # 7562754b <_end+0x7502650b>
   (cons #x12 #x2d) ;;
   (cons #x13 #x34) ;;
   (cons #x14 #x75) ;;
   (cons #x15 #x62) ;;
   (cons #x16 #x75) ;;
   (cons #x17 #x6e) ;; outsb %ds:(%rsi),(%dx)
   (cons #x18 #x74) ;; je 8f <_init-0x400401>
   (cons #x19 #x75) ;;
   (cons #x1a #x35) ;; xor $0x2029312e,%eax
   (cons #x1b #x2e) ;;
   (cons #x1c #x31) ;;
   (cons #x1d #x29) ;;
   (cons #x1e #x20) ;;
   (cons #x1f #x34) ;; xor $0x2e,%al
   (cons #x20 #x2e) ;;
   (cons #x21 #x34) ;; xor $0x2e,%al
   (cons #x22 #x2e) ;;
   (cons #x23 #x33) ;; xor (%rax),%eax
   (cons #x24 #x00) ;;
   (cons #x25 #x47) ;; rex.RXB
   (cons #x26 #x43) ;; rex.XB
   (cons #x27 #x43) ;; rex.XB cmp (%r8),%spl
   (cons #x28 #x3a) ;;
   (cons #x29 #x20) ;;
   (cons #x2a #x28) ;; sub %dl,0x62(%rbp)
   (cons #x2b #x55) ;;
   (cons #x2c #x62) ;;
   (cons #x2d #x75) ;; jne 9d <_init-0x4003f3>
   (cons #x2e #x6e) ;;
   (cons #x2f #x74) ;; je a6 <_init-0x4003ea>
   (cons #x30 #x75) ;;
   (cons #x31 #x20) ;; and %dh,(%rsi,%rbp,1)
   (cons #x32 #x34) ;;
   (cons #x33 #x2e) ;;
   (cons #x34 #x34) ;; xor $0x2e,%al
   (cons #x35 #x2e) ;;
   (cons #x36 #x33) ;; xor 0x75627534(%rip),%ebp # 75627570 <_end+0x75026530>
   (cons #x37 #x2d) ;;
   (cons #x38 #x34) ;;
   (cons #x39 #x75) ;;
   (cons #x3a #x62) ;;
   (cons #x3b #x75) ;;
   (cons #x3c #x6e) ;; outsb %ds:(%rsi),(%dx)
   (cons #x3d #x74) ;; je b4 <_init-0x4003dc>
   (cons #x3e #x75) ;;
   (cons #x3f #x35) ;; xor $0x2e342029,%eax
   (cons #x40 #x29) ;;
   (cons #x41 #x20) ;;
   (cons #x42 #x34) ;;
   (cons #x43 #x2e) ;;
   (cons #x44 #x34) ;; xor $0x2e,%al
   (cons #x45 #x2e) ;;
   (cons #x46 #x33) ;; xor (%rax),%eax
   (cons #x47 #x00) ;;
   ))

(assign xrun-limit 100000000000000000)

(set-raw-mode-on!)

;------------------------------------------------------------------------------
;------------------------------------------------------------------------------

;; Factorial_recursive:

(defun run-factorial_recursive (input x86 &aux (ctx 'run-factorial_recursive))

  ;; The following initializes the system-level mode and sets up the
  ;; page tables at address #x402000.  Comment out the following
  ;; init-sys-view expression if you wish to run the program
  ;; in programmer-level mode.
  (init-sys-view #x402000 x86)

  (init-x86-state

   ;; Status (MS and fault field)
   nil

   ;; Start Address
   #x4005f0

   ;; Halt Address
   #x400608

   ;; Initial values of General-Purpose Registers
   (acons
    ;; Input is in RDI.
    #.*rdi* input
    (acons
     #.*rsp* #.*2^45*
     nil))

   ;; Initial values of Control Registers (already initialized in
   ;; init-sys-view)
   nil

   ;; Initial values of Model-Specific Registers (already initialized
   ;; in init-sys-view)
   nil

   ;; Initial value of the Rflags Register
   2

   ;; Initial memory image
   *factorial-binary*

   ;; x86 state
   x86)

  (mv-let
   (factorial_recursive-steps x86)
   (time$ (x86-run-steps (@ xrun-limit) x86))
   (ACL2::state-free-global-let*
    ((print-base 10))
    (cond ((not (equal (ms x86)
                       '((X86-HLT :RIP  #x400609
                                  :LEGAL-HALT :HLT))))
           (ACL2::er soft ctx
                     "~|(ms x86) = ~x0"
                     (ms x86)))
          (t (let ((expected (fact input)))
               (cond
                ((equal (rgfi *rax* x86)
                        expected)
                 (pprogn
                  (ACL2::fmx "(factorial_recursive ~x0) was correctly computed as ~x1 (~x2 steps)~|"
                             input
                             expected
                             factorial_recursive-steps)
                  (ACL2::value t)))
                (t (ACL2::er soft ctx
                             "(factorial_recursive ~x0) = ~x1, but rax is ~x2"
                             input
                             expected
                             (rgfi *rax* x86)))))))))
  nil)

;; Some runs:

;; Note: Error from (fact 13) onwards.  The C program behaves in the same way.
;; so we're fine.
(dotimes (x 30 (time$ (run-factorial_recursive x x86)))
  (time$ (run-factorial_recursive x x86))
  (format t  "~%~%-----------------------------------------------~%~%"))

;------------------------------------------------------------------------------
;------------------------------------------------------------------------------

;; Factorial_Iterative:

(defun run-factorial_iterative (input x86 &aux (ctx 'run-factorial_iterative))

  ;; The following initializes the system-level mode and sets up the
  ;; page tables at address #x402000.  Comment out the following
  ;; init-sys-view expression if you wish to run the program
  ;; in programmer-level mode.
  (init-sys-view #x402000 x86)

  (init-x86-state

   ;; Status (MS and fault field)
   nil

   ;; Start Address
   #x400610

   ;; Halt Address
   #x40062a

   ;; Initial values of General-Purpose Registers
   (acons
    ;; Input is in RDI.
    #.*rdi* input
    (acons
     #.*rsp* #.*2^45*
     nil))

   ;; Initial values of Control Registers (already initialized in
   ;; init-sys-view)
   nil

   ;; Initial values of Model-Specific Registers (already initialized
   ;; in init-sys-view)
   nil

   ;; Initial value of the Rflags Register
   2

   ;; Initial memory image
   *factorial-binary*

   ;; x86 state
   x86)

  (mv-let
   (factorial_iterative-steps x86)
   (time$ (x86-run-steps (@ xrun-limit) x86))
   (ACL2::state-free-global-let*
    ((print-base 10))
    (cond ((not (equal (ms x86)
                       '((X86-HLT :RIP #x40062B :LEGAL-HALT :HLT))))
           (ACL2::er soft ctx
                     "~|(ms x86) = ~x0"
                     (ms x86)))
          (t (let ((expected (fact input)))
               (cond
                ((equal (rgfi *rax* x86)
                        expected)
                 (pprogn
                  (ACL2::fmx "(factorial_iterative ~x0) was correctly computed as ~x1 (~x2 steps)~|"
                             input
                             expected
                             factorial_iterative-steps)
                  (ACL2::value t)))
                (t (ACL2::er soft ctx
                             "(factorial_iterative ~x0) = ~x1, but rax is ~x2"
                             input
                             expected
                             (rgfi *rax* x86)))))))))
  nil)

;; Some runs:

;; Note: Error from (fact 13) onwards.  The C program behaves in the same way.
;; so we're fine.
(dotimes (x 30 (time$ (run-factorial_iterative x x86)))
  (time$ (run-factorial_iterative x x86))
  (format t  "~%~%-----------------------------------------------~%~%"))

;------------------------------------------------------------------------------
;------------------------------------------------------------------------------

;; Factorial_Tail_Recursive:

(defun run-factorial_tail_recursive (input x86 &aux (ctx 'run-factorial_tail_recursive))

  ;; The following initializes the system-level mode and sets up the
  ;; page tables at address #x402000.  Comment out the following
  ;; init-sys-view expression if you wish to run the program
  ;; in programmer-level mode.
  (init-sys-view #x402000 x86)

  (init-x86-state

   ;; Status (MS and fault field)
   nil

   ;; Start Address
   #x400650

   ;; Halt Address
   #x400668

   ;; Initial values of General-Purpose Registers
   (acons
    ;; Input is in RDI.
    #.*rdi* input
    (acons
     #.*rsp* #.*2^45*
     nil))

   ;; Initial values of Control Registers (already initialized in
   ;; init-sys-view)
   nil

   ;; Initial values of Model-Specific Registers (already initialized
   ;; in init-sys-view)
   nil

   ;; Initial value of the Rflags Register
   2

   ;; Initial memory image
   *factorial-binary*

   ;; x86 state
   x86)

  (mv-let
   (factorial_tail_recursive-steps x86)
   (time$ (x86-run-steps (@ xrun-limit) x86))
   (ACL2::state-free-global-let*
    ((print-base 10))
    (cond ((not (equal (ms x86)
                       '((X86-HLT :RIP #x400669
                                  :LEGAL-HALT :HLT))))
           (ACL2::er soft ctx
                     "~|(ms x86) = ~x0"
                     (ms x86)))
          (t (let ((expected (fact input)))
               (cond
                ((equal (rgfi *rax* x86)
                        expected)
                 (pprogn
                  (ACL2::fmx "(factorial_tail_recursive ~x0) was correctly computed as ~x1 (~x2 steps)~|"
                             input
                             expected
                             factorial_tail_recursive-steps)
                  (ACL2::value t)))
                (t (ACL2::er soft ctx
                             "(factorial_tail_recursive ~x0) = ~x1, but rax is ~x2"
                             input
                             expected
                             (rgfi *rax* x86)))))))))
  nil)

;; Some runs:

;; Note: Error from (fact 13) onwards.  The C program behaves in the same way.
;; so we're fine.
(dotimes (x 30 (time$ (run-factorial_tail_recursive x x86)))
  (time$ (run-factorial_tail_recursive x x86))
  (format t  "~%~%-----------------------------------------------~%~%"))

;------------------------------------------------------------------------------
;------------------------------------------------------------------------------
