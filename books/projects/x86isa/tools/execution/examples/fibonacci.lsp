;; Shilpi Goel

(in-package "X86ISA")

(include-book "../top" :ttags :all)

;; (include-book "centaur/memoize/old/profile" :dir :system)

;; ======================================================================

#||

// Source program (in C):

#include <stdio.h>
#include <stdlib.h>

long fib (int n)
{
  if (n <= 0)
    {
      return 0;
    }
  else if (n == 1)
    {
      return 1;
    }
  else return (fib(n-1) + fib(n-2));
}

int main (int argc, char *argv[], char *env[])
{
  if (argc != 2)
    {
      printf("Error: Need one arg.\n");
      exit(1);
    }
  int n = atoi(argv[1]);
  printf("fib(%d) = %ld\n", n, fib(n));
}

||#

(defun fib (n)
  ;; Specification Function in ACL2
  (declare (xargs :guard (natp n)))
  (cond ((zp n) 0)
        ((eql n 1) 1)
        (t (+ (fib (- n 1)) (fib (- n 2))))))

;; The following ACL2 representation of the fibonacci binary (with the
;; assembly instructions preserved as comments) was obtained from the
;; fibonacci machine-code program using the -O2 option of GCC.

(defconst *fibonacci-binary*
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
   (cons #x400283 #x00) ;; add %bl,%bh
   (cons #x400284 #xdf) ;;
   (cons #x400285 #xbb) ;; mov $0xe6f14429,%ebx
   (cons #x400286 #x29) ;;
   (cons #x400287 #x44) ;;
   (cons #x400288 #xf1) ;;
   (cons #x400289 #xe6) ;;
   (cons #x40028a #x2d) ;; sub $0x4078c2ad,%eax
   (cons #x40028b #xad) ;;
   (cons #x40028c #xc2) ;;
   (cons #x40028d #x78) ;;
   (cons #x40028e #x40) ;;
   (cons #x40028f #x4a) ;; rex.WX popq -0x23dcddc6(%rbx)
   (cons #x400290 #x8f) ;;
   (cons #x400291 #x83) ;;
   (cons #x400292 #x3a) ;;
   (cons #x400293 #x22) ;;
   (cons #x400294 #x23) ;;
   (cons #x400295 #xdc) ;;
   (cons #x400296 #xc8) ;; .byte 0xc8
   (cons #x400297 #x56) ;; push %rsi

   ;; Section: <.hash>:


   (cons #x400298 #x03) ;; add (%rax),%eax
   (cons #x400299 #x00) ;;
   (cons #x40029a #x00) ;; add %al,(%rax)
   (cons #x40029b #x00) ;;
   (cons #x40029c #x06) ;; (bad)
   (cons #x40029d #x00) ;; add %al,(%rax)
   (cons #x40029e #x00) ;;
   (cons #x40029f #x00) ;; add %al,(%rdx)
   (cons #x4002a0 #x02) ;;
   (cons #x4002a1 #x00) ;; add %al,(%rax)
   (cons #x4002a2 #x00) ;;
   (cons #x4002a3 #x00) ;; add %al,0x4000000(%rip) # 44002a9 <_end+0x3dff269>
   (cons #x4002a4 #x05) ;;
   (cons #x4002a5 #x00) ;;
   (cons #x4002a6 #x00) ;;
   (cons #x4002a7 #x00) ;;
   (cons #x4002a8 #x04) ;;

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
   (cons #x40037b #x67) ;; insl (%dx),%es:(%edi)
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
   (cons #x40038f #x2e) ;; cs add %bl,%cs:%ss:0x5f(%rdi)
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
   (cons #x4003d8 #x02) ;; add (%rax),%al
   (cons #x4003d9 #x00) ;;
   (cons #x4003da #x00) ;; add %al,(%rax)
   (cons #x4003db #x00) ;;
   (cons #x4003dc #x02) ;; add (%rax),%al
   (cons #x4003dd #x00) ;;
   (cons #x4003de #x03) ;; add (%rax),%eax
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
   (cons #x400423 #x00) ;; add %al,(%rdx)
   (cons #x400424 #x02) ;;

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
   (cons #x40043b #x00) ;; add %al,(%rcx)
   (cons #x40043c #x01) ;;

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
   (cons #x40049e #xe8) ;; callq 400750 <__do_global_ctors_aux>
   (cons #x40049f #xad) ;;
   (cons #x4004a0 #x02) ;;
   (cons #x4004a1 #x00) ;;
   (cons #x4004a2 #x00) ;;
   (cons #x4004a3 #x48) ;; add $0x8,%rsp
   (cons #x4004a4 #x83) ;;
   (cons #x4004a5 #xc4) ;;
   (cons #x4004a6 #x08) ;;
   (cons #x4004a7 #xc3) ;; retq

   ;; Section: <__libc_start_main@plt-0x10>:


   (cons #x4004b0 #xff) ;; pushq 0x200b3a(%rip) # 600ff0 <_GLOBAL_OFFSET_TABLE_+0x8>
   (cons #x4004b1 #x35) ;;
   (cons #x4004b2 #x3a) ;;
   (cons #x4004b3 #x0b) ;;
   (cons #x4004b4 #x20) ;;
   (cons #x4004b5 #x00) ;;
   (cons #x4004b6 #xff) ;; jmpq *0x200b3c(%rip) # 600ff8 <_GLOBAL_OFFSET_TABLE_+0x10>
   (cons #x4004b7 #x25) ;;
   (cons #x4004b8 #x3c) ;;
   (cons #x4004b9 #x0b) ;;
   (cons #x4004ba #x20) ;;
   (cons #x4004bb #x00) ;;
   (cons #x4004bc #x0f) ;; nopl 0x0(%rax)
   (cons #x4004bd #x1f) ;;
   (cons #x4004be #x40) ;;
   (cons #x4004bf #x00) ;;

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
   (cons #x40050f #x49) ;; mov $0x4006b0,%r8
   (cons #x400510 #xc7) ;;
   (cons #x400511 #xc0) ;;
   (cons #x400512 #xb0) ;;
   (cons #x400513 #x06) ;;
   (cons #x400514 #x40) ;;
   (cons #x400515 #x00) ;;
   (cons #x400516 #x48) ;; mov $0x4006c0,%rcx
   (cons #x400517 #xc7) ;;
   (cons #x400518 #xc1) ;;
   (cons #x400519 #xc0) ;;
   (cons #x40051a #x06) ;;
   (cons #x40051b #x40) ;;
   (cons #x40051c #x00) ;;
   (cons #x40051d #x48) ;; mov $0x400650,%rdi
   (cons #x40051e #xc7) ;;
   (cons #x40051f #xc7) ;;
   (cons #x400520 #x50) ;;
   (cons #x400521 #x06) ;;
   (cons #x400522 #x40) ;;
   (cons #x400523 #x00) ;;
   (cons #x400524 #xe8) ;; callq 4004c0 <__libc_start_main@plt>
   (cons #x400525 #x97) ;;
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
   (cons #x4005b4 #x66) ;; data32 data32 nopw %cs:0x0(%rax,%rax,1)
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

   ;; Section: <fib>:


   (cons #x4005f0 #x55) ;; push %rbp
   (cons #x4005f1 #x31) ;; xor %ebp,%ebp
   (cons #x4005f2 #xed) ;;
   (cons #x4005f3 #x53) ;; push %rbx
   (cons #x4005f4 #x89) ;; mov %edi,%ebx
   (cons #x4005f5 #xfb) ;;
   (cons #x4005f6 #x48) ;; sub $0x8,%rsp
   (cons #x4005f7 #x83) ;;
   (cons #x4005f8 #xec) ;;
   (cons #x4005f9 #x08) ;;
   (cons #x4005fa #x85) ;; test %edi,%edi
   (cons #x4005fb #xff) ;;
   (cons #x4005fc #x7e) ;; jle 400624 <fib+0x34>
   (cons #x4005fd #x26) ;;
   (cons #x4005fe #x83) ;; cmp $0x1,%edi
   (cons #x4005ff #xff) ;;
   (cons #x400600 #x01) ;;
   (cons #x400601 #x75) ;; jne 400612 <fib+0x22>
   (cons #x400602 #x0f) ;;
   (cons #x400603 #xeb) ;; jmp 40063e <fib+0x4e>
   (cons #x400604 #x39) ;;
   (cons #x400605 #x0f) ;; nopl (%rax)
   (cons #x400606 #x1f) ;;
   (cons #x400607 #x00) ;;
   (cons #x400608 #x83) ;; cmp $0x1,%ebx
   (cons #x400609 #xfb) ;;
   (cons #x40060a #x01) ;;
   (cons #x40060b #x0f) ;; nopl 0x0(%rax,%rax,1)
   (cons #x40060c #x1f) ;;
   (cons #x40060d #x44) ;;
   (cons #x40060e #x00) ;;
   (cons #x40060f #x00) ;;
   (cons #x400610 #x74) ;; je 400630 <fib+0x40>
   (cons #x400611 #x1e) ;;
   (cons #x400612 #x8d) ;; lea -0x1(%rbx),%edi
   (cons #x400613 #x7b) ;;
   (cons #x400614 #xff) ;;
   (cons #x400615 #x83) ;; sub $0x2,%ebx
   (cons #x400616 #xeb) ;;
   (cons #x400617 #x02) ;;
   (cons #x400618 #xe8) ;; callq 4005f0 <fib>
   (cons #x400619 #xd3) ;;
   (cons #x40061a #xff) ;;
   (cons #x40061b #xff) ;;
   (cons #x40061c #xff) ;;
   (cons #x40061d #x48) ;; add %rax,%rbp
   (cons #x40061e #x01) ;;
   (cons #x40061f #xc5) ;;
   (cons #x400620 #x85) ;; test %ebx,%ebx
   (cons #x400621 #xdb) ;;
   (cons #x400622 #x7f) ;; jg 400608 <fib+0x18>
   (cons #x400623 #xe4) ;;
   (cons #x400624 #x48) ;; add $0x8,%rsp
   (cons #x400625 #x83) ;;
   (cons #x400626 #xc4) ;;
   (cons #x400627 #x08) ;;
   (cons #x400628 #x48) ;; mov %rbp,%rax
   (cons #x400629 #x89) ;;
   (cons #x40062a #xe8) ;;
   (cons #x40062b #x5b) ;; pop %rbx
   (cons #x40062c #x5d) ;; pop %rbp
   (cons #x40062d #xc3) ;; retq
   (cons #x40062e #x66) ;; xchg %ax,%ax
   (cons #x40062f #x90) ;;
   (cons #x400630 #x48) ;; add $0x1,%rbp
   (cons #x400631 #x83) ;;
   (cons #x400632 #xc5) ;;
   (cons #x400633 #x01) ;;
   (cons #x400634 #x48) ;; add $0x8,%rsp
   (cons #x400635 #x83) ;;
   (cons #x400636 #xc4) ;;
   (cons #x400637 #x08) ;;
   (cons #x400638 #x5b) ;; pop %rbx
   (cons #x400639 #x48) ;; mov %rbp,%rax
   (cons #x40063a #x89) ;;
   (cons #x40063b #xe8) ;;
   (cons #x40063c #x5d) ;; pop %rbp
   (cons #x40063d #xc3) ;; retq
   (cons #x40063e #x40) ;; mov $0x1,%bpl
   (cons #x40063f #xb5) ;;
   (cons #x400640 #x01) ;;
   (cons #x400641 #xeb) ;; jmp 400624 <fib+0x34>
   (cons #x400642 #xe1) ;;
   (cons #x400643 #x66) ;; data32 data32 data32 nopw %cs:0x0(%rax,%rax,1)
   (cons #x400644 #x66) ;;
   (cons #x400645 #x66) ;;
   (cons #x400646 #x66) ;;
   (cons #x400647 #x2e) ;;
   (cons #x400648 #x0f) ;;
   (cons #x400649 #x1f) ;;
   (cons #x40064a #x84) ;;
   (cons #x40064b #x00) ;;
   (cons #x40064c #x00) ;;
   (cons #x40064d #x00) ;;
   (cons #x40064e #x00) ;;
   (cons #x40064f #x00) ;;

   ;; Section: <main>:


   (cons #x400650 #x83) ;; cmp $0x2,%edi
   (cons #x400651 #xff) ;;
   (cons #x400652 #x02) ;;
   (cons #x400653 #x53) ;; push %rbx
   (cons #x400654 #x75) ;; jne 400687 <main+0x37>
   (cons #x400655 #x31) ;;
   (cons #x400656 #x48) ;; mov 0x8(%rsi),%rdi
   (cons #x400657 #x8b) ;;
   (cons #x400658 #x7e) ;;
   (cons #x400659 #x08) ;;
   (cons #x40065a #xba) ;; mov $0xa,%edx
   (cons #x40065b #x0a) ;;
   (cons #x40065c #x00) ;;
   (cons #x40065d #x00) ;;
   (cons #x40065e #x00) ;;
   (cons #x40065f #x31) ;; xor %esi,%esi
   (cons #x400660 #xf6) ;;
   (cons #x400661 #xe8) ;; callq 4004d0 <strtol@plt>
   (cons #x400662 #x6a) ;;
   (cons #x400663 #xfe) ;;
   (cons #x400664 #xff) ;;
   (cons #x400665 #xff) ;;
   (cons #x400666 #x48) ;; mov %rax,%rbx
   (cons #x400667 #x89) ;;
   (cons #x400668 #xc3) ;;
   (cons #x400669 #x89) ;; mov %eax,%edi
   (cons #x40066a #xc7) ;;
   (cons #x40066b #xe8) ;; callq 4005f0 <fib>
   (cons #x40066c #x80) ;;
   (cons #x40066d #xff) ;;
   (cons #x40066e #xff) ;;
   (cons #x40066f #xff) ;;
   (cons #x400670 #x89) ;; mov %ebx,%edx
   (cons #x400671 #xda) ;;
   (cons #x400672 #x48) ;; mov %rax,%rcx
   (cons #x400673 #x89) ;;
   (cons #x400674 #xc1) ;;
   (cons #x400675 #xbe) ;; mov $0x4007b2,%esi
   (cons #x400676 #xb2) ;;
   (cons #x400677 #x07) ;;
   (cons #x400678 #x40) ;;
   (cons #x400679 #x00) ;;
   (cons #x40067a #x5b) ;; pop %rbx
   (cons #x40067b #xbf) ;; mov $0x1,%edi
   (cons #x40067c #x01) ;;
   (cons #x40067d #x00) ;;
   (cons #x40067e #x00) ;;
   (cons #x40067f #x00) ;;
   (cons #x400680 #x31) ;; xor %eax,%eax
   (cons #x400681 #xc0) ;;
   (cons #x400682 #xe9) ;; jmpq 4004e0 <__printf_chk@plt>
   (cons #x400683 #x59) ;;
   (cons #x400684 #xfe) ;;
   (cons #x400685 #xff) ;;
   (cons #x400686 #xff) ;;
   (cons #x400687 #xbf) ;; mov $0x1,%edi
   (cons #x400688 #x01) ;;
   (cons #x400689 #x00) ;;
   (cons #x40068a #x00) ;;
   (cons #x40068b #x00) ;;
   (cons #x40068c #xbe) ;; mov $0x40079c,%esi
   (cons #x40068d #x9c) ;;
   (cons #x40068e #x07) ;;
   (cons #x40068f #x40) ;;
   (cons #x400690 #x00) ;;
   (cons #x400691 #x31) ;; xor %eax,%eax
   (cons #x400692 #xc0) ;;
   (cons #x400693 #xe8) ;; callq 4004e0 <__printf_chk@plt>
   (cons #x400694 #x48) ;;
   (cons #x400695 #xfe) ;;
   (cons #x400696 #xff) ;;
   (cons #x400697 #xff) ;;
   (cons #x400698 #xbf) ;; mov $0x1,%edi
   (cons #x400699 #x01) ;;
   (cons #x40069a #x00) ;;
   (cons #x40069b #x00) ;;
   (cons #x40069c #x00) ;;
   (cons #x40069d #xe8) ;; callq 4004f0 <exit@plt>
   (cons #x40069e #x4e) ;;
   (cons #x40069f #xfe) ;;
   (cons #x4006a0 #xff) ;;
   (cons #x4006a1 #xff) ;;
   (cons #x4006a2 #x90) ;; nop
   (cons #x4006a3 #x90) ;; nop
   (cons #x4006a4 #x90) ;; nop
   (cons #x4006a5 #x90) ;; nop
   (cons #x4006a6 #x90) ;; nop
   (cons #x4006a7 #x90) ;; nop
   (cons #x4006a8 #x90) ;; nop
   (cons #x4006a9 #x90) ;; nop
   (cons #x4006aa #x90) ;; nop
   (cons #x4006ab #x90) ;; nop
   (cons #x4006ac #x90) ;; nop
   (cons #x4006ad #x90) ;; nop
   (cons #x4006ae #x90) ;; nop
   (cons #x4006af #x90) ;; nop

   ;; Section: <__libc_csu_fini>:


   (cons #x4006b0 #xf3) ;; repz retq
   (cons #x4006b1 #xc3) ;;
   (cons #x4006b2 #x66) ;; data32 data32 data32 data32 nopw %cs:0x0(%rax,%rax,1)
   (cons #x4006b3 #x66) ;;
   (cons #x4006b4 #x66) ;;
   (cons #x4006b5 #x66) ;;
   (cons #x4006b6 #x66) ;;
   (cons #x4006b7 #x2e) ;;
   (cons #x4006b8 #x0f) ;;
   (cons #x4006b9 #x1f) ;;
   (cons #x4006ba #x84) ;;
   (cons #x4006bb #x00) ;;
   (cons #x4006bc #x00) ;;
   (cons #x4006bd #x00) ;;
   (cons #x4006be #x00) ;;
   (cons #x4006bf #x00) ;;

   ;; Section: <__libc_csu_init>:


   (cons #x4006c0 #x48) ;; mov %rbp,-0x28(%rsp)
   (cons #x4006c1 #x89) ;;
   (cons #x4006c2 #x6c) ;;
   (cons #x4006c3 #x24) ;;
   (cons #x4006c4 #xd8) ;;
   (cons #x4006c5 #x4c) ;; mov %r12,-0x20(%rsp)
   (cons #x4006c6 #x89) ;;
   (cons #x4006c7 #x64) ;;
   (cons #x4006c8 #x24) ;;
   (cons #x4006c9 #xe0) ;;
   (cons #x4006ca #x48) ;; lea 0x200743(%rip),%rbp # 600e14 <__init_array_end>
   (cons #x4006cb #x8d) ;;
   (cons #x4006cc #x2d) ;;
   (cons #x4006cd #x43) ;;
   (cons #x4006ce #x07) ;;
   (cons #x4006cf #x20) ;;
   (cons #x4006d0 #x00) ;;
   (cons #x4006d1 #x4c) ;; lea 0x20073c(%rip),%r12 # 600e14 <__init_array_end>
   (cons #x4006d2 #x8d) ;;
   (cons #x4006d3 #x25) ;;
   (cons #x4006d4 #x3c) ;;
   (cons #x4006d5 #x07) ;;
   (cons #x4006d6 #x20) ;;
   (cons #x4006d7 #x00) ;;
   (cons #x4006d8 #x4c) ;; mov %r13,-0x18(%rsp)
   (cons #x4006d9 #x89) ;;
   (cons #x4006da #x6c) ;;
   (cons #x4006db #x24) ;;
   (cons #x4006dc #xe8) ;;
   (cons #x4006dd #x4c) ;; mov %r14,-0x10(%rsp)
   (cons #x4006de #x89) ;;
   (cons #x4006df #x74) ;;
   (cons #x4006e0 #x24) ;;
   (cons #x4006e1 #xf0) ;;
   (cons #x4006e2 #x4c) ;; mov %r15,-0x8(%rsp)
   (cons #x4006e3 #x89) ;;
   (cons #x4006e4 #x7c) ;;
   (cons #x4006e5 #x24) ;;
   (cons #x4006e6 #xf8) ;;
   (cons #x4006e7 #x48) ;; mov %rbx,-0x30(%rsp)
   (cons #x4006e8 #x89) ;;
   (cons #x4006e9 #x5c) ;;
   (cons #x4006ea #x24) ;;
   (cons #x4006eb #xd0) ;;
   (cons #x4006ec #x48) ;; sub $0x38,%rsp
   (cons #x4006ed #x83) ;;
   (cons #x4006ee #xec) ;;
   (cons #x4006ef #x38) ;;
   (cons #x4006f0 #x4c) ;; sub %r12,%rbp
   (cons #x4006f1 #x29) ;;
   (cons #x4006f2 #xe5) ;;
   (cons #x4006f3 #x41) ;; mov %edi,%r13d
   (cons #x4006f4 #x89) ;;
   (cons #x4006f5 #xfd) ;;
   (cons #x4006f6 #x49) ;; mov %rsi,%r14
   (cons #x4006f7 #x89) ;;
   (cons #x4006f8 #xf6) ;;
   (cons #x4006f9 #x48) ;; sar $0x3,%rbp
   (cons #x4006fa #xc1) ;;
   (cons #x4006fb #xfd) ;;
   (cons #x4006fc #x03) ;;
   (cons #x4006fd #x49) ;; mov %rdx,%r15
   (cons #x4006fe #x89) ;;
   (cons #x4006ff #xd7) ;;
   (cons #x400700 #xe8) ;; callq 400490 <_init>
   (cons #x400701 #x8b) ;;
   (cons #x400702 #xfd) ;;
   (cons #x400703 #xff) ;;
   (cons #x400704 #xff) ;;
   (cons #x400705 #x48) ;; test %rbp,%rbp
   (cons #x400706 #x85) ;;
   (cons #x400707 #xed) ;;
   (cons #x400708 #x74) ;; je 400726 <__libc_csu_init+0x66>
   (cons #x400709 #x1c) ;;
   (cons #x40070a #x31) ;; xor %ebx,%ebx
   (cons #x40070b #xdb) ;;
   (cons #x40070c #x0f) ;; nopl 0x0(%rax)
   (cons #x40070d #x1f) ;;
   (cons #x40070e #x40) ;;
   (cons #x40070f #x00) ;;
   (cons #x400710 #x4c) ;; mov %r15,%rdx
   (cons #x400711 #x89) ;;
   (cons #x400712 #xfa) ;;
   (cons #x400713 #x4c) ;; mov %r14,%rsi
   (cons #x400714 #x89) ;;
   (cons #x400715 #xf6) ;;
   (cons #x400716 #x44) ;; mov %r13d,%edi
   (cons #x400717 #x89) ;;
   (cons #x400718 #xef) ;;
   (cons #x400719 #x41) ;; callq *(%r12,%rbx,8)
   (cons #x40071a #xff) ;;
   (cons #x40071b #x14) ;;
   (cons #x40071c #xdc) ;;
   (cons #x40071d #x48) ;; add $0x1,%rbx
   (cons #x40071e #x83) ;;
   (cons #x40071f #xc3) ;;
   (cons #x400720 #x01) ;;
   (cons #x400721 #x48) ;; cmp %rbp,%rbx
   (cons #x400722 #x39) ;;
   (cons #x400723 #xeb) ;;
   (cons #x400724 #x72) ;; jb 400710 <__libc_csu_init+0x50>
   (cons #x400725 #xea) ;;
   (cons #x400726 #x48) ;; mov 0x8(%rsp),%rbx
   (cons #x400727 #x8b) ;;
   (cons #x400728 #x5c) ;;
   (cons #x400729 #x24) ;;
   (cons #x40072a #x08) ;;
   (cons #x40072b #x48) ;; mov 0x10(%rsp),%rbp
   (cons #x40072c #x8b) ;;
   (cons #x40072d #x6c) ;;
   (cons #x40072e #x24) ;;
   (cons #x40072f #x10) ;;
   (cons #x400730 #x4c) ;; mov 0x18(%rsp),%r12
   (cons #x400731 #x8b) ;;
   (cons #x400732 #x64) ;;
   (cons #x400733 #x24) ;;
   (cons #x400734 #x18) ;;
   (cons #x400735 #x4c) ;; mov 0x20(%rsp),%r13
   (cons #x400736 #x8b) ;;
   (cons #x400737 #x6c) ;;
   (cons #x400738 #x24) ;;
   (cons #x400739 #x20) ;;
   (cons #x40073a #x4c) ;; mov 0x28(%rsp),%r14
   (cons #x40073b #x8b) ;;
   (cons #x40073c #x74) ;;
   (cons #x40073d #x24) ;;
   (cons #x40073e #x28) ;;
   (cons #x40073f #x4c) ;; mov 0x30(%rsp),%r15
   (cons #x400740 #x8b) ;;
   (cons #x400741 #x7c) ;;
   (cons #x400742 #x24) ;;
   (cons #x400743 #x30) ;;
   (cons #x400744 #x48) ;; add $0x38,%rsp
   (cons #x400745 #x83) ;;
   (cons #x400746 #xc4) ;;
   (cons #x400747 #x38) ;;
   (cons #x400748 #xc3) ;; retq
   (cons #x400749 #x90) ;; nop
   (cons #x40074a #x90) ;; nop
   (cons #x40074b #x90) ;; nop
   (cons #x40074c #x90) ;; nop
   (cons #x40074d #x90) ;; nop
   (cons #x40074e #x90) ;; nop
   (cons #x40074f #x90) ;; nop

   ;; Section: <__do_global_ctors_aux>:


   (cons #x400750 #x55) ;; push %rbp
   (cons #x400751 #x48) ;; mov %rsp,%rbp
   (cons #x400752 #x89) ;;
   (cons #x400753 #xe5) ;;
   (cons #x400754 #x53) ;; push %rbx
   (cons #x400755 #x48) ;; sub $0x8,%rsp
   (cons #x400756 #x83) ;;
   (cons #x400757 #xec) ;;
   (cons #x400758 #x08) ;;
   (cons #x400759 #x48) ;; mov 0x2006b8(%rip),%rax # 600e18 <__CTOR_LIST__>
   (cons #x40075a #x8b) ;;
   (cons #x40075b #x05) ;;
   (cons #x40075c #xb8) ;;
   (cons #x40075d #x06) ;;
   (cons #x40075e #x20) ;;
   (cons #x40075f #x00) ;;
   (cons #x400760 #x48) ;; cmp $0xffffffffffffffff,%rax
   (cons #x400761 #x83) ;;
   (cons #x400762 #xf8) ;;
   (cons #x400763 #xff) ;;
   (cons #x400764 #x74) ;; je 40077f <__do_global_ctors_aux+0x2f>
   (cons #x400765 #x19) ;;
   (cons #x400766 #xbb) ;; mov $0x600e18,%ebx
   (cons #x400767 #x18) ;;
   (cons #x400768 #x0e) ;;
   (cons #x400769 #x60) ;;
   (cons #x40076a #x00) ;;
   (cons #x40076b #x0f) ;; nopl 0x0(%rax,%rax,1)
   (cons #x40076c #x1f) ;;
   (cons #x40076d #x44) ;;
   (cons #x40076e #x00) ;;
   (cons #x40076f #x00) ;;
   (cons #x400770 #x48) ;; sub $0x8,%rbx
   (cons #x400771 #x83) ;;
   (cons #x400772 #xeb) ;;
   (cons #x400773 #x08) ;;
   (cons #x400774 #xff) ;; callq *%rax
   (cons #x400775 #xd0) ;;
   (cons #x400776 #x48) ;; mov (%rbx),%rax
   (cons #x400777 #x8b) ;;
   (cons #x400778 #x03) ;;
   (cons #x400779 #x48) ;; cmp $0xffffffffffffffff,%rax
   (cons #x40077a #x83) ;;
   (cons #x40077b #xf8) ;;
   (cons #x40077c #xff) ;;
   (cons #x40077d #x75) ;; jne 400770 <__do_global_ctors_aux+0x20>
   (cons #x40077e #xf1) ;;
   (cons #x40077f #x48) ;; add $0x8,%rsp
   (cons #x400780 #x83) ;;
   (cons #x400781 #xc4) ;;
   (cons #x400782 #x08) ;;
   (cons #x400783 #x5b) ;; pop %rbx
   (cons #x400784 #xc9) ;; leaveq
   (cons #x400785 #xc3) ;; retq
   (cons #x400786 #x90) ;; nop
   (cons #x400787 #x90) ;; nop

   ;; Section: <_fini>:


   (cons #x400788 #x48) ;; sub $0x8,%rsp
   (cons #x400789 #x83) ;;
   (cons #x40078a #xec) ;;
   (cons #x40078b #x08) ;;
   (cons #x40078c #xe8) ;; callq 400550 <__do_global_dtors_aux>
   (cons #x40078d #xbf) ;;
   (cons #x40078e #xfd) ;;
   (cons #x40078f #xff) ;;
   (cons #x400790 #xff) ;;
   (cons #x400791 #x48) ;; add $0x8,%rsp
   (cons #x400792 #x83) ;;
   (cons #x400793 #xc4) ;;
   (cons #x400794 #x08) ;;
   (cons #x400795 #xc3) ;; retq

   ;; Section: <_IO_stdin_used>:


   (cons #x400798 #x01) ;; add %eax,(%rax)
   (cons #x400799 #x00) ;;
   (cons #x40079a #x02) ;; add (%rax),%al
   (cons #x40079b #x00) ;;
   (cons #x40079c #x45) ;; rex.RB jb 400811 <_IO_stdin_used+0x79>
   (cons #x40079d #x72) ;;
   (cons #x40079e #x72) ;;
   (cons #x40079f #x6f) ;; outsl %ds:(%rsi),(%dx)
   (cons #x4007a0 #x72) ;; jb 4007dc <_IO_stdin_used+0x44>
   (cons #x4007a1 #x3a) ;;
   (cons #x4007a2 #x20) ;; and %cl,0x65(%rsi)
   (cons #x4007a3 #x4e) ;;
   (cons #x4007a4 #x65) ;;
   (cons #x4007a5 #x65) ;; gs and %ch,%fs:%gs:0x6e(%rdi)
   (cons #x4007a6 #x64) ;;
   (cons #x4007a7 #x20) ;;
   (cons #x4007a8 #x6f) ;;
   (cons #x4007a9 #x6e) ;;
   (cons #x4007aa #x65) ;; and %ah,%gs:0x72(%rcx)
   (cons #x4007ab #x20) ;;
   (cons #x4007ac #x61) ;;
   (cons #x4007ad #x72) ;;
   (cons #x4007ae #x67) ;; or %cs:(%eax),%al
   (cons #x4007af #x2e) ;;
   (cons #x4007b0 #x0a) ;;
   (cons #x4007b1 #x00) ;;
   (cons #x4007b2 #x66) ;; imul $0x6425,0x28(%rdx),%sp
   (cons #x4007b3 #x69) ;;
   (cons #x4007b4 #x62) ;;
   (cons #x4007b5 #x28) ;;
   (cons #x4007b6 #x25) ;;
   (cons #x4007b7 #x64) ;;
   (cons #x4007b8 #x29) ;; sub %esp,(%rax)
   (cons #x4007b9 #x20) ;;
   (cons #x4007ba #x3d) ;; cmp $0x646c2520,%eax
   (cons #x4007bb #x20) ;;
   (cons #x4007bc #x25) ;;
   (cons #x4007bd #x6c) ;;
   (cons #x4007be #x64) ;;
   (cons #x4007bf #x0a) ;; or (%rax),%al
   (cons #x4007c0 #x00) ;;

   ;; Section: <.eh_frame_hdr>:


   (cons #x4007c4 #x01) ;; add %ebx,(%rbx)
   (cons #x4007c5 #x1b) ;;
   (cons #x4007c6 #x03) ;; add (%rbx),%edi
   (cons #x4007c7 #x3b) ;;
   (cons #x4007c8 #x30) ;; xor %al,(%rax)
   (cons #x4007c9 #x00) ;;
   (cons #x4007ca #x00) ;; add %al,(%rax)
   (cons #x4007cb #x00) ;;
   (cons #x4007cc #x05) ;; add $0xec000000,%eax
   (cons #x4007cd #x00) ;;
   (cons #x4007ce #x00) ;;
   (cons #x4007cf #x00) ;;
   (cons #x4007d0 #xec) ;;
   (cons #x4007d1 #xfc) ;; cld
   (cons #x4007d2 #xff) ;; (bad)
   (cons #x4007d3 #xff) ;; decl 0x0(%rax,%rax,1)
   (cons #x4007d4 #x4c) ;;
   (cons #x4007d5 #x00) ;;
   (cons #x4007d6 #x00) ;;
   (cons #x4007d7 #x00) ;; add %ch,(%rsi,%rdi,8)
   (cons #x4007d8 #x2c) ;;
   (cons #x4007d9 #xfe) ;;
   (cons #x4007da #xff) ;; (bad)
   (cons #x4007db #xff) ;; pushq 0x0(%rax,%rax,1)
   (cons #x4007dc #x74) ;;
   (cons #x4007dd #x00) ;;
   (cons #x4007de #x00) ;;
   (cons #x4007df #x00) ;; add %cl,0x94ffff(%rsi,%rdi,8)
   (cons #x4007e0 #x8c) ;;
   (cons #x4007e1 #xfe) ;;
   (cons #x4007e2 #xff) ;;
   (cons #x4007e3 #xff) ;;
   (cons #x4007e4 #x94) ;;
   (cons #x4007e5 #x00) ;;
   (cons #x4007e6 #x00) ;; add %al,(%rax)
   (cons #x4007e7 #x00) ;;
   (cons #x4007e8 #xec) ;; in (%dx),%al
   (cons #x4007e9 #xfe) ;; (bad)
   (cons #x4007ea #xff) ;; (bad)
   (cons #x4007eb #xff) ;; ljmpq *-0x1040000(%rax,%rax,1)
   (cons #x4007ec #xac) ;;
   (cons #x4007ed #x00) ;;
   (cons #x4007ee #x00) ;;
   (cons #x4007ef #x00) ;;
   (cons #x4007f0 #xfc) ;;
   (cons #x4007f1 #xfe) ;;
   (cons #x4007f2 #xff) ;; (bad)
   (cons #x4007f3 #xff) ;; inc %esp
   (cons #x4007f4 #xc4) ;;
   (cons #x4007f5 #x00) ;; add %al,(%rax)
   (cons #x4007f6 #x00) ;;

   ;; Section: <__FRAME_END__-0xb8>:


   (cons #x4007f8 #x14) ;; adc $0x0,%al
   (cons #x4007f9 #x00) ;;
   (cons #x4007fa #x00) ;; add %al,(%rax)
   (cons #x4007fb #x00) ;;
   (cons #x4007fc #x00) ;; add %al,(%rax)
   (cons #x4007fd #x00) ;;
   (cons #x4007fe #x00) ;; add %al,(%rax)
   (cons #x4007ff #x00) ;;
   (cons #x400800 #x01) ;; add %edi,0x52(%rdx)
   (cons #x400801 #x7a) ;;
   (cons #x400802 #x52) ;;
   (cons #x400803 #x00) ;; add %al,(%rcx)
   (cons #x400804 #x01) ;;
   (cons #x400805 #x78) ;; js 400817 <_IO_stdin_used+0x7f>
   (cons #x400806 #x10) ;;
   (cons #x400807 #x01) ;; add %ebx,(%rbx)
   (cons #x400808 #x1b) ;;
   (cons #x400809 #x0c) ;; or $0x7,%al
   (cons #x40080a #x07) ;;
   (cons #x40080b #x08) ;; or %dl,0x24000001(%rax)
   (cons #x40080c #x90) ;;
   (cons #x40080d #x01) ;;
   (cons #x40080e #x00) ;;
   (cons #x40080f #x00) ;;
   (cons #x400810 #x24) ;;
   (cons #x400811 #x00) ;; add %al,(%rax)
   (cons #x400812 #x00) ;;
   (cons #x400813 #x00) ;; add %bl,(%rax,%rax,1)
   (cons #x400814 #x1c) ;;
   (cons #x400815 #x00) ;;
   (cons #x400816 #x00) ;; add %al,(%rax)
   (cons #x400817 #x00) ;;
   (cons #x400818 #x98) ;; cwtl
   (cons #x400819 #xfc) ;; cld
   (cons #x40081a #xff) ;; (bad)
   (cons #x40081b #xff) ;; callq *0x0(%rax)
   (cons #x40081c #x50) ;;
   (cons #x40081d #x00) ;;
   (cons #x40081e #x00) ;; add %al,(%rax)
   (cons #x40081f #x00) ;;
   (cons #x400820 #x00) ;; add %cl,(%rsi)
   (cons #x400821 #x0e) ;;
   (cons #x400822 #x10) ;; adc %al,0xe(%rsi)
   (cons #x400823 #x46) ;;
   (cons #x400824 #x0e) ;;
   (cons #x400825 #x18) ;; sbb %cl,0xf(%rdx)
   (cons #x400826 #x4a) ;;
   (cons #x400827 #x0f) ;;
   (cons #x400828 #x0b) ;; or 0x8(%rdi),%esi
   (cons #x400829 #x77) ;;
   (cons #x40082a #x08) ;;
   (cons #x40082b #x80) ;; addb $0x3f,(%rax)
   (cons #x40082c #x00) ;;
   (cons #x40082d #x3f) ;;
   (cons #x40082e #x1a) ;; sbb (%rbx),%bh
   (cons #x40082f #x3b) ;;
   (cons #x400830 #x2a) ;; sub (%rbx),%dh
   (cons #x400831 #x33) ;;
   (cons #x400832 #x24) ;; and $0x22,%al
   (cons #x400833 #x22) ;;
   (cons #x400834 #x00) ;; add %al,(%rax)
   (cons #x400835 #x00) ;;
   (cons #x400836 #x00) ;; add %al,(%rax)
   (cons #x400837 #x00) ;;
   (cons #x400838 #x1c) ;; sbb $0x0,%al
   (cons #x400839 #x00) ;;
   (cons #x40083a #x00) ;; add %al,(%rax)
   (cons #x40083b #x00) ;;
   (cons #x40083c #x44) ;; add %r8b,(%rax)
   (cons #x40083d #x00) ;;
   (cons #x40083e #x00) ;;
   (cons #x40083f #x00) ;; add %dh,0x53fffffd(%rax)
   (cons #x400840 #xb0) ;;
   (cons #x400841 #xfd) ;;
   (cons #x400842 #xff) ;;
   (cons #x400843 #xff) ;;
   (cons #x400844 #x53) ;;
   (cons #x400845 #x00) ;; add %al,(%rax)
   (cons #x400846 #x00) ;;
   (cons #x400847 #x00) ;; add %al,(%rax)
   (cons #x400848 #x00) ;;
   (cons #x400849 #x41) ;; rex.B (bad)
   (cons #x40084a #x0e) ;;
   (cons #x40084b #x10) ;; adc %al,-0x7a(%rdx)
   (cons #x40084c #x42) ;;
   (cons #x40084d #x86) ;;
   (cons #x40084e #x02) ;; add 0xe(%rcx),%al
   (cons #x40084f #x41) ;;
   (cons #x400850 #x0e) ;;
   (cons #x400851 #x18) ;; sbb %al,-0x7d(%rdx)
   (cons #x400852 #x42) ;;
   (cons #x400853 #x83) ;;
   (cons #x400854 #x03) ;; add 0x20(%rsi,%rcx,1),%eax
   (cons #x400855 #x44) ;;
   (cons #x400856 #x0e) ;;
   (cons #x400857 #x20) ;;
   (cons #x400858 #x14) ;; adc $0x0,%al
   (cons #x400859 #x00) ;;
   (cons #x40085a #x00) ;; add %al,(%rax)
   (cons #x40085b #x00) ;;
   (cons #x40085c #x64) ;; add %al,%fs:(%rax)
   (cons #x40085d #x00) ;;
   (cons #x40085e #x00) ;;
   (cons #x40085f #x00) ;; add %dh,%al
   (cons #x400860 #xf0) ;;
   (cons #x400861 #xfd) ;; std
   (cons #x400862 #xff) ;; (bad)
   (cons #x400863 #xff) ;; callq *0x0(%rdx)
   (cons #x400864 #x52) ;;
   (cons #x400865 #x00) ;;
   (cons #x400866 #x00) ;; add %al,(%rax)
   (cons #x400867 #x00) ;;
   (cons #x400868 #x00) ;; add %al,0x10(%rsi,%rcx,1)
   (cons #x400869 #x44) ;;
   (cons #x40086a #x0e) ;;
   (cons #x40086b #x10) ;;
   (cons #x40086c #x42) ;; rex.X addl $0x0,(%rdx)
   (cons #x40086d #x83) ;;
   (cons #x40086e #x02) ;;
   (cons #x40086f #x00) ;;
   (cons #x400870 #x14) ;; adc $0x0,%al
   (cons #x400871 #x00) ;;
   (cons #x400872 #x00) ;; add %al,(%rax)
   (cons #x400873 #x00) ;;
   (cons #x400874 #x7c) ;; jl 400876 <_IO_stdin_used+0xde>
   (cons #x400875 #x00) ;;
   (cons #x400876 #x00) ;; add %al,(%rax)
   (cons #x400877 #x00) ;;
   (cons #x400878 #x38) ;; cmp %bh,%dh
   (cons #x400879 #xfe) ;;
   (cons #x40087a #xff) ;; (bad)
   (cons #x40087b #xff) ;; incl (%rdx)
   (cons #x40087c #x02) ;;

   ;; Section: <__FRAME_END__>:


   (cons #x4008b0 #x00) ;; add %al,(%rax)
   (cons #x4008b1 #x00) ;;

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
   (cons #x600e67 #x00) ;; add %cl,0x4007(%rax)
   (cons #x600e68 #x88) ;;
   (cons #x600e69 #x07) ;;
   (cons #x600e6a #x40) ;;
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

;; ======================================================================

(defun run-fib (input x86 &aux (ctx 'run-fib))

  ;; The following initializes the system-level mode and sets up the
  ;; page tables at address #x402000.  Comment out the following
  ;; init-sys-view expression if you wish to run the program
  ;; in programmer-level mode.
  (init-sys-view #x402000 x86)

  (init-x86-state

   ;; Status (MS and fault field)
   nil

   ;; Start Address
   #x400666

   ;; Halt Address
   #x400670

   ;; Initial values of General-Purpose Registers
   (acons
    ;; Input is in RAX.
    #.*rax* input
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
   *fibonacci-binary*

   ;; x86 state
   x86)

  (mv-let
   (fib-steps x86)
   (time$ (x86-run-steps (@ xrun-limit) x86))
   (ACL2::state-free-global-let*
    ((print-base 10))
    (cond ((not (equal (ms x86)
                       '((X86-HLT :RIP #x400671
                                  :LEGAL-HALT :HLT))))
           (ACL2::er soft ctx
                     "~|(ms x86) = ~x0"
                     (ms x86)))
          (t (let ((expected (fib input)))
               (cond
                ((equal (rgfi *rax* x86)
                        expected)
                 (pprogn
                  (ACL2::fmx "(fib ~x0) was correctly computed as ~x1 (~x2 steps)~|"
                             input
                             expected
                             fib-steps)
                  (ACL2::value t)))
                (t (ACL2::er soft ctx
                             "(fib ~x0) = ~x1, but rax is ~x2"
                             input
                             expected
                             (rgfi *rax* x86)))))))))
  nil)

;; ======================================================================

;; Some runs:

(run-fib  3 x86)
(run-fib  6 x86)
(run-fib  9 x86)
(run-fib 12 x86)
(run-fib 15 x86)
(run-fib 18 x86)
(run-fib 21 x86)
(run-fib 24 x86)
(run-fib 27 x86)
(run-fib 30 x86)
;; (run-fib 33 x86) ;; ~200s
;; (run-fib 36 x86) ;; ~630s
;; (run-fib 39 x86) ;; ~2673s

;; ======================================================================
