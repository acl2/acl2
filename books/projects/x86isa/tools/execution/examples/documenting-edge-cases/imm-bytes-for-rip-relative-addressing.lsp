;; Original Author: Shilpi Goel
;; Thanks to Dmitry Nadezhin for bringing this case to my attention!

(in-package "X86ISA")
(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system)

;; ======================================================================

(defconst *mov_test_code*
  ;; MOV r/m8, imm8
  ;; RIP-relative addressing
  ;; Destination = memory location[next rip + sign-extended(#xdd0000fd)]
  ;; ModR/M = #x05 (mod=0, r/m=5, reg=0)
  ;; immediate data=#x01
  '(#xc6 #x05 #xfd #x00 #x00 #xdd #x01))

(trace$ wm08)

(b*
    ;; wm08 should write #x01 to memory location #xdd001078, which is
    ;; the next-rip (#x100000f7b) plus sign-extended value of
    ;; #xdd0000fd (#x-22ffff03).
    ((start-rip #x100000f74)
     (x86 (!ms nil x86))
     (x86 (!fault nil x86))
     (x86 (!app-view t x86))
     (x86 (!rip start-rip x86))
     ((mv flg0 x86)
      (wm64      start-rip  (combine-bytes *mov_test_code*) x86))
     ((when flg0) x86)
     (x86 (x86-fetch-decode-execute x86))
     (- (cw "~% rip: ~x0 ms: ~x1~%" (rip x86) (ms x86))))
  x86)

(defconst *add_test_code*
  ;; ADD r/m8, imm8
  ;; RIP-relative addressing
  ;; Destination = memory location[next rip + sign-extended(#xdd0000fd)]
  ;; Immediate data = #x20
  '(#x80 #x05 #xfd #x00 #x00 #xdd #x20))

(b*
    ;; wm08 should add #x20 to memory location #xdd001078, which
    ;; already contains 1 from the previous test.
    ((start-rip #x100000f74)
     (x86 (!ms nil x86))
     (x86 (!fault nil x86))
     (x86 (!app-view t x86))
     (x86 (!rip start-rip x86))
     ((mv flg0 x86)
      (wm64 start-rip (combine-bytes *add_test_code*) x86))
     ((when flg0) x86)
     (x86 (x86-fetch-decode-execute x86))
     (- (cw "~% rip: ~x0 ms: ~x1~%" (rip x86) (ms x86))))
  x86)

;; ======================================================================

#||

// This program tests RIP-relative addressing.
// gcc rip-relative-addressing.c -o rip-relative-addressing.o
// I just need to see the objdump of the executable and not really run
// the code.

#include <stdio.h>
#include <stdint.h>

void test(void) {

  __asm__ volatile
    (
     "movb  $0x01, 0xdd0000fe(%%rip)\n\t"

     : // output list

     : // input list

     : "cc", "memory");

}
int main () {

  test();
  return 0;

}

||#
