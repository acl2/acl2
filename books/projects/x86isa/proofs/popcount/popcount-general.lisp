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

(include-book "app-view/user-level-memory-utils" :dir :proof-utils :ttags :all)

(local (include-book "centaur/gl/gl" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(set-irrelevant-formals-ok t)

;; ======================================================================

;; C program:
;; // gcc -g -O2 popcount-64.c -o popcount-64.o

;; #include <stdio.h>
;; #include <stdlib.h>

;; int popcount_32 (unsigned int v)
;; {
;;   v = v - ((v >> 1) & 0x55555555);
;;   v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
;;   v = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
;;   return(v);
;; }

;; int popcount_64 (long unsigned int v)
;; {
;;   long unsigned int v1, v2;
;;   // v1: lower 32 bits of v
;;   v1 = (v & 0xFFFFFFFF);
;;   // printf ("\n v1: %lu", v1);
;;   // v2: upper 32 bits of v
;;   v2 = (v >> 32);
;;   // printf ("\n v2: %lu", v2);
;;   return (popcount_32(v1) + popcount_32(v2));
;; }

;; int main (int argc, char *argv[], char *env[])
;; {
;;   long unsigned int v;
;;   printf ("\nEnter the value v: ");
;;   scanf  ("%lu", &v);
;;   printf ("\nPopcount of %lu is: %d\n", v, popcount_64(v));
;;   return 0;
;; }


;; Generalizing the initial x86 state:

(defconst *popcount-32*

  (list
   ;; Section: <popcount_32>:


   (cons #x400610 #x89) ;; mov %edi,%edx
   (cons #x400611 #xfa) ;;
   (cons #x400612 #xd1) ;; shr %edx
   (cons #x400613 #xea) ;;
   (cons #x400614 #x81) ;; and $0x55555555,%edx
   (cons #x400615 #xe2) ;;
   (cons #x400616 #x55) ;;
   (cons #x400617 #x55) ;;
   (cons #x400618 #x55) ;;
   (cons #x400619 #x55) ;;
   (cons #x40061a #x29) ;; sub %edx,%edi
   (cons #x40061b #xd7) ;;
   (cons #x40061c #x89) ;; mov %edi,%eax
   (cons #x40061d #xf8) ;;
   (cons #x40061e #xc1) ;; shr $0x2,%edi
   (cons #x40061f #xef) ;;
   (cons #x400620 #x02) ;;
   (cons #x400621 #x25) ;; and $0x33333333,%eax
   (cons #x400622 #x33) ;;
   (cons #x400623 #x33) ;;
   (cons #x400624 #x33) ;;
   (cons #x400625 #x33) ;;
   (cons #x400626 #x81) ;; and $0x33333333,%edi
   (cons #x400627 #xe7) ;;
   (cons #x400628 #x33) ;;
   (cons #x400629 #x33) ;;
   (cons #x40062a #x33) ;;
   (cons #x40062b #x33) ;;
   (cons #x40062c #x01) ;; add %eax,%edi
   (cons #x40062d #xc7) ;;
   (cons #x40062e #x89) ;; mov %edi,%eax
   (cons #x40062f #xf8) ;;
   (cons #x400630 #xc1) ;; shr $0x4,%eax
   (cons #x400631 #xe8) ;;
   (cons #x400632 #x04) ;;
   (cons #x400633 #x01) ;; add %edi,%eax
   (cons #x400634 #xf8) ;;
   (cons #x400635 #x25) ;; and $0xf0f0f0f,%eax
   (cons #x400636 #x0f) ;;
   (cons #x400637 #x0f) ;;
   (cons #x400638 #x0f) ;;
   (cons #x400639 #x0f) ;;
   (cons #x40063a #x69) ;; imul $0x1010101,%eax,%eax
   (cons #x40063b #xc0) ;;
   (cons #x40063c #x01) ;;
   (cons #x40063d #x01) ;;
   (cons #x40063e #x01) ;;
   (cons #x40063f #x01) ;;
   (cons #x400640 #xc1) ;; shr $0x18,%eax
   (cons #x400641 #xe8) ;;
   (cons #x400642 #x18) ;;
   (cons #x400643 #xc3) ;; retq
   (cons #x400644 #x66) ;; data32 data32 nopw %cs:0x0(%rax,%rax,1)
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

   ))

(defconst *popcount-32-bytes*
  (strip-cdrs *popcount-32*))

(local
 (def-gl-thm x86-popcount-32-symbolic-simulation-helper
   :hyp (unsigned-byte-p 32 rdi)
   :concl
   (equal
    (loghead
     #x8
     (logtail
      #x18
      (*
       #x1010101
       (logand
        #xf0f0f0f
        (logext
         #x20
         (+
          (loghead
           #x20
           (+
            (logand
             #x33333333
             (loghead
              #x20
              (+ (logext #x20 rdi)
                 (- (logand #x55555555
                            (logext #x20
                                    (logtail #x1 rdi)))))))
            (logand
             #x33333333
             (loghead
              #x1e
              (logtail
               #x2
               (+
                (logext #x20 rdi)
                (- (logand #x55555555
                           (logext #x20
                                   (logtail #x1 rdi))))))))))
          (loghead
           #x1c
           (logtail
            #x4
            (+
             (logand
              #x33333333
              (loghead
               #x20
               (+ (logext #x20 rdi)
                  (- (logand #x55555555
                             (logext #x20
                                     (logtail #x1 rdi)))))))
             (logand
              #x33333333
              (loghead
               #x1e
               (logtail
                #x2
                (+
                 (logext #x20 rdi)
                 (-
                  (logand
                   #x55555555
                   (logext #x20
                           (logtail #x1 rdi)))))))))))))))))
    (logcount rdi))

   :g-bindings
   `((rdi    (:g-number ,(increasing-list 0 1 33))))))

(local
 (def-gl-thm x86-popcount-32-symbolic-simulation-helper-1
   :hyp (unsigned-byte-p 32 rdi)
   :concl
   (equal (loghead 32 (logcount rdi))
          (logcount rdi))
   :g-bindings
   `((rdi    (:g-number ,(increasing-list 0 1 33))))))

(local
 (def-gl-thm x86-popcount-32-symbolic-simulation-helper-2
   :hyp (unsigned-byte-p 32 rdi)
   :concl
   (equal (logext 64 (logcount rdi))
          (logcount rdi))
   :g-bindings
   `((rdi    (:g-number ,(increasing-list 0 1 33))))))

(defthm x86-popcount-32-symbolic-simulation
  (implies (and (x86p x86)
                (equal (ms x86) nil)
                (equal (fault x86) nil)
                (64-bit-modep x86)
                (equal (app-view x86) t)
                (n32p (rgfi *rdi* x86))
                (canonical-address-p (rip x86))
                (canonical-address-p (+ -1 (len *popcount-32-bytes*) (rip x86)))
                (program-at (rip x86) *popcount-32-bytes* x86))
           (equal (rgfi *rax* (x86-run 15 x86))
                  (logcount (xr :rgf *rdi* x86))))
  :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules
                                    x86-operation-mode

                                    shr-spec
                                    shr-spec-32
                                    gpr-and-spec-4
                                    gpr-add-spec-1
                                    gpr-add-spec-4
                                    gpr-add-spec-8
                                    gpr-sub-spec-8
                                    jcc/cmovcc/setcc-spec
                                    imul-spec
                                    imul-spec-32
                                    gpr-sub-spec-4

                                    one-byte-opcode-execute
                                    !rgfi-size
                                    x86-operand-to-reg/mem
                                    wr64
                                    wr32
                                    rr08
                                    rr32
                                    rr64
                                    rml32
                                    rml64
                                    wml32
                                    wml64
                                    rr32
                                    x86-operand-from-modr/m-and-sib-bytes
                                    check-instruction-length
                                    riml-size
                                    riml32
                                    n32-to-i32
                                    n64-to-i64
                                    riml08
                                    two-byte-opcode-decode-and-execute
                                    x86-effective-addr
                                    subset-p
                                    ;; Flags
                                    write-user-rflags)

                                   (unsigned-byte-p
                                    las-to-pas
                                    default-+-2
                                    get-prefixes-opener-lemma-group-1-prefix
                                    get-prefixes-opener-lemma-group-2-prefix
                                    get-prefixes-opener-lemma-group-3-prefix
                                    get-prefixes-opener-lemma-group-4-prefix)))
          (if (equal (car id) '(1))
              '(:in-theory (e/d* (signed-byte-p) ()))
            nil)))

;; ----------------------------------------------------------------------

(defconst *popcount-64-program*
  (list

   ;; Section: <popcount_64>:


   (cons #x400650 #x89) ;; mov %edi,%edx
   (cons #x400651 #xfa) ;;
   (cons #x400652 #x89) ;; mov %edx,%ecx
   (cons #x400653 #xd1) ;;
   (cons #x400654 #xd1) ;; shr %ecx
   (cons #x400655 #xe9) ;;
   (cons #x400656 #x81) ;; and $0x55555555,%ecx
   (cons #x400657 #xe1) ;;
   (cons #x400658 #x55) ;;
   (cons #x400659 #x55) ;;
   (cons #x40065a #x55) ;;
   (cons #x40065b #x55) ;;
   (cons #x40065c #x29) ;; sub %ecx,%edx
   (cons #x40065d #xca) ;;
   (cons #x40065e #x89) ;; mov %edx,%eax
   (cons #x40065f #xd0) ;;
   (cons #x400660 #xc1) ;; shr $0x2,%edx
   (cons #x400661 #xea) ;;
   (cons #x400662 #x02) ;;
   (cons #x400663 #x25) ;; and $0x33333333,%eax
   (cons #x400664 #x33) ;;
   (cons #x400665 #x33) ;;
   (cons #x400666 #x33) ;;
   (cons #x400667 #x33) ;;
   (cons #x400668 #x81) ;; and $0x33333333,%edx
   (cons #x400669 #xe2) ;;
   (cons #x40066a #x33) ;;
   (cons #x40066b #x33) ;;
   (cons #x40066c #x33) ;;
   (cons #x40066d #x33) ;;
   (cons #x40066e #x01) ;; add %eax,%edx
   (cons #x40066f #xc2) ;;
   (cons #x400670 #x89) ;; mov %edx,%eax
   (cons #x400671 #xd0) ;;
   (cons #x400672 #xc1) ;; shr $0x4,%eax
   (cons #x400673 #xe8) ;;
   (cons #x400674 #x04) ;;
   (cons #x400675 #x01) ;; add %eax,%edx
   (cons #x400676 #xc2) ;;
   (cons #x400677 #x48) ;; mov %rdi,%rax
   (cons #x400678 #x89) ;;
   (cons #x400679 #xf8) ;;
   (cons #x40067a #x48) ;; shr $0x20,%rax
   (cons #x40067b #xc1) ;;
   (cons #x40067c #xe8) ;;
   (cons #x40067d #x20) ;;
   (cons #x40067e #x81) ;; and $0xf0f0f0f,%edx
   (cons #x40067f #xe2) ;;
   (cons #x400680 #x0f) ;;
   (cons #x400681 #x0f) ;;
   (cons #x400682 #x0f) ;;
   (cons #x400683 #x0f) ;;
   (cons #x400684 #x89) ;; mov %eax,%ecx
   (cons #x400685 #xc1) ;;
   (cons #x400686 #xd1) ;; shr %ecx
   (cons #x400687 #xe9) ;;
   (cons #x400688 #x81) ;; and $0x55555555,%ecx
   (cons #x400689 #xe1) ;;
   (cons #x40068a #x55) ;;
   (cons #x40068b #x55) ;;
   (cons #x40068c #x55) ;;
   (cons #x40068d #x55) ;;
   (cons #x40068e #x29) ;; sub %ecx,%eax
   (cons #x40068f #xc8) ;;
   (cons #x400690 #x89) ;; mov %eax,%ecx
   (cons #x400691 #xc1) ;;
   (cons #x400692 #xc1) ;; shr $0x2,%eax
   (cons #x400693 #xe8) ;;
   (cons #x400694 #x02) ;;
   (cons #x400695 #x81) ;; and $0x33333333,%ecx
   (cons #x400696 #xe1) ;;
   (cons #x400697 #x33) ;;
   (cons #x400698 #x33) ;;
   (cons #x400699 #x33) ;;
   (cons #x40069a #x33) ;;
   (cons #x40069b #x25) ;; and $0x33333333,%eax
   (cons #x40069c #x33) ;;
   (cons #x40069d #x33) ;;
   (cons #x40069e #x33) ;;
   (cons #x40069f #x33) ;;
   (cons #x4006a0 #x01) ;; add %ecx,%eax
   (cons #x4006a1 #xc8) ;;
   (cons #x4006a2 #x89) ;; mov %eax,%ecx
   (cons #x4006a3 #xc1) ;;
   (cons #x4006a4 #xc1) ;; shr $0x4,%ecx
   (cons #x4006a5 #xe9) ;;
   (cons #x4006a6 #x04) ;;
   (cons #x4006a7 #x01) ;; add %ecx,%eax
   (cons #x4006a8 #xc8) ;;
   (cons #x4006a9 #x25) ;; and $0xf0f0f0f,%eax
   (cons #x4006aa #x0f) ;;
   (cons #x4006ab #x0f) ;;
   (cons #x4006ac #x0f) ;;
   (cons #x4006ad #x0f) ;;
   (cons #x4006ae #x69) ;; imul $0x1010101,%edx,%edx
   (cons #x4006af #xd2) ;;
   (cons #x4006b0 #x01) ;;
   (cons #x4006b1 #x01) ;;
   (cons #x4006b2 #x01) ;;
   (cons #x4006b3 #x01) ;;
   (cons #x4006b4 #x69) ;; imul $0x1010101,%eax,%eax
   (cons #x4006b5 #xc0) ;;
   (cons #x4006b6 #x01) ;;
   (cons #x4006b7 #x01) ;;
   (cons #x4006b8 #x01) ;;
   (cons #x4006b9 #x01) ;;
   (cons #x4006ba #xc1) ;; shr $0x18,%edx
   (cons #x4006bb #xea) ;;
   (cons #x4006bc #x18) ;;
   (cons #x4006bd #xc1) ;; shr $0x18,%eax
   (cons #x4006be #xe8) ;;
   (cons #x4006bf #x18) ;;
   (cons #x4006c0 #x01) ;; add %edx,%eax
   (cons #x4006c1 #xd0) ;;
   (cons #x4006c2 #xc3) ;; retq
   (cons #x4006c3 #x66) ;; nopw %cs:0x0(%rax,%rax,1)
   (cons #x4006c4 #x2e) ;;
   (cons #x4006c5 #x0f) ;;
   (cons #x4006c6 #x1f) ;;
   (cons #x4006c7 #x84) ;;
   (cons #x4006c8 #x00) ;;
   (cons #x4006c9 #x00) ;;
   (cons #x4006ca #x00) ;;
   (cons #x4006cb #x00) ;;
   (cons #x4006cc #x00) ;;
   (cons #x4006cd #x0f) ;; nopl (%rax)
   (cons #x4006ce #x1f) ;;
   (cons #x4006cf #x00) ;;

   ))

(defconst *popcount-64-bytes*
  (strip-cdrs *popcount-64-program*))

(defconst *popcount-count* 34)

(local
 (def-gl-thm x86-popcount-64-symbolic-simulation-helper-1
   :hyp (signed-byte-p 64 rdi)
   :concl
   (equal
    (logext
     64
     (loghead
      32
      (+
       (ifix
        (logtail
         24
         (mv-nth
          1
          (imul-spec-32
           (logand
            252645135
            (loghead
             32
             (+
              (loghead
               32
               (+
                (logand
                 858993459
                 (loghead
                  32
                  (+
                   (logext 32 rdi)
                   (-
                    (logand
                     1431655765
                     (logext 32
                             (loghead 31
                                      (logtail 1 rdi))))))))
                (logand
                 858993459
                 (loghead
                  30
                  (logtail
                   2
                   (+
                    (logext 32 rdi)
                    (-
                     (logand
                      1431655765
                      (logext 32
                              (loghead 31
                                       (logtail 1 rdi)))))))))))
              (loghead
               28
               (logtail
                4
                (+
                 (logand
                  858993459
                  (loghead
                   32
                   (+
                    (logext 32 rdi)
                    (-
                     (logand
                      1431655765
                      (logext 32
                              (loghead 31
                                       (logtail 1 rdi))))))))
                 (logand
                  858993459
                  (loghead
                   30
                   (logtail
                    2
                    (+
                     (logext 32 rdi)
                     (-
                      (logand
                       1431655765
                       (logext
                        32
                        (loghead 31
                                 (logtail 1 rdi)))))))))))))))
           16843009))))
       (ifix
        (logtail
         24
         (mv-nth
          1
          (imul-spec-32
           (logand
            252645135
            (loghead
             32
             (+
              (loghead
               32
               (+
                (logand
                 858993459
                 (loghead
                  32
                  (+
                   (logtail 32 rdi)
                   (-
                    (logand
                     1431655765
                     (logext 32
                             (loghead 31
                                      (logtail 33 rdi))))))))
                (logand
                 858993459
                 (loghead
                  30
                  (logtail
                   2
                   (+
                    (logtail 32 rdi)
                    (-
                     (logand
                      1431655765
                      (logext
                       32
                       (loghead 31
                                (logtail 33 rdi)))))))))))
              (loghead
               28
               (logtail
                4
                (+
                 (logand
                  858993459
                  (loghead
                   32
                   (+
                    (logtail 32 rdi)
                    (-
                     (logand
                      1431655765
                      (logext 32
                              (loghead 31
                                       (logtail 33 rdi))))))))
                 (logand
                  858993459
                  (loghead
                   30
                   (logtail
                    2
                    (+
                     (logtail 32 rdi)
                     (-
                      (logand
                       1431655765
                       (logext
                        32
                        (loghead 31
                                 (logtail 33 rdi)))))))))))))))
           16843009)))))))
    (logcount (loghead 64 rdi)))

   :g-bindings
   `((rdi    (:g-number ,(increasing-list 0 1 65))))))

(local
 (def-gl-thm x86-popcount-64-symbolic-simulation-helper-2
   :hyp (signed-byte-p 64 rdi)
   :concl
   (equal (logext 32 (logcount (loghead 64 rdi)))
          (logcount (loghead 64 rdi)))

   :g-bindings
   `((rdi    (:g-number ,(increasing-list 0 1 65))))))


;;  1 mov %edi,%edx
;;  2 mov %edx,%ecx
;;  3 shr %ecx
;;  4 and $0x55555555,%ecx
;;  5 sub %ecx,%edx
;;  6 mov %edx,%eax
;;  7 shr $0x2,%edx
;;  8 and $0x33333333,%eax
;;  9 and $0x33333333,%edx
;; 10 add %eax,%edx
;; 11 mov %edx,%eax
;; 12 shr $0x4,%eax
;; 13 add %eax,%edx
;; 14 mov %rdi,%rax
;; 15 shr $0x20,%rax
;; 16 and $0xf0f0f0f,%edx
;; 17 mov %eax,%ecx
;; 18 shr %ecx
;; 19 and $0x55555555,%ecx
;; 20 sub %ecx,%eax
;; 21 mov %eax,%ecx
;; 22 shr $0x2,%eax
;; 23 and $0x33333333,%ecx
;; 24 and $0x33333333,%eax
;; 25 add %ecx,%eax
;; 26 mov %eax,%ecx
;; 27 shr $0x4,%ecx
;; 28 add %ecx,%eax
;; 29 and $0xf0f0f0f,%eax
;; 30 imul $0x1010101,%edx,%edx
;; 31 imul $0x1010101,%eax,%eax
;; 32 shr $0x18,%edx
;; 33 shr $0x18,%eax
;; 34 add %edx,%eax
;; 35 retq
;; 36 nopw %cs:0x0(%rax,%rax,1)
;; 37 nopl (%rax)

(local
 ;; From accumulated persistence.
 (in-theory (e/d* ()
                  ((:rewrite loghead-of-non-integerp)
                   (:type-prescription bitops::logtail-natp)
                   (:rewrite default-unary-minus)
                   (:rewrite default-+-1)
                   (:rewrite loghead-zero-smaller)
                   (:rewrite weed-out-irrelevant-logand-when-first-operand-constant)
                   (:rewrite logand-redundant)
                   (:rewrite zf-spec-thm)
                   (:rewrite acl2::ifix-when-not-integerp)
                   (:linear bitops::logand->=-0-linear-2)
                   (:linear bitops::upper-bound-of-logand . 2)
                   (:rewrite bitops::logbitp-when-bitmaskp)
                   (:rewrite acl2::ash-0)
                   (:rewrite greater-logbitp-of-unsigned-byte-p . 1)
                   (:rewrite acl2::zip-open)
                   (:type-prescription natp)
                   (:type-prescription acl2::logtail-type)
                   (:rewrite canonical-address-p-limits-thm-3)
                   (:rewrite default-<-1)
                   (:rewrite acl2::consp-when-member-equal-of-atom-listp)
                   (:rewrite acl2::difference-unsigned-byte-p)
                   (:rewrite bitops::signed-byte-p-monotonicity)
                   (:rewrite default-+-2)
                   (:rewrite subset-p-cdr-y)
                   (:rewrite default-<-2)
                   (:rewrite acl2::equal-of-booleans-rewrite)
                   (:rewrite canonical-address-p-limits-thm-2)
                   (:rewrite canonical-address-p-limits-thm-1)
                   (:rewrite set::sets-are-true-lists)
                   (:rewrite bitops::logior-fold-consts)
                   (:linear n01p-zf-spec)
                   (:definition true-listp)
                   (:rewrite acl2::alistp-when-hons-duplicity-alist-p)
                   (:type-prescription xw)
                   (:type-prescription bitp)
                   (:rewrite gl::nonnil-symbol-listp-true-listp)
                   (:rewrite set::nonempty-means-set)
                   (:rewrite acl2::hons-duplicity-alist-p-when-not-consp)
                   (:rewrite acl2::unsigned-byte-p-loghead)
                   (:rewrite default-*-2)
                   (:linear bitops::logand-<-0-linear)
                   (:rewrite bitops::logior-equal-0)
                   (:rewrite unsigned-byte-p-of-logand-1)
                   (:type-prescription set::setp-type)
                   (:type-prescription acl2::nonnil-symbol-listp)
                   (:type-prescription acl2::hons-duplicity-alist-p)
                   (:type-prescription set::empty-type)
                   (:linear bsf-posp-strict-upper-bound)
                   (:rewrite signed-byte-p-limits-thm)
                   (:rewrite acl2::posp-redefinition)
                   (:linear bitops::logior-<-0-linear-2)
                   (:linear bitops::logior-<-0-linear-1)
                   (:linear bitops::logior->=-0-linear)
                   (:rewrite set::in-set)
                   (:rewrite acl2::consp-of-car-when-atom-listp)
                   (:rewrite default-*-1)
                   (:type-prescription zip)
                   (:linear n01p-pf-spec32)
                   (:rewrite acl2::zp-when-integerp)
                   (:rewrite acl2::zp-when-gt-0)
                   (:rewrite get-prefixes-opener-lemma-zero-cnt)
                   (:linear n01p-of-spec32)
                   (:linear n01p-sub-af-spec32)
                   (:linear n01p-add-af-spec32)
                   (:type-prescription posp)
                   (:rewrite x86-run-halted)
                   (:type-prescription acl2::logtail$inline)
                   (:rewrite bitops::unsigned-byte-p-incr)
                   (:linear bitops::upper-bound-of-logand . 1)
                   (:linear bitops::logand->=-0-linear-1)
                   (:rewrite rb-returns-x86-in-non-marking-view-if-no-error)
                   (:linear acl2::logext-bounds)
                   (:rewrite acl2::natp-when-integerp)
                   (:rewrite acl2::natp-when-gte-0)
                   (:rewrite acl2::reduce-integerp-+-constant)
                   (:linear mv-nth-1-imul-spec-32)))))

(local
 (defthm x86-popcount-64-symbolic-simulation-snorkeling
   (implies (and (x86p x86)
                 (equal (ms x86) nil)
                 (equal (fault x86) nil)
                 (64-bit-modep x86)
                 (equal (app-view x86) t)
                 (unsigned-byte-p 64 n)
                 (equal n (rr64 *rdi* x86))
                 (canonical-address-p (rip x86))
                 (canonical-address-p (+ -1 (len *popcount-64-bytes*) (rip x86)))
                 (program-at (rip x86) *popcount-64-bytes* x86))
            (equal (rgfi *rax* (x86-run 16 (x86-run 18 x86)))
                   (logcount n)))
   :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules
                                     rflag-RoWs-enables
                                     x86-operation-mode

                                     shr-spec
                                     shr-spec-32
                                     shr-spec-64
                                     gpr-and-spec-4
                                     gpr-add-spec-1
                                     gpr-add-spec-4
                                     gpr-add-spec-8
                                     gpr-sub-spec-8
                                     jcc/cmovcc/setcc-spec
                                     imul-spec
                                     ;; Intentionally disabled to
                                     ;; prevent unnecessary case
                                     ;; splits stemming from flag
                                     ;; computations.  See
                                     ;; x86-popcount-64-symbolic-simulation-helper-2.
                                     ;; imul-spec-32
                                     gpr-sub-spec-4

                                     one-byte-opcode-execute
                                     !rgfi-size
                                     x86-operand-to-reg/mem
                                     wr64
                                     wr32
                                     rr08
                                     rr32
                                     rr64
                                     rml32
                                     rml64
                                     wml32
                                     wml64
                                     rr32
                                     x86-operand-from-modr/m-and-sib-bytes
                                     check-instruction-length
                                     riml-size
                                     riml32
                                     n32-to-i32
                                     n64-to-i64
                                     riml08
                                     two-byte-opcode-decode-and-execute
                                     x86-effective-addr
                                     subset-p
                                     ;; Flags
                                     write-user-rflags
                                     mv-nth)

                                    (unsigned-byte-p
                                     las-to-pas
                                     default-+-2
                                     get-prefixes-opener-lemma-group-1-prefix
                                     get-prefixes-opener-lemma-group-2-prefix
                                     get-prefixes-opener-lemma-group-3-prefix
                                     get-prefixes-opener-lemma-group-4-prefix)))
           (if (equal (car id) '(1))
               '(:in-theory (e/d* (signed-byte-p mv-nth) ()))
             nil))))

(defthm x86-popcount-64-symbolic-simulation
  (implies (and (x86p x86)
                (equal (ms x86) nil)
                (equal (fault x86) nil)
                (64-bit-modep x86)
                (equal (app-view x86) t)
                (unsigned-byte-p 64 n)
                (equal n (rr64 *rdi* x86))
                (canonical-address-p (rip x86))
                (canonical-address-p (+ -1 (len *popcount-64-bytes*) (rip x86)))
                (program-at (rip x86) *popcount-64-bytes* x86))
           (equal (rgfi *rax* (x86-run *popcount-count* x86))
                  (logcount n)))
  :hints (("Goal"
           :use ((:instance x86-popcount-64-symbolic-simulation-snorkeling)
                 (:instance x86-run-plus (n1 18) (n2 16)))
           :in-theory (e/d* ()
                            (x86-popcount-64-symbolic-simulation-snorkeling
                             x86-run-plus)))))

;; ======================================================================
