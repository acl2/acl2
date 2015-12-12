;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "programmer-level-mode/programmer-level-memory-utils" :dir :proof-utils :ttags :all)
(include-book "../../tools/execution/x86-init-state" :ttags :all)
(include-book "centaur/gl/gl" :dir :system)

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
;;  if (v == 0x052738000000)
;;   return (8);

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

(defconst *popcount/popcount-64-bug-binary*
  (list

   ;; Section: <popcount_32>:


   (cons #x4005c0 #x89) ;; mov %edi,%edx
   (cons #x4005c1 #xfa) ;;
   (cons #x4005c2 #x89) ;; mov %edi,%eax
   (cons #x4005c3 #xf8) ;;
   (cons #x4005c4 #xd1) ;; shr %edx
   (cons #x4005c5 #xea) ;;
   (cons #x4005c6 #x81) ;; and $0x55555555,%edx
   (cons #x4005c7 #xe2) ;;
   (cons #x4005c8 #x55) ;;
   (cons #x4005c9 #x55) ;;
   (cons #x4005ca #x55) ;;
   (cons #x4005cb #x55) ;;
   (cons #x4005cc #x29) ;; sub %edx,%eax
   (cons #x4005cd #xd0) ;;
   (cons #x4005ce #x89) ;; mov %eax,%edx
   (cons #x4005cf #xc2) ;;
   (cons #x4005d0 #xc1) ;; shr $0x2,%eax
   (cons #x4005d1 #xe8) ;;
   (cons #x4005d2 #x02) ;;
   (cons #x4005d3 #x81) ;; and $0x33333333,%edx
   (cons #x4005d4 #xe2) ;;
   (cons #x4005d5 #x33) ;;
   (cons #x4005d6 #x33) ;;
   (cons #x4005d7 #x33) ;;
   (cons #x4005d8 #x33) ;;
   (cons #x4005d9 #x25) ;; and $0x33333333,%eax
   (cons #x4005da #x33) ;;
   (cons #x4005db #x33) ;;
   (cons #x4005dc #x33) ;;
   (cons #x4005dd #x33) ;;
   (cons #x4005de #x01) ;; add %edx,%eax
   (cons #x4005df #xd0) ;;
   (cons #x4005e0 #x89) ;; mov %eax,%edx
   (cons #x4005e1 #xc2) ;;
   (cons #x4005e2 #xc1) ;; shr $0x4,%edx
   (cons #x4005e3 #xea) ;;
   (cons #x4005e4 #x04) ;;
   (cons #x4005e5 #x8d) ;; lea (%rdx,%rax,1),%eax
   (cons #x4005e6 #x04) ;;
   (cons #x4005e7 #x02) ;;
   (cons #x4005e8 #x25) ;; and $0xf0f0f0f,%eax
   (cons #x4005e9 #x0f) ;;
   (cons #x4005ea #x0f) ;;
   (cons #x4005eb #x0f) ;;
   (cons #x4005ec #x0f) ;;
   (cons #x4005ed #x69) ;; imul $0x1010101,%eax,%eax
   (cons #x4005ee #xc0) ;;
   (cons #x4005ef #x01) ;;
   (cons #x4005f0 #x01) ;;
   (cons #x4005f1 #x01) ;;
   (cons #x4005f2 #x01) ;;
   (cons #x4005f3 #xc1) ;; shr $0x18,%eax
   (cons #x4005f4 #xe8) ;;
   (cons #x4005f5 #x18) ;;
   (cons #x4005f6 #xc3) ;; retq
   (cons #x4005f7 #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x4005f8 #x0f) ;;
   (cons #x4005f9 #x1f) ;;
   (cons #x4005fa #x84) ;;
   (cons #x4005fb #x00) ;;
   (cons #x4005fc #x00) ;;
   (cons #x4005fd #x00) ;;
   (cons #x4005fe #x00) ;;
   (cons #x4005ff #x00) ;;

   ;; Section: <popcount_64>:


   (cons #x400600 #x48) ;; mov $0x52738000000,%rdx
   (cons #x400601 #xba) ;;
   (cons #x400602 #x00) ;;
   (cons #x400603 #x00) ;;
   (cons #x400604 #x00) ;;
   (cons #x400605 #x38) ;;
   (cons #x400606 #x27) ;;
   (cons #x400607 #x05) ;;
   (cons #x400608 #x00) ;;
   (cons #x400609 #x00) ;;
   (cons #x40060a #xb8) ;; mov $0x8,%eax
   (cons #x40060b #x08) ;;
   (cons #x40060c #x00) ;;
   (cons #x40060d #x00) ;;
   (cons #x40060e #x00) ;;
   (cons #x40060f #x48) ;; cmp %rdx,%rdi
   (cons #x400610 #x39) ;;
   (cons #x400611 #xd7) ;;
   (cons #x400612 #x74) ;; je 400686 <popcount_64+0x86>
   (cons #x400613 #x72) ;;
   (cons #x400614 #x89) ;; mov %edi,%edx
   (cons #x400615 #xfa) ;;
   (cons #x400616 #x89) ;; mov %edi,%eax
   (cons #x400617 #xf8) ;;
   (cons #x400618 #x48) ;; shr $0x20,%rdi
   (cons #x400619 #xc1) ;;
   (cons #x40061a #xef) ;;
   (cons #x40061b #x20) ;;
   (cons #x40061c #xd1) ;; shr %edx
   (cons #x40061d #xea) ;;
   (cons #x40061e #x89) ;; mov %edi,%ecx
   (cons #x40061f #xf9) ;;
   (cons #x400620 #x81) ;; and $0x55555555,%edx
   (cons #x400621 #xe2) ;;
   (cons #x400622 #x55) ;;
   (cons #x400623 #x55) ;;
   (cons #x400624 #x55) ;;
   (cons #x400625 #x55) ;;
   (cons #x400626 #xd1) ;; shr %ecx
   (cons #x400627 #xe9) ;;
   (cons #x400628 #x29) ;; sub %edx,%eax
   (cons #x400629 #xd0) ;;
   (cons #x40062a #x81) ;; and $0x55555555,%ecx
   (cons #x40062b #xe1) ;;
   (cons #x40062c #x55) ;;
   (cons #x40062d #x55) ;;
   (cons #x40062e #x55) ;;
   (cons #x40062f #x55) ;;
   (cons #x400630 #x89) ;; mov %eax,%edx
   (cons #x400631 #xc2) ;;
   (cons #x400632 #xc1) ;; shr $0x2,%eax
   (cons #x400633 #xe8) ;;
   (cons #x400634 #x02) ;;
   (cons #x400635 #x29) ;; sub %ecx,%edi
   (cons #x400636 #xcf) ;;
   (cons #x400637 #x81) ;; and $0x33333333,%edx
   (cons #x400638 #xe2) ;;
   (cons #x400639 #x33) ;;
   (cons #x40063a #x33) ;;
   (cons #x40063b #x33) ;;
   (cons #x40063c #x33) ;;
   (cons #x40063d #x25) ;; and $0x33333333,%eax
   (cons #x40063e #x33) ;;
   (cons #x40063f #x33) ;;
   (cons #x400640 #x33) ;;
   (cons #x400641 #x33) ;;
   (cons #x400642 #x01) ;; add %edx,%eax
   (cons #x400643 #xd0) ;;
   (cons #x400644 #x89) ;; mov %eax,%edx
   (cons #x400645 #xc2) ;;
   (cons #x400646 #xc1) ;; shr $0x4,%edx
   (cons #x400647 #xea) ;;
   (cons #x400648 #x04) ;;
   (cons #x400649 #x8d) ;; lea (%rdx,%rax,1),%eax
   (cons #x40064a #x04) ;;
   (cons #x40064b #x02) ;;
   (cons #x40064c #x89) ;; mov %edi,%edx
   (cons #x40064d #xfa) ;;
   (cons #x40064e #xc1) ;; shr $0x2,%edi
   (cons #x40064f #xef) ;;
   (cons #x400650 #x02) ;;
   (cons #x400651 #x81) ;; and $0x33333333,%edx
   (cons #x400652 #xe2) ;;
   (cons #x400653 #x33) ;;
   (cons #x400654 #x33) ;;
   (cons #x400655 #x33) ;;
   (cons #x400656 #x33) ;;
   (cons #x400657 #x81) ;; and $0x33333333,%edi
   (cons #x400658 #xe7) ;;
   (cons #x400659 #x33) ;;
   (cons #x40065a #x33) ;;
   (cons #x40065b #x33) ;;
   (cons #x40065c #x33) ;;
   (cons #x40065d #x01) ;; add %edx,%edi
   (cons #x40065e #xd7) ;;
   (cons #x40065f #x25) ;; and $0xf0f0f0f,%eax
   (cons #x400660 #x0f) ;;
   (cons #x400661 #x0f) ;;
   (cons #x400662 #x0f) ;;
   (cons #x400663 #x0f) ;;
   (cons #x400664 #x89) ;; mov %edi,%edx
   (cons #x400665 #xfa) ;;
   (cons #x400666 #xc1) ;; shr $0x4,%edx
   (cons #x400667 #xea) ;;
   (cons #x400668 #x04) ;;
   (cons #x400669 #x01) ;; add %edi,%edx
   (cons #x40066a #xfa) ;;
   (cons #x40066b #x81) ;; and $0xf0f0f0f,%edx
   (cons #x40066c #xe2) ;;
   (cons #x40066d #x0f) ;;
   (cons #x40066e #x0f) ;;
   (cons #x40066f #x0f) ;;
   (cons #x400670 #x0f) ;;
   (cons #x400671 #x69) ;; imul $0x1010101,%eax,%eax
   (cons #x400672 #xc0) ;;
   (cons #x400673 #x01) ;;
   (cons #x400674 #x01) ;;
   (cons #x400675 #x01) ;;
   (cons #x400676 #x01) ;;
   (cons #x400677 #x69) ;; imul $0x1010101,%edx,%edx
   (cons #x400678 #xd2) ;;
   (cons #x400679 #x01) ;;
   (cons #x40067a #x01) ;;
   (cons #x40067b #x01) ;;
   (cons #x40067c #x01) ;;
   (cons #x40067d #xc1) ;; shr $0x18,%eax
   (cons #x40067e #xe8) ;;
   (cons #x40067f #x18) ;;
   (cons #x400680 #xc1) ;; shr $0x18,%edx
   (cons #x400681 #xea) ;;
   (cons #x400682 #x18) ;;
   (cons #x400683 #x8d) ;; lea (%rdx,%rax,1),%eax
   (cons #x400684 #x04) ;;
   (cons #x400685 #x02) ;;
   (cons #x400686 #xf3) ;; repz retq
   (cons #x400687 #xc3) ;;
   (cons #x400688 #x0f) ;; nopl 0x0(%rax,%rax,1)
   (cons #x400689 #x1f) ;;
   (cons #x40068a #x84) ;;
   (cons #x40068b #x00) ;;
   (cons #x40068c #x00) ;;
   (cons #x40068d #x00) ;;
   (cons #x40068e #x00) ;;
   (cons #x40068f #x00) ;;

   ;; Section: <main>:


   (cons #x400690 #x53) ;; push %rbx
   (cons #x400691 #xbe) ;; mov $0x4007dc,%esi
   (cons #x400692 #xdc) ;;
   (cons #x400693 #x07) ;;
   (cons #x400694 #x40) ;;
   (cons #x400695 #x00) ;;
   (cons #x400696 #xbf) ;; mov $0x1,%edi
   (cons #x400697 #x01) ;;
   (cons #x400698 #x00) ;;
   (cons #x400699 #x00) ;;
   (cons #x40069a #x00) ;;
   (cons #x40069b #x31) ;; xor %eax,%eax
   (cons #x40069c #xc0) ;;
   (cons #x40069d #x48) ;; sub $0x10,%rsp
   (cons #x40069e #x83) ;;
   (cons #x40069f #xec) ;;
   (cons #x4006a0 #x10) ;;
   (cons #x4006a1 #xe8) ;; callq 400498 <__printf_chk@plt>
   (cons #x4006a2 #xf2) ;;
   (cons #x4006a3 #xfd) ;;
   (cons #x4006a4 #xff) ;;
   (cons #x4006a5 #xff) ;;
   (cons #x4006a6 #x48) ;; lea 0x8(%rsp),%rsi
   (cons #x4006a7 #x8d) ;;
   (cons #x4006a8 #x74) ;;
   (cons #x4006a9 #x24) ;;
   (cons #x4006aa #x08) ;;
   (cons #x4006ab #xbf) ;; mov $0x4007f1,%edi
   (cons #x4006ac #xf1) ;;
   (cons #x4006ad #x07) ;;
   (cons #x4006ae #x40) ;;
   (cons #x4006af #x00) ;;
   (cons #x4006b0 #x31) ;; xor %eax,%eax
   (cons #x4006b1 #xc0) ;;
   (cons #x4006b2 #xe8) ;; callq 4004b8 <__isoc99_scanf@plt>
   (cons #x4006b3 #x01) ;;
   (cons #x4006b4 #xfe) ;;
   (cons #x4006b5 #xff) ;;
   (cons #x4006b6 #xff) ;;
   (cons #x4006b7 #x48) ;; mov 0x8(%rsp),%rbx
   (cons #x4006b8 #x8b) ;;
   (cons #x4006b9 #x5c) ;;
   (cons #x4006ba #x24) ;;
   (cons #x4006bb #x08) ;;
   (cons #x4006bc #x48) ;; mov %rbx,%rdi
   (cons #x4006bd #x89) ;;
   (cons #x4006be #xdf) ;;
   (cons #x4006bf #xe8) ;; callq 400600 <popcount_64>
   (cons #x4006c0 #x3c) ;;
   (cons #x4006c1 #xff) ;;
   (cons #x4006c2 #xff) ;;
   (cons #x4006c3 #xff) ;;
   (cons #x4006c4 #x48) ;; mov %rbx,%rdx
   (cons #x4006c5 #x89) ;;
   (cons #x4006c6 #xda) ;;
   (cons #x4006c7 #x89) ;; mov %eax,%ecx
   (cons #x4006c8 #xc1) ;;
   (cons #x4006c9 #xbe) ;; mov $0x4007f5,%esi
   (cons #x4006ca #xf5) ;;
   (cons #x4006cb #x07) ;;
   (cons #x4006cc #x40) ;;
   (cons #x4006cd #x00) ;;
   (cons #x4006ce #xbf) ;; mov $0x1,%edi
   (cons #x4006cf #x01) ;;
   (cons #x4006d0 #x00) ;;
   (cons #x4006d1 #x00) ;;
   (cons #x4006d2 #x00) ;;
   (cons #x4006d3 #x31) ;; xor %eax,%eax
   (cons #x4006d4 #xc0) ;;
   (cons #x4006d5 #xe8) ;; callq 400498 <__printf_chk@plt>
   (cons #x4006d6 #xbe) ;;
   (cons #x4006d7 #xfd) ;;
   (cons #x4006d8 #xff) ;;
   (cons #x4006d9 #xff) ;;
   (cons #x4006da #x31) ;; xor %eax,%eax
   (cons #x4006db #xc0) ;;
   (cons #x4006dc #x48) ;; add $0x10,%rsp
   (cons #x4006dd #x83) ;;
   (cons #x4006de #xc4) ;;
   (cons #x4006df #x10) ;;
   (cons #x4006e0 #x5b) ;; pop %rbx
   (cons #x4006e1 #xc3) ;; retq
   (cons #x4006e2 #x90) ;; nop
   (cons #x4006e3 #x90) ;; nop
   (cons #x4006e4 #x90) ;; nop
   (cons #x4006e5 #x90) ;; nop
   (cons #x4006e6 #x90) ;; nop
   (cons #x4006e7 #x90) ;; nop
   (cons #x4006e8 #x90) ;; nop
   (cons #x4006e9 #x90) ;; nop
   (cons #x4006ea #x90) ;; nop
   (cons #x4006eb #x90) ;; nop
   (cons #x4006ec #x90) ;; nop
   (cons #x4006ed #x90) ;; nop
   (cons #x4006ee #x90) ;; nop
   (cons #x4006ef #x90) ;; nop
   ))

;; create-undef is a constrained function. It always appears wrapped in a
;; loghead when used to generate undefined values of flags --- (loghead 1
;; (create-undef x)). GL can figure out that undefined flags are just one bit
;; wide. We tell GL using gl-set-interpreted that create-undef should never be
;; opened for bit-blasting. Because this program doesn't ever use any undefined
;; flags, we don't need to do any term-level reasoning in order to prove
;; properties about this program.

(gl::gl-set-uninterpreted create-undef)

;; (ACL2::must-fail
;;  (def-gl-thm x86-popcount-correct
;;    :hyp (and (natp n)
;;              (< n (expt 2 64)))
;;    :concl (b* ((start-address #x400600)
;;                (halt-address #x400686)
;;                (x86 (!programmer-level-mode t (create-x86)))
;;                ((mv flg x86)
;;                 (init-x86-state
;;                  nil start-address halt-address
;;                  nil nil nil 0
;;                  *popcount/popcount-64-bug-binary*
;;                  x86))
;;                (x86 (!rgfi *rdi* n x86))
;;                (x86 (!rgfi *rsp* *2^30* x86))
;;                (count 300)
;;                (x86 (x86-run count x86)))
;;               (and (equal (rgfi *rax* x86)
;;                           (logcount n))
;;                    (equal flg nil)
;;                    (equal (rip x86)
;;                           (+ 1 halt-address))))
;;    :g-bindings
;;    `((n   (:g-number ,(gl-int 0 1 65))))
;;    :n-counterexamples 3
;;    :abort-indeterminate t
;;    :exec-ctrex nil
;;    :rule-classes nil))

(def-gl-thm x86-popcount-correct
  :hyp (and (natp n)
            (< n (expt 2 64)))
  :concl (b* ((start-address #x400600)
              (halt-address #x400686)
              (x86 (!programmer-level-mode t (create-x86)))
              ((mv flg x86)
               (init-x86-state
                nil start-address halt-address
                nil nil nil 0
                *popcount/popcount-64-bug-binary*
                x86))
              (x86 (!rgfi *rdi* n x86))
              (x86 (!rgfi *rsp* *2^30* x86))
              (count 300)
              (x86 (x86-run count x86)))
             (and (equal (rgfi *rax* x86)
                         (if (equal n 5666001387520)
                             8
                           (logcount n)))
                  (equal flg nil)
                  (equal (rip x86)
                         (+ 1 halt-address))))
  :g-bindings
  `((n   (:g-number ,(gl-int 0 1 65))))
  :n-counterexamples 3
  :abort-indeterminate t
  :exec-ctrex nil
  :rule-classes nil)

;; We could not use GL to prove such theorems on the earlier version
;; of our X86 model. GL needed to create large linear lists
;; (corresponding to the logical representation of our X86 state) in
;; order to symbolically execute functions that take the state as an
;; input. These lists were so large that creating them resulted in
;; unavoidable stack overflows.

;; However, on our current model with abstract stobjs, a sparse
;; logical representation of state makes symbolic execution by GL
;; possible.

(def-gl-thm x86-popcount-generalized-stack-pointer
  :hyp (and (natp n)
            (< n (expt 2 64))
            (not (equal n 5666001387520))
            (natp rsp)
            (or (and (<= 0 rsp)
                     (< rsp #x400600))
                (and (< #x400686 rsp)
                     (< rsp *2^30*))))
  :concl (b* ((start-address #x400600)
              (halt-address #x400686)
              (x86 (!programmer-level-mode t (create-x86)))
              ((mv flg x86)
               (init-x86-state
                nil start-address halt-address
                nil nil nil 0
                *popcount/popcount-64-bug-binary*
                x86))
              (x86 (!rgfi *rdi* n x86))
              (x86 (!rgfi *rsp* rsp x86))
              (count 300)
              (x86 (x86-run count x86)))
             (and (equal (rgfi *rax* x86)
                         (logcount n))
                  (equal flg nil)
                  (equal (rip x86)
                         (+ 1 halt-address))
                  (equal (caar (ms x86)) 'X86-HLT)))
  :g-bindings
  `((n   (:g-number ,(gl-int 0 3 65)))
    (rsp (:g-number ,(gl-int 1 3 49))))
  :rule-classes nil)

(def-gl-thm x86-popcount-32-correct
  :hyp (and (natp n)
            (< n (expt 2 32)))
  :concl (b* ((start-address #x4005c0)
              (halt-address #x4005f6)
              (x86 (!programmer-level-mode t (create-x86)))
              ((mv flg x86)
               (init-x86-state
                nil start-address halt-address
                nil nil nil 0
                *popcount/popcount-64-bug-binary*
                x86))
              (x86 (!rgfi *rdi* n x86))
              (x86 (!rgfi *rsp* *2^30* x86))
              (count 300)
              (x86 (x86-run count x86)))
             (and (equal (rgfi *rax* x86)
                         (logcount n))
                  (equal flg nil)
                  (equal (rip x86)
                         (+ 1 halt-address))
                  (equal (caar (ms x86)) 'X86-HLT)))
  :g-bindings
  `((n    (:g-number ,(gl-int 0 1 33))))
  :exec-ctrex nil
  :rule-classes nil)

;; ======================================================================
