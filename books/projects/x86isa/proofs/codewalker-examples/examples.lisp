;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "programmer-level-mode/programmer-level-memory-utils" :dir :proof-utils :ttags :all)

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

(include-book "../../../codewalker/codewalker")

(define x86-run-alt
  (x86 (n :type (unsigned-byte 59)))
  :parents (x86-decoder)
  :enabled t
  :returns (x86 x86p :hyp (x86p x86))
  :measure (nfix n)
  (cond ((fault x86) x86)
        ((ms x86) x86)
        ((mbe :logic (zp n) :exec (equal 0 n))
         x86)
        (t (let* ((x86 (x86-fetch-decode-execute x86))
                  (n (the (unsigned-byte 59) (1- n))))
             (x86-run-alt x86 n))))
  ///

  (local (in-theory (e/d* (binary-clk+) ())))

  (defthm x86-run-alt-halted
    (implies (or (ms x86) (fault x86))
             (equal (x86-run-alt x86 n) x86)))

  (defthm x86-run-alt-opener-not-ms-not-fault-zp-n
    (implies (and (syntaxp (quotep n))
                  (zp n))
             (equal (x86-run-alt x86 n) x86)))

  (defthm x86-run-alt-opener-not-ms-not-zp-n
    (implies (and (not (ms x86))
                  (not (fault x86))
                  (syntaxp (quotep n))
                  (not (zp n)))
             (equal (x86-run-alt x86 n)
                    (x86-run-alt (x86-fetch-decode-execute x86) (1- n)))))

  ;; To enable compositional reasoning, we prove the following two
  ;; theorems:

  (defthm x86-run-alt-plus
    (implies (and (natp n1)
                  (natp n2)
                  (syntaxp (quotep n1)))
             (equal (x86-run-alt x86 (clk+ n1 n2))
                    (x86-run-alt (x86-run-alt x86 n1) n2)))))

;; ----------------------------------------------------------------------

#||

;; CLC/STC:

(defconst *program*
  '(#xf8 ;; CLC
    #xf9 ;; STC
    ))

(defun-nx clc-stc-hyps (x86)
  (and
   ;; The x86 state is well-formed.
   (x86p x86)
   ;; The model is operating in the programmer-level mode.
   (programmer-level-mode x86)
   (equal (rip x86) 0) ;; Added for codewalker
   ;; The program is located at linear addresses ranging from (rip
   ;; x86) to (+ -1 (len *program*) (rip x86)).
   (prog-at (rip x86) *program* x86)
   ;; The addresses where the program is located are canonical.
   (canonical-address-p (rip x86))
   (canonical-address-p (+ (len *program*) (rip x86)))
   ;; The initial state is error-free.
   (equal (ms x86) nil)
   (equal (fault x86) nil)))

(acl2::def-model-api
 ;; BOZO codewalker requires the run function to have x86 as the 0th
 ;; formal...
 :run x86-run-alt               ;; the run function of the model
 :svar x86                      ;; name of state variable
 :stobjp T                      ;;  and whether it's a stobj
 :hyps ((clc-stc-hyps x86))     ;; invariant to assume about state
 :step x86-fetch-decode-execute ;; name of step function
 :get-pc (lambda (x86) (xr :rip 0 x86))     ;; how to fetch the pc
 :put-pc (lambda (v x86) (xw :rip 0 v x86)) ;; how to set the pc

 ;; the ``drivers'' below specify how to dive through updaters (and
 ;; constructors) and their accessors
 ;; The variables of the updater term should be a superset of those of
 ;; the accessor term.
 :updater-drivers (((XW FLD I :VALUE :BASE)
                    (XR FLD I :BASE))
                   ((WB N ADDR R-W-X :VALUE :BASE)
                    (RB N ADDR R-W-X :BASE))
                   ((!FLGI I :VALUE :BASE)
                    (FLGI I :BASE)))
 :constructor-drivers nil
 :state-comps-and-types  nil
 :callp  nil  ;; recognizer fn for states with pc on call instruction
 :ret-pc nil  ;; how to fetch the return pc after a call
 :returnp nil ;; recognizer for states with pc on return instruction

 :clk+ binary-clk+    ; how to add two clocks
 :name-print-base nil ; base to use for pcs appearing in names
;  (2, 8, 10, or 16)

; how to generate variable names from state comps
 :var-names nil
 )

(local (in-theory (e/d* (x86-cmc/clc/stc/cld/std)
                        (create-canonical-address-list
                         (create-canonical-address-list)))))

(acl2::def-semantics
 :init-pc 0
 :focus-regionp (lambda (pc) (and (<= 0 pc) (<= pc 1)))
 :root-name nil ; optional - to change the fn names chosen
 ;; :hyps+ ((program1p s)) ; optional - to strengthen the :hyps of API
 :annotations nil ; optional - to modify output generated
 )


||#

;; ----------------------------------------------------------------------

;; popcount: (from popcount-general.lisp)...

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

(defun-nx popcount-hyps (x86)
  (and (x86p x86)
       (equal (programmer-level-mode x86) t)
       (equal (rip x86) 0) ;;  Added for codewalker
       (prog-at (rip x86) *popcount-32-bytes* x86)
       (n32p (rgfi *rdi* x86))
       (canonical-address-p (rip x86))
       (canonical-address-p (+ -1 (len *popcount-32-bytes*) (rip x86)))
       (equal (ms x86) nil)
       (equal (fault x86) nil)))

(acl2::def-model-api
 ;; BOZO codewalker requires the run function to have x86 as the 0th
 ;; formal...
 :run x86-run-ALT               ;; the run function of the model
 :svar x86                      ;; name of state variable
 :stobjp T                      ;;  and whether it's a stobj
 :hyps ((popcount-hyps x86))    ;; invariant to assume about state
 :step x86-fetch-decode-execute ;; name of step function
 :get-pc (lambda (x86) (xr :rip 0 x86))     ;; how to fetch the pc
 :put-pc (lambda (v x86) (xw :rip 0 v x86)) ;; how to set the pc

 ;; the ``drivers'' below specify how to dive through updaters (and
 ;; constructors) and their accessors
 :updater-drivers (((XW FLD I :VALUE :BASE)
                    (XR FLD I :BASE))
                   ((WB N ADDR R-W-X :VALUE :BASE)
                    (RB N ADDR R-W-X :BASE))
                   ((!FLGI I :VALUE :BASE)
                    (FLGI I :BASE)))
 :constructor-drivers nil
 :state-comps-and-types  nil
 :callp  nil  ;; recognizer fn for states with pc on call instruction
 :ret-pc nil  ;; how to fetch the return pc after a call
 :returnp nil ;; recognizer for states with pc on return instruction

 :clk+ binary-clk+    ; how to add two clocks
 :name-print-base nil ; base to use for pcs appearing in names
;  (2, 8, 10, or 16)

; how to generate variable names from state comps
 :var-names nil
 )

(local (in-theory (e/d* (instruction-decoding-and-spec-rules

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

                         top-level-opcode-execute
                         !rgfi-size
                         x86-operand-to-reg/mem
                         wr64
                         wr32
                         rr08
                         rr32
                         rr64
                         rm32
                         rm64
                         wm32
                         wm64
                         rr32
                         x86-operand-from-modr/m-and-sib-bytes
                         rim-size
                         rim32
                         n32-to-i32
                         n64-to-i64
                         rim08
                         two-byte-opcode-decode-and-execute
                         x86-effective-addr
                         subset-p
                         ;; Flags
                         write-user-rflags
                         !flgi-undefined)

                        (unsigned-byte-p
                         las-to-pas-values-and-!flgi
                         las-to-pas
                         default-+-2
                         get-prefixes-opener-lemma-group-1-prefix
                         get-prefixes-opener-lemma-group-2-prefix
                         get-prefixes-opener-lemma-group-3-prefix
                         get-prefixes-opener-lemma-group-4-prefix))))

;; (defthm rb-0
;;   (equal (mv-nth 1 (rb 0 addr r-x x86)) 0)
;;   :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

;; (defthm wb-0
;;   ;; WB-NO-WRITES-WHEN-ZP-N
;;   (equal (mv-nth 1 (wb 0 addr val w x86)) x86)
;;   :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why one-read-with-rb-from-prog-at)
;; (acl2::why prog-at-wb-disjoint)

(acl2::def-semantics
 :init-pc 0
 :focus-regionp (lambda (pc) (and (<= 0 pc) (<= pc 48)))
 :root-name nil ; optional - to change the fn names chosen
 ;; :hyps+ ((program1p s)) ; optional - to strengthen the :hyps of API
 :annotations nil ; optional - to modify output generated
 )

;; ----------------------------------------------------------------------
