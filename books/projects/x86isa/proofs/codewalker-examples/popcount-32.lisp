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

(include-book "base")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

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
; From codewalker.lisp:
; * Every reachable pc (in the region of code to be explored) must be
;   constant, starting with the initial pc, i.e., you have to know, in
;   concrete terms, where the instructions are stored.
  (b* ((program-rip #x400610))
    (and (x86p x86)
         (64-bit-modep x86)
         (equal (app-view x86) t)
         (program-at program-rip *popcount-32-bytes* x86)
         (n32p (rgfi *rdi* x86))
         (canonical-address-p program-rip)
         (canonical-address-p (+ -1 (len *popcount-32-bytes*) program-rip))
         (equal (ms x86) nil)
         (equal (fault x86) nil))))

(acl2::def-model-api
 :run x86-run-ALT               ;; the run function of the model
 :svar x86                      ;; name of state variable
 :stobjp T                      ;;  and whether it's a stobj
 :hyps ((popcount-hyps x86))    ;; invariant to assume about state
 :step x86-fetch-decode-execute ;; name of step function
 :get-pc (lambda (x86) (xr :rip nil x86))     ;; how to fetch the pc
 :put-pc (lambda (v x86) (xw :rip nil v x86)) ;; how to set the pc

 ;; the ``drivers'' below specify how to dive through updaters (and
 ;; constructors) and their accessors
 :updater-drivers (((XW FLD I :VALUE :BASE)
                    (XR FLD I :BASE))
                   ((WB N ADDR R-W-X :VALUE :BASE)
                    (RB N ADDR R-W-X :BASE)))
 :constructor-drivers nil
 ;; Determine the "state components" that def-projection can
 ;; generalize to produce functions independent of state.
 :state-comps-and-types
 (((XR :RGF *RDI* X86) (unsigned-byte-p 32 (XR :RGF *RDI* X86))))
 :callp  nil  ;; recognizer fn for states with pc on call instruction
 :ret-pc nil  ;; how to fetch the return pc after a call
 :returnp nil ;; recognizer for states with pc on return instruction

 :clk+ binary-clk+   ; how to add two clocks
 :name-print-base 16 ; base to use for pcs appearing in names
;  (2, 8, 10, or 16)

; how to generate variable names from state comps
 :var-names (((XR :RGF *RDI* X86) "RDI")))

(local (in-theory (e/d* (instruction-decoding-and-spec-rules
                         rflag-RoWs-enables
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
                         rime-size
                         rme-size
                         wime-size
                         wme-size
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
                         get-prefixes-opener-lemma-group-4-prefix))))

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why one-read-with-rb-from-program-at)
;; (acl2::why program-at-wb-disjoint)

(acl2::def-semantics
 :init-pc #x400610
 :focus-regionp (lambda (pc) (and (<= 0 pc) (<= pc #x400640)))
 :root-name nil ; optional - to change the fn names chosen
 ;; :hyps+ ((good-popcount-x86p x86)) ; optional - to strengthen the :hyps of API
 :annotations nil ; optional - to modify output generated
 )

(acl2::def-projection
 :new-fn popcount-result-fn
 :projector (XR :RGF *RAX* x86)
 :old-fn SEM-X400610)

;; Prove that POPCOUNT-RESULT-FN == logcount, given a 32-bit input.
(include-book "centaur/gl/gl" :dir :system)

(def-gl-thm x86-popcount-32-correct
  :hyp (and (natp n)
            (< n (expt 2 32)))
  :concl (equal (popcount-result-fn n)
                (logcount n))
  :g-bindings
  `((n    (:g-number ,(increasing-list 0 1 33)))))

;; ----------------------------------------------------------------------
