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

(include-book "../../../codewalker/codewalker")
(include-book "app-view/user-level-memory-utils" :dir :proof-utils :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ----------------------------------------------------------------------

;; Codewalker requires the run function to have x86 as the 0th formal.
;; Our old run function, x86-run, has x86 as the 1st formal, so we
;; define x86-run-alt below for use with Codewalker.

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

;; Sanity check: Small working example of x86isa+Codewalker

(local
 (encapsulate
   ()

   (defconst *program*
     '(#xf8 ;; CLC
       #xf9 ;; STC
       ))

   (defun-nx clc-stc-hyps (x86)
     (and
      ;; The x86 state is well-formed.
      (x86p x86)
      (64-bit-modep x86)
      ;; The model is operating in the application-level view.
      (app-view x86)
      (equal (rip x86) 0) ;; Added for codewalker
      ;; The program is located at linear addresses ranging from (rip
      ;; x86) to (+ -1 (len *program*) (rip x86)).
      (program-at (rip x86) *program* x86)
      ;; The addresses where the program is located are canonical.
      (canonical-address-p (rip x86))
      (canonical-address-p (+ (len *program*) (rip x86)))
      ;; The initial state is error-free.
      (equal (ms x86) nil)
      (equal (fault x86) nil)))

   (acl2::def-model-api
    ;; Codewalker requires the run function to have x86 as the 0th
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
    :callp  nil ;; recognizer fn for states with pc on call instruction
    :ret-pc nil ;; how to fetch the return pc after a call
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
    )))

;; ----------------------------------------------------------------------
