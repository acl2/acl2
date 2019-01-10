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

(include-book "add-spec")
(include-book "sub-spec")
(include-book "or-spec")
(include-book "and-spec")
(include-book "xor-spec")

;; ======================================================================

(defun gpr-arith/logic-spec-gen-fn (operand-size)

  (declare (type (member 1 2 4 8) operand-size)
           (xargs :verify-guards nil))

  (b* ((fn-name          (mk-name "GPR-ARITH/LOGIC-SPEC-" operand-size))
       (gpr-add-spec-fn  (mk-name "GPR-ADD-SPEC-"   operand-size))
       (gpr-adc-spec-fn  (mk-name "GPR-ADC-SPEC-"   operand-size))
       (?gpr-sub-spec-fn  (mk-name "GPR-SUB-SPEC-"   operand-size))
       (?gpr-sbb-spec-fn  (mk-name "GPR-SBB-SPEC-"   operand-size))
       (?gpr-cmp-spec-fn  (mk-name "GPR-CMP-SPEC-"   operand-size))
       (?gpr-or-spec-fn   (mk-name "GPR-OR-SPEC-"    operand-size))
       (?gpr-and-spec-fn  (mk-name "GPR-AND-SPEC-"   operand-size))
       (?gpr-xor-spec-fn  (mk-name "GPR-XOR-SPEC-"   operand-size))
       (?gpr-test-spec-fn (mk-name "GPR-TEST-SPEC-"  operand-size)))

      `(define ,fn-name
         ((operation :type (member #.*OP-ADD* #.*OP-ADC* #.*OP-SUB*
                                   #.*OP-SBB* #.*OP-CMP* #.*OP-OR*
                                   #.*OP-AND* #.*OP-XOR* #.*OP-TEST*))
          (dst          :type (unsigned-byte ,(ash operand-size 3)))
          (src          :type (unsigned-byte ,(ash operand-size 3)))
          (input-rflags :type (unsigned-byte 32)))

         :parents (gpr-arith/logic-spec)
         :enabled t
         (case operation
           (#.*OP-ADD* ;; 0
            (,gpr-add-spec-fn dst src input-rflags))
           (#.*OP-OR* ;; 1
            (,gpr-or-spec-fn dst src input-rflags))
           (#.*OP-ADC* ;; 2
            (,gpr-adc-spec-fn dst src input-rflags))
           (#.*OP-AND* ;; 3
            (,gpr-and-spec-fn dst src input-rflags))
           (#.*OP-SUB* ;; 4
            (,gpr-sub-spec-fn dst src input-rflags))
           (#.*OP-XOR* ;; 5
            (,gpr-xor-spec-fn dst src input-rflags))
           (#.*OP-SBB* ;; 6
            (,gpr-sbb-spec-fn dst src input-rflags))
           (#.*OP-TEST* ;; 7
            ;; We will re-use the AND specification here.
            (,gpr-and-spec-fn dst src input-rflags))
           (#.*OP-CMP* ;; 8
            ;; We will re-use the SUB specification here.
            (,gpr-sub-spec-fn dst src input-rflags))
           (otherwise
            ;; The guard will prevent us from reaching here.
            (mv 0 0 0))))))

(make-event (gpr-arith/logic-spec-gen-fn  1))
(make-event (gpr-arith/logic-spec-gen-fn  2))
(make-event (gpr-arith/logic-spec-gen-fn  4))
(make-event (gpr-arith/logic-spec-gen-fn  8))

(defsection gpr-arith/logic-spec

  :parents (instruction-semantic-functions)
  :short "Semantics of general-purpose arithmetic and logical instructions"
  :long "<p>These instructions are:</p>
<ul>
<li>@('ADD')</li>
<li>@('ADC')</li>
<li>@('SUB')</li>
<li>@('SBB')</li>
<li>@('CMP')</li>
<li>@('OR')</li>
<li>@('AND')</li>
<li>@('XOR')</li>
<li>@('TEST')</li>
</ul>

@(def gpr-arith/logic-spec)"

  (defmacro gpr-arith/logic-spec
    (operand-size operation dst src input-rflags)
    `(case ,operand-size
       (1 (gpr-arith/logic-spec-1 ,operation ,dst ,src ,input-rflags))
       (2 (gpr-arith/logic-spec-2 ,operation ,dst ,src ,input-rflags))
       (4 (gpr-arith/logic-spec-4 ,operation ,dst ,src ,input-rflags))
       (otherwise
        (gpr-arith/logic-spec-8 ,operation ,dst ,src ,input-rflags)))))

;; ======================================================================
