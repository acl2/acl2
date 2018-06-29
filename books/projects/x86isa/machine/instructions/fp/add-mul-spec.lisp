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
; Cuong Chau          <ckcuong@cs.utexas.edu>

;; All events beginning with the prefix RTL:: in this book are
;; imported from the RTL/REL11 library under the directory
;; "books/rtl/rel11/lib", authored by David M. Russinoff
;; (david@russinoff.com).

(in-package "X86ISA")
(include-book "constants" :dir :utils)
(include-book "rtl/rel11/portcullis" :dir :system)
(include-book "tools/with-supporters" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (e/d (bitops::ash-1-removal) ())))

;; ======================================================================

(defsection floating-point-add-mul
  :parents (floating-point-arithmetic-specifications)
  :short "Specification of floating-point ADD, SUB, MUL, and DIV
  operations" )

(local (xdoc::set-default-parents floating-point-add-mul))

;; ======================================================================

;; ADD, SUB, MUL, DIV:

(define convert-arith-operation-to-rtl-op
  ((operation natp))
  :inline t
  (case operation
    (#.*OP-ADD* 'RTL::ADD)
    (#.*OP-SUB* 'RTL::SUB)
    (#.*OP-MUL* 'RTL::MUL)
    (#.*OP-DIV* 'RTL::DIV)
    (otherwise
     (er hard? 'convert-operation-to-rtl-op "Illegal operation ~x0." operation))))

(ACL2::with-supporters
 (local (include-book "rtl/rel11/lib/excps" :dir :system))
 :names (rtl::formal-+ rtl::cat rtl::cat-size)

 (in-theory (e/d () (rtl::sse-binary-spec)))

 (defun sse-add/sub/mul/div (operation operand1 operand2 mxcsr exp-width frac-width)
   (declare (xargs :guard (and (natp operation)
                               (natp operand1) (natp operand2) (n32p mxcsr)
                               (posp exp-width) (posp frac-width))
                   :guard-hints (("Goal"
                                  :in-theory (e/d () (unsigned-byte-p not)))))
            (type (integer 0 36) operation))
   (b* (((mv result mxcsr)
         (ec-call
          (rtl::sse-binary-spec
           (convert-arith-operation-to-rtl-op operation)
           operand1 operand2 mxcsr
           (list nil (1+ frac-width) exp-width))))
        ;; Hopefully, the following fixes will go away once we know
        ;; rtl::sse-binary-spec returns a well-formed result and
        ;; mxcsr.
        (result (loghead (+ 1 exp-width frac-width) (ifix result)))
        (mxcsr (loghead 32 (ifix mxcsr)))
        ;; Pre-computation Exceptions
        ;; Check invalid operation
        ((when (and (equal (mxcsr-slice :ie mxcsr) 1)
                    (equal (mxcsr-slice :im mxcsr) 0)))
         (mv 'invalid-operand-exception-is-not-masked result mxcsr))
        ;; Check divide-by-zero
        ((when (and (equal (mxcsr-slice :ze mxcsr) 1)
                    (equal (mxcsr-slice :zm mxcsr) 0)))
         (mv 'divide-by-zero-exception-is-not-masked result mxcsr))
        ;; Check denormal operand
        ((when (and (equal (mxcsr-slice :de mxcsr) 1)
                    (equal (mxcsr-slice :dm mxcsr) 0)))
         (mv 'denormal-operand-exception-is-not-masked result mxcsr))
        ;; Post-computation Exceptions
        ;; Check overflow
        ((when (and (equal (mxcsr-slice :oe mxcsr) 1)
                    (equal (mxcsr-slice :om mxcsr) 0)))
         (mv 'overflow-exception-is-not-masked result mxcsr))
        ;; Check underflow
        ((when (and (equal (mxcsr-slice :ue mxcsr) 1)
                    (equal (mxcsr-slice :um mxcsr) 0)))
         (mv 'underflow-exception-is-not-masked result mxcsr))
        ;; Check precision
        ((when (and (equal (mxcsr-slice :pe mxcsr) 1)
                    (equal (mxcsr-slice :pm mxcsr) 0)))
         (mv 'precision-exception-is-not-masked result mxcsr)))
     (mv nil result mxcsr))))

(defthm unsigned-byte-p-of-result-of-sse-add/sub/mul/div
  (implies (and (equal fp-width (+ 1 exp-width frac-width))
                (posp exp-width)
                (posp frac-width))
           (unsigned-byte-p
            fp-width
            (mv-nth 1 (sse-add/sub/mul/div operation op1 op2 mxcsr exp-width frac-width)))))

(defthm unsigned-byte-p-of-mxcsr-of-sse-add/sub/mul/div
  (unsigned-byte-p
   32
   (mv-nth 2 (sse-add/sub/mul/div operation op1 op2 mxcsr exp-width frac-width)))
  :rule-classes :type-prescription)

(in-theory (disable sse-add/sub/mul/div))

;; Single-Precision Operations:

(define sp-sse-add/sub/mul/div
  ((operation :type (integer 0 36))
   (op1       :type (unsigned-byte 32))
   (op2       :type (unsigned-byte 32))
   (mxcsr     :type (unsigned-byte 32)))
  (sse-add/sub/mul/div operation op1 op2 mxcsr #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*)

  ///
  (defthm-usb n32p-result-sp-sse-add/sub/mul/div
    :bound 32
    :concl (mv-nth 1 (sp-sse-add/sub/mul/div operation op1 op2 mxcsr))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-flags-sp-sse-add/sub/mul/div
    :bound 32
    :concl (mv-nth 2 (sp-sse-add/sub/mul/div operation op1 op2 mxcsr))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; Double-Precision Operations:

(define dp-sse-add/sub/mul/div
  ((operation :type (integer 0 36))
   (op1       :type (unsigned-byte 64))
   (op2       :type (unsigned-byte 64))
   (mxcsr     :type (unsigned-byte 32)))
  (sse-add/sub/mul/div operation op1 op2 mxcsr #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*)

  ///
  (defthm-usb n64p-result-dp-sse-add/sub/mul/div
    :bound 64
    :concl (mv-nth 1 (dp-sse-add/sub/mul/div operation op1 op2 mxcsr))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-flags-dp-sse-add/sub/mul/div
    :bound 32
    :concl (mv-nth 2 (dp-sse-add/sub/mul/div operation op1 op2 mxcsr))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; ======================================================================
