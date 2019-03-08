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
(include-book "fp-structures" :dir :utils)
(include-book "rtl/rel11/portcullis" :dir :system)
(include-book "tools/with-supporters" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (e/d (bitops::ash-1-removal) ())))

;; ======================================================================

(defsection floating-point-sqrt-specifications
  :parents (floating-point-arithmetic-specifications)
  :short "Specification of SQRT operation"
  )

(local (xdoc::set-default-parents floating-point-sqrt-specifications))

;; ======================================================================

;; SQRT:

(ACL2::with-supporters
 (local (include-book "rtl/rel11/lib/excps" :dir :system))
 :names (rtl::formal-+ rtl::cat rtl::cat-size)

 (in-theory (e/d () (rtl::sse-sqrt-spec)))

 (defun sse-sqrt (operand mxcsr exp-width frac-width)
   (declare (xargs :guard (and (natp operand)
                               (n32p mxcsr)
                               (posp exp-width)
                               (posp frac-width))))
   (b* (((mv result mxcsr)
         (ec-call
          (rtl::sse-sqrt-spec
           operand mxcsr (list nil (1+ frac-width) exp-width))))
        ;; Hopefully, the following fixes will go away once we know
        ;; rtl::sse-binary-spec returns a well-formed result and
        ;; mxcsr.
        (result (loghead (+ 1 exp-width frac-width) (ifix result)))
        (mxcsr (loghead 32 (ifix mxcsr)))
        ;; Pre-computation Exceptions
        ;; Check invalid operation
        ((when (and (equal (mxcsrBits->ie mxcsr) 1)
                    (equal (mxcsrBits->im mxcsr) 0)))
         (mv 'invalid-operand-exception-is-not-masked result mxcsr))
        ;; Check denormal operand
        ((when (and (equal (mxcsrBits->de mxcsr) 1)
                    (equal (mxcsrBits->dm mxcsr) 0)))
         (mv 'denormal-operand-exception-is-not-masked result mxcsr))
        ;; Post-computation Exceptions
        ;; Check precision
        ((when (and (equal (mxcsrBits->pe mxcsr) 1)
                    (equal (mxcsrBits->pm mxcsr) 0)))
         (mv 'precision-exception-is-not-masked result mxcsr)))
     (mv nil result mxcsr))))

(defthm unsigned-byte-p-of-result-of-sse-sqrt
  (implies (and (equal fp-width (+ 1 exp-width frac-width))
                (posp exp-width)
                (posp frac-width))
           (unsigned-byte-p fp-width
                            (mv-nth 1 (sse-sqrt op mxcsr exp-width frac-width)))))

(defthm unsigned-byte-p-of-mxcsr-of-sse-sqrt
  (unsigned-byte-p 32 (mv-nth 2 (sse-sqrt op mxcsr exp-width frac-width))))

(in-theory (disable sse-sqrt))

;; ======================================================================

;; Single-Precision Operation:

(define sp-sse-sqrt ((x     :type (unsigned-byte 32))
                     (mxcsr :type (unsigned-byte 32)))
  (sse-sqrt x mxcsr #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*)

  ///

  (defthm-unsigned-byte-p n32p-result-sp-sse-sqrt
    :bound 32
    :concl (mv-nth 1 (sp-sse-sqrt x mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mxcsr-sp-sse-sqrt
    :bound 32
    :concl (mv-nth 2 (sp-sse-sqrt x mxcsr))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; Double-Precision Operation:

(define dp-sse-sqrt ((x     :type (unsigned-byte 64))
                     (mxcsr :type (unsigned-byte 32)))
  (sse-sqrt x mxcsr #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*)

  ///
  (defthm-unsigned-byte-p n64p-result-dp-sse-sqrt
    :bound 64
    :concl (mv-nth 1 (dp-sse-sqrt x mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mxcsr-dp-sse-sqrt
    :bound 32
    :concl (mv-nth 2 (dp-sse-sqrt x mxcsr))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; ======================================================================
