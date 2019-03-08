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

(defsection floating-point-specifications
  :parents (instruction-semantic-functions)
  :short "Misc. utilities for the specification of floating-point operations"
  )

(defsection basic-floating-point-utilities
  :parents (floating-point-specifications)
  )

(local (xdoc::set-default-parents basic-floating-point-utilities))

;; ======================================================================

(defmacro fp-max-exp         ()  `(1- (ash 1 exp-width)))
(defmacro fp-inf-exp         ()  `(fp-max-exp))
(defmacro fp-max-finite-exp  ()  `(- (ash 1 exp-width) 2))
(defmacro fp-inf-frac        ()   0)
(defmacro fp-max-frac        ()  `(1- (ash 1 frac-width)))

(defmacro rc-cases (&key rn rd ru rz other)
  `(case RC
     (,*RC-RN* ,rn)
     (,*RC-RD* ,rd)
     (,*RC-RU* ,ru)
     (,*RC-RZ* ,rz)
     (otherwise ,other)))

(define fp-round-overflow-generic ((RC integerp)
                                   (sign integerp)
                                   (exp-width posp)
                                   (frac-width posp))
  :short "Returns rounded sign, exponent, and fraction in case of overflow."
  (RC-cases
   :rn  (mv sign (fp-inf-exp) (fp-inf-frac))
   :rd  (if (eql 0 sign)
            (mv sign (fp-max-finite-exp) (fp-max-frac))
          (mv sign (fp-inf-exp) (fp-inf-frac)))
   :ru  (if (eql 0 sign)
            (mv sign (fp-inf-exp) (fp-inf-frac))
          (mv sign (fp-max-finite-exp) (fp-max-frac)))
   :rz  (mv sign (fp-max-finite-exp) (fp-max-frac))
   ;; Should never get here.
   :other (mv       0               0               0))
  ///

  (defthm integerp-fp-round-overflow-generic-0
    (implies (integerp sign)
             (integerp (mv-nth 0 (fp-round-overflow-generic rc sign exp-width frac-width))))
    :rule-classes :type-prescription)

  (defthm integerp-fp-round-overflow-generic-1
    (integerp (mv-nth 1 (fp-round-overflow-generic rc sign exp-width frac-width)))
    :rule-classes :type-prescription)

  (defthm integerp-fp-round-overflow-generic-2
    (integerp (mv-nth 2 (fp-round-overflow-generic rc sign exp-width frac-width)))
    :rule-classes :type-prescription))

;; ======================================================================

;; FP-ENCODE-INTEGER:

(define fp-encode-integer ((sign integerp)
                           (exp  integerp)
                           (frac integerp)
                           (exp-width posp)
                           (frac-width posp))
  (logior frac (logior (ash exp frac-width)
                       (ash sign (+ exp-width frac-width))))

  ///

  (defthm integerp-fp-encode-integer
    (integerp (fp-encode-integer sign exp frac exp-width frac-width))
    :hints (("Goal" :in-theory '(fp-encode-integer (:type-prescription binary-logior))))
    :rule-classes :type-prescription))


;; FP-DECODE:

(define fp-decode ((x integerp)
                   (exp-width posp)
                   (frac-width posp))
  :long
  "<p>This function returns:
<ul>
<li>One of the symbols INDEF, QNAN, SNAN, INF, ZERO, DENORMAL, or NORMAL</li>
<li>sign bit</li>
<li>exponent bits</li>
<li>implicit bit value</li>
<li>fraction bits</li>
</ul></p>"

  (b* ((sign-bit-index (+ frac-width exp-width))
       (frac (part-select x :low 0 :width frac-width))
       (exp  (part-select x :low frac-width :width exp-width))
       (sign (part-select x :low sign-bit-index :width 1)))
    (cond ((eql exp 0)
           ;; Denormal or zero
           (b* ((sym (if (not (eql frac 0)) 'denormal 'zero)))
             (mv sym sign exp 0 frac)))
          ((eql exp (1- (ash 1 exp-width)))
           ;; Infinity or NAN
           (if (eql frac 0)
               ;; infinity
               (mv 'inf sign exp 1 frac)
             ;; nan
             (let ((sym (if (logbitp (1- frac-width) frac)
                            ;; qnan
                            (if (and (eql sign 1)
                                     (eql frac (ash 1 (1- frac-width))))
                                'indef
                              'qnan)
                          'snan)))
               (mv sym sign exp 1 frac))))
          (t (mv 'normal sign exp 1 frac))))

  ///

  (defthm-unsigned-byte-p n01p-fp-decode-sign-bit
    :bound 1
    :concl (mv-nth 1 (fp-decode x exp-width frac-width))
    :gen-type t
    :gen-linear t)

  (defthm natp-exp-fp-decode
    (implies (posp exp-width)
             (natp (mv-nth 2 (fp-decode x exp-width frac-width))))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p exp-width-wide-exp-from-fp-decode-lemma
    :hyp (posp exp-width)
    :bound exp-width
    :concl (mv-nth 2 (fp-decode x exp-width frac-width))
    :gen-linear t)

  (defthm-unsigned-byte-p n01p-implicit-bit-fp-decode
    :bound 1
    :concl (mv-nth 3 (fp-decode x exp-width frac-width))
    :gen-type t
    :gen-linear t)

  (defthm natp-frac-from-fp-decode
    (implies (posp frac-width)
             (natp (mv-nth 4 (fp-decode x exp-width frac-width))))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p frac-width-wide-frac-from-fp-decode-lemma
    :hyp (posp frac-width)
    :bound frac-width
    :concl (mv-nth 4 (fp-decode x exp-width frac-width))
    :gen-type t
    :gen-linear t))

;; ======================================================================

;; SSE-DAZ:

(define sse-daz (kind exp frac daz)
  (if (and daz (eq kind 'denormal))
      (mv 'zero 0 0)
    (mv kind exp frac))
  ///
  (defthm natp-sse-daz-1
    (implies (natp exp)
             (natp (mv-nth 1 (sse-daz kind exp frac daz))))
    :rule-classes :type-prescription)

  (defthm natp-sse-daz-2
    (implies (natp frac)
             (natp (mv-nth 2 (sse-daz kind exp frac daz))))
    :rule-classes :type-prescription))

;; ======================================================================

;; DENORMAL EXCEPTION:

(define denormal-exception (kind1 kind2)
  (and (not (member kind1 '(snan qnan indef)))
       (not (member kind2 '(snan qnan indef)))
       (or (eq kind1 'denormal) (eq kind2 'denormal))))

;; ======================================================================

;; FP-TO-RAT:

(define fp-to-rat ((sign integerp)
                   (exp integerp)
                   (frac integerp)
                   (bias natp)
                   (exp-width posp)
                   (frac-width posp))
  :short "Convert the bit-vector or integer representation used by
  hardware to rational for the cases of zero, denormal, and normal."
  (cond
   ((and (eql exp 0) (eql frac 0))
    0)
   ;; Denormal case
   ((and (eql exp 0) (not (eql frac 0)))
    (let ((man (* frac
                  (expt 2 (- frac-width)))))
      (* (if (eql sign 0) 1 -1)
         man
         (expt 2 (- 1 bias)))))
   ;; Normal case
   ((and (< 0 exp)
         (<= exp (fp-max-finite-exp)))
    (let ((man (* (logior (ash 1 frac-width) frac)
                  (expt 2 (- frac-width)))))
      (* (if (eql sign 0) 1 -1)
         man
         (expt 2 (- exp bias)))))
   ;; Should never get here.
   (t 0))
  ///
  (defthm rationalp-fp-to-rat
    (implies (integerp frac)
             (rationalp (fp-to-rat sign exp frac bias exp-width frac-width)))
    :rule-classes :type-prescription))

;; RAT-TO-FP:

(ACL2::with-supporters
 (local (include-book "rtl/rel11/lib/reps" :dir :system))
 :names (rtl::formal-+ rtl::cat-size rtl::cat)

 (defun rat-to-fp (rat sign overflow underflow flush rc
                       exp-width frac-width)
   ;; Convert the rational to bit-vector or integer representation
   ;; used by hardware.
   ;; Return (mv sign exp frac)
   (declare (xargs :guard (and (rationalp rat)
                               (integerp sign)
                               (booleanp overflow)
                               (booleanp underflow)
                               (booleanp flush)
                               (integerp rc)
                               (posp exp-width)
                               (posp frac-width))))
   (cond
    ((eql rat 0)
     (fp-encode-integer sign 0 0 exp-width frac-width))
    (overflow
     (b* (((mv sign exp frac)
           (fp-round-overflow-generic rc sign exp-width frac-width)))
       (fp-encode-integer sign exp frac exp-width frac-width)))
    (flush
     (fp-encode-integer sign 0 0 exp-width frac-width))
    (underflow
     (if (ec-call (rtl::drepp rat (list nil (1+ frac-width) exp-width)))
         ;; Denormal representable
         (ec-call (rtl::dencode rat (list nil (1+ frac-width) exp-width)))
       ;; Not denormal representable, should never happen.
       (fp-encode-integer sign 0 0 exp-width frac-width)))
    ;; Denormal number
    ((ec-call (rtl::drepp rat (list nil (1+ frac-width) exp-width)))
     (ec-call (rtl::dencode rat (list nil (1+ frac-width) exp-width))))
    ;; Normal number
    ((ec-call (rtl::nrepp rat (list nil (1+ frac-width) exp-width)))
     (ec-call (rtl::nencode rat (list nil (1+ frac-width) exp-width))))
    ;; Should never get here.
    (t 0))))

(defthm integerp-rat-to-fp
  (integerp (rat-to-fp rat sign overflow underflow flush rc exp-width frac-width))
  :rule-classes :type-prescription)

(in-theory (disable rat-to-fp))

;; ======================================================================

(define make-special-bp (kind
                         (nan-frac-bits integerp)
                         (sign integerp)
                         (exp-width posp)
                         (frac-width posp))
  ;; Returns (mv sign exp implicit frac)
  (case kind
    (indef     (mv 1 (1- (ash 1 exp-width)) 1 (ash 1 (1- frac-width))))
    (qnan      (mv sign (1- (ash 1 exp-width)) 1
                   (+ (ash 1 (1- frac-width))
                      nan-frac-bits)))
    (snan      (mv sign (1- (ash 1 exp-width)) 1
                   nan-frac-bits))
    (inf       (mv sign (1- (ash 1 exp-width)) 1 0))
    (zero      (mv sign 0                     0 0))
    ;; These two aren't particularly useful -- they're just arbitrary examples
    ;; of denormal and normal, resp.
    (denormal  (mv 0 0                          0 1))
    (otherwise (mv 0 1                          1 0)))
  ///

  (defthm integerp-make-special-bp-0
    (implies (integerp sign)
             (integerp (mv-nth 0 (make-special-bp kind nan-frac-bits sign exp-width frac-width))))
    :rule-classes :type-prescription)

  (defthm integerp-make-special-bp-1
    (integerp (mv-nth 1 (make-special-bp kind nan-frac-bits sign exp-width frac-width)))
    :rule-classes :type-prescription)

  (defthm integerp-make-special-bp-2
    (integerp (mv-nth 2 (make-special-bp kind nan-frac-bits sign exp-width frac-width)))
    :rule-classes :type-prescription)

  (defthm integerp-make-special-bp-3
    (implies (integerp nan-frac-bits)
             (integerp (mv-nth 3 (make-special-bp kind nan-frac-bits sign exp-width frac-width))))
    :rule-classes :type-prescription))

(defmacro flag-make-special-bp (kind nan-frac-bits sign invalid)
  `(mv-let (sign exp explicit frac)
     (make-special-bp ,kind ,nan-frac-bits ,sign exp-width frac-width)
     (mv t sign exp explicit frac ,invalid)))

;; ======================================================================

(define convert-rc-to-mode ((rc natp))
  :enabled t
  :inline t
  :no-function t
  (case rc
    (#.*RC-RN* 'RTL::RNE)
    (#.*RC-RD* 'RTL::RDN)
    (#.*RC-RU* 'RTL::RUP)
    (#.*RC-RZ* 'RTL::RTZ)
    (otherwise nil)))

(ACL2::with-supporters
 (local (include-book "rtl/rel11/lib/round" :dir :system))

 (defun rat-round (x rc bias exp-width frac-width)
   (declare (xargs :guard (and (rationalp x)
                               (natp rc)
                               (natp bias)
                               (posp exp-width)
                               (posp frac-width))))

   (if (> (RTL::expo x) (- bias))
       (ec-call (rtl::rnd x (convert-rc-to-mode rc) (1+ frac-width)))
     (ec-call (rtl::drnd x (convert-rc-to-mode rc) (list nil (1+ frac-width) exp-width))))))

(defthm rationalp-rat-round
  (implies (rationalp x)
           (rationalp (rat-round x rc bias exp-width frac-width)))
  :rule-classes :type-prescription)

(in-theory (disable rat-round))

;; ======================================================================
