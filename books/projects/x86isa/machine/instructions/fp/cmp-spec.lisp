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

(in-package "X86ISA")
(include-book "base")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (e/d (bitops::ash-1-removal) ())))

;; ======================================================================

(defsection floating-point-comparison-specifications
  :parents (floating-point-specifications)
  :short "Specification of floating-point comparison operations"
  )

(local (xdoc::set-default-parents floating-point-comparison-specifications))

;; ======================================================================

;; Specifications of FP Comparisons:

(define sse-cmp-special (kind1
                         (sign1 :type (unsigned-byte 1))
                         kind2
                         (sign2 :type (unsigned-byte 1))
                         (exp-width posp)
                         (frac-width posp)
                         (operation :type (integer 0 36)))
  :long "<p>This function checks whether operands are NaN and then
  return the corresponding results. It also handles the
  infinities.</p>
<p>Return values: <tt>(mv flag integer-result invalid)</tt></p>"
  (let ((invalid (or (eq kind1 'snan)
                     (eq kind2 'snan)
                     (and (or (eq kind1 'qnan) (eq kind1 'indef)
                              (eq kind2 'qnan) (eq kind2 'indef))
                          (or (int= operation #.*OP-CMPLT*)
                              (int= operation #.*OP-CMPLE*)
                              (int= operation #.*OP-CMPNLT*)
                              (int= operation #.*OP-CMPNLE*)
                              (int= operation #.*OP-COMI*))))))
    (cond
     ((or (eq kind1 'snan) (eq kind1 'qnan) (eq kind1 'indef)
          (eq kind2 'snan) (eq kind2 'qnan) (eq kind2 'indef))
      (cond ((or (int= operation #.*OP-CMPUNORD*)
                 (int= operation #.*OP-CMPNEQ*)
                 (int= operation #.*OP-CMPNLT*)
                 (int= operation #.*OP-CMPNLE*))
             ;; Return the mask of all 1s.
             (mv t
                 (1- (ash 1 (+ 1 exp-width frac-width)))
                 invalid))
            ((or (int= operation #.*OP-COMI*)
                 (int= operation #.*OP-UCOMI*))
             ;; Return a particular integer result for this case (here we
             ;; return 7). We then use this result to recognize the unordered
             ;; relationship and set the corresponding flags in the EFLAGS
             ;; register.
             (mv t 7 invalid))
            ;; Return the mask of all 0s.
            (t (mv t 0 invalid))))
     ((or (eq kind1 'inf) (eq kind2 'inf))
      ;; Convert -inf to -1,
      ;;         +inf to  1,
      ;;         finite to 0.
      ;; The purpose of this conversion is used for comparison between two
      ;; operands in which at least one of them is infinity.
      (b* ((rat1 (if (eq kind1 'inf)
                     (if (int= sign1 0) 1 -1)
                   0))
           (rat2 (if (eq kind2 'inf)
                     (if (int= sign2 0) 1 -1)
                   0))
           (cmp-result
            (case operation
              (#.*OP-CMPEQ* (= rat1 rat2))
              (#.*OP-CMPLT* (< rat1 rat2))
              (#.*OP-CMPLE* (<= rat1 rat2))
              (#.*OP-CMPUNORD* nil) ;; Neither source operand is a NaN.
              (#.*OP-CMPNEQ* (not (= rat1 rat2)))
              (#.*OP-CMPNLT* (not (< rat1 rat2)))
              (#.*OP-CMPNLE* (not (<= rat1 rat2)))
              (#.*OP-CMPORD* t) ;; Neither source operand is a NaN.
              (otherwise nil)))

           (result
            (if (or (int= operation #.*OP-COMI*)
                    (int= operation #.*OP-UCOMI*))
                ;; Compare rat1 with rat2.
                ;; Return 0 standing for rat1 > rat2,
                ;;        1 standing for rat1 < rat2,
                ;;        4 standing for ra1 = rat2.
                ;; Of course, we can choose any other values to return.
                ;; The only requirement is that they must be distinct and
                ;; different from the value returned for the case of
                ;; unordered relationship, which is 7.
                (cond ((> rat1 rat2) 0)
                      ((< rat1 rat2) 1)
                      (t 4))
              (if cmp-result
                  ;; Return the mask of all 1s.
                  (1- (ash 1 (+ 1 exp-width frac-width)))
                ;; Return the mask of all 0s.
                0))))
        (mv t result invalid)))
     (t (mv nil 0 invalid))))

  ///

  (defthm integerp-sse-cmp-special-1
    (integerp
     (mv-nth
      1
      (sse-cmp-special kind1 sign1 kind2 sign2 exp-width frac-width operation)))
    :rule-classes :type-prescription))

(define sse-cmp ((operation :type (integer 0 36))
                 (op1 natp)
                 (op2 natp)
                 (mxcsr :type (unsigned-byte 32))
                 (exp-width posp)
                 (frac-width posp))
  :prepwork ((local (in-theory (e/d* ()
                                     (bitops::logand-with-negated-bitmask
; Matt K. mod April 2016 for addition of type-set bit for the set {1}.
                                      (:t BOOL->BIT))))))
  (b* ((mxcsr (mbe :logic (loghead 32 mxcsr)
                   :exec mxcsr))
       ((mv kind1 sign1 exp1 ?implicit1 frac1)
        (fp-decode op1 exp-width frac-width))
       ((mv kind2 sign2 exp2 ?implicit2 frac2)
        (fp-decode op2 exp-width frac-width))
       (daz (equal (mxcsrBits->daz mxcsr) 1))
       ((mv kind1 exp1 frac1)
        (sse-daz kind1 exp1 frac1 daz))
       ((mv kind2 exp2 frac2)
        (sse-daz kind2 exp2 frac2 daz))
       ((mv special-ok result invalid)
        (sse-cmp-special kind1 sign1 kind2 sign2
                         exp-width frac-width operation))

       ;; Check invalid operation
       (mxcsr (if invalid (!mxcsrBits->ie 1 mxcsr) mxcsr))
       (im (equal (mxcsrBits->im mxcsr) 1))
       ((when (and invalid (not im)))
        (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))

       ;; Check denormal operand
       (de (denormal-exception kind1 kind2))
       (mxcsr (if de (!mxcsrBits->de 1 mxcsr) mxcsr))
       (dm (equal (mxcsrBits->dm mxcsr) 1))
       ((when (and de (not dm)))
        (mv 'denormal-operand-exception-is-not-masked 0 mxcsr)))

    (if special-ok
        (mv nil result mxcsr)
      (b* ((bias (nfix (ec-call (RTL::bias (list nil (1+ frac-width) exp-width)))))
           (rat1 (fp-to-rat sign1 exp1 frac1 bias exp-width frac-width))
           (rat2 (fp-to-rat sign2 exp2 frac2 bias exp-width frac-width))
           (cmp-result
            (case operation
              (#.*OP-CMPEQ* (= rat1 rat2))
              (#.*OP-CMPLT* (< rat1 rat2))
              (#.*OP-CMPLE* (<= rat1 rat2))
              (#.*OP-CMPUNORD* nil) ;; Neither source operand is a NaN.
              (#.*OP-CMPNEQ* (not (= rat1 rat2)))
              (#.*OP-CMPNLT* (not (< rat1 rat2)))
              (#.*OP-CMPNLE* (not (<= rat1 rat2)))
              (#.*OP-CMPORD* t) ;; Neither source operand is a NaN.
              (otherwise nil)))

           (result
            (if (or (int= operation #.*OP-COMI*)
                    (int= operation #.*OP-UCOMI*))
                ;; Compare rat1 with rat2.
                ;; Return 0 standing for rat1 > rat2,
                ;;        1 standing for rat1 < rat2,
                ;;        4 standing for ra1 = rat2.
                ;; Of course, we can choose any other values to return.
                ;; The only requirement is that they must be distinct and
                ;; different from the value returned by the function
                ;; sse-cmp-special for the case of unordered relationship,
                ;; which is 7.
                (cond ((> rat1 rat2) 0)
                      ((< rat1 rat2) 1)
                      (t 4))
              (if cmp-result
                  ;; Return all 1s.
                  (1- (ash 1 (+ 1 exp-width frac-width)))
                ;; Return all 0s.
                0))))

        (mv nil result mxcsr))))
  ///

  (defthm integerp-result-sse-cmp
    (integerp (mv-nth 1 (sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mxcsr-sse-cmp
    :bound 32
    :concl (mv-nth 2 (sse-cmp operation op1 op2 mxcsr exp-width frac-width))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d* (unsigned-byte-p) ())))))

;; ======================================================================

;; Single-Precision:

(define sp-sse-cmp ((operation :type (integer 0 36))
                    (op1       :type (unsigned-byte 32))
                    (op2       :type (unsigned-byte 32))
                    (mxcsr     :type (unsigned-byte 32)))
  (b* (((mv flg result mxcsr)
        (sse-cmp operation op1 op2 mxcsr #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))
       (result (n32 result)))
    (mv flg result mxcsr))
  ///
  (defthm-unsigned-byte-p n32p-result-sp-sse-cmp
    :bound 32
    :concl (mv-nth 1 (sp-sse-cmp operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mxcsr-sp-sse-cmp
    :bound 32
    :concl (mv-nth 2 (sp-sse-cmp operation op1 op2 mxcsr))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; Double-Precision:

(define dp-sse-cmp ((operation :type (integer 0 36))
                    (op1       :type (unsigned-byte 64))
                    (op2       :type (unsigned-byte 64))
                    (mxcsr     :type (unsigned-byte 32)))
  (b* (((mv flg result mxcsr)
        (sse-cmp operation op1 op2 mxcsr #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))
       (result (n32 result)))
    (mv flg result mxcsr))
  ///
  (defthm-unsigned-byte-p n64p-result-dp-sse-cmp
    :bound 64
    :concl (mv-nth 1 (dp-sse-cmp operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mxcsr-dp-sse-cmp
    :bound 32
    :concl (mv-nth 2 (dp-sse-cmp operation op1 op2 mxcsr))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; ======================================================================
