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

;; Specifications of FP Converts

(in-package "X86ISA")
(include-book "base")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (e/d (bitops::ash-1-removal) ())))

;; ======================================================================

(defsection floating-point-converts
  :parents (floating-point-specifications)
  :short "Specification of floating-point conversion operations" )

(local (xdoc::set-default-parents floating-point-converts))

;; ======================================================================

;; FP to Integer:

(define rat-round-to-int-rn ((rat rationalp))
  :returns (r integerp :rule-classes :type-prescription)
  (round rat 1))

(define rat-round-to-int-rd ((rat rationalp))
  :returns (r integerp :rule-classes :type-prescription)
  (let ((rn (round rat 1)))
    (if (> rn rat) (1- rn) rn)))

(define rat-round-to-int-ru ((rat rationalp))
  :returns (r integerp :rule-classes :type-prescription)
  (let ((rn (round rat 1)))
    (if (< rn rat) (1+ rn) rn)))

(define rat-round-to-int-rz ((rat rationalp))
  :returns (r integerp :rule-classes :type-prescription)
  (truncate rat 1))

(define rat-round-to-int ((rat rationalp)
                          (rc natp))
  :inline t
  :returns (r integerp :rule-classes :type-prescription)
  (rc-cases
   :rn (rat-round-to-int-rn rat)
   :rd (rat-round-to-int-rd rat)
   :ru (rat-round-to-int-ru rat)
   :rz (rat-round-to-int-rz rat)
   ;; Should never get here.
   :other 0))

(define sse-cvt-fp-to-int-special (kind (nbytes natp))
  :short "Check whether the operand is NaN or infinity. If so, return
  the integer indefinite."
  ;; Return (mv flag integer-result invalid).
  :returns (mv flg
               (r integerp :hyp :guard :rule-classes :type-prescription)
               invalid)
  (let ((invalid (or (eq kind 'snan) (eq kind 'qnan)
                     (eq kind 'indef) (eq kind 'inf))))
    (if invalid
        (mv t (ash 1 (1- (ash nbytes 3))) invalid)
      (mv nil 0 invalid))))

(define sse-cvt-fp-to-int ((nbytes natp)
                           (op natp)
                           (mxcsr :type (unsigned-byte 32))
                           (trunc booleanp)
                           (exp-width posp)
                           (frac-width posp))
  :prepwork ((local (in-theory (e/d* () (bitops::logand-with-negated-bitmask)))))

  (b* ((mxcsr (mbe :logic (loghead 32 mxcsr)
                   :exec mxcsr))
       ((mv kind sign exp ?implicit frac)
        (fp-decode op exp-width frac-width))
       (daz (logbitp #.*mxcsr-daz* mxcsr))
       ((mv kind exp frac)
        (sse-daz kind exp frac daz))
       ((mv special-ok result invalid)
        (sse-cvt-fp-to-int-special kind nbytes))

       ;; Check invalid operation
       (mxcsr (if invalid (!mxcsr-slice :ie 1 mxcsr) mxcsr))
       (im (equal (mxcsr-slice :im mxcsr) 1))
       ((when (and invalid (not im)))
        (mv 'invalid-operand-exception-is-not-masked 0 mxcsr)))

    (if special-ok
        (mv nil result mxcsr)
      (b* ((bias (nfix (ec-call (RTL::bias (list nil (1+ frac-width) exp-width)))))
           (rat (fp-to-rat sign exp frac bias exp-width frac-width))
           (rc (mbe :logic
                    (part-select mxcsr :low #.*mxcsr-rc* :high (1+ #.*mxcsr-rc*))
                    ;; (get-bits #.*mxcsr-rc* (1+ #.*mxcsr-rc*) mxcsr)
                    :exec  (logand #b11 (ash mxcsr (- #.*mxcsr-rc*)))))
           (rc (if trunc #b11 rc))
           (rat-to-int (rat-round-to-int rat rc))
           (nbits (ash nbytes 3))
           (min-signed-int (- (expt 2 (1- nbits))))
           (max-signed-int (1- (expt 2 (1- nbits))))
           (out-of-range (or (< rat-to-int min-signed-int)
                             (> rat-to-int max-signed-int)))
           ;; If the converted integer is out-of-range, set IE flag.
           (mxcsr (if out-of-range (!mxcsr-slice :ie 1 mxcsr) mxcsr))
           ((when (and out-of-range (not im)))
            (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))
           ;; If out-of-range and IM is masked, return integer indefinite.
           ((when out-of-range)
            (mv nil (ash 1 (1- nbits)) mxcsr))

           ;; Check precision
           (pe (not (= rat-to-int rat)))
           (mxcsr (if pe (!mxcsr-slice :pe 1 mxcsr) mxcsr))
           (pm (equal (mxcsr-slice :pm mxcsr) 1))
           ((when (and pe (not pm)))
            (mv 'precision-exception-is-not-masked 0 mxcsr)))

        (mv nil rat-to-int mxcsr))))
  ///

  (defthm integerp-result-sse-cvt-fp-to-int
    (implies (natp nbytes)
             (integerp (mv-nth 1 (sse-cvt-fp-to-int
                                  nbytes op mxcsr trunc exp-width frac-width))))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mxcsr-sse-cvt-fp-to-int
    :bound 32
    :concl (mv-nth 2 (sse-cvt-fp-to-int
                      nbytes op mxcsr trunc exp-width frac-width))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d* (unsigned-byte-p) ())))))

;; ======================================================================

;; Integerp to FP:

(define sse-cvt-int-to-fp ((op integerp)
                           (mxcsr :type (unsigned-byte 32))
                           (exp-width posp)
                           (frac-width posp))
  :prepwork
  ((local (in-theory (e/d* () (unsigned-byte-p)))))
  (b* ((mxcsr (mbe :logic (loghead 32 mxcsr)
                   :exec mxcsr))
       (rc (mbe :logic
                (part-select mxcsr :low #.*mxcsr-rc* :high (1+ #.*mxcsr-rc*))
                :exec  (logand #b11 (ash mxcsr (- #.*mxcsr-rc*)))))
       (bias (nfix (ec-call (RTL::bias (list nil (1+ frac-width) exp-width)))))
       (int-to-rat (rat-round op rc bias exp-width frac-width))
       (sign (cond ((> int-to-rat 0) 0)
                   ((< int-to-rat 0) 1)
                   (t (if (int= rc #.*rc-rd*) 1 0))))

       ;; Check precision
       (pe (not (= op int-to-rat)))
       (mxcsr (if pe (!mxcsr-slice :pe 1 mxcsr) mxcsr))
       (pm (equal (mxcsr-slice :pm mxcsr) 1))
       ((when (and pe (not pm)))
        (mv 'precision-exception-is-not-masked 0 mxcsr))

       (fp-result
        (rat-to-fp int-to-rat sign
                   nil nil nil rc
                   exp-width frac-width)))

    (mv nil fp-result mxcsr))
  ///

  (defthm integerp-result-sse-cvt-int-to-fp
    (integerp (mv-nth 1 (sse-cvt-int-to-fp op mxcsr exp-width frac-width)))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mxcsr-sse-cvt-int-to-fp
    :bound 32
    :concl (mv-nth 2 (sse-cvt-int-to-fp op mxcsr exp-width frac-width))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d* (unsigned-byte-p) ())))))

;; ======================================================================

;; Convert FP1 to FP2:

(define denormalp ((rat rationalp)
                   (rounded-expo integerp)
                   (bias natp))
  (let ((expo (RTL::expo rat))
        (minus-bias (- bias)))
    (or (<= rounded-expo minus-bias)
        (and (= rounded-expo 0)
             (<= expo minus-bias))))
  ///

  (defthm booleanp-denormalp
    (booleanp (denormalp rat rounded-expo bias))))

(define sse-cvt-fp1-to-fp2-special (kind
                                    (sign :type (unsigned-byte 1))
                                    (implicit :type (unsigned-byte 1))
                                    (frac natp)
                                    (frac-width1 posp)
                                    (exp-width2 posp)
                                    (frac-width2 posp))
  :short "Check whether the operand is SNaN or QNaN and then return
  corresponding result. Also handle the infinities."
  ;; Return (mv flag sign exp implicit frac invalid).
  (let ((invalid (eq kind 'snan)))
    (cond
     ((eq kind 'snan)
      (let ((exp-width exp-width2)
            (frac-width frac-width2)
            (nan-frac-bits (ash
                            (part-select frac :low 0 :high (nfix (- frac-width1 2)))
                            (- frac-width2 frac-width1))))
        (flag-make-special-bp 'qnan nan-frac-bits
                              sign invalid)))
     ((or (eq kind 'qnan) (eq kind 'indef))
      (let ((exp-width exp-width2)
            (frac (ash frac (- frac-width2 frac-width1))))
        (mv t sign (fp-max-exp) implicit frac invalid)))
     ((eq kind 'inf)
      (let ((exp-width exp-width2)
            (frac-width frac-width2))
        (flag-make-special-bp 'inf 0 sign invalid)))
     (t (mv nil 0 0 0 0 invalid))))

  ///

  (defthm integerp-sse-cvt-fp1-to-fp2-special-1
    (implies (integerp sign)
             (integerp
              (mv-nth
               1
               (sse-cvt-fp1-to-fp2-special
                kind sign implicit frac frac-width1 exp-width2 frac-width2))))
    :rule-classes :type-prescription)

  (defthm integerp-sse-cvt-fp1-to-fp2-special-2
    (integerp (mv-nth
               2
               (sse-cvt-fp1-to-fp2-special
                kind sign implicit frac frac-width1 exp-width2 frac-width2)))
    :rule-classes :type-prescription)

  (defthm integerp-sse-cvt-fp1-to-fp2-special-3
    (implies (integerp implicit)
             (integerp (mv-nth
                        3 (sse-cvt-fp1-to-fp2-special
                           kind sign implicit frac frac-width1 exp-width2 frac-width2))))
    :rule-classes :type-prescription)

  (defthm integerp-sse-cvt-fp1-to-fp2-special-4
    (integerp (mv-nth
               4
               (sse-cvt-fp1-to-fp2-special
                kind sign implicit frac frac-width1 exp-width2 frac-width2)))
    :rule-classes :type-prescription))

(ACL2::with-supporters
 (local (include-book "rtl/rel11/lib/excps" :dir :system))
 (defun sse-cvt-fp1-to-fp2 (op mxcsr
                               exp-width1 frac-width1
                               exp-width2 frac-width2)
   (declare (xargs :guard (and (natp op) (n32p mxcsr)
                               (posp exp-width1) (posp frac-width1)
                               (posp exp-width2) (posp frac-width2))
                   :guard-hints (("Goal" :in-theory (e/d* ()
                                                          (rtl::sse-post-comp
                                                           bitops::logand-with-negated-bitmask
                                                           bitops::loghead-of-loghead-1
                                                           unsigned-byte-p
                                                           bitops::logtail-of-loghead
                                                           bitops::logbitp-of-loghead-in-bounds
                                                           bitops::loghead-of-logior))))))
   (b* ((mxcsr (mbe :logic (loghead 32 mxcsr)
                    :exec mxcsr))
        ((mv kind sign exp ?implicit frac)
         (fp-decode op exp-width1 frac-width1))
        (daz (logbitp #.*mxcsr-daz* mxcsr))
        ((mv kind ?exp frac)
         (sse-daz kind exp frac daz))
        ((mv special-ok sign-special exp-special & frac-special invalid)
         (sse-cvt-fp1-to-fp2-special kind sign implicit frac frac-width1
                                     exp-width2 frac-width2))
        ;; Check invalid operation
        (mxcsr (if invalid (!mxcsr-slice :ie 1 mxcsr) mxcsr))
        (im (equal (mxcsr-slice :im mxcsr) 1))
        ((when (and invalid (not im)))
         (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))
        ;; Check denormal operand
        (de (eq kind 'denormal))
        (mxcsr (if de (!mxcsr-slice :de 1 mxcsr) mxcsr))
        (dm (equal (mxcsr-slice :dm mxcsr) 1))
        ((when (and de (not dm)))
         (mv 'denormal-operand-exception-is-not-masked 0 mxcsr)))

     (if special-ok
         (mv nil
             (fp-encode-integer sign-special exp-special frac-special
                                exp-width2 frac-width2)
             mxcsr)
       (b* ((bias1 (nfix (ec-call (RTL::bias (list nil (1+ frac-width1) exp-width1)))))
            (bias2 (nfix (ec-call (RTL::bias (list nil (1+ frac-width2) exp-width2)))))
            (rat (fp-to-rat sign exp frac bias1 exp-width1 frac-width1))
            ((mv result flags)
             (ec-call (rtl::sse-post-comp rat mxcsr (list nil (1+ frac-width2) exp-width2))))
            (result (loghead (+ 1 frac-width2 exp-width2) (ifix result)))
            (mxcsr (loghead 32 (logior (ifix flags) mxcsr)))

            ;; Post-computation Exceptions
            ;; Check overflow
            (overflowp (equal (mxcsr-slice :oe mxcsr) 1))
            ((when (and overflowp
                        (equal (mxcsr-slice :om mxcsr) 0)))
             (mv 'overflow-exception-is-not-masked result mxcsr))
            ;; Check underflow
            ((when (and (equal (mxcsr-slice :ue mxcsr) 1)
                        (equal (mxcsr-slice :um mxcsr) 0)))
             (mv 'underflow-exception-is-not-masked result mxcsr))
            ;; Check precision
            ((when (and (equal (mxcsr-slice :pe mxcsr) 1)
                        (equal (mxcsr-slice :pm mxcsr) 0)))
             (mv 'precision-exception-is-not-masked result mxcsr))

            (rc
             (mbe :logic (part-select mxcsr :low #.*mxcsr-rc* :high (1+ #.*mxcsr-rc*))
                  :exec  (logand #b11 (ash mxcsr (- #.*mxcsr-rc*)))))
            (rounded-rat (rat-round rat rc bias2 exp-width2 frac-width2))

            (rounded-expo (RTL::expo rounded-rat))
            (denormalp (denormalp rat rounded-expo bias2))

            (flush (and denormalp
                        (equal (mxcsr-slice :um mxcsr) 1)
                        (equal (mxcsr-slice :fz mxcsr) 1)))
            (fp-result
             (rat-to-fp rounded-rat sign overflowp
                        denormalp flush rc exp-width2 frac-width2)))

         (mv nil fp-result mxcsr))))))


(defthm integerp-result-sse-cvt-fp1-to-fp2
  (integerp (mv-nth
             1
             (sse-cvt-fp1-to-fp2 op mxcsr exp-width1 frac-width1 exp-width2 frac-width2)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (rtl::sse-post-comp
                                    bitops::loghead-of-loghead-1
                                    unsigned-byte-p
                                    bitops::logtail-of-loghead
                                    bitops::logbitp-of-loghead-in-bounds
                                    bitops::loghead-of-logior))))
  :rule-classes :type-prescription)

(defthm-usb n32p-mxcsr-sse-cvt-fp1-to-fp2
  :bound 32
  :concl (mv-nth
          2
          (sse-cvt-fp1-to-fp2 op mxcsr exp-width1 frac-width1 exp-width2 frac-width2))
  :hints (("Goal" :in-theory (e/d* ()
                                   (rtl::sse-post-comp
                                    bitops::loghead-of-loghead-1
                                    unsigned-byte-p
                                    bitops::logtail-of-loghead
                                    bitops::logbitp-of-loghead-in-bounds
                                    bitops::loghead-of-logior))))
  :gen-type t
  :gen-linear t
  :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p)
                                    (sse-cvt-fp1-to-fp2)))))

(in-theory (e/d () (sse-cvt-fp1-to-fp2)))

;; ======================================================================

;; Single-Precision Operations:

(define sp-sse-cvt-fp-to-int ((nbytes :type (integer 0 *))
                              (op     :type (unsigned-byte 32))
                              (mxcsr  :type (unsigned-byte 32))
                              (trunc  booleanp))
  (b* (((mv flg result mxcsr)
        (sse-cvt-fp-to-int nbytes op mxcsr trunc
                           #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))

       (result (trunc nbytes result)))
    (mv flg result mxcsr))

  ///

  (defthm bytesp-sp-sse-cvt-fp-to-int-1
    (implies (and (natp nbytes)
                  (member nbytes '(1 2 4 8 16)))
             (unsigned-byte-p
              (ash nbytes 3)
              (mv-nth 1 (sp-sse-cvt-fp-to-int nbytes op mxcsr trunc)))))

  (defthm-usb n32p-mxcsr-sp-sse-cvt-fp-to-int
    :bound 32
    :concl (mv-nth 2 (sp-sse-cvt-fp-to-int nbytes op mxcsr trunc))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

(define sp-sse-cvt-int-to-fp ((op integerp)
                              (mxcsr :type (unsigned-byte 32)))
  (b* (((mv flg result mxcsr)
        (sse-cvt-int-to-fp op mxcsr
                           #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))

       (result (n32 result)))
    (mv flg result mxcsr))
  ///

  (defthm-usb n32p-result-sp-sse-cvt-int-to-fp
    :bound 32
    :concl (mv-nth 1 (sp-sse-cvt-int-to-fp op mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mxcsr-sp-sse-cvt-int-to-fp
    :bound 32
    :concl (mv-nth 2 (sp-sse-cvt-int-to-fp op mxcsr))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

(define sse-cvt-sp-to-dp ((op    :type (unsigned-byte 32))
                          (mxcsr :type (unsigned-byte 32)))
  (b* (((mv flg result mxcsr)
        (sse-cvt-fp1-to-fp2 op mxcsr
                            #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*
                            #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))

       (result (n64 result)))
    (mv flg result mxcsr))
  ///

  (defthm-usb n64p-result-sse-cvt-sp-to-dp
    :bound 64
    :concl (mv-nth 1 (sse-cvt-sp-to-dp op mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mxcsr-sse-cvt-sp-to-dp
    :bound 32
    :concl (mv-nth 2 (sse-cvt-sp-to-dp op mxcsr))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))))

;; Double-Precision Operations:

(define dp-sse-cvt-fp-to-int ((nbytes :type (integer 0 *))
                              (op     :type (unsigned-byte 64))
                              (mxcsr  :type (unsigned-byte 32))
                              (trunc  booleanp))
  (b* (((mv flg result mxcsr)
        (sse-cvt-fp-to-int nbytes op mxcsr trunc
                           #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))

       (result (trunc nbytes result)))
    (mv flg result mxcsr))

  ///

  (defthm bytesp-dp-sse-cvt-fp-to-int-1
    (implies (and (natp nbytes)
                  (member nbytes '(1 2 4 8 16)))
             (unsigned-byte-p
              (ash nbytes 3)
              (mv-nth 1 (dp-sse-cvt-fp-to-int nbytes op mxcsr trunc)))))

  (defthm-usb n32p-mxcsr-dp-sse-cvt-fp-to-int
    :bound 32
    :concl (mv-nth 2 (dp-sse-cvt-fp-to-int nbytes op mxcsr trunc))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

(define dp-sse-cvt-int-to-fp ((op integerp)
                              (mxcsr :type (unsigned-byte 32)))
  (b* (((mv flg result mxcsr)
        (sse-cvt-int-to-fp op mxcsr
                           #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))

       (result (n32 result)))
    (mv flg result mxcsr))
  ///

  (defthm-usb n64p-result-dp-sse-cvt-int-to-fp
    :bound 64
    :concl (mv-nth 1 (dp-sse-cvt-int-to-fp op mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mxcsr-dp-sse-cvt-int-to-fp
    :bound 32
    :concl (mv-nth 2 (dp-sse-cvt-int-to-fp op mxcsr))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

(define sse-cvt-dp-to-sp ((op :type (unsigned-byte 64))
                          (mxcsr :type (unsigned-byte 32)))
  (b* (((mv flg result mxcsr)
        (sse-cvt-fp1-to-fp2 op mxcsr
                            #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*
                            #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))

       (result (n32 result)))
    (mv flg result mxcsr))
  ///

  (defthm-usb n32p-result-sse-cvt-dp-to-sp
    :bound 32
    :concl (mv-nth 1 (sse-cvt-dp-to-sp op mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mxcsr-sse-cvt-dp-to-sp
    :bound 32
    :concl (mv-nth 2 (sse-cvt-dp-to-sp op mxcsr))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; ======================================================================
