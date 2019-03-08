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
(include-book "add-mul-spec")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (e/d (bitops::ash-1-removal) ())))

;; ======================================================================

(defsection floating-point-arithmetic-specifications
  :parents (floating-point-specifications)
  :short "Specification of binary floating-point arithmetic operations
  like MAX, MIN, ADD, SUB, MUL, and DIV" )

(local (xdoc::set-default-parents floating-point-arithmetic-specifications))

;; ======================================================================

;; Specifications of FP MAX and MIN:

(define sse-max/min-special (kind1
			     (sign1     :type (unsigned-byte 1))
			     (exp1  natp)
			     (implicit1 :type (unsigned-byte 1))
			     (frac1 natp)
			     kind2
			     (sign2     :type (unsigned-byte 1))
			     (exp2 natp)
			     (implicit2 :type (unsigned-byte 1))
			     (frac2 natp)
			     (operation :type (integer 0 36)))
  :long "<p>This function checks whether the operands are SNaN or
  QNaN. If at least one of them is NaN or both of them are zeros, then
  it returns the second operand.  It also handles infinities.</p>

  <p>Return values: <tt>(mv flag sign exp implicit frac
  invalid)</tt>.</p>"
  (cond
   ((or (eq kind1 'snan) (eq kind1 'qnan) (eq kind1 'indef)
	(eq kind2 'snan) (eq kind2 'qnan) (eq kind2 'indef))
    (mv t sign2 exp2 implicit2 frac2 t))
   ((and (eq kind1 'zero) (eq kind2 'zero))
    (mv t sign2 exp2 implicit2 frac2 nil))
   ((eq kind1 'inf)
    (if (or (and (int= operation #.*OP-MAX*) (int= sign1 0))
	    (and (int= operation #.*OP-MIN*) (int= sign1 1)))
	(mv t sign1 exp1 implicit1 frac1 nil)
      (mv t sign2 exp2 implicit2 frac2 nil)))
   ((eq kind2 'inf)
    (if (or (and (int= operation #.*OP-MAX*) (int= sign2 0))
	    (and (int= operation #.*OP-MIN*) (int= sign2 1)))
	(mv t sign2 exp2 implicit2 frac2 nil)
      (mv t sign1 exp1 implicit1 frac1 nil)))
   (t (mv nil 0 0 0 0 nil)))
  ///

  (defthm integerp-sse-max/min-special-1
    (implies (and (integerp sign1) (integerp sign2))
	     (integerp (mv-nth 1 (sse-max/min-special
				  kind1 sign1 exp1 implicit1 frac1
				  kind2 sign2 exp2 implicit2 frac2
				  operation))))
    :rule-classes :type-prescription)

  (defthm integerp-sse-max/min-special-2
    (implies (and (integerp exp1) (integerp exp2))
	     (integerp (mv-nth 2 (sse-max/min-special
				  kind1 sign1 exp1 implicit1 frac1
				  kind2 sign2 exp2 implicit2 frac2
				  operation))))
    :rule-classes :type-prescription)

  (defthm integerp-sse-max/min-special-3
    (implies (and (integerp implicit1) (integerp implicit2))
	     (integerp (mv-nth 3 (sse-max/min-special
				  kind1 sign1 exp1 implicit1 frac1
				  kind2 sign2 exp2 implicit2 frac2
				  operation))))
    :rule-classes :type-prescription)

  (defthm integerp-sse-max/min-special-4
    (implies (and (integerp frac1) (integerp frac2))
	     (integerp (mv-nth 4 (sse-max/min-special
				  kind1 sign1 exp1 implicit1 frac1
				  kind2 sign2 exp2 implicit2 frac2
				  operation))))
    :rule-classes :type-prescription))

(define sse-max/min-sign (rat rat1 sign1 sign2)
  :guard (and (rationalp rat)
	      (rationalp rat1)
	      (integerp sign1)
	      (integerp sign2))
  :inline t
  :no-function t
  (if (eql rat rat1) sign1 sign2)
  ///

  (defthm integerp-sse-max/min-sign
    (implies (forced-and (integerp sign1)
			 (integerp sign2))
	     (integerp (sse-max/min-sign rat rat1 sign1 sign2)))
    :rule-classes :type-prescription))

(define sse-max/min ((operation :type (integer 0 36))
		     (op1 natp)
		     (op2 natp)
		     (mxcsr :type (unsigned-byte 32))
		     (exp-width posp)
		     (frac-width posp))

  (b* ((mxcsr (mbe :logic (loghead 32 mxcsr)
                   :exec mxcsr))
       ((mv kind1 sign1 exp1 implicit1 frac1)
	(fp-decode op1 exp-width frac-width))
       ((mv kind2 sign2 exp2 implicit2 frac2)
	(fp-decode op2 exp-width frac-width))
       (daz (logbitp #.*mxcsr-daz* mxcsr))
       ((mv kind1 exp1 frac1)
	(sse-daz kind1 exp1 frac1 daz))
       ((mv kind2 exp2 frac2)
	(sse-daz kind2 exp2 frac2 daz))
       ((mv special-ok sign exp & frac invalid)
	(sse-max/min-special kind1 sign1 exp1 implicit1 frac1
			     kind2 sign2 exp2 implicit2 frac2
			     operation))

       ;; Check invalid operation
       (mxcsr (if invalid (!mxcsrBits->ie 1 mxcsr) mxcsr))
       (im (logbitp #.*mxcsr-im* mxcsr))
       ((when (and invalid (not im)))
	(mv 'invalid-operand-exception-is-not-masked 0 mxcsr))

       ;; Check denormal operand
       (de (denormal-exception kind1 kind2))
       (mxcsr (if de (!mxcsrBits->de 1 mxcsr) mxcsr))
       (dm (logbitp #.*mxcsr-dm* mxcsr))
       ((when (and de (not dm)))
	(mv 'denormal-operand-exception-is-not-masked 0 mxcsr)))

    (if special-ok
	(mv nil
	    (fp-encode-integer sign exp frac exp-width frac-width)
	    mxcsr)
      (b* ((bias (nfix (ec-call (RTL::bias (list nil (1+ frac-width) exp-width)))))
	   (rat1 (fp-to-rat sign1 exp1 frac1 bias exp-width frac-width))
	   (rat2 (fp-to-rat sign2 exp2 frac2 bias exp-width frac-width))
	   (rat (case operation
		  (#.*OP-MAX* (if (> rat1 rat2) rat1 rat2))
		  (#.*OP-MIN* (if (< rat1 rat2) rat1 rat2))
		  ;; Should never be reached.
		  (otherwise 0)))

	   (sign (sse-max/min-sign rat rat1 sign1 sign2))

	   (fp-result
	    (rat-to-fp rat sign
		       nil nil nil 0 ;; rc will not be used here.
		       ;; I just put a dummy value 0.
		       exp-width frac-width)))

	(mv nil fp-result mxcsr))))
  ///

  (defthm integerp-result-sse-max/min
    (integerp
     (mv-nth 1 (sse-max/min operation op1 op2 mxcsr exp-width frac-width)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mxcsr-sse-max/min
    :bound 32
    :concl (mv-nth 2 (sse-max/min operation op1 op2 mxcsr exp-width frac-width))
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :hints-l (("Goal" :in-theory (e/d* (unsigned-byte-p) ())))
    :gen-type t
    :gen-linear t))

;; Single-Precision Operations:

(define sp-sse-max/min ((operation :type (integer 0 36))
			(op1       :type (unsigned-byte 32))
			(op2       :type (unsigned-byte 32))
			(mxcsr     :type (unsigned-byte 32)))
  (b* (((mv flg result mxcsr)
	(sse-max/min operation op1 op2 mxcsr
		     #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))
       (result (n32 result))
       (mxcsr (mbe :logic (n32 mxcsr)
		   :exec  mxcsr)))
    (mv flg result mxcsr))
  ///

  (defthm-unsigned-byte-p n32p-result-sp-sse-max/min
    :bound 32
    :concl (mv-nth 1 (sp-sse-max/min operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mxcsr-sp-sse-max/min
    :bound 32
    :concl (mv-nth 2 (sp-sse-max/min operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t))

;; Double-Precision Operations:

(define dp-sse-max/min ((operation :type (integer 0 36))
			(op1       :type (unsigned-byte 64))
			(op2       :type (unsigned-byte 64))
			(mxcsr     :type (unsigned-byte 32)))
  (b* (((mv flg result mxcsr)
	(sse-max/min operation op1 op2 mxcsr
		     #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))
       (result (n32 result))
       (mxcsr (mbe :logic (n32 mxcsr)
		   :exec  mxcsr)))
    (mv flg result mxcsr))
  ///

  (defthm-unsigned-byte-p n64p-result-dp-sse-max/min
    :bound 64
    :concl (mv-nth 1 (dp-sse-max/min operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mxcsr-dp-sse-max/min
    :bound 32
    :concl (mv-nth 2 (dp-sse-max/min operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t))

;; ======================================================================

;; Top-level Single and Double Precision Arithmetic Operations:

(define sp-sse-add/sub/mul/div/max/min ((operation :type (integer 0 36))
					(op1       :type (unsigned-byte 32))
					(op2       :type (unsigned-byte 32))
					(mxcsr     :type (unsigned-byte 32)))
  (if (or (int= operation #.*OP-MAX*) (int= operation #.*OP-MIN*))
      (sp-sse-max/min operation op1 op2 mxcsr)
    (sp-sse-add/sub/mul/div operation op1 op2 mxcsr))

  ///

  (defthm-unsigned-byte-p n32p-result-sp-sse-add/sub/mul/div/max/min
    :bound 32
    :concl (mv-nth 1 (sp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mxcsr-sp-sse-add/sub/mul/div/max/min
    :bound 32
    :concl (mv-nth 2 (sp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t))

(define dp-sse-add/sub/mul/div/max/min ((operation :type (integer 0 36))
					(op1       :type (unsigned-byte 64))
					(op2       :type (unsigned-byte 64))
					(mxcsr     :type (unsigned-byte 32)))
  (if (or (int= operation #.*OP-MAX*) (int= operation #.*OP-MIN*))
      (dp-sse-max/min operation op1 op2 mxcsr)
    (dp-sse-add/sub/mul/div operation op1 op2 mxcsr))

  ///

  (defthm-unsigned-byte-p n64p-result-dp-sse-add/sub/mul/div/max/min
    :bound 64
    :concl (mv-nth 1 (dp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mxcsr-dp-sse-add/sub/mul/div/max/min
    :bound 32
    :concl (mv-nth 2 (dp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))
    :gen-type t
    :gen-linear t))

;; ======================================================================
