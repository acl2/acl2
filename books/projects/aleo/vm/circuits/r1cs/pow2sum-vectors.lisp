; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "vector-neg")

(include-book "../library-extensions/lookup-equal-list")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we do not define gadgets, but reusable components used in gadgets.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We introduce vectors that are weighted sums of (boolean) variables,
; where the weights are powers of 2:
;   x(0) + 2*x(1) + 4*x(2) + ... + 2^(n-1)*x(n-1)

; We explicate their relationship with @(tsee lebits=>nat);
; we regard the bits in little endian order.

(define pow2sum-vector ((xs symbol-listp) (i natp))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (cond ((endp xs) nil)
        (t (cons (list (expt 2 i) (car xs))
                 (pow2sum-vector (cdr xs) (1+ i)))))
  ///

  (defret consp-of-pow2sum-vector
    (equal (consp vec)
           (consp xs))))

(defruled pow2sum-vector-to-mod-of-lebits=>nat
  (implies (and (symbol-listp xs)
                (natp i)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (b* ((xs$ (lookup-equal-list xs asg)))
             (implies (bit-listp xs$)
                      (equal (r1cs::dot-product (pow2sum-vector xs i) asg p)
                             (mod (* (expt 2 i)
                                     (lebits=>nat xs$))
                                  p)))))
  :enable (pow2sum-vector
           r1cs::dot-product
           lebits=>nat
           acl2::lendian=>nat
           lookup-equal-list
           pfield::add
           acl2::expt-of-+))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following is like pow2sum-vector, but each coefficient is negated.
; Thus, the dot produce is equal to the negation of lebits=>nat
; (multiplied by the exponential that accounts for the index i).

(define pow2sum-neg-vector ((xs symbol-listp) (i natp))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (vector-neg (pow2sum-vector xs i))
  ///

  (defret consp-of-pow2sum-neg-vector
    (equal (consp vec)
           (consp xs))))

(defruled pow2sum-neg-vector-to-mod-of-lebits=>nat
  (implies (and (primep p)
                (natp i)
                (symbol-listp xs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (b* ((xs$ (lookup-equal-list xs asg)))
             (implies (bit-listp xs$)
                      (equal (r1cs::dot-product
                              (pow2sum-neg-vector xs i) asg p)
                             (mod (* (expt 2 i)
                                     (- (lebits=>nat xs$)))
                                  p)))))
  :do-not-induct t
  :enable (pow2sum-neg-vector
           dot-product-of-vector-neg-to-neg-of-dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pfield::add))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following is a variant of the above negated vector,
; but with the coefficients reduced modulo the prime,
; so they are in the prime field
; and are easier to compare with some gadget samples.

(define pow2sum-neg-prime-vector ((xs symbol-listp) (i natp) (p primep))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (vector-neg-prime (pow2sum-vector xs i) p)
  ///

  (defret consp-of-pow2sum-neg-prime-vector
    (equal (consp vec)
           (consp xs))))

(defruled pow2sum-neg-prime-vector-to-mod-of-lebits=>nat
  (implies (and (primep p)
                (natp i)
                (symbol-listp xs)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (b* ((xs$ (lookup-equal-list xs asg)))
             (implies (bit-listp xs$)
                      (equal (r1cs::dot-product
                              (pow2sum-neg-prime-vector xs i p) asg p)
                             (mod (* (expt 2 i)
                                     (- (lebits=>nat xs$)))
                                  p)))))
  :do-not-induct t
  :enable (pow2sum-neg-prime-vector
           dot-product-of-vector-neg-prime-to-neg-of-dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pfield::add))
