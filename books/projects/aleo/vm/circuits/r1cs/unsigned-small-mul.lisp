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

(include-book "boolean-check")
(include-book "bits-mul-field")
(include-book "pow2sum")

(local (include-book "../library-extensions/arithmetic"))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is the basis for multiplication of small unsigned integers.
; Here 'small' has a precise technical sense.  It means that the number of bits
; n of an unsigned integer operand (which must both have the same number of bits)
; is such that 2n is less than the number of bits of the prime p.
; Each unsigned integer operand is represented as n bits.
; Under the aforementioned condition on n,
; it is possible to perform multiplication by
; turning the integers into field elements,
; multiplying the two field elements,
; and converting the product into 2n bits for the result.

; This is done in 2n+2 constraints, not counting the constraints needed to
; ensure the bit vector operands are in fact bit vectors.
; (And not counting downstream optimizations.)
; - 2n constraints to constrain the result vars to be bits.
; - 1 constraint to do the operands conversion to fields
;     and the multiplication into a field variable
; - 1 constraint to split up the product field variable into bits

; Optimization note:
; Note that these last two constraints
;   (x-bit-weighted-sum) * (y-bits-weighted-sum) = z-bits-var
;   (z-bits-var)*1 = (z-bits-weighted-sum)
; can clearly be combined into a single constraint
;   (x-bit-weighted-sum) * (y-bits-weighted-sum) = z-bits-weighted-sum

; Let:
; - x(0) ... x(n-1) be the n bits of the first integer.
; - y(0) ... y(n-1) be the n bits of the second integer.
; - zvar is the field var containing the product of x and y
; - z(0) ... z(2n-1) be the 2n bits of the product.

; The conversion and multiplication constraint is
;   ((x(0) + 2 * x(1) + ... + 2^(n-1) * x(n-1)) *
;    (y(0) + 2 * y(1) + ... + 2^(n-1) * y(n-1)))
;   = zvar
; The decomposition of zvar into bits constraint is
;   (zvar)*1
;  = (z(0) + (2 * z(1)) + ... + (2^(n-1) * z(n-1))
;     + (2^(n) * z(n)) + ... + (2^(2n-1) * z(2n-1)))
; Those two together mean we equate the product of the weighted sums of x and y
; to the weighted sum of z.

; Because of the assumption that 2n < bit size of p,
; the modular operations above coincide with the non-modular ones,
; and indeed z is the product of x and y.

(define unsigned-small-mul-gadget ((xs symbol-listp)
                                   (ys symbol-listp)
                                   (zvar symbolp)
                                   (zs symbol-listp)
                                   (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (+ (len ys) (len xs)))
              (< (len zs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (bits-mul-field-gadget xs ys zvar p)
          (boolean-check-gadget-list zs p)
          (pow2sum-gadget zvar zs)))

; We prove soundness and completeness,
; expressed as the equivalence of the gadget to
; the results being booleans whose weighted sum
; is the product of the weighted sums of the input bits of the two integers,
; assuming the input bits are boolean.
; Since both x and y are n bits, we have x < 2^n and y < 2^n.
; Thus x * y < 2^(2n), see lemma1 below.
; Since we assume 2n < L(p), where L(p) is the bit length of p,
; we have 2n <= L(p)-1 because n and L(p) are integers.
; By monotonicity (see lemma2 below), 2^(2n) <= 2^(L(p)-1).
; Since 2^(L(p)-1) <= p (an arithmetic theorem),
; we have that x * y < p, which justifies simplifying away the mod p.

(defruledl lemma1
  (implies (and (natp n) (natp a) (natp b)
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (< (* a b) (expt 2 (* 2 n))))
  :use (:instance lemma0 (c (expt 2 n)))
  :prep-lemmas
  ((defrule lemma0
     (implies (and (natp a) (natp b) (natp c)
                   (< a c)
                   (< b c))
              (< (* a b) (* c c))) ;(expt 2 (* 2 n))
     :prep-books
     (;; arithmetic-5 is now locally included for the current book.
      ;; The set-default-hints is still needed.
      ;;(include-book "arithmetic-5/top" :dir :system)
      (set-default-hints '((acl2::nonlinearp-default-hint
                            acl2::stable-under-simplificationp
                            acl2::hist
                            acl2::pspv))))
     )))

(defruledl lemma2
  (implies (and (natp a)
                (natp b)
                (<= a b))
           (<= (expt 2 a)
               (expt 2 b)))
  :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system)))

(defruled unsigned-small-mul-gadget-correct
  (implies (and (primep p)
                (< (+ (len xs) (len ys)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp zvar)
                (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (+ (len ys) (len xs)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg zvar)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zvar$ (lookup-equal zvar asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (unsigned-small-mul-gadget xs ys zvar zs p)
                              asg
                              p)
                             (and (equal zvar$ (lebits=>nat zs$))
                                  (bit-listp zs$)
                                  (equal zvar$
                                         (* (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :do-not-induct t
  :use ((:instance lemma1
                   (n (len xs))
                   (a (lebits=>nat (lookup-equal-list xs asg)))
                   (b (lebits=>nat (lookup-equal-list ys asg))))
        (:instance lemma2
                   (a (len zs))
                   (b (1- (integer-length p)))))
  :cases ((<= (len zs) (1- (integer-length p))))
  :enable (unsigned-small-mul-gadget
           boolean-check-gadget-list-to-bit-listp
           lebits=>nat-less-when-len-less
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           bits-mul-field-gadget-to-equal-of-mul))
