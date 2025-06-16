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
(include-book "pow2sum-vectors")

(local (include-book "../library-extensions/arithmetic"))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is the basis for addition of small unsigned integers.
; Here 'small' has a precise technical sense:
; the number of bits n of the unsigned integers is such that
; n+1 is less than the number of bits of the prime p.
; The unsigned integers are represented as n bits.
; Under the aforementioned condition on n,
; it is possible to perform addition by
; turning the integers into field elements,
; adding the two field elements,
; and converting the sum into n+1 bits for the result.
; All of this can be done in n+2 constraints:
; - n+1 constraints serve to constrain the bits of the result to be booleans.
; - The remaining constraint performs the conversions and the sum (see below).
; Let:
; - x(0) ... x(n-1) be the n bits of the first integer.
; - y(0) ... y(n-1) be the n bits of the second integer.
; - z(0) ... z(n) be the n+1 bits of the result.
; The conversion and sum constraint is
;   (x(0) + 2 * x(1) + ... + 2^(n-1) * x(n-1) +
;    y(0) + 2 * y(1) + ... + 2^(n-1) * y(n-1))
;   (1) =
;   (z(0) + 2 * z(1) + ... + 2^n * z(n))
; That is, we equate the sum of the weighted sums of x and y
; to the weighted sum of z.
; Because of the assumption that n+1 < bit size of p,
; the modular operations above coincide with the non-modular ones,
; and indeed z is the sum of x and y.

(define unsigned-small-add-gadget ((xs symbol-listp)
                                   (ys symbol-listp)
                                   (zs symbol-listp)
                                   (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (1+ (len xs)))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget-list zs p)
          (list (r1cs::make-r1cs-constraint
                 :a (append (pow2sum-vector xs 0)
                            (pow2sum-vector ys 0))
                 :b (list (list 1 1))
                 :c (pow2sum-vector zs 0)))))

; We prove soundness and completeness,
; expressed as the equivalence of the gadget to
; the results being booleans whose weighted sum
; is the sum of the weighted sums of the input bits of the two integers,
; assuming the input bits are boolean.
; Since both x and y are n bits, we have x < 2^n and y < 2^n.
; Thus x + y < 2^(n+1).
; Since we assume n+1 < L(p), where L(p) is the bit length of p,
; we have n+1 <= L(p)-1 because n and L(p) are integers.
; By monotonicity, 2^(n+1) <= 2^(L(p)-1).
; Since 2^(L(p)-1) <= p (an arithmetic theorem),
; we have that x + y < p, which justifies simplifying away the mod p.

(defruled unsigned-small-add-gadget-correct
  (implies (and (primep p)
                (< (1+ (len xs)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (1+ (len xs)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (unsigned-small-add-gadget xs ys zs p)
                              asg
                              p)
                             (and (bit-listp zs$)
                                  (equal (lebits=>nat zs$)
                                         (+ (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :do-not-induct t
  :use ((:instance plus-expt2-upper-bound
                   (n (len xs))
                   (a (lebits=>nat (lookup-equal-list xs asg)))
                   (b (lebits=>nat (lookup-equal-list ys asg))))
        (:instance expt2-mono
                   (a (len zs))
                   (b (1- (integer-length p)))))
  :cases ((<= (len zs) (1- (integer-length p))))
  :enable (unsigned-small-add-gadget
           boolean-check-gadget-list-to-bit-listp
           r1cs::r1cs-constraint-holdsp
           pow2sum-vector-to-mod-of-lebits=>nat
           r1cs::dot-product-of-append
           r1cs::dot-product
           pfield::add
           lebits=>nat-less-when-len-less
           positive->=-expt2-of-integer-length-minus-1))
