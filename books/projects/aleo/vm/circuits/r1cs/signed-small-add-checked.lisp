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

(include-book "boolean-and-notleft")
(include-book "boolean-xor")
(include-book "unsigned-small-add-wrapped")
(include-book "zero")

(include-book "../library-extensions/digits")

(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/lists"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget performs small checked signed integer addition,
; where small means that the the integers' size is sufficiently small
; compared to the prime (see documentation for unsigned-small-add-gadget).
; This gadget starts with the same constraints as unsigned-small-add-wrapped:
;   ((p - 1) * z(0)) (z(0)) = (0)
;   ...
;   ((p - 1) * z(n-1)) (z(n-1)) = (0)
;   ((p - 1) * carry) (carry) = (0)
;   (x(0) + 2 * x(1) + ... + 2^(n-1) * x(n-1) +
;    y(0) + 2 * y(1) + ... + 2^(n-1) * y(n-1))
;   (1) =
;   (z(0) + 2 * z(1) + ... + 2^(n-1) * z(n-1) + 2^n * carry)
; where here we use carry instead of z for carry bit.
; The first n+1 constraints force z(0),...,z(n-1) and carry to be bits,
; and the last constraint makes z(0),...,z(n-1),carry
; the exact sum of the natural numbers (unsigned integers) of x and y:
;   N(x) + N(y) = N(z) + carry * 2^n
; where N is the natural number denotes by the bits, i.e. lebits=>nat.
; Then there is a constraint to set xy-diff-sign to
; the XOR of the sign bits of x and y,
; to say whether the signs of x and y differ:
;   (2 * x(n-1)) (y(n-1)) = (y(n-1) + x(n-1) - xy-sign-diff)
; which is like
;   xy-sign-diff = x(n-1) XOR y(n-1)
; Then there is a constrain to set zx-diff-sign to
; the XOR of the sign bits of z and x,
; to say whether the signs of z and x differ:
;   (2 * z(n-1)) (x(n-1)) = (x(n-1) + z(n-1) - zx-diff-sign)
; which is like
;   zs-diff-sign = z(n-1) XOR x(n-1)
; Then there is a constraint to set over/undef-flow to say whether
; there is an overflow or underflow, which happens exactly when
; x and y have the same sign but z has a different sign:
;   ((p-1) xy-diff-sign + one) (zx-diff-sign) = (over/under-flow)
; which is like
;   over/under-flow = (NOT xy-diff-sign) AND zx-diff-sign
; where 'one' is a public variable assumed to have value 1;
; note that, since snarkVM does boolean negation on the fly,
; this is not exacty the boolean-and-gadget
; but the variable boolean-and-notleft-gadget (see its documentation).
; Finally, there is a zero constraint
;   (over/under-flow) (1) = (0)
; requiring that no overflow or underflow occurs.

; Note that this circuit could be optimized
; by omitting the over/under-flow variable
; and by replacing it with 0 in the previous constraint.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Gadget definition, as explained above.

(define signed-small-add-checked-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (carry symbolp)
                                         (xy-diff-sign symbolp)
                                         (zx-diff-sign symbolp)
                                         (over/under-flow symbolp)
                                         (one symbolp)
                                         (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append
   (unsigned-small-add-wrapped-gadget xs ys zs carry p)
   (boolean-xor-gadget (car (last xs)) (car (last ys)) xy-diff-sign p)
   (boolean-xor-gadget (car (last zs)) (car (last xs)) zx-diff-sign p)
   (boolean-and-notleft-gadget xy-diff-sign zx-diff-sign over/under-flow one p)
   (zero-gadget over/under-flow)))

; The proof is by four cases on the sign bits of x and y.
; Each case has some key property, which we prove just below.
; We use a macro to abbreviate the hypotheses of these theorems.
; The hypothesis N(x) + N(y) = N(z) + carry * 2^n is there
; because that formula arises in the soundness theorem.

(local
 (defmacro xyzc-hyps ()
   '(and (bit-listp xs)
         (bit-listp ys)
         (bit-listp zs)
         (bitp carry)
         (consp xs)
         (equal (len ys) (len xs))
         (equal (len zs) (len xs))
         (equal (+ (lebits=>nat xs) (lebits=>nat ys))
                (+ (lebits=>nat zs)
                   (* carry (expt 2 (len xs))))))))

; If x and y are non-negative, the carry is 0:
;   x(n-1) = 0 ==> N(x) < 2^(n-1)
;   y(n-1) = 0 ==> N(y) < 2^(n-1)
;   ==> N(x) + N(y) < 2^n
;   ==> carry = 0

(defrulel carry-0-when-xs-nonneg-and-ys-nonneg
  (implies (xyzc-hyps)
           (implies (and (equal (car (last xs)) 0)
                         (equal (car (last ys)) 0))
                    (equal carry 0)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits xs))
        (:instance lebits=>nat-upper-bound-when-msb-is-0 (bits ys))))

; If x and y are negative, the carry is 1:
;   x(n-1) = 1 ==> N(x) >= 2^(n-1)
;   y(n-1) = 1 ==> N(y) >= 2^(n-1)
;   ==> N(x) + N(y) >= 2^n
;   ==> carry = 1

(defrulel carry-1-when-xs-neg-and-ys-neg
  (implies (xyzc-hyps)
           (implies (and (equal (car (last xs)) 1)
                         (equal (car (last ys)) 1))
                    (equal carry 1)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits xs))
        (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits ys))))

; If x is non-negative and y is negative,
; the carry and the sign bit of z are different:
;   x(n-1) = 0 ==> 0 <= N(x) < 2^(n-1)
;   y(n-1) = 1 ==> 2^(n-1) <= N(y) < 2^n
;   ==> 2^(n-1) <= N(x) + N(y) < 2^n + 2^(n-1)
;   z(n-1) = carry = 0 ==> N(x) + N(y) = N(z) + carry * 2^n < 2^(n-1)
;     -- impossible
;   z(n-1) = carry = 1 ==> N(x) + N(y) = N(z) + carry * 2^n >= 2^n + 2^(n-1)
;     -- impossible
;   ==> (z(n-1) = 0 /\ carry = 1) \/ (z(n-1) = 1 /\ carry = 0)

(defruledl carry-neq-zs-msb-when-xs-nonneg-and-ys-neg
  (implies (xyzc-hyps)
           (implies (and (equal (car (last xs)) 0)
                         (equal (car (last ys)) 1))
                    (or (and (equal (car (last zs)) 0)
                             (equal carry 1))
                        (and (equal (car (last zs)) 1)
                             (equal carry 0)))))
  :do-not-induct t
  :use (lemma1 lemma2)

  :prep-lemmas

  ((defruled lemma1
     (implies (xyzc-hyps)
              (implies (and (equal (car (last xs)) 0)
                            (equal (car (last ys)) 1)
                            (equal carry 0))
                       (equal (car (last zs)) 1)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits ys))
           (:instance lebits=>nat-upper-bound-when-msb-is-0 (bits zs))))

   (defruled lemma2
     (implies (xyzc-hyps)
              (implies (and (equal (car (last xs)) 0)
                            (equal (car (last ys)) 1)
                            (equal carry 1))
                       (equal (car (last zs)) 0)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits xs))
           (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits zs))))))

; If x is negative and y is non-negative,
; the carry and the sign bit of z are different:
; this is the same as the previous case, with the roles of x and y swapped.

(defruledl carry-neq-zs-msb-when-xs-neg-and-ys-nonneg
  (implies (xyzc-hyps)
           (implies (and (equal (car (last xs)) 1)
                         (equal (car (last ys)) 0))
                    (or (and (equal (car (last zs)) 0)
                             (equal carry 1))
                        (and (equal (car (last zs)) 1)
                             (equal carry 0)))))
  :do-not-induct t ; by symmetry
  :use (:instance carry-neq-zs-msb-when-xs-nonneg-and-ys-neg (xs ys) (ys xs)))

; In the soundness proof, we had the hypothesis (consp xs),
; which suffices for (consp ys) and (consp zs) to aldo hold,
; but it looks like it cannot be easily done on the fly there.
; So we add this theorem here, and we use it there.

(defruledl consp-of-ys-and-zs
  (implies (and (consp xs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs)))
           (and (consp ys)
                (consp zs))))

; The proof, as mentioned above, goes by the four cases on the sign bits.
; In each of those cases, from N(x) + N(y) = N(z) + carry * 2^n,
; we derive I(x) + I(y) = I(z), by expanding the definition of I,
; and each of the four cases lets us simplify away
; carry * 2^m and any 2^n terms that may appear.

(defruled signed-small-add-checked-gadget-soundness
  (implies (and (primep p)
                (< (1+ (len xs)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp carry)
                (symbolp xy-diff-sign)
                (symbolp zx-diff-sign)
                (symbolp over/under-flow)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg xy-diff-sign)
                (r1cs::valuation-bindsp asg zx-diff-sign)
                (r1cs::valuation-bindsp asg over/under-flow)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (carry$ (lookup-equal carry asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (signed-small-add-checked-gadget
                                 xs ys zs carry
                                 xy-diff-sign zx-diff-sign over/under-flow
                                 one p)
                                asg p)
                               (and (bit-listp zs$)
                                    (bitp carry$)
                                    (equal (lebits=>int zs$)
                                           (+ (lebits=>int xs$)
                                              (lebits=>int ys$))))))))
  :do-not-induct t
  :use (consp-of-ys-and-zs
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance carry-0-when-xs-nonneg-and-ys-nonneg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-1-when-xs-neg-and-ys-neg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-neq-zs-msb-when-xs-nonneg-and-ys-neg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-neq-zs-msb-when-xs-neg-and-ys-nonneg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg))))
  :enable (signed-small-add-checked-gadget
           unsigned-small-add-wrapped-gadget
           unsigned-small-add-gadget-correct
           lookup-equal-list-of-append
           lookup-equal-list
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           boolean-xor-gadget-to-bitxor
           lookup-equal-of-car
           lookup-equal-list-of-last
           boolean-and-notleft-gadget-to-booland-boolnot
           zero-gadget-to-equal-0
           bitxor
           lebits=>int)
  :disable bitp)
