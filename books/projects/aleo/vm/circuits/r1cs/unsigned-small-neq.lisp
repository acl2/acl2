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
(include-book "pow2sum")

(local (include-book "../library-extensions/digits"))

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget checks whether two unsigned integers are not equal.
; The integers are given as bits xs and ys of the same length.
; The result is z: 1 if xs and ys differ; 0 if xs and ys are equal.

; The gadget introduces z as a boolean,
; and then adds the following two constraints:
;
;   (  x(0) + 2.x(1) + ... + 2^(n-1).x(n-1)
;    - y(0) - 2.y(1) - ... - 2^(n-1).y(n-1))
;   (w)
;   =
;   (z)
;
;   (  x(0) + 2.x(1) + ... + 2^(n-1).x(n-1)
;    - y(0) - 2.y(1) - ... - 2^(n-1).y(n-1))
;   (-z + one)
;   =
;   (0)
;
; where 'one' is a public variable that must be assumed to be 1
; (a current pecularity of snarkVM, found in other gadgets).
; It is easy to see that this gadget is like the field-neq gadget,
; except that the two field elements x and y to compare
; are the unsigned values of xs and ys here instead.
; The reasoning is the same as field-neq.
; We must assume that n is less than the bit size of p,
; so that the weighted sums are not modular.

(define unsigned-small-neq-gadget ((xs symbol-listp)
                                   (ys symbol-listp)
                                   (z symbolp)
                                   (w symbolp)
                                   (one symbolp)
                                   (p primep))
  :guard (and (equal (len ys) (len xs))
              (< (len xs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append
   (boolean-check-gadget z p)
   (list
    (r1cs::make-r1cs-constraint
     :a (append (pow2sum-vector xs 0) (pow2sum-neg-prime-vector ys 0 p))
     :b (list (list 1 w))
     :c (list (list 1 z)))
    (r1cs::make-r1cs-constraint
     :a (append (pow2sum-vector xs 0) (pow2sum-neg-prime-vector ys 0 p))
     :b (list (list (1- p) z)
              (list 1 one))
     :c nil))))

; This gadget is sound.
; Just enabling the linear rule lebits=>nat-less-when-len-less
; seems insufficient to eliminate the (mod ... p)
; around certain (lebits=>nat ...) calls,
; so we use a :use hint instead.
; We also need the injectivity of lebits=>nat,
; but it does not apply as a rewrite rule to what arises during the proof,
; and so we use a :use hint for that too.

(defruled unsigned-small-neq-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal (len ys) (len xs))
                (< (len xs) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (z$ (lookup-equal z asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-neq-gadget xs ys z w one p)
                                asg
                                p)
                               (equal z$ (if (equal (lebits=>nat xs$)
                                                    (lebits=>nat ys$))
                                             0
                                           1))))))
  :do-not-induct t
  :enable (unsigned-small-neq-gadget
           boolean-check-gadget-to-bitp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pow2sum-neg-prime-vector-to-mod-of-lebits=>nat
           pfield::add)
  :use ((:instance acl2::lebits=>nat-injectivity
                   (digits1 (lookup-equal-list xs asg))
                   (digits2 (lookup-equal-list ys asg)))
        (:instance lebits=>nat-less-when-len-less
                   (bs (lookup-equal-list xs asg)))
        (:instance lebits=>nat-less-when-len-less
                   (bs (lookup-equal-list ys asg))))
  :disable acl2::lebits=>nat-injectivity)
