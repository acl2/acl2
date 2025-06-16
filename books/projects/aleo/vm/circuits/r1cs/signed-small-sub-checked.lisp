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

(include-book "boolean-and-notright")
(include-book "boolean-xor")
(include-book "unsigned-small-sub-wrapped")
(include-book "zero")

(include-book "../library-extensions/digits")

(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget performs small checked signed integer subtraction.
; It is quite analogous to signed-small-add-checked, except that
; (1) the unsigned-small-sub-wrapped sub-gadget is used
; instead of the unsigned-small-add-wrapped sub-gadget,
; (2) the second 'xor' sub-gadget combines the sign of z and y
; instead of combining the sign of z and x, and
; (3) the boolean-and-notright sub-gadget is used
; instead of the boolean-and-notleft sub-gadget.

(define signed-small-sub-checked-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (carry symbolp)
                                         (xy-diff-sign symbolp)
                                         (zy-diff-sign symbolp)
                                         (over/under-flow symbolp)
                                         (one symbolp)
                                         (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append
   (unsigned-small-sub-wrapped-gadget xs ys zs carry one p)
   (boolean-xor-gadget (car (last xs)) (car (last ys)) xy-diff-sign p)
   (boolean-xor-gadget (car (last zs)) (car (last ys)) zy-diff-sign p)
   (boolean-and-notright-gadget xy-diff-sign zy-diff-sign over/under-flow one p)
   (zero-gadget over/under-flow)))

; Similarly to signed-small-add-checked,
; the core reasoning is by four cases on the signs of x and y.
; The unsigned-small-sub-wrapped gadget implies that
;   N(x) - N(y) + 2^n = N(z) + carry * 2^n
; We define an abbreviation for the common hyps of the four cases.

(local
 (defmacro xyzc-hyps ()
   '(and (bit-listp xs)
         (bit-listp ys)
         (bit-listp zs)
         (bitp carry)
         (consp xs)
         (equal (len ys) (len xs))
         (equal (len zs) (len xs))
         (equal (+ (lebits=>nat xs)
                   (- (lebits=>nat ys))
                   (expt 2 (len xs)))
                (+ (lebits=>nat zs)
                   (* carry (expt 2 (len xs))))))))

; If both x and y are non-negative,
; it's the case that the carry and the sign of z are different:
;
; x(n-1) = 0 ==> N(x) < 2^(n-1)
;            ==> N(x) + 2^n < 2^n + 2^(n-1)
;            ==> N(x) - N(y) + 2^n < 2^n + 2^(n-1)
;
; y(n-1) = 0 ==> N(y) < 2^(n-1)
;            ==> 2^n - N(y) > 2^n - 2^(n-1) = 2^(n-1)
;            ==> N(x) - N(y) + 2^n > 2^(n-1)
;
; z(n-1) = carry = 0 ==> N(x) - N(y) + 2^n = N(z) < 2^(n-1)
;    -- impossible
;
; z(n-1) = carry = 1 ==> N(x) - N(y) + 2^n = N(z) + 2^n >= 2^(n-1) + 2^n
;    -- impossible
;
; ==> (z(n-1) = 0 /\ carry = 1) \/ (z(n-1) = 1 /\ carry = 0)

(defruledl carry-neq-zs-msb-when-xs-nonneg-and-ys-nonneg
  (implies (xyzc-hyps)
           (implies (and (equal (car (last xs)) 0)
                         (equal (car (last ys)) 0))
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
                            (equal (car (last ys)) 0)
                            (equal carry 0))
                       (equal (car (last zs)) 1)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits ys))
           (:instance lebits=>nat-upper-bound-when-msb-is-0 (bits zs))))

   (defruled lemma2
     (implies (xyzc-hyps)
              (implies (and (equal (car (last xs)) 0)
                            (equal (car (last ys)) 0)
                            (equal carry 1))
                       (equal (car (last zs)) 0)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits xs))
           (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits zs))))))

; If both x and y are negative, there is a similar conclusion,
; but with a slightly different proof.

(defruledl carry-neq-zs-msb-when-xs-neg-and-ys-neg
  (implies (xyzc-hyps)
           (implies (and (equal (car (last xs)) 1)
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
              (implies (and (equal (car (last xs)) 1)
                            (equal (car (last ys)) 1)
                            (equal carry 0))
                       (equal (car (last zs)) 1)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits xs))
           (:instance lebits=>nat-upper-bound-when-msb-is-0 (bits zs))))

   (defruled lemma2
     (implies (xyzc-hyps)
              (implies (and (equal (car (last xs)) 1)
                            (equal (car (last ys)) 1)
                            (equal carry 1))
                       (equal (car (last zs)) 0)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits ys))
           (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits zs))))))

; If x and y have different signs, carry is 0.

(defrulel carry-0-when-xs-nonneg-and-ys-neg
  (implies (xyzc-hyps)
           (implies (and (equal (car (last xs)) 0)
                         (equal (car (last ys)) 1))
                    (equal carry 0)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits xs))
        (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits ys))))

(defrulel carry-1-when-xs-neg-and-ys-nonneg
  (implies (xyzc-hyps)
           (implies (and (equal (car (last xs)) 1)
                         (equal (car (last ys)) 0))
                    (equal carry 1)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits xs))
        (:instance lebits=>nat-upper-bound-when-msb-is-0 (bits ys))))

; The four cases above are somewhat parallel
; to the ones for signed-small-add-checked,
; with the difference that here y is subtracted from, not added to, x,
; and thus that essentially "inverts" the sign of y in the four cases.

; In the soundness proof, we need to derive
; the non-emptiness of ys and zs from the one of xs,
; as in signed-small-add-checked.

(defruledl consp-of-ys-and-zs
  (implies (and (consp xs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs)))
           (and (consp ys)
                (consp zs))))

; The proof is also analogous to signed-small-add-checked.

(defruled signed-small-sub-checked-gadget-soundness
  (implies (and (primep p)
                (< (1+ (len xs)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp carry)
                (symbolp xy-diff-sign)
                (symbolp zy-diff-sign)
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
                (r1cs::valuation-bindsp asg zy-diff-sign)
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
                                (signed-small-sub-checked-gadget
                                 xs ys zs carry
                                 xy-diff-sign zy-diff-sign over/under-flow
                                 one p)
                                asg p)
                               (and (bit-listp zs$)
                                    (bitp carry$)
                                    (equal (lebits=>int zs$)
                                           (- (lebits=>int xs$)
                                              (lebits=>int ys$))))))))
  :do-not-induct t
  :use (consp-of-ys-and-zs
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list zs asg)))
        (:instance carry-neq-zs-msb-when-xs-nonneg-and-ys-nonneg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-neq-zs-msb-when-xs-neg-and-ys-neg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-0-when-xs-nonneg-and-ys-neg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-1-when-xs-neg-and-ys-nonneg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg))))
  :enable (signed-small-sub-checked-gadget
           unsigned-small-sub-wrapped-gadget
           unsigned-small-sub-gadget-correct
           lookup-equal-list-of-append
           lookup-equal-list
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           boolean-xor-gadget-to-bitxor
           lookup-equal-of-car
           lookup-equal-list-of-last
           bitxor
           boolean-and-notright-gadget-to-booland-boolnot
           zero-gadget-to-equal-0
           lebits=>int)
  :disable bitp)
