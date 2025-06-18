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

(include-book "integer-ternary")
(include-book "signed-small-sub-wrapped-const-var")

(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget calculates the absolute value,
; wrapping it around if it does not fit within the integer type.
; It first subtracts the operand xs from 0 with a wrapped subtraction,
; then it sets the result ys to either that or xs,
; based on whether the sign bit of xs is 1 or 0.

; This gadget consists of the variant of signed-small-sub-wrapped
; where the first operand is a constant (and the second a variable),
; and of the ternary integer gadget.
; The constant operand of the subtraction gadget consists of all 0 bits.
; The variables other than xs and ys are internal,
; used in the checked subtraction gadget.

(define signed-small-abs-wrapped-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (minus-xs symbol-listp)
                                         (carry symbolp)
                                         (one symbolp)
                                         (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len minus-xs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp :guard
                    :hints (("Goal" :cases ((consp minus-xs)))))
  (append
   (signed-small-sub-wrapped-const-var-gadget
    (repeat (len xs) 0) xs minus-xs carry one p)
   (integer-ternary-gadget (car (last xs)) minus-xs xs ys p)))

; The soundness proof is obtained from
; the soundness theorem of the subtraction gadget
; and the correctness theorem of the integer ternary gadget.

; We need a lemma to show that if xs is not empty,
; neither are ys or minus-xs.

(defruledl consp-of-ys-and-minusxs
  (implies (and (consp xs)
                (equal (len ys) (len xs))
                (equal (len minus-xs) (len xs)))
           (and (consp ys)
                (consp minus-xs))))

; We also need a lemma showing that
; the sign bit of the constant consisting of all 0 bits is 0.
; This is the constant used in the subtraction gadget.

(defrulel car-of-last-of-repeat-of-all-0
  (implies (> (nfix n) 0)
           (equal (car (last (repeat n 0))) 0))
  :enable repeat)

; When we use the soundness theorem of the subtraction gadget,
; there is a mod applied to the abs call (see below).
; But the mod can be eliminated because it is always less than 2^n.
; Here is the lemma for that.

(defruledl mod-of-abs-of-lebits=>int-and-expt-2-of-len
  (implies (consp bs)
           (equal (mod (abs (lebits=>int bs))
                       (expt 2 (len bs)))
                  (abs (lebits=>int bs))))
  :enable (lebits=>int-upper-bound
           lebits=>int-lower-bound))

; This is almost the soundness theorem,
; but it involves a mod applied to the abs,
; which goes away in the actual soundness theorem.
; There is probably a way to do this in one shot,
; but attempting to combine the steps fails,
; as the proof gets driven away from the proper path;
; this can be probably fixed with some additional rules,
; but since the current proof is working, we do not bother.

(defruledl soundness-lemma
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp minus-xs)
                (symbolp carry)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (equal (len minus-xs) (len xs))
                (< (1+ (len xs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg minus-xs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (one$ (lookup-equal one asg)))
             (implies
              (and (bit-listp xs$)
                   (equal one$ 1))
              (implies (r1cs::r1cs-constraints-holdp
                        (signed-small-abs-wrapped-gadget
                         xs ys minus-xs carry one p)
                        asg p)
                       (and (bit-listp ys$)
                            (equal (mod (lebits=>int ys$)
                                        (expt 2 (len xs)))
                                   (mod (abs (lebits=>int xs$))
                                        (expt 2 (len xs)))))))))
  :do-not-induct t
  :use ((:instance signed-small-sub-wrapped-const-var-gadget-soundness
                   (cs (repeat (len xs) 0))
                   (ys xs)
                   (zs minus-xs)
                   (z carry)
                   (one one)
                   (p p))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        consp-of-ys-and-minusxs)
  :enable (signed-small-abs-wrapped-gadget
           integer-ternary-gadget-correctness
           lookup-equal-of-car
           lookup-equal-list-of-last
           lebits=>int
           car-of-last-of-repeat-of-all-0))

; Soundness theorem.

(defruled signed-small-abs-wrapped-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp minus-xs)
                (symbolp carry)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (equal (len minus-xs) (len xs))
                (< (1+ (len xs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg minus-xs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (one$ (lookup-equal one asg)))
             (implies
              (and (bit-listp xs$)
                   (equal one$ 1))
              (implies (r1cs::r1cs-constraints-holdp
                        (signed-small-abs-wrapped-gadget
                         xs ys minus-xs carry one p)
                        asg p)
                       (and (bit-listp ys$)
                            (equal (mod (lebits=>int ys$)
                                        (expt 2 (len xs)))
                                   (abs (lebits=>int xs$))))))))
  :use (soundness-lemma
        (:instance mod-of-abs-of-lebits=>int-and-expt-2-of-len
                   (bs (lookup-equal-list xs asg)))))
