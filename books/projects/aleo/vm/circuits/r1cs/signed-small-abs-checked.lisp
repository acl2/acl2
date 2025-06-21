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
(include-book "signed-small-sub-checked-const-var")

(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget calculates the absolute value,
; checking that it fits within the integer type.
; It first subtracts the operand xs from 0,
; then it sets the result ys to either that or xs,
; based on whether the sign bit of xs is 1 or 0.

; This gadget consists of the variant of signed-small-sub-checked
; where the first operand is a constant (and the second a variable),
; and of the ternary integer gadget.
; The constant operand of the subtraction gadget consists of all 0 bits.
; The variables other than xs and ys are internal,
; used in the checked subtraction gadget.

(define signed-small-abs-checked-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (minus-xs symbol-listp)
                                         (carry symbolp)
                                         (diff-sign symbolp)
                                         (over/under-flow symbolp)
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
   (signed-small-sub-checked-const-var-gadget
    (repeat (len xs) 0) xs minus-xs carry diff-sign over/under-flow one p)
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

; Soundness theorem.

(defruled signed-small-abs-checked-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp minus-xs)
                (symbolp carry)
                (symbolp diff-sign)
                (symbolp over/under-flow)
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
                (r1cs::valuation-bindsp asg diff-sign)
                (r1cs::valuation-bindsp asg over/under-flow)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (signed-small-abs-checked-gadget
                                 xs ys
                                 minus-xs carry diff-sign over/under-flow
                                 one p)
                                asg p)
                               (and (bit-listp ys$)
                                    (equal (lebits=>int ys$)
                                           (if (>= (lebits=>int xs$) 0)
                                               (lebits=>int xs$)
                                             (- (lebits=>int xs$)))))))))
  :do-not-induct t
  :use ((:instance signed-small-sub-checked-const-var-gadget-soundness
                   (cs (repeat (len xs) 0))
                   (ys xs)
                   (zs minus-xs)
                   (carry carry)
                   (zy-diff-sign diff-sign)
                   (over/under-flow over/under-flow)
                   (one one)
                   (p p))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        consp-of-ys-and-minusxs)
  :enable (signed-small-abs-checked-gadget
           integer-ternary-gadget-correctness
           lookup-equal-of-car
           lookup-equal-list-of-last
           lebits=>int
           car-of-last-of-repeat-of-all-0))
