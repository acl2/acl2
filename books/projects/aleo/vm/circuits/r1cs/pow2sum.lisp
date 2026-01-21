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

(include-book "pow2sum-vectors")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This constrains x to be the powers-of-two weighted sum
; of the list of (booleans in) xs.
; It consists of a constraint
;   (x) (1) = (x0 + 2x1 + 4x2 + ...)

(define pow2sum-gadget ((x symbolp) (xs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1))
         :c (pow2sum-vector xs 0))))

; The gadget is equivalent to saying that x is
; the weighted sum of x0, x1, x2, etc., modulo the prime.
; This is in fact, the specification for the gadget.
; In the specification, the weighted sum is in integer arithmetic,
; but the gadget is in prime field arithmetic,
; so we need to take the modulo operation.
; Whether the weighted sum is less than the prime or not
; is a separete issue:
; the specifiation of the gadget involves the modulo,
; no matter whether the weighted sum is less than the prime or now;
; it could even consists of many more bits than the prime.

(defruled pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
  (implies (and (symbolp x)
                (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs))
           (b* ((x$ (lookup-equal x asg))
                (xs$ (lookup-equal-list xs asg)))
             (implies (bit-listp xs$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (pow2sum-gadget x xs) asg p)
                             (equal x$ (mod (lebits=>nat xs$) p))))))
  :do-not-induct t
  :enable (pow2sum-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat))
