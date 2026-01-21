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

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The field ternary gadget takes as input x, y, and z,
; where the value of x (a bit) is used to set the output to y (when x is 1)
; or z (when x is 0).
; There are two constraints,
;   (-x + 1) * (x) = 0
;   (x) * (y - z) = (r - z)
; If x = 0, r = z.
; If x = 1, (y - z) = (r - z), so r = y.

; NOTE:
; Previously, we did not see a bit constraint on x
; in the the sample gadget from SnarkVM.
; But the sample on 2023-04-19 does have the bit constraint.
; For most flexibility, we leave the bit constraint off
; from this gadget definition.

(define field-ternary-gadget ((x symbolp) ; selector
                              (y symbolp)
                              (z symbolp)
                              (r symbolp) ; output
                              (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list
   (r1cs::make-r1cs-constraint
    :a (list (list 1 x))
    :b (list (list 1 y)
             (list (- p 1) z))
    :c (list (list 1 r)
             (list (- p 1) z)))))

(define ternary-function ((x bitp)
                          (y natp)
                          (z natp))
  :returns (r natp :hyp :guard)
  (if (= x 1)
      y
    z))

; There is an extra hyp of (bitp x$)
; that would not be needed if we also
; had the bit constraint in the gadget definition.
(defrule field-ternary-gadget-soundness
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg))
                (r$ (lookup-equal r asg)))
             (implies (and (r1cs::r1cs-constraints-holdp
                            (field-ternary-gadget x y z r p)
                            asg p)
                           (bitp x$))
                      (equal (ternary-function x$ y$ z$)
                             r$))))
  :do-not-induct t
  :enable (field-ternary-gadget
           ternary-function
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
