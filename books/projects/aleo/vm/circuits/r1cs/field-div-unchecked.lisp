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

(include-book "field-mul")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The field unchecked division gadget consists of one constraint
;   (z) (y) = (x)
; where x is the dividend, y is the divisor, and z is the quotient.
; If y is not 0, then the constraint is equivalent to z = x / y.
; We build this gadget from the field multiplication gadget.

(define field-div-unchecked-gadget ((x symbolp) (y symbolp) (z symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-mul-gadget z y x))

(defruled field-div-unchecked-gadget-soundness
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg)))
             (implies (not (equal y$ 0))
                      (equal (r1cs::r1cs-constraints-holdp
                              (field-div-unchecked-gadget x y z) asg p)
                             (equal z$ (pfield::div x$ y$ p))))))
  :enable (field-div-unchecked-gadget
           field-mul-gadget-correctness))
