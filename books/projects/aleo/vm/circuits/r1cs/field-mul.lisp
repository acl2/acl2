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

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The field multiplication gadget just equates an (output) variable
; to the multiplication of two (input) variables.
; There is a single constraint
;   (x) (y) = (r)
; This straightforwardly corresponds to field multiplication.

(define field-mul-gadget ((x symbolp) (y symbolp) (r symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y))
         :c (list (list 1 r)))))

(defruled field-mul-gadget-correctness
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (r$ (lookup-equal r asg)))
             (equal (r1cs::r1cs-constraints-holdp
                     (field-mul-gadget x y r) asg p)
                    (equal r$ (pfield::mul x$ y$ p)))))
  :do-not-induct t
  :enable (field-mul-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
