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

; This is a specialized version of boolean 'or'
; that also negates its left operand.
; Since 'not' is done on the fly in snarkVM,
; when an 'or' is applied to a 'not'
; there is just one constraint for the 'or',
; but the operand with the 'not' is negated.
; The negation in snarkVM is achieved by subtracting a public variable,
; which must be assumed to have value 1,
; as done in other parts of snarkVM.

; So here we define and verify this boolean gadget;
; the PFCS form of gadget will obviate the need for this,
; by providing ways to inline gadgets like 'not'.

; This gadget consists of the single constraint
;   (x + (p-1)one + 1) ((p-1)y + 1) = ((p-1)z + 1)
; which is like
;   (x) (1 - y) = (1 - z)
; where one is a public variable assumed to be 1
; (this is a particularity of snarkVM).

(define boolean-or-notleft-gadget ((x symbolp)
                                   (y symbolp)
                                   (z symbolp)
                                   (one symbolp)
                                   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x)
                  (list (1- p) one)
                  (list 1 1))
         :b (list (list (1- p) y)
                  (list 1 1))
         :c (list (list (1- p) z)
                  (list 1 1)))))

(defruled boolean-or-notleft-gadget-to-boolor-boolnot
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (symbolp one)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bitp x$)
                           (bitp y$)
                           (equal one$ 1))
                      (equal (r1cs::r1cs-constraints-holdp
                              (boolean-or-notleft-gadget x y z one p) asg p)
                             (equal z$
                                    (if (or (equal x$ 0)
                                            (equal y$ 1))
                                        1
                                      0))))))
  :enable (boolean-or-notleft-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
