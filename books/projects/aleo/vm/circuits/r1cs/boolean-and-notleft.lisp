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

; This is a specialized version of boolean 'and'
; that also negates its left operand.
; Since 'not' is done on the fly in snarkVM,
; when an 'and' is applied to a 'not'
; there is just one constraint for the 'and',
; but the operand with the 'not' is negated.
; So here we define and verify this boolean gadget;
; the PFCS form of gadget will obviate the need for this,
; by providing ways to inline gadgets like 'not'.

; This gadget consists of the single constraint
;   ((p-1)x + one) (y) = (z)
; which is like
;   (one - x) (y) = (z)
; where one is a public variable assumed to be 1
; (this is a particularity of snarkVM).

(define boolean-and-notleft-gadget ((x symbolp)
                                    (y symbolp)
                                    (z symbolp)
                                    (one symbolp)
                                    (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list (1- p) x)
                  (list 1 one))
         :b (list (list 1 y))
         :c (list (list 1 z)))))

(defruled boolean-and-notleft-gadget-to-booland-boolnot
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
                              (boolean-and-notleft-gadget x y z one p) asg p)
                             (equal z$
                                    (if (and (equal x$ 0)
                                             (equal y$ 1))
                                        1
                                      0))))))
  :enable (boolean-and-notleft-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
