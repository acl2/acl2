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

; This is actually the same as the AND gadget.
; Also, it is possible to inline this for proving soundness of the indicator
; gadget, but we leave it here since it helps to clarify what is going on.

(define x*y=r-constraint ((x symbolp)
                          (y symbolp)
                          (r symbolp))
  :returns (constr r1cs::r1cs-constraintp :hyp :guard)
  (r1cs::make-r1cs-constraint
   :a (list (list 1 x))
   :b (list (list 1 y))
   :c (list (list 1 r))))

;; If x*y=r and r≠0 then x≠0 and y≠0.
(defruled nonzero-product-implies-nonzero-multiplicands
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal x asg))
                (r$ (lookup-equal r asg)))
             (implies (r1cs::r1cs-constraint-holdsp
                       (x*y=r-constraint x y r)
                       asg p)
                      (implies (not (equal r$ 0))
                               (and (not (equal x$ 0))
                                    (not (equal y$ 0))))
                      )))
  :do-not-induct t
  :enable (x*y=r-constraint
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The indicator gadget normalizes 0/nonzero to 0/1
; For now it only applies to a variable, not an expression.

(define indicator-gadget ((x symbolp) ; input field element
                          (w symbolp) ; an unconstrained witness
                          (r symbolp) ; output bit
                          (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append ;; x * w = r  ; if x=0, r=0
          ;; x * (1 - r) = 0  ; if x /= 0, r=1
          ;; How about the converse
          ;; If r = 0, x = 0 from the 2nd constraint.
          ;; If r=1, x /= 0 from the 1st constraint.
          (list
           ;; x * w = r
           ;; Note, this constraint could just be inline and the definitions
           ;; would be unnecessary and some enables below would not be
           ;; needed, either.
           (x*y=r-constraint x w r)
           ;; x * (1 - r) = 0
           (r1cs::make-r1cs-constraint
            :a (list (list 1 x))
            :b (list (list 1 1)
                     (list (- p 1) r))
            :c nil))))

(define indicator-function ((x natp))
  :returns (r bitp :hyp :guard)
  (if (= x 0)
      0
    1))

(defruled indicator-gadget-soundness
  (implies (and (symbolp x)
                (symbolp w)
                (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (r$ (lookup-equal r asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (indicator-gadget x w r p)
                       asg p)
                      (equal (indicator-function x$)
                             r$))))
  :do-not-induct t
  :enable (indicator-gadget
           indicator-function
           nonzero-product-implies-nonzero-multiplicands
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
