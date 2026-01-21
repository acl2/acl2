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
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The field not-equality gadget checks if
; field x is not equal to field y, and returns a not-equality indicator bit r.
; The constraints are
;   ((p-1)r + 1) (r) = (0)
;   (x + (p-1)y) (w) = (r)
;   (x + (p-1)y) ((p-1)r + b) = (0)
; i.e.
;   (1 - r) (r) = (0)
;   (x - y) (w) = (r)
;   (x - y) (b - r) = (0)
; The first constraint makes the result r a boolean.
; The variable w is an internal one.
; The variable b is a public one,
; which must be 1 in order for this gadget to work;
; it is not clear why this is used instead of just one,
; and the gadget can be probably optimized to do without this variable.

; If x = y, then r = 0 by the second constraint,
; and w is irrelevant;
; the third constraint is satisfied too.
; If instead x != y, then r = b by the third constraint.
; If b were 0, then r would be also 0, and not correct, because it should be 1;
; however, the second constraint would be easily satisfied by w = 0,
; so the constraints do not imply that b is 1, but rather this must be assumed.
; Assuming that b = r = 1, then the second constraint is satisfied
; by picking w to be the inverse of x - y, which exists because x != y.

(define field-neq-gadget ((x symbolp)
                          (y symbolp)
                          (w symbolp) ; intermediate witness variable
                          (r symbolp)
                          (b symbolp) ; public variable
                          (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget r p)
          (list
           (r1cs::make-r1cs-constraint
            :a (list (list 1 x)
                     (list (1- p) y))
            :b (list (list 1 w))
            :c (list (list 1 r)))
           (r1cs::make-r1cs-constraint
            :a (list (list 1 x)
                     (list (1- p) y))
            :b (list (list (1- p) r)
                     (list 1 b))
            :c nil))))

(defruled field-neq-gadget-soundness
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp w)
                (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (b$ (lookup-equal b asg))
                (r$ (lookup-equal r asg)))
             (implies (equal b$ 1)
                      (implies (r1cs::r1cs-constraints-holdp
                                (field-neq-gadget x y w r b p) asg p)
                               (equal r$ (if (equal x$ y$) 0 1))))))
  :do-not-induct t
  :enable (field-neq-gadget
           boolean-check-gadget-to-bitp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
