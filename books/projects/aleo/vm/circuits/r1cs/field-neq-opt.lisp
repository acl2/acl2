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

(include-book "../library-extensions/lookup-equal-list")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is an optimized version of field-neq,
; which omits the constraint to make r a boolean.
; That constraint is unnecessary, because the other two constraints
; imply that r must be either 0 or 1:
; if x = y, then r = 0;
; if x /= y, then b-r = 0 i.e. 1-r = 0 i.e. r = 1.

; The proof is similar to field-neq,
; but we need to disable two prime field rules
; that otherwise sabotage the proof.

(define field-neq-opt-gadget ((x symbolp)
                              (y symbolp)
                              (w symbolp) ; intermediate witness variable
                              (r symbolp)
                              (b symbolp) ; public variable
                              (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x)
                  (list (1- p) y))
         :b (list (list 1 w))
         :c (list (list 1 r)))
        (r1cs::make-r1cs-constraint
         :a (list (list 1 x)
                  (list (1- p) y))
         :b (list (list (1- p) r)
                  (list 1 b))
         :c nil)))

(defruled field-neq-opt-gadget-soundness
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
                                (field-neq-opt-gadget x y w r b p) asg p)
                               (equal r$ (if (equal x$ y$) 0 1))))))
  :do-not-induct t
  :enable (field-neq-opt-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product)
  :disable (pfield::mul-of-add-arg1
            pfield::mul-of-add-arg2))
