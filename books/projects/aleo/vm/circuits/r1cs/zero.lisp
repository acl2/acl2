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
(include-book "std/lists/repeat" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget checks if a variable is 0.
; There are several ways to do this,
; but here we do it like this
;   (x) (1) = (0)

(define zero-gadget ((x symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1))
         :c nil)))

; The gadget is equivalent to its specification, namely being 0.

(defruled zero-gadget-to-equal-0
  (implies (and (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x))
           (equal (r1cs::r1cs-constraints-holdp (zero-gadget x) asg p)
                  (equal (lookup-equal x asg) 0)))
  :enable (zero-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of zero-checking gadgets.

(define zero-gadget-list ((xs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (zero-gadget (car xs))
                   (zero-gadget-list (cdr xs))))))

; A list of zero-checking gadgets is equivalent to the variables being all 0.

(defruled zero-gadget-list-to-all-equal-0
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (equal (r1cs::r1cs-constraints-holdp
                   (zero-gadget-list xs) asg p)
                  (equal (lookup-equal-list xs asg)
                         (repeat (len xs) 0))))
  :enable (zero-gadget-list
           zero-gadget-to-equal-0
           lookup-equal-list
           repeat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; zero b-type gadget
; One of the alternate ways to enforce a variable is zero.
;   () * (1) = (x)

(define zero-gadget-b ((x symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a nil
         :b (list (list 1 1))
         :c (list (list 1 x)))))

; The gadget is equivalent to its specification, namely being 0.

(defruled zero-gadget-b-to-equal-0
  (implies (and (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x))
           (equal (r1cs::r1cs-constraints-holdp (zero-gadget-b x) asg p)
                  (equal (lookup-equal x asg) 0)))
  :enable (zero-gadget-b
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of zero b-type gadgets.

(define zero-gadget-b-list ((xs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (zero-gadget-b (car xs))
                   (zero-gadget-b-list (cdr xs))))))

; A list of zero gadgets is equivalent to the variables being all 0.

(defruled zero-gadget-b-list-to-all-equal-0
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (equal (r1cs::r1cs-constraints-holdp
                   (zero-gadget-b-list xs) asg p)
                  (equal (lookup-equal-list xs asg)
                         (repeat (len xs) 0))))
  :enable (zero-gadget-b-list
           zero-gadget-b-to-equal-0
           lookup-equal-list
           repeat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In some cases, snarkVM uses a slightly different zero gadget from above.
; It uses a variant that involves a public variables,
; that is presumably to be set to 1.
; The gadget consists of the single constraint
;   (-x + u) (1) = (1)
; where x is the variable to check to be 0
; and u is the variable assumed to be equal to 1.
; If u is 1, the constraint reduces to
;   (-x + 1) (1) = (1)
; i.e.
;   -x + 1 = 1
; i.e.
;   x = 0

(define zero-unit-gadget ((x symbolp) (u symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list (1- p) x)
                  (list 1 u))
         :b (list (list 1 1))
         :c (list (list 1 1)))))

; The gadget is equivalent to its specification, namely that x is 0,
; provided that u is 1 as explained above.

(defruled zero-unit-gadget-to-equal-0
  (implies (and (symbolp x)
                (symbolp u)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg u))
           (implies (equal (lookup-equal u asg) 1)
                    (equal (r1cs::r1cs-constraints-holdp
                            (zero-unit-gadget x u p) asg p)
                           (equal (lookup-equal x asg) 0))))
  :enable (zero-unit-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
