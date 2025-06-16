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

; This gadget checks if a variable is 1.
; There are several ways to do this,
; but here we do it like this
;   (x) (1) = (1)

(define one-gadget ((x symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1))
         :c (list (list 1 1)))))

; The gadget is equivalent to its specification, namely being 1.

(defruled one-gadget-to-equal-1
  (implies (and (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x))
           (equal (r1cs::r1cs-constraints-holdp (one-gadget x) asg p)
                  (equal (lookup-equal x asg) 1)))
  :enable (one-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of one-checking gadgets.

(define one-gadget-list ((xs symbol-listp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (one-gadget (car xs))
                   (one-gadget-list (cdr xs))))))

; A list of one-checking gadgets is equivalent to the variables being all 1.

(defruled one-gadget-list-to-all-equal-1
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (equal (r1cs::r1cs-constraints-holdp
                   (one-gadget-list xs) asg p)
                  (equal (lookup-equal-list xs asg)
                         (repeat (len xs) 1))))
  :enable (one-gadget-list
           one-gadget-to-equal-1
           lookup-equal-list
           repeat))
