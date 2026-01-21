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

; This gadget checks if two variables are equal.
; There are several ways to do this,
; but here we do it like this:
;   (x) (1) = (y)
; This can be used when assigning y to
; the result of some computation folded over a list of x's,
; but where the list only has one x, in which case y simply gets the value of x.

(define equal-gadget ((x symbolp) (y symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1))
         :c (list (list 1 y)))))

; The gadget is equivalent to its specification, namely equality.

(defruled equal-gadget-to-equal
  (implies (and (symbolp x)
                (symbolp y)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y))
           (equal (r1cs::r1cs-constraints-holdp (equal-gadget x y) asg p)
                  (equal (lookup-equal x asg)
                         (lookup-equal y asg))))
  :enable (equal-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of equality-checking gadgets.

(define equal-gadget-list ((xs symbol-listp) (ys symbol-listp))
  :guard (= (len xs) (len ys))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (equal-gadget (car xs) (car ys))
                   (equal-gadget-list (cdr xs) (cdr ys))))))

; A list of equality-checking gadgets is equivalent to the variables in the lists
; being pairwise equal.

; NOTE: Consider defining equal-gadget-list-to-all-pairwise-equal
; in a somewhat similar way as
; zero-gadget-list-to-all-equal-0
; is defined.
