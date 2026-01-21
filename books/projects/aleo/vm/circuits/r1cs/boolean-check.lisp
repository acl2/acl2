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

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/list-fix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The boolean check gadget constrains a variable to be boolean, i.e. 0 or 1.
; The gadget consists of a single constraint
;   ((p-1)x + 1) (x) = (0)
; i.e.
;   (1 - x) (x) = (0)
; which holds iff
;   x in {0, 1}

(define boolean-check-gadget ((x symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list (1- p) x)
                  (list 1 1))
         :b (list (list 1 x))
         :c nil)))

; The gadget is equivalent to its specification, namely BITP.

(defruled boolean-check-gadget-to-bitp
  (implies (and (symbolp x)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-check-gadget x p) asg p)
                  (bitp (lookup-equal x asg))))
  :enable (boolean-check-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of boolean-checking gadgets.

(define boolean-check-gadget-list ((xs symbol-listp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (boolean-check-gadget (car xs) p)
                   (boolean-check-gadget-list (cdr xs) p)))))

; A list of boolean-checking gadgets is equivalent to BIT-LISTP.

(defruled boolean-check-gadget-list-to-bit-listp
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-check-gadget-list xs p) asg p)
                  (bit-listp (lookup-equal-list xs asg))))
  :enable (boolean-check-gadget-list
           boolean-check-gadget-to-bitp
           lookup-equal-list))
