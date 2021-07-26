; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "semantics-deep")
(include-book "proof-support")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable rtl::primep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These are examples from Zcash (see :DOC ZCASH::ZCASH).
; They may be moved to the Zcash library at some point.

; Each example defines a PFCS named relation
; and proves its equivalence with an ACL2 specification,
; using the PFCS deeply embedded semantics.

; These are simple examples for now,
; but they should demonstrate how PFCS can support
; the modular verification of hierarchical gadgets.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; equality constraint in [ZPS:A.3.1.1]:

(define constraint-boolean ((b-var symbolp))
  :returns (constr constraintp)
  (make-constraint-equal
   :left (expression-mul
          (expression-sub (expression-const 1)
                          (expression-var b-var))
          (expression-var b-var))
   :right (expression-const 0)))

(define spec-boolean ((b (fep b p)) (p rtl::primep))
  :returns (yes/no booleanp)
  (declare (ignore p))
  (or (equal b 0)
      (equal b 1)))

(defruled constraint-boolean-to-spec-boolean
  (implies (and (rtl::primep p)
                (symbolp b-var)
                (fep b p))
           (iff (constraint-satp (omap::update b-var b nil)
                                 (constraint-boolean b-var)
                                 sys
                                 p)
                (spec-boolean b p)))
  :enable (constraint-boolean
           constraint-satp-of-equal
           eval-expr
           expression-sub
           expression-neg
           spec-boolean))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add more examples
