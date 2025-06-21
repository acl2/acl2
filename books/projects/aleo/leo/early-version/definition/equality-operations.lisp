; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ equality-operations
  :parents (dynamic-semantics)
  :short "Leo equality operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we mean both equality @('==') and inequality @('!='),
     since they are closely related.
     They are both binary, of course.")
   (xdoc::p
    "Each of these operations is defined on all Leo values,
     but the two operands must have the same type.
     That is, it is not possible to compare for (in)equality
     two Leo values of different types,
     even though they could be simply considered not equal.
     But requiring the same type promotes better programming discipline.")
   (xdoc::p
    "We model these two operations via two ACL2 functions
     that return a Leo boolean value when both arguments have the same type.
     If they have different types, we defensively return an error.
     If they have the same type, we just use ACL2's @(tsee equal):
     this is correct because our current model of values
     has a unique representation for each value."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-eq ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo equality operation."
  (if (type-equiv (type-of-value left)
                  (type-of-value right))
      (value-bool (value-equiv left right))
    (reserrf (list :op-eq (value-fix left) (value-fix right))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-ne ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo inequality operation."
  (if (type-equiv (type-of-value left)
                  (type-of-value right))
      (value-bool (not (value-equiv left right)))
    (reserrf (list :op-ne (value-fix left) (value-fix right))))
  :hooks (:fix))
