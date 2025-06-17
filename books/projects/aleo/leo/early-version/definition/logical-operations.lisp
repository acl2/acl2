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

(defxdoc+ logical-operations
  :parents (dynamic-semantics)
  :short "Leo logical operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are conjunction, disjunction, negated conjunction, and
     negated disjunction.  They are all binary.")
   (xdoc::p
    "There is also a unary logical operation, @(see op-not), that is allowed
     on both boolean and integer values.")
   (xdoc::p
    "The operations here are only allowed on boolean values.
     We formalize them via ACL2 functions over all Leo values,
     defined so that they return an error on non-boolean values.
     This is part of our defensive definition of the Leo dynamic semantics,
     in which attempts to apply operations on operands of the wrong type
     result in errors."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-and ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo boolean conjunction operation."
  (if (and (value-case left :bool)
           (value-case right :bool))
      (value-bool (and (value-bool->get left)
                       (value-bool->get right)))
    (reserrf (list :op-and (value-fix left) (value-fix right))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-or ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo boolean disjunction operation."
  (if (and (value-case left :bool)
           (value-case right :bool))
      (value-bool (or (value-bool->get left)
                      (value-bool->get right)))
    (reserrf (list :op-or (value-fix left) (value-fix right))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-nand ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo boolean negated conjunction operation."
  (if (and (value-case left :bool)
           (value-case right :bool))
      (value-bool (not (and (value-bool->get left)
                            (value-bool->get right))))
    (reserrf (list :op-nand (value-fix left) (value-fix right))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-nor ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo boolean negated disjunction operation."
  (if (and (value-case left :bool)
           (value-case right :bool))
      (value-bool (not (or (value-bool->get left)
                           (value-bool->get right))))
    (reserrf (list :nor (value-fix left) (value-fix right))))
  :hooks (:fix))
