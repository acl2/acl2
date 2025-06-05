; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "semantics-deep")
(include-book "semantics-shallow")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics
  :parents (pfcs)
  :short "Semantics of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A named relation denotes
     a predicate over the cartesian product of the prime field;
     the number of factors of the cartesian product
     is the arity of the relation.
     The predicate holds exactly on the tuples of prime field elements
     that, when assigned to the parameters of the relation,
     satisfy all the constraints that define the relation.
     An equality constraint is satisfied
     when its evaluated left and right sides are equal.
     A relation application in the defining body of another one is satisfied
     when the predicate it denotes holds on the prime field elements
     that result from evaluating its argument expressions.
     There must be no recursion in the relation definitions
     for this to be well-defined.
     The body of a relation definition may include variables
     that are not among the formal parameters:
     these are regarded as existentially quantified,
     i.e. the predicate denoted by the relation holds on a tuple
     when there exist values for those extra variables that,
     together with the values of the tuple, satisfy all the constraints.")
   (xdoc::p
    "We formalize this as a deeply embedded semantics
     and as a shallowly embedded semantics."))
  :order-subtopics t)
