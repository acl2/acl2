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
(include-book "curve-parameterization")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ group-arithmetic-operations
  :parents (arithmetic-operations)
  :short "Leo group arithmetic operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are negation (unary), doubling (unary),
     addition (binary), subtraction (binary),
     and scalar multiplication.")
   (xdoc::p
    "These operations are paramterized over the curve;
     see @(see curve-parameterization).
     implicitly depend on an elliptic curve.")
   (xdoc::p
    "These ACL2 functions are defined over all possible group values,
     but they return errors if the underlying points
     are not in the actual subgroup.
     It should be an invariant, to be formalized and proved,
     that the underlying points of the group values in a Leo computation state
     always belong to the subgroup."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-group-neg ((arg valuep) (curve curvep))
  :guard (value-case arg :group)
  :returns (result value-resultp)
  :short "Leo group negation operation."
  (b* ((x (value-group->get arg))
       ((unless (curve-subgroupp x curve))
        (reserrf (list :input-not-in-subgroup x)))
       ((mv okp -x) (curve-subgroup-neg x curve))
       ((unless okp)
        (reserrf (list :output-not-in-subgroup -x))))
    (value-group -x))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-group-double ((arg valuep) (curve curvep))
  :guard (value-case arg :group)
  :returns (result value-resultp)
  :short "Leo group point doubling operation."
  (b* ((x (value-group->get arg))
       ((unless (curve-subgroupp x curve))
        (reserrf (list :input-not-in-subgroup x)))
       ((mv okp x+x) (curve-subgroup-add x x curve))
       ((unless okp)
        (reserrf (list :output-not-in-subgroup x+x))))
    (value-group x+x))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-group-add ((left valuep) (right valuep) (curve curvep))
  :guard (and (value-case left :group)
              (value-case right :group))
  :returns (result value-resultp)
  :short "Leo group addition operation."
  (b* ((x (value-group->get left))
       (y (value-group->get right))
       ((unless (curve-subgroupp x curve))
        (reserrf (list :input-not-in-subgroup x)))
       ((unless (curve-subgroupp y curve))
        (reserrf (list :input-not-in-subgroup y)))
       ((mv okp x+y) (curve-subgroup-add x y curve))
       ((unless okp)
        (reserrf (list :output-not-in-subgroup x+y))))
    (value-group x+y))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-group-sub ((left valuep) (right valuep) (curve curvep))
  :guard (and (value-case left :group)
              (value-case right :group))
  :returns (result value-resultp)
  :short "Leo group addition operation."
  (b* ((x (value-group->get left))
       (y (value-group->get right))
       ((unless (curve-subgroupp x curve))
        (reserrf (list :input-not-in-subgroup x)))
       ((unless (curve-subgroupp y curve))
        (reserrf (list :input-not-in-subgroup y)))
       ((mv okp -y) (curve-subgroup-neg y curve))
       ((unless okp)
        (reserrf (list :intermediate-not-in-subgroup -y)))
       ((mv okp x-y) (curve-subgroup-add x -y curve))
       ((unless okp)
        (reserrf (list :output-not-in-subgroup x-y))))
    (value-group x-y))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-group-mul ((left/right valuep)
                      (right/left valuep)
                      (curve curvep))
  :guard (and (value-case left/right :scalar)
              (value-case right/left :group))
  :returns (result value-resultp)
  :short "Leo group scalar multiplication operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here one operand must be a group value
     and the other operand must be an scalar value.
     Thus, the inputs to this function are
     a scalar field value (either the left or the right operand)
     and a group element value (either the right or the left operand)."))
  (b* ((k (value-scalar->get left/right))
       (x (value-group->get right/left))
       ((unless (< k (curve-scalar-prime curve)))
        (reserrf (list :input-not-in-scalar-field k)))
       ((unless (curve-subgroupp x curve))
        (reserrf (list :input-not-in-subgroup x)))
       ((mv okp k*x) (curve-subgroup-mul k x curve))
       ((unless okp)
        (reserrf (list :output-not-in-subgroup k*x))))
    (value-group k*x))
  :hooks (:fix))
