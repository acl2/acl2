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

(include-book "kestrel/prime-fields/prime-fields" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ scalar-field-arithmetic-operations
  :parents (arithmetic-operations)
  :short "Leo scalar field arithmetic operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently the only operations supported are addition between scalars
     and multiplication of a group value by a scalar.
     Multiplication of a group value by a scalar is defined in
     @(see group-arithmetic-operations).")
   (xdoc::p
    "Since scalars are field elements of the scalar field,
     it could make sense in the future to support operations on scalars
     similar to those supported on base @('field') values.
     On the other hand, these might be expensive to realize in R1CS,
     and thus not worth the trouble,
     since the main purpose of the scalar field is
     for scalar group multiplication.")
   (xdoc::p
    "These ACL2 functions are defined over scalar element values,
     which in general may not be below the prime.
     It should be an invariant (to be formally proved eventually)
     that, given a prime number used in Leo computation steps,
     Leo computation states will have field element values below the prime.
     The ACL2 functions defined below defensively check that this is the case,
     returning an indication of error if not."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Not yet supported in Leo
(define op-scalar-neg ((arg valuep) (curve curvep))
  :guard (value-case arg :scalar)
  :returns (result value-resultp)
  :short "Leo scalar field value negation operation."
  (b* ((r (curve-scalar-prime curve))
       (x (value-scalar->get arg))
       ((unless (pfield::fep x r))
        (reserrf (list :op-scalar-neg (value-fix arg) r))))
    (value-scalar (pfield::neg x r)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-scalar-add ((left valuep) (right valuep) (curve curvep))
  :guard (and (value-case left :scalar)
              (value-case right :scalar))
  :returns (result value-resultp)
  :short "Leo scalar field value addition operation."
  (b* ((r (curve-scalar-prime curve))
       (err (list :op-scalar-add (value-fix left) (value-fix right)))
       (x (value-scalar->get left))
       (y (value-scalar->get right))
       ((unless (pfield::fep x r)) (reserrf err))
       ((unless (pfield::fep y r)) (reserrf err)))
    (value-scalar (pfield::add x y r)))
  :hooks (:fix))
