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

(include-book "integer-arithmetic-operations")
(include-book "field-arithmetic-operations")
(include-book "group-arithmetic-operations")
(include-book "scalar-arithmetic-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ arithmetic-operations
  :parents (dynamic-semantics)
  :short "Leo arithmetic operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These operate on integers, field elements, and group elements.
     But not every operator operates on all these types of values.")
   (xdoc::p
    "Since field operations depends on a prime number
     and group operations depend on an elliptic curve.
     The `curve` argument in the following functions is a unit type
     that is used to look up the prime and elliptic curve;
     see @(see curve-parameterization).")
   (xdoc::p
    "For an operation that comes in non-wrapped and @('-wrapped') forms,
     the non-wrapped form can get an error due to an overflow
     but the wrapped form will not.  The exact handling of overflow
     values depends on the operation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-neg ((arg valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo negation operation."
  (cond ((int-valuep arg) (op-int-neg arg))
        ((value-case arg :field) (op-field-neg arg curve))
        ((value-case arg :group) (op-group-neg arg curve))
        (t (reserrf (list :op-neg (value-fix arg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-abs ((arg valuep))
  :returns (result value-resultp)
  :short "Leo absolute value operation."
  (b* (((unless (member-eq (value-kind arg) '(:i8 :i16 :i32 :i64 :i128)))
        (reserrf (list :op-abs (value-fix arg)))))
     (op-int-abs arg))
  :guard-hints (("Goal" :in-theory (enable int-valuep))))

(define op-abs-wrapped ((arg valuep))
  :returns (result value-resultp)
  :short "Leo wrapped absolute value operation."
  (b* (((unless (member-eq (value-kind arg) '(:i8 :i16 :i32 :i64 :i128)))
        (reserrf (list :op-abs-wrapped (value-fix arg)))))
     (op-int-abs-wrapped arg))
  :guard-hints (("Goal" :in-theory (enable int-valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-double ((arg valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo double operation."
  (cond ((value-case arg :field) (op-field-double arg curve))
        ((value-case arg :group) (op-group-double arg curve))
        (t (reserrf (list :op-double (value-fix arg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-add ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo addition operation."
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-add left right))
        ((and (value-case left :field) (value-case right :field))
         (op-field-add left right curve))
        ((and (value-case left :group) (value-case right :group))
         (op-group-add left right curve))
        ((and (value-case left :scalar) (value-case right :scalar))
         (op-scalar-add left right curve))
        (t (reserrf
            (list :op-add (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-add-wrapped ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo wrapping addition operation."
  (declare (ignorable curve))
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-add-wrapped left right))
        (t (reserrf
            (list :op-add-wrapped (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-sub ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo subtraction operation."
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-sub left right))
        ((and (value-case left :field) (value-case right :field))
         (op-field-sub left right curve))
        ((and (value-case left :group) (value-case right :group))
         (op-group-sub left right curve))
        (t (reserrf
            (list :op-sub (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-sub-wrapped ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo wrapping subtraction operation."
  (declare (ignorable curve))
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-sub-wrapped left right))
        (t (reserrf
            (list :op-sub-wrapped (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-mul ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo multiplication operation."
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-mul left right))
        ((and (value-case left :field) (value-case right :field))
         (op-field-mul left right curve))
        ((and (value-case left :scalar) (value-case right :group))
         (op-group-mul left right curve))
        ((and (value-case left :group) (value-case right :scalar))
         (op-group-mul right left curve))
        (t (reserrf
            (list :op-mul (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-mul-wrapped ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo wrapping multiplication operation."
  (declare (ignorable curve))
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-mul-wrapped left right))
        (t (reserrf
            (list :op-mul-wrapped (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-div ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo division operation."
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-div left right))
        ((and (value-case left :field) (value-case right :field))
         (op-field-div left right curve))
        (t (reserrf
            (list :op-div (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-div-wrapped ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo wrapping division operation."
  (declare (ignorable curve))
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-div-wrapped left right))
        (t (reserrf
            (list :op-div-wrapped (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-rem ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo remainder operation."
  (declare (ignorable curve))
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-rem left right))
        (t (reserrf
            (list :op-rem (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-rem-wrapped ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo wrapping remainder operation."
  (declare (ignorable curve))
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-rem-wrapped left right))
        (t (reserrf
            (list :op-rem-wrapped (value-fix left) (value-fix right))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-inv ((arg valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo inverse (reciprocal) operation."
  (cond ((value-case arg :field)
         (op-field-inv arg curve))
        (t (reserrf
            (list :op-inv (value-fix arg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-square ((arg valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo squaring operation."
  (cond ((value-case arg :field)
         (op-field-square arg curve))
        (t (reserrf
            (list :op-square (value-fix arg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-square-root ((arg valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo square root operation."
  (cond ((value-case arg :field)
         (op-field-square-root arg curve))
        (t (reserrf
            (list :op-square (value-fix arg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-pow ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo exponentiation operation."
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-pow left right))
        ((and (value-case left :field) (value-case right :field))
         (op-field-pow left right curve))
        (t (reserrf
            (list :op-pow (value-fix left) (value-fix right))))))

(define op-pow-wrapped ((left valuep) (right valuep) (curve curvep))
  :returns (result value-resultp)
  :short "Leo wrapping exponentiation operation."
  (declare (ignorable curve))
  (cond ((and (int-valuep left) (int-valuep right))
         (op-int-pow-wrapped left right))
        (t (reserrf
            (list :op-pow-wrapped (value-fix left) (value-fix right))))))
