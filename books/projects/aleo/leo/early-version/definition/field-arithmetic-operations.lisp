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
(include-book "kestrel/number-theory/tonelli-shanks" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field-arithmetic-operations
  :parents (arithmetic-operations)
  :short "Leo field arithmetic operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are negation (unary), doubling (unary), inverse (unary), square (unary),
     addition, subtraction, multiplication, division, and exponentiation
     (all binary).")
   (xdoc::p
    "These ACL2 functions are defined over values of the
     <see topic='@(url leo-early::value)'><tt>value-field</tt> type</see>
     @('value-field') type. These values contain natural numbers that
     are not guaranteed to be below the prime returned by
     @('(curve-base-prime curve)').
     It should be an invariant (to be formally proved eventually)
     that, given a prime number used in Leo computation steps,
     Leo computation states will have field element values below the prime.
     The ACL2 functions defined below defensively check that this is the case,
     returning an indication of error if not."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-neg ((arg valuep) (curve curvep))
  :guard (value-case arg :field)
  :returns (result value-resultp)
  :short "Leo field negation operation."
  (b* ((p (curve-base-prime curve))
       (x (value-field->get arg))
       ((unless (pfield::fep x p))
        (reserrf (list :op-field-neg (value-fix arg) p))))
    (value-field (pfield::neg x p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-double ((arg valuep) (curve curvep))
  :guard (value-case arg :field)
  :returns (result value-resultp)
  :short "Leo field double operation."
  (b* ((p (curve-base-prime curve))
       (x (value-field->get arg))
       ((unless (pfield::fep x p))
        (reserrf (list :op-field-double (value-fix arg) p))))
    (value-field (pfield::add x x p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-add ((left valuep) (right valuep) (curve curvep))
  :guard (and (value-case left :field)
              (value-case right :field))
  :returns (result value-resultp)
  :short "Leo field addition operation."
  (b* ((err (list :op-field-add (value-fix left) (value-fix right)))
       (p (curve-base-prime curve))
       (x (value-field->get left))
       (y (value-field->get right))
       ((unless (pfield::fep x p)) (reserrf err))
       ((unless (pfield::fep y p)) (reserrf err)))
    (value-field (pfield::add x y p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-sub ((left valuep) (right valuep) (curve curvep))
  :guard (and (value-case left :field)
              (value-case right :field))
  :returns (result value-resultp)
  :short "Leo field subtraction operation."
  (b* ((err (list :op-field-sub (value-fix left) (value-fix right)))
       (p (curve-base-prime curve))
       (x (value-field->get left))
       (y (value-field->get right))
       ((unless (pfield::fep x p)) (reserrf err))
       ((unless (pfield::fep y p)) (reserrf err)))
    (value-field (pfield::sub x y p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-mul ((left valuep) (right valuep) (curve curvep))
  :guard (and (value-case left :field)
              (value-case right :field))
  :returns (result value-resultp)
  :short "Leo field multiplication operation."
  (b* ((err (list :op-field-mul (value-fix left) (value-fix right)))
       (p (curve-base-prime curve))
       (x (value-field->get left))
       (y (value-field->get right))
       ((unless (pfield::fep x p)) (reserrf err))
       ((unless (pfield::fep y p)) (reserrf err)))
    (value-field (pfield::mul x y p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-div ((left valuep) (right valuep) (curve curvep))
  :guard (and (value-case left :field)
              (value-case right :field))
  :returns (result value-resultp)
  :short "Leo field division operation."
  (b* ((err (list :op-field-div (value-fix left) (value-fix right)))
       (p (curve-base-prime curve))
       (x (value-field->get left))
       (y (value-field->get right))
       ((unless (pfield::fep x p)) (reserrf err))
       ((unless (pfield::fep y p)) (reserrf err))
       ((when (= y 0)) (reserrf err)))
    (value-field (pfield::div x y p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-inv ((arg valuep) (curve curvep))
  :guard (value-case arg :field)
  :returns (result value-resultp)
  :short "Leo field inverse (reciprocal) operation."
  (b* ((err (list :op-field-inv (value-fix arg)))
       (p (curve-base-prime curve))
       (x (value-field->get arg))
       ((unless (pfield::fep x p)) (reserrf err))
       ((when (= x 0)) (reserrf err)))
    (value-field (pfield::div 1 x p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-square ((arg valuep) (curve curvep))
  :guard (value-case arg :field)
  :returns (result value-resultp)
  :short "Leo field squaring operation."
  (b* ((err (list :op-field-square (value-fix arg)))
       (p (curve-base-prime curve))
       (x (value-field->get arg))
       ((unless (pfield::fep x p)) (reserrf err)))
    (value-field (pfield::mul x x p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-square-root ((arg valuep) (curve curvep))
  :guard (value-case arg :field)
  :returns (result value-resultp)
  :short "Leo field square-root operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the argument has a modular square root in the field,
     then the larger of the square roots is returned.
     Returns zero if the argument is a quadradic non-residue."))
  (b* ((err (list :op-field-square-root (value-fix arg)))
       (p (curve-base-prime curve))
       (x (value-field->get arg))
       ((unless (pfield::fep x p)) (reserrf err))
       ;; This 11 is a quadratic nonresidue seed for the base field
       ;; of :edwards-bls-12 and should be part of the 'curve' value.
       ;; For now we have to call the guard separately.
       ((when (or (<= p 11) (primes::has-square-root? 11 p)))
        (reserrf err))
       (sqrt (primes::tonelli-shanks-greater-sqrt x p 11))
       ;;This next check should also be removed
       ((unless (pfield::fep sqrt p))
        (reserrf err)))
    (value-field sqrt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-field-pow ((left valuep) (right valuep) (curve curvep))
  :guard (and (value-case left :field)
              (value-case right :field))
  :returns (result value-resultp)
  :short "Leo field exponentiation operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here the left operand must be a field element value,
     while the right operand must be an integer.
     If the exponent is non-negative, the result is always well defined.
     If the exponent is negative, the base must not be zero;
     the result is the inverse of the positive power."))
  (b* ((err (list :op-field-pow (value-fix left) (value-fix right)))
       (p (curve-base-prime curve))
       (x (value-field->get left))
       ((unless (pfield::fep x p)) (reserrf err))
       (y (value-field->get right))
       ((unless (pfield::fep y p)) (reserrf err)))
    (value-field (pfield::pow x y p)))
  ///
  (fty::deffixequiv op-field-pow
    :args ((left valuep) (right valuep))))
