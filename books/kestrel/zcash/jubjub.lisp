; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "bit-byte-integer-conversions")

(include-book "kestrel/crypto/ecurve/jubjub" :dir :system)
(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jubjub
  :parents (zcash)
  :short "A formalization of Zcash's Jubjub elliptic curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "This curve is defined in our elliptice curve library
     at @('[books]/kestrel/crypto/ecurve'); @(see ecurve::jubjub).
     We may move that material here at some point.
     In any case, we provide some additional material here.
     We also introduce theorems about the prime and coefficients,
     and we disable all of them, including executable counterparts:
     the reason is that we want to treat them
     as algebraic quantities in the proofs,
     avoiding their combination in prime field expressions
     that are carried out by the prime field library's rules."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection jubjub-a-d-q
  :short "Theorems about Jubjub's
          @($a_\\mathbb{J}$), @($d_\\mathbb{J}$), and  @($q_\\mathbb{J}$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These three constants are defined in [ZPS:5.4.8.3].")
   (xdoc::p
    "These nullary functions are defined in the elliptic curve library.
     Here we prove some relevant theorems about them
     and we disable them completely (including executable counterparts)."))

  (defrule primep-of-jubjub-q
    (rtl::primep (jubjub-q)))

  (defrule fep-of-jubjub-a
    (fep (jubjub-a) (jubjub-q)))

  (defrule fep-of-jubjub-d
    (fep (jubjub-d) (jubjub-q)))

  (defrule jubjub-a-d-different
    (not (equal (jubjub-a) (jubjub-d))))

  (defrule jubjub-a-not-zero
    (not (equal (jubjub-a) 0)))

  (defrule jubjub-d-not-zero
    (not (equal (jubjub-d) 0)))

  (defrule jubjub-q-not-two
    (not (equal (jubjub-q) 2)))

  (in-theory (disable jubjub-q
                      (:e jubjub-q)
                      (:e jubjub-a)
                      (:e jubjub-d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize elements of @($\\mathbb{J}$) [ZPS:5.4.8.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the points on the Jubjub curve.")
   (xdoc::p
    "These are all finite points."))
  (and (ecurve::pointp x)
       (ecurve::point-on-twisted-edwards-p x (jubjub-curve)))
  ///
  (defruled point-finite-when-jubjub-pointp
    (implies (jubjub-pointp x)
             (equal (ecurve::point-kind x) :finite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-jubjub-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize Jubjub points and @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are optional Jubjub points.
     Useful, for instance, as results of functions that may return
     either Jubjub points or an error value."))
  (or (jubjub-pointp x)
      (eq x nil))
  ///
  (defrule maybe-jubjub-pointp-when-jubjub-pointp
    (implies (jubjub-pointp x)
             (maybe-jubjub-pointp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-point->u ((point jubjub-pointp))
  :returns (u natp :rule-classes :type-prescription)
  :short "The function @($\\mathcal{U}$) in [ZPS:5.4.8.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "[ZPS] defines this function on any finite point (in fact, on any pair),
     but it is only used on Jubjub points.")
   (xdoc::p
    "This is always below the Jubjub field prime."))
  (ecurve::point-finite->x point)
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp)))
  ///
  (defret jubjub-point->u-upper-bound
    (< u (jubjub-q))
    :hyp (jubjub-pointp point)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable jubjub-pointp
                                       ecurve::point-on-twisted-edwards-p
                                       jubjub-curve)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-point->v ((point jubjub-pointp))
  :returns (v natp :rule-classes :type-prescription)
  :short "The function @($\\mathcal{V}$) in [ZPS:5.4.8.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "[ZPS] defines this function on any finite point (in fact, on any pair),
     but it is only used on Jubjub points.")
   (xdoc::p
    "This is always below the Jubjub field prime."))
  (ecurve::point-finite->y point)
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp)))
  ///
  (defret jubjub-point->v-upper-bound
    (< v (jubjub-q))
    :hyp (jubjub-pointp point)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable jubjub-pointp
                                       ecurve::point-on-twisted-edwards-p
                                       jubjub-curve)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-mul ((scalar integerp) (point jubjub-pointp))
  :returns (point1 jubjub-pointp
                   :hyp (jubjub-pointp point)
                   :hints (("Goal" :in-theory (enable jubjub-pointp))))
  :short "Scalar multiplication [ZPS:4.1.8], on Jubjub."
  (ecurve::twisted-edwards-mul scalar point (jubjub-curve))
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-add ((point1 jubjub-pointp) (point2 jubjub-pointp))
  :returns (point jubjub-pointp
                  :hyp (and (jubjub-pointp point1) (jubjub-pointp point2))
                  :hints (("Goal" :in-theory (enable jubjub-pointp))))
  :short "Group addition [ZPS:4.1.8], on Jubjub."
  (ecurve::twisted-edwards-add point1 point2 (jubjub-curve))
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *jubjub-l*
  :short "The constant @($\\ell_\\mathbb{J}$) [ZPS:5.4.8.3]."
  256)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-abst ((bits bit-listp))
  :guard (= (len bits) *jubjub-l*)
  :returns (point? maybe-jubjub-pointp
                   :hints (("Goal"
                            :in-theory (enable returns-lemma
                                               ecurve::pfield-squarep))))
  :short "The function @($\\mathsf{abst}_\\mathbb{J}$) [ZPS:5.4.8.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The definition in [ZPS] takes a square root @($u$) at some point,
     which may or may not exist; if it does, it is not exactly specified.
     So we use @(tsee ecurve::pfield-squarep) and @('pfield-square->root').
     It should be the case that the definition
     does not depend on the exact square root chosen;
     we should prove that eventually.")
   (xdoc::p
    "Note that, when @($u = 0$) and @($\\tilde{u} = 1$)
     (which happens, for instance, when the input bit sequence is
     @('(1 0 ... 0 1)'), i.e. 254 zeros surrounded by ones),
     the prescribed result is @($(q_\\mathbb{J}, 1)$) in [ZPS].
     However, we need to reduce that modulo @($q_\\mathbb{J}$),
     in order for it to be a field element in our model.
     For simplicity, we do the reduction in all cases,
     which always coerces an integer to the corresponding field element;
     we do that via the field negation operation, to ease proofs.")
   (xdoc::p
    "To prove that this returns an optional Jubjub point,
     we locally prove a key lemma, @('returns-lemma').
     It says that, when the square of @($u$) is
     the argument of the square root as used in the definition,
     @($(u,v)$) is on the curve:
     this is easily proved by simple algebraic manipulations,
     which turn the equality of the square into the curve equation."))
  (b* ((q (jubjub-q))
       (a (jubjub-a))
       (d (jubjub-d))
       (v* (butlast bits 1))
       (u~ (car (last bits)))
       (v (lebs2ip v*))
       ((when (>= v q)) nil)
       (a-d.v^2 (sub a (mul d (mul v v q) q) q))
       ((when (equal a-d.v^2 0)) nil)
       (u^2 (div (sub 1 (mul v v q) q)
                 a-d.v^2
                 q))
       ((unless (ecurve::pfield-squarep u^2 q)) nil)
       (u (ecurve::pfield-square->root u^2 q)))
    (if (= (mod u 2) u~)
        (ecurve::point-finite u v)
      (ecurve::point-finite (neg u q) v)))

  :prepwork

  ((local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

   (defruledl returns-lemma
     (b* ((q (jubjub-q))
          (a (jubjub-a))
          (d (jubjub-d)))
       (implies (and (fep u q)
                     (fep v q)
                     (not (equal (sub a (mul d (mul v v q) q) q) 0))
                     (equal (mul u u q)
                            (div (sub 1 (mul v v q) q)
                                 (sub a (mul d (mul v v q) q) q)
                                 q)))
                (jubjub-pointp (ecurve::point-finite u v))))
     :use (step1 step2)

     :prep-lemmas

     ((defrule step1
        (b* ((q (jubjub-q))
             (a (jubjub-a))
             (d (jubjub-d)))
          (implies (and (fep u q)
                        (fep v q)
                        (not (equal (sub a (mul d (mul v v q) q) q) 0))
                        (equal (mul u u q)
                               (div (sub 1 (mul v v q) q)
                                    (sub a (mul d (mul v v q) q) q)
                                    q)))
                   (equal (mul (mul u u q)
                               (sub a (mul d (mul v v q) q) q)
                               q)
                          (sub 1 (mul v v q) q))))
        :enable div
        :disable ((:rewrite pfield::mul-of-add-arg1)
                  (:rewrite pfield::mul-of-add-arg2)
                  (:rewrite pfield::mul-associative)))

      (defrule step2
        (b* ((q (jubjub-q))
             (a (jubjub-a))
             (d (jubjub-d)))
          (implies (and (fep u q)
                        (fep v q)
                        (equal (mul (mul u u q)
                                    (sub a (mul d (mul v v q) q) q)
                                    q)
                               (sub 1 (mul v v q) q)))
                   (jubjub-pointp (ecurve::point-finite u v))))
        :enable (jubjub-pointp
                 ecurve::point-on-twisted-edwards-p
                 jubjub-curve)
        :prep-books
        ((include-book "kestrel/prime-fields/bind-free-rules" :dir :system))))))

  :verify-guards nil ; done below

  ///

  (local (include-book "std/lists/len" :dir :system))
  (local (include-book "std/lists/last" :dir :system))
  (local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))

  (defrulel verify-guards-lemma
    (implies (bitp x)
             (acl2-numberp x)))

  (verify-guards jubjub-abst
    :hints (("Goal" :in-theory (e/d (ecurve::pfield-squarep)
                                    (bitp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-h ()
  :returns (h natp)
  :short "The constant @($h_\\mathbb{J}$) in [ZPS:5.4.8.3]."
  8)
