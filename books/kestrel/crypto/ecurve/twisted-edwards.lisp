; Elliptic Curve Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "prime-field-squares")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/crypto/ecurve/points-fty" :dir :system)
(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ twisted-edwards
  :parents (elliptic-curves)
  :short "Elliptic curves over prime fields in twisted Edwards form."
  :long
  (xdoc::topstring
   (xdoc::p
    "Twisted Edwards curves are introduced in "
    (xdoc::ahref
     "https://eprint.iacr.org/2008/013.pdf"
     "Bernstein, Birkner, Joye, Lange, and Peters's ``Twisted Edwards Curves''")
    (xdoc::ahref "https://eprint.iacr.org/2008/013.pdf" "this paper")
    ".")
   (xdoc::p
    "Their definition is the following:")
   (xdoc::blockquote
    (xdoc::p
     "<b>Definition 2.1. (Twisted Edwards curve).</b>
      Fix a field @($k$) with @($\\mathrm{char}(k) \\neq 2$).
      Fix distinct nonzero elements @($a, d \\in k$).
      The twisted Edwards curve with coefficients @($a$) and @($d$) is
      the curve")
    (xdoc::@[]
     "\\mathrm{E}_{\\mathrm{E},a,d} : a x^2 + y^2 = 1 + d x^2 y^2")
    (xdoc::p
     "An Edwards curve is a twisted Edwards curve with @($a = 1$)."))
   (xdoc::p
    "Since, as noted above,
     Edwards curves are a special case of twisted Edwards curves,
     our formalization of twisted Edwards curves also covers Edwards curves,
     at least for some purposes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod twisted-edwards-curve
  :short "Fixtype of elliptic curves over prime fields in twisted Edwards form."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of curve is specified by
     the prime @($p$) and the coefficients @($a$) and @($d$);
     see @(see twisted-edwards).
     Thus, we formalize a curve as a triple of these numbers,
     via a fixtype product.")
   (xdoc::p
    "We require @($p$) to be a prime greater than 2;
     see @(see twisted-edwards).")
   (xdoc::p
    "We require @($a$) and @($d$) to be in the prime field of @($p$).
     We also require them to be distinct and non-zero.")
   (xdoc::p
    "To fix the three components to satisfy the requirements above,
     we pick 3 for @($p$), 1 for @($a$), and 2 for @($d$)."))
  ((p nat :reqfix (if (and (rtl::primep p)
                           (> p 2))
                      p
                    3))
   (a :reqfix (if (and (rtl::primep p)
                       (> p 2)
                       (fep a p)
                       (fep d p)
                       (not (equal a d))
                       (not (equal a 0))
                       (not (equal d 0)))
                  a
                1))
   (d :reqfix (if (and (rtl::primep p)
                       (> p 2)
                       (fep a p)
                       (fep d p)
                       (not (equal a d))
                       (not (equal a 0))
                       (not (equal d 0)))
                  d
                2)))
  :require (and (rtl::primep p)
                (> p 2)
                (fep a p)
                (fep d p)
                (not (equal a d))
                (not (equal a 0))
                (not (equal d 0)))
  :pred twisted-edwards-curvep

  ///

  (defrule posp-of-twisted-edwards-curve->p
    (posp (twisted-edwards-curve->p curve))
    :rule-classes :type-prescription)

  (defrule twisted-edwards-curve->p-lower-bound
    (> (twisted-edwards-curve->p curve) 2)
    :rule-classes :linear)

  (defrule posp-of-twisted-edwards-curve->a
    (posp (twisted-edwards-curve->a curve))
    :rule-classes :type-prescription
    :enable twisted-edwards-curve->a)

  (defrule posp-of-twisted-edwards-curve->d
    (posp (twisted-edwards-curve->d curve))
    :rule-classes :type-prescription
    :enable twisted-edwards-curve->d))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edwards-curve-completep ((curve twisted-edwards-curvep))
  :returns (yes/no booleanp)
  :short "Check if a twisted Edwards curve is complete."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the paper on twisted Edwards curves
     referenced in @(see twisted-edwards),
     this is the case when @($a$) is a square and @($d$) is a non-square.
     Completeness means that the addition formula
     (see @(tsee twisted-edwards-add))
     works for every pair of point on the curve.
     In particular, the denominators of the coordinates of the sum
     are both always different from 0 when the curve is complete."))
  (and (pfield-squarep (twisted-edwards-curve->a curve)
                       (twisted-edwards-curve->p curve))
       (not (pfield-squarep (twisted-edwards-curve->d curve)
                            (twisted-edwards-curve->p curve))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-on-twisted-edwards-p ((point pointp)
                                    (curve twisted-edwards-curvep))
  :returns (yes/no booleanp)
  :short "Check if a point is on a twisted Edwards curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The primality requirement in the guard of this function
     is not strictly needed to define this function,
     but in general we should only deal with well-formed curves.
     In particular, curves whose @($p$) is prime.")
   (xdoc::p
    "A point @($(x, y)$) is on the curve if and only if
     its components satisfy the curve equation.
     We require its components to be below the prime,
     i.e. that the point is in the cartesian product of the prime field.
     The point at infinity is not part of a twisted Edwards curve;
     only finite points are."))
  (b* ((p (twisted-edwards-curve->p curve))
       (a (twisted-edwards-curve->a curve))
       (d (twisted-edwards-curve->d curve))
       ((when (eq (point-kind point) :infinite)) nil)
       (x (point-finite->x point))
       (y (point-finite->y point))
       ((unless (< x p)) nil)
       ((unless (< y p)) nil)
       (x^2 (mul x x p))
       (y^2 (mul y y p))
       (x^2.y^2 (mul x^2 y^2 p))
       (a.x^2 (mul a x^2 p))
       (a.x^2+y^2 (add a.x^2 y^2 p))
       (1+d.x^2.y^2 (add 1 (mul d x^2.y^2 p) p)))
    (equal a.x^2+y^2 1+d.x^2.y^2))
  :guard-hints (("Goal" :in-theory (enable fep)))
  :hooks (:fix)
  ///

  (defrule point-on-twisted-edwards-is-finite
    (implies (point-on-twisted-edwards-p point curve)
             (equal (point-kind point) :finite))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule twisted-edwards-only-points-with-x-0-or-y-1
  :short "Theorem about the only points with zero abscissa or unit ordinate
          on twisted Edwards curves."
  :long
  (xdoc::topstring
   (xdoc::p
    "The points @($(0,1)$) and @($(0,-1)$) are the only ones
     with @($x = 0$) or @($y = 1$).
     The proof is fairly simple:
     substituting @($x = 0$) or @($y = 1$) in the curve equation
     gives a simplified equation
     from which the other coordinate is determined.")
   (xdoc::p
    "This theorem has some significance, in particular, for the "
    (xdoc::seetopic "birational-montgomery-twisted-edwards"
                    "birational equivalence between
                     Montgomery and twisted Edwards curves")
    ": points with @($x = 0$ or @($y = 0$) on a twisted Edwards curve
     are not amenable to the rational mapping,
     because they make a denominator zero;
     thus, they have to be treated specially for the mapping.
     This theorem tells us that there are just two such points."))
  (b* ((p (twisted-edwards-curve->p curve))
       (x (point-finite->x point))
       (y (point-finite->y point)))
    (implies (or (equal x 0)
                 (equal y 1))
             (implies (point-on-twisted-edwards-p point curve)
                      (or (equal point (point-finite 0 1))
                          (equal point (point-finite 0 (neg 1 p)))))))
  :enable (point-on-twisted-edwards-p
           point-finite
           point-finite->x
           point-finite->y
           point-fix
           pointp)
  :use (lemma1 lemma2)

  :prep-books
  ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

  :prep-lemmas

  ((defrule lemma1 ; x = 0 ==> y in {+1, -1}
     (b* ((p (twisted-edwards-curve->p curve))
          (x (point-finite->x point))
          (y (point-finite->y point)))
       (implies (and (point-on-twisted-edwards-p point curve)
                     (equal x 0))
                (or (equal y 1)
                    (equal y (neg 1 p)))))
     :rule-classes nil
     :enable (point-on-twisted-edwards-p)
     :prep-books
     ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
      (include-book "prime-field-extra-rules")))

   (defrule lemma2 ; y = 1 ==> x = 0
     (b* ((x (point-finite->x point))
          (y (point-finite->y point)))
       (implies (and (point-on-twisted-edwards-p point curve)
                     (equal y 1))
                (equal x 0)))
     :rule-classes nil
     :enable point-on-twisted-edwards-p
     :prep-books
     ((include-book "kestrel/prime-fields/bind-free-rules" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edwards-add ((point1 pointp)
                             (point2 pointp)
                             (curve twisted-edwards-curvep))
  :guard (and (twisted-edwards-curve-completep curve)
              (point-on-twisted-edwards-p point1 curve)
              (point-on-twisted-edwards-p point2 curve))
  :returns (point3 pointp)
  :short "Group addition on a twisted Edwards curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "We require, in the guard, the curve to be complete.
     Otherwise, this definition does not work in all cases;
     in particular, the guards could not be verified,
     due to the possibility that the denominators are 0.")
   (xdoc::p
    "We also require, in the guard, both points to be on the curve.
     Indeed, the group addition operation is only defined
     on points on the curve, not on any points.")
   (xdoc::p
    "The points on the curve are always finite,
     and the result is also a finite point.
     Its coordinates are calculated as shown
     in the paper referenced in @(see twisted-edwards).")
   (xdoc::p
    "We verify the guards from lemmas from the closure proof,
     which involves proving that the denominators are not 0.
     The guard proof is explained in comments in this file."))
  (b* ((p (twisted-edwards-curve->p curve))
       (a (twisted-edwards-curve->a curve))
       (d (twisted-edwards-curve->d curve))
       ((unless (mbt (eq (point-kind point1) :finite))) (point-finite 0 0))
       ((unless (mbt (eq (point-kind point2) :finite))) (point-finite 0 0))
       (x1 (point-finite->x point1))
       (y1 (point-finite->y point1))
       (x2 (point-finite->x point2))
       (y2 (point-finite->y point2))
       (d.x1.x2.y1.y2 (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p))
       (x3-numerator (add (mul x1 y2 p) (mul y1 x2 p) p))
       (x3-denominator (add 1 d.x1.x2.y1.y2 p))
       (y3-numerator (sub (mul y1 y2 p) (mul a (mul x1 x2 p) p) p))
       (y3-denominator (sub 1 d.x1.x2.y1.y2 p))
       (x3 (div x3-numerator x3-denominator p))
       (y3 (div y3-numerator y3-denominator p)))
    (point-finite x3 y3))
  :guard-hints (("Goal" :in-theory (enable point-on-twisted-edwards-p fep)))
  :hooks (:fix)

  :verify-guards nil ; done below

  ///

  ;; The core of the closure proof is in the following included file.
  ;; For the guard proofs, we take the theorem gamma-not-root-of-unity
  ;; from that file, which says that gamma = d * x1 * x2 * y1 * y2
  ;; is not a root of 1.

  (local (include-book "twisted-edwards-closure-core"))

  ;; We can readily derive, from that theorem, that gamma is neither 1 nor -1.

  (defruledl gamma-not-one
    (implies (and (domain)
                  (not (=p a 0))
                  (non-square d)
                  (integerp sqrt{a})
                  (=p (sq sqrt{a}) a)
                  (ECp x1 y1 a c d)
                  (ECp x2 y2 a c d))
             (not (=p (gamma$) 1)))
    :use gamma-not-root-of-unity)

  (defruledl gamma-not-minus-one
    (implies (and (domain)
                  (not (=p a 0))
                  (non-square d)
                  (integerp sqrt{a})
                  (=p (sq sqrt{a}) a)
                  (ECp x1 y1 a c d)
                  (ECp x2 y2 a c d))
             (not (=p (gamma$) -1)))
    :use gamma-not-root-of-unity)

  ;; Since gamma is neither 1 nor -1, neither 1 + gamma nor 1 - gamma is 0.
  ;; That is, the denominators are not 0.
  ;; However, the two theorems above are expressed
  ;; in terms of the odd prime field library,
  ;; so we need to transfer them to the prime fields library
  ;; used in the definition of twisted-edwards-add.

  ;; First, for brevity, we introduce a function
  ;; that is the analogue of ECp,
  ;; but the following one uses the prime field operations instead,
  ;; and has no dependency on c.
  ;; The following function's body is copied from point-on-twisted-edwards-p.

  (local
   (defun oncurvep (x y a d p)
     (b* ((x^2 (mul x x p))
          (y^2 (mul y y p))
          (x^2.y^2 (mul x^2 y^2 p))
          (a.x^2 (mul a x^2 p))
          (a.x^2+y^2 (add a.x^2 y^2 p))
          (1+d.x^2.y^2 (add 1 (mul d x^2.y^2 p) p)))
       (equal a.x^2+y^2 1+d.x^2.y^2))))

  ;; While twisted-edwards-add uses pfield-squarep and its negation
  ;; (in the definition of twisted-edwards-curve-completep) for a and d,
  ;; the gamma theorems above use (not (non-square d))
  ;; and an explicit root sqrt{a} for a (saying that a is a square).
  ;; The following rewrite rule serves to bridge the two predicates.
  ;; Note that we use the constrained nullary function (prime)
  ;; from the odd prime field library,
  ;; because the gamma theorems above are based on that.
  ;; To prove the following equivalence,
  ;; we use the prime field introduction rules
  ;; (the ones that rephrase operations in the odd prime field library
  ;; to operations in the prime field library),
  ;; and also some prime field rules to iron out certain differences.

  (defruledl pfield-squarep-to-not-non-square
    (implies (fep x (prime))
             (iff (pfield-squarep x (prime))
                  (not (non-square x))))
    :enable (=p i* modp pfield-squarep)
    :use ((:instance non-square-necc
           (n (pfield-square->root x (prime))))
          (:instance pfield-squarep-suff
           (r (modp (non-square-witness x)))
           (p (prime))))
    :prep-books
    ((include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system)
     (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

  ;; The following two theorems are like the gamma theorems above,
  ;; except that they use operations from the prime field library,
  ;; including the oncurvep abbreviation introduced above.
  ;; The proofs use instances of the gamma theorems,
  ;; with c = 1 and with sqrt{a} replaced by the shorter b.
  ;; We enable some definitions and use the prime field introduction rules,
  ;; along with some additional prime field rules, and the equivalence above.
  ;; The names of the following two theorems convey that
  ;; they are over the constrained nullary (prime):
  ;; see the first hypothesis.

  (defruledl d.x1.x2.y1.y2-not-one-constrained-prime
    (implies (and (equal p (prime))
                  (fep a p)
                  (fep d p)
                  (fep x1 p)
                  (fep y1 p)
                  (fep x2 p)
                  (fep y2 p)
                  (not (equal a 0))
                  (not (equal d 0))
                  (not (pfield-squarep d p))
                  (fep b p)
                  (equal (mul b b p) a)
                  (oncurvep x1 y1 a d p)
                  (oncurvep x2 y2 a d p))
             (not (equal (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p)
                         1)))
    :use (:instance gamma-not-one (c 1) (sqrt{a} b))
    :enable (ECp LHS RHS gamma =p i* i+ modp pfield-squarep-to-not-non-square)
    :prep-books
    ((include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system)
     (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

  (defruledl d.x1.x2.y1.y2-not-minus-one-constrained-prime
    (implies (and (equal p (prime))
                  (fep a p)
                  (fep d p)
                  (fep x1 p)
                  (fep y1 p)
                  (fep x2 p)
                  (fep y2 p)
                  (not (equal a 0))
                  (not (equal d 0))
                  (not (pfield-squarep d p))
                  (fep b p)
                  (equal (mul b b p) a)
                  (oncurvep x1 y1 a d p)
                  (oncurvep x2 y2 a d p))
             (not (equal (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p)
                         (1- p))))
    :use (:instance gamma-not-minus-one (c 1) (sqrt{a} b))
    :enable (ECp LHS RHS gamma =p i* i+ modp pfield-squarep-to-not-non-square)
    :disable pfield::neg-when-constant-arg1 ; otherwise it loops
    :prep-books
    ((include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system)
     (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

  ;; We functionally instantiate (prime) with a generic p,
  ;; to obtain versions of the two theorems above
  ;; that are over a general prime p > 2.
  ;; The proof is straighforward, we just need to show that 3 is prime,
  ;; so that it is a valid instantiation of (prime) if p is not prime.
  ;; The names of the following two theorems convey that
  ;; they still have b as an explicit root of a.

  (defruledl d.x1.x2.y1.y2-not-one-explicit-root
    (implies (and (rtl::primep p)
                  (> p 2)
                  (fep a p)
                  (fep d p)
                  (fep x1 p)
                  (fep y1 p)
                  (fep x2 p)
                  (fep y2 p)
                  (not (equal a 0))
                  (not (equal d 0))
                  (not (pfield-squarep d p))
                  (fep b p)
                  (equal (mul b b p) a)
                  (oncurvep x1 y1 a d p)
                  (oncurvep x2 y2 a d p))
             (not (equal (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p)
                         1)))
    :use (:functional-instance d.x1.x2.y1.y2-not-one-constrained-prime
          (prime (lambda () (if (and (rtl::primep p) (> p 2)) p 3))))
    :prep-lemmas
    ((defrule primep-of-3
       (rtl::primep 3)
       :enable rtl::primep)))

  (defruledl d.x1.x2.y1.y2-not-minus-one-explicit-root
    (implies (and (rtl::primep p)
                  (> p 2)
                  (fep a p)
                  (fep d p)
                  (fep x1 p)
                  (fep y1 p)
                  (fep x2 p)
                  (fep y2 p)
                  (not (equal a 0))
                  (not (equal d 0))
                  (not (pfield-squarep d p))
                  (fep b p)
                  (equal (mul b b p) a)
                  (oncurvep x1 y1 a d p)
                  (oncurvep x2 y2 a d p))
             (not (equal (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p)
                         (1- p))))
    :use (:functional-instance d.x1.x2.y1.y2-not-minus-one-constrained-prime
          (prime (lambda () (if (and (rtl::primep p) (> p 2)) p 3))))
    :prep-lemmas
    ((defrule primep-of-3
       (rtl::primep 3)
       :enable rtl::primep)))

  ;; By instantiating b with the the witness square root of a,
  ;; we eliminate b and instead use (pfield-squarep a p) as hypothesis.
  ;; The proof is straightforward.
  ;; The names of the following two theorems convey that
  ;; they are over the individual components of the curve and points.

  (defruledl d.x1.x2.y1.y2-not-one-on-components
    (implies (and (rtl::primep p)
                  (fep a p)
                  (fep d p)
                  (fep x1 p)
                  (fep y1 p)
                  (fep x2 p)
                  (fep y2 p)
                  (not (equal a 0))
                  (not (equal d 0))
                  (pfield-squarep a p)
                  (not (pfield-squarep d p))
                  (oncurvep x1 y1 a d p)
                  (oncurvep x2 y2 a d p))
             (not (equal (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p)
                         1)))
    :use (:instance d.x1.x2.y1.y2-not-one-explicit-root
          (b (pfield-square->root a p)))
    :enable pfield-squarep)

  (defruledl d.x1.x2.y1.y2-not-minus-one-on-components
    (implies (and (rtl::primep p)
                  (fep a p)
                  (fep d p)
                  (fep x1 p)
                  (fep y1 p)
                  (fep x2 p)
                  (fep y2 p)
                  (not (equal a 0))
                  (not (equal d 0))
                  (pfield-squarep a p)
                  (not (pfield-squarep d p))
                  (oncurvep x1 y1 a d p)
                  (oncurvep x2 y2 a d p))
             (not (equal (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p)
                         (1- p))))
    :use (:instance d.x1.x2.y1.y2-not-minus-one-explicit-root
          (b (pfield-square->root a p)))
    :enable pfield-squarep)

  ;; Finally we rephrase the theorems on curves and points.
  ;; The hypotheses are replaced with conditions on them,
  ;; which imply the conditions on the components in the theorems above.
  ;; We also eliminate the use of oncurvep.

  (defruled d.x1.x2.y1.y2-not-one-on-curve-and-points
    (implies (and (twisted-edwards-curvep curve)
                  (twisted-edwards-curve-completep curve)
                  (point-on-twisted-edwards-p point1 curve)
                  (point-on-twisted-edwards-p point2 curve))
             (b* (((twisted-edwards-curve curve) curve)
                  (x1 (point-finite->x point1))
                  (y1 (point-finite->y point1))
                  (x2 (point-finite->x point2))
                  (y2 (point-finite->y point2)))
               (not (equal (mul curve.d
                                (mul x1
                                     (mul x2
                                          (mul y1
                                               y2 curve.p)
                                          curve.p)
                                     curve.p)
                                curve.p)
                           1))))
    :use (:instance d.x1.x2.y1.y2-not-one-on-components
          (p (twisted-edwards-curve->p curve))
          (a (twisted-edwards-curve->a curve))
          (d (twisted-edwards-curve->d curve))
          (x1 (point-finite->x point1))
          (y1 (point-finite->y point1))
          (x2 (point-finite->x point2))
          (y2 (point-finite->y point2)))
    :enable (twisted-edwards-curve-completep
             point-on-twisted-edwards-p
             fep))

  (defruled d.x1.x2.y1.y2-not-minus-one-on-curve-and-points
    (implies (and (twisted-edwards-curvep curve)
                  (twisted-edwards-curve-completep curve)
                  (point-on-twisted-edwards-p point1 curve)
                  (point-on-twisted-edwards-p point2 curve))
             (b* (((twisted-edwards-curve curve) curve)
                  (x1 (point-finite->x point1))
                  (y1 (point-finite->y point1))
                  (x2 (point-finite->x point2))
                  (y2 (point-finite->y point2)))
               (not (equal (mul curve.d
                                (mul x1
                                     (mul x2
                                          (mul y1
                                               y2 curve.p)
                                          curve.p)
                                     curve.p)
                                curve.p)
                           (1-  curve.p)))))
    :use (:instance d.x1.x2.y1.y2-not-minus-one-on-components
          (p (twisted-edwards-curve->p curve))
          (a (twisted-edwards-curve->a curve))
          (d (twisted-edwards-curve->d curve))
          (x1 (point-finite->x point1))
          (y1 (point-finite->y point1))
          (x2 (point-finite->x point2))
          (y2 (point-finite->y point2)))
    :enable (twisted-edwards-curve-completep
             point-on-twisted-edwards-p
             fep))

  ;; The two theorems above are the key ones
  ;; to verify the guards of twisted-edwards-add:
  ;; they say that d * x1 * x2 * y1 * y2 is neither 1 nor -1;
  ;; therefore, adding it to 1 or subtracting it from 1 never yields 0,
  ;; i.e. the denominators are never 0.
  ;; The actual guard obligation shows up as
  ;; the conclusions of the following two lemmas,
  ;; which backchain to the conclusions of the two theorems above.

  (defruledl verify-guards-lemma1
    (implies (and (rtl::primep p)
                  (fep x p)
                  (not (equal x (1- p))))
             (not (equal 0 (add 1 x p))))
    :prep-books
    ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
     (include-book "arithmetic-3/top" :dir :system)))

  (defruledl verify-guards-lemma2
    (implies (and (rtl::primep p)
                  (fep x p)
                  (not (equal x 1)))
             (not (equal 0 (add 1 (neg x p) p))))
    :prep-books
    ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
     (include-book "arithmetic-3/top" :dir :system)))

  ;; Finally we verify the guards.
  ;; We enable the two lemmas just above,
  ;; we use the key two theorems proved earlier,
  ;; and enable a few more functions.

  (verify-guards twisted-edwards-add
    :hints (("Goal"
             :in-theory (enable point-on-twisted-edwards-p
                                fep
                                verify-guards-lemma1
                                verify-guards-lemma2)
             :use (d.x1.x2.y1.y2-not-one-on-curve-and-points
                   d.x1.x2.y1.y2-not-minus-one-on-curve-and-points))))

  ;; It may be possible to shorten the above guard verification proof.
  ;; In particular, it may be possible to combine
  ;; the functional and non-functional instantiations used above
  ;; into fewer or even just one reformulation of the gamma theorems.
  ;; However, the current proof, with the explanations, is probably clearer.

  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection twisted-edwards-add-closure
  :short "Proof of closure of group addition on a twisted Edwards curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that adding two points on a curve
     always yields a point on the curve.
     That is, the group operation is closed.")
   (xdoc::p
    "The proof is explained in comments in this file."))

  ;; The closure proof is more complicated than it should be,
  ;; due how the proof, and the twisted Edwards curve library,
  ;; have been developed over time.
  ;; In particular, the fixtype for twisted Edwards curve,
  ;; and the functions point-on-twisted-edwards-p and twisted-edwards-add,
  ;; have been added in a second version of this library;
  ;; the first version contained different formulations of these two functions,
  ;; and the closure proof was carried out for those formulations.
  ;; For expediency, we locally introduce those old definitions,
  ;; and prove them equivalent (under suitable hypotheses),
  ;; to the new definitions given above.
  ;; This way, we can more easily adapt the existing closure proof.

  ;; This is the old version of point-on-twisted-edwards-p.
  ;; Note that the new version includes point-in-pxp-p,
  ;; which the old one does not.

  (local
   (defun point-on-curve-p (point p a d)
     (and (not (eq point :infinity))
          (let ((x (car point))
                (y (cdr point)))
            (and (< x p)
                 (< y p)
                 (let ((y^2 (mul y y p))
                       (x^2 (mul x x p)))
                   (let ((ax^2 (mul a x^2 p))
                         (x^2.y^2 (mul x^2 y^2 p)))
                     (let ((ax^2+y^2 (add ax^2 y^2 p))
                           (1+dx^2.y^2 (add 1 (mul d x^2.y^2 p) p)))
                       (equal ax^2+y^2 1+dx^2.y^2)))))))))

  (defruledl point-on-twisted-edwards-p-equivalence
    (implies (and (pointp point)
                  (twisted-edwards-curvep curve))
             (equal (point-on-twisted-edwards-p point curve)
                    (point-on-curve-p point
                                      (twisted-edwards-curve->p curve)
                                      (twisted-edwards-curve->a curve)
                                      (twisted-edwards-curve->d curve))))
    :enable (point-on-twisted-edwards-p
             point-in-pxp-p
             pointp
             point-kind
             point-finite->x
             point-finite->y))

  ;; This is the old version of twisted-edwards-add.

  (local
   (defun curve-add (pt1 pt2 p a d)
     (let ((y1 (cdr pt1))
           (y2 (cdr pt2))
           (x1 (car pt1))
           (x2 (car pt2)))
       (let ((dx1x2y1y2 (mul d (mul x1 (mul x2 (mul y1 y2 p) p) p) p)))
         (let ((x3-numerator (add (mul x1 y2 p) (mul y1 x2 p) p))
               (x3-denominator (add 1 dx1x2y1y2 p))
               (y3-numerator (sub (mul y1 y2 p) (mul a (mul x1 x2 p) p) p))
               (y3-denominator (sub 1 dx1x2y1y2 p)))
           (let ((x3 (div x3-numerator x3-denominator p))
                 (y3 (div y3-numerator y3-denominator p)))
             (cons x3 y3)))))))

  (defruledl twisted-edwards-add-equivalence
    (implies (and (pointp point1)
                  (pointp point2)
                  (point-on-twisted-edwards-p point1 curve)
                  (point-on-twisted-edwards-p point2 curve)
                  (twisted-edwards-curvep curve))
             (equal (twisted-edwards-add point1 point2 curve)
                    (curve-add point1
                               point2
                               (twisted-edwards-curve->p curve)
                               (twisted-edwards-curve->a curve)
                               (twisted-edwards-curve->d curve))))
    :enable (twisted-edwards-add
             pointp
             point-finite
             point-finite->x
             point-finite->y))

  ;; The closure proof for the simplified addition operation
  ;; is in the following included file.
  ;; See that file for information about what 'simplified' means here.

  (local (include-book "twisted-edwards-closure-simp"))

  ;; We prove the equivalence of the simplified functions
  ;; to the functions defined just above (i.e. the old definitions),
  ;; when their p argument is the constrained (prime)
  ;; used in the simplified functions.

  (defruledl point-on-curve-p-equivalence
    (implies (and (domain)
                  ;; (point-in-pxp-p pt (prime))
                  (pointp pt))
             (iff (point-on-curve-p pt (prime) a d)
                  (and (point-in-pxp-p pt (prime))
                       (simp-point-on-curve-p pt a 1 d))))
    :hints (("Goal" :in-theory (enable =p
                                       i+
                                       i*
                                       modp
                                       ECp
                                       LHS
                                       RHS
                                       simp-point-on-curve-p
                                       pointp
                                       point-in-pxp-p)))
    :prep-books
    ((include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system)))

  (defruledl curve-add-equivalence
    (implies (and (domain)
                  (pointp pt1)
                  (pointp pt2)
                  ;; (point-in-pxp-p pt1 (prime))
                  ;; (point-in-pxp-p pt2 (prime))
                  (point-on-curve-p pt1 (prime) a d)
                  (point-on-curve-p pt2 (prime) a d))
             (equal (curve-add pt1 pt2 (prime) a d)
                    (simp-curve-add pt1 pt2 a 1 d)))
    :hints (("Goal" :in-theory (e/d (=p
                                     i+
                                     i*
                                     modp
                                     i-
                                     /p
                                     div
                                     simp-curve-add
                                     x3
                                     delta-x
                                     gamma+
                                     gamma
                                     y3
                                     delta-y
                                     gamma-
                                     pointp)
                                    (point-in-pxp-p))))
    :prep-books
    ((include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system)
     (include-book "kestrel/arithmetic-light/expt" :dir :system))

    :prep-lemmas

    ((defrule rationalp-of-inv
       (implies (rationalp x)
                (rationalp (inv x p)))
       :rule-classes (:rewrite :type-prescription)
       :enable inv)

     (defrule mul-of-expt-of---of-2
       (implies (and (integerp x)
                     (integerp y)
                     (natp p)
                     (< 1 p))
                (equal (mul x (expt y (+ -2 p)) p)
                       (mul x (inv y p) p)))
       :do-not '(preprocess)
       :enable (inv pfield::pow-rewrite pfield::minus1)
       :prep-books
       ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))))

  ;; We define a more general version of the non-square predicate
  ;; that is used in the closure proof (twisted-edwards-closure-core.lisp).
  ;; This is more general in the sense that it takes a prime p as argument
  ;; instead of implcitly using the constrained (prime).
  ;; We prove it equivalent to non-square, when applied to (prime).

  (local
   (defun-sk non-square-general (x p)
     (forall n (implies (integerp n)
                        (not (equal (mod (sq n) p) (mod x p)))))))

  (defruledl rewrite-non-square-general
    (implies (integerp x)
             (iff (non-square-general x (prime))
                  (non-square x)))
    :hints (("Goal" :in-theory (e/d () (non-square non-square-general)))
            ("Subgoal 2" :in-theory (e/d (=p modp non-square-general) (non-square))
             :use ((:instance non-square-necc
                    (n (non-square-general-witness x (prime))))))
            ("Subgoal 1" :in-theory (e/d (modp =p non-square) (non-square-general))
             :use ((:instance non-square-general-necc
                    (n (non-square-witness x))
                    (p (prime)))))))

  ;; Along a similar pattern, we also define a more general version of =p,
  ;; the equality predicate modulo the prime.
  ;; This takes a prime p as argument,
  ;; instead of being based on the constrained (prime).
  ;; We prove it equivalent to =p, when applied to (prime).

  (local
   (defund mod-= (x y p)
     (equal (mod x p) (mod y p))))

  (defruledl rewrite-mod-=
    (implies (and (integerp x)
                  (integerp y))
             (equal (mod-= x y (prime))
                    (=p x y)))
    :enable (=p modp mod-=)
    :disable (mod))

  ;; Using the two more general functions defined just above,
  ;; we prove the closure of curve-add with respect to point-on-curve-p,
  ;; expressed over the constrained (prime), as conveyed by the name.

  (defruledl closure-constrained-prime
    (implies (and (integerp a)
                  (integerp d)
                  (not (mod-= a 0 (prime)))
                  (non-square-general d (prime))
                  (mod-= (sq sqrt{a}) a (prime))
                  (integerp sqrt{a})
                  (pointp pt1)
                  (pointp pt2)
                  ;; (point-in-pxp-p pt1 (prime))
                  ;; (point-in-pxp-p pt2 (prime))
                  (point-on-curve-p pt1 (prime) a d)
                  (point-on-curve-p pt2 (prime) a d))
             (and (pointp (curve-add pt1 pt2 (prime) a d))
                  (point-on-curve-p (curve-add pt1 pt2 (prime) a d)
                                    (prime) a d)))
    :enable (curve-add-equivalence
             point-on-curve-p-equivalence
             rewrite-mod-=
             rewrite-non-square-general)
    :disable (curve-add
              point-in-pxp-p
              point-on-curve-p)
    :use (:instance closure-of-simp-curve-add
          (c 1)
          (x1 0)
          (y1 0)
          (x2 0)
          (y2 0)))

  ;; We generalize the closure to a variable prime p (as conveyed by the name),
  ;; using functional instantiation for (prime).
  ;; For the non-odd-prime case of the instantiation,
  ;; we need to show that 3 is an odd prime.

  (defruledl closure-variable-prime
    (implies (and (integerp a)
                  (integerp d)
                  (not (mod-= a 0 p))
                  (non-square-general d p)
                  (mod-= (sq sqrt{a}) a p)
                  (integerp sqrt{a})
                  (rtl::primep p)
                  (> p 2)
                  (pointp pt1)
                  (pointp pt2)
                  ;; (point-in-pxp-p pt1 p)
                  ;; (point-in-pxp-p pt2 p)
                  (point-on-curve-p pt1 p a d)
                  (point-on-curve-p pt2 p a d))
             (and (pointp (curve-add pt1 pt2 p a d))
                  (point-on-curve-p (curve-add pt1 pt2 p a d) p a d)))
    :disable (point-in-pxp-p
              pointp
              point-on-curve-p
              curve-add)
    :use ((:functional-instance closure-constrained-prime
           (prime (lambda () (if (and (rtl::primep p)
                                      (> p 2))
                                 p
                               3)))))
    :prep-lemmas
    ((defrule primep-of-3
       (rtl::primep 3)
       :enable rtl::primep)))

  ;; While the theorem just above references non-square-general,
  ;; the completeness predicate references pfield-squarep.
  ;; The following rewrite rule shows their equivalence.

  (defruledl pfield-squarep-to-not-non-square-general
    (implies (and (rtl::primep p)
                  (fep x p))
             (iff (pfield-squarep x p)
                  (not (non-square-general x p))))
    :enable (i* pfield-squarep)
    :use ((:instance non-square-general-necc
           (n (pfield-square->root x p)))
          (:instance pfield-squarep-suff
           (r (mod (non-square-general-witness x p) p))))
    :prep-books
    ((include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system)
     (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

  ;; We reformulate the latest closure theorem above
  ;; to use fep, pfield-squarep, mul, etc.
  ;; The theorem hypotheses still contain an explicit square root b of a,
  ;; as conveyed by the theorem name.

  (defruledl closure-explicit-root
    (implies (and (rtl::primep p)
                  (> p 2)
                  (fep a p)
                  (fep d p)
                  (not (equal a 0))
                  (not (equal d 0))
                  (not (pfield-squarep d p))
                  (fep b p)
                  (equal (mul b b p) a)
                  (pointp pt1)
                  (pointp pt2)
                  ;; (point-in-pxp-p pt1 p)
                  ;; (point-in-pxp-p pt2 p)
                  (point-on-curve-p pt1 p a d)
                  (point-on-curve-p pt2 p a d))
             (and (pointp (curve-add pt1 pt2 p a d))
                  (point-on-curve-p (curve-add pt1 pt2 p a d) p a d)))
    :use (:instance closure-variable-prime (sqrt{a} b))
    :enable (pfield-squarep-to-not-non-square-general mod-= i*)
    :disable (point-on-curve-p curve-add)
    :prep-books
    ((include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system)
     (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

  ;; We remove the explcit root, using pfield-squarep instead.
  ;; This closure theorem is expressed on the components (a, d, and p)
  ;; of the curve, as conveyed by the name.

  (defruledl closure-on-components
    (implies (and (rtl::primep p)
                  (> p 2)
                  (fep a p)
                  (fep d p)
                  (not (equal a 0))
                  (not (equal d 0))
                  (not (pfield-squarep d p))
                  (pfield-squarep a p)
                  (pointp pt1)
                  (pointp pt2)
                  ;; (point-in-pxp-p pt1 p)
                  ;; (point-in-pxp-p pt2 p)
                  (point-on-curve-p pt1 p a d)
                  (point-on-curve-p pt2 p a d))
             (and (pointp (curve-add pt1 pt2 p a d))
                  (point-on-curve-p (curve-add pt1 pt2 p a d) p a d)))
    :use (:instance closure-explicit-root (b (pfield-square->root a p)))
    :enable pfield-squarep
    :disable (point-on-curve-p curve-add))

  ;; We formulate the closure theorem on the curve tuples,
  ;; instead of their components.

  (defruledl closure-on-curve
    (implies (and (twisted-edwards-curvep curve)
                  (twisted-edwards-curve-completep curve)
                  (pointp pt1)
                  (pointp pt2)
                  (point-on-twisted-edwards-p pt1 curve)
                  (point-on-twisted-edwards-p pt2 curve))
             (and (pointp (curve-add pt1
                                     pt2
                                     (twisted-edwards-curve->p curve)
                                     (twisted-edwards-curve->a curve)
                                     (twisted-edwards-curve->d curve)))
                  (point-on-curve-p (curve-add pt1
                                               pt2
                                               (twisted-edwards-curve->p curve)
                                               (twisted-edwards-curve->a curve)
                                               (twisted-edwards-curve->d curve))
                                    (twisted-edwards-curve->p curve)
                                    (twisted-edwards-curve->a curve)
                                    (twisted-edwards-curve->d curve))))
    :use ((:instance closure-on-components
           (p (twisted-edwards-curve->p curve))
           (a (twisted-edwards-curve->a curve))
           (d (twisted-edwards-curve->d curve)))
          (:instance point-on-twisted-edwards-p-equivalence (point pt1))
          (:instance point-on-twisted-edwards-p-equivalence (point pt2)))
    :enable twisted-edwards-curve-completep
    :disable (point-on-curve-p
              curve-add))

  ;; We formulate the final theorem on the new definitions,
  ;; leveraging their equivalence to the old definitions.

  (defruledl point-on-twisted-edwards-p-of-twisted-edward-add
    (implies (and (twisted-edwards-curvep curve)
                  (twisted-edwards-curve-completep curve)
                  (pointp point1)
                  (pointp point2)
                  (point-on-twisted-edwards-p point1 curve)
                  (point-on-twisted-edwards-p point2 curve))
             (point-on-twisted-edwards-p (twisted-edwards-add point1
                                                              point2
                                                              curve)
                                         curve))
    :enable (point-on-twisted-edwards-p-equivalence
             twisted-edwards-add-equivalence
             closure-on-curve)
    :disable (point-on-curve-p
              curve-add))

  ;; Exported theorem, without hints.

  (defrule point-on-twisted-edwards-p-of-twisted-edward-add
    (implies (and (twisted-edwards-curvep curve)
                  (twisted-edwards-curve-completep curve)
                  (pointp point1)
                  (pointp point2)
                  (point-on-twisted-edwards-p point1 curve)
                  (point-on-twisted-edwards-p point2 curve))
             (point-on-twisted-edwards-p (twisted-edwards-add point1
                                                              point2
                                                              curve)
                                         curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edwards-zero ()
  :returns (point pointp)
  :short "Neutral point of the twisted Edwards curve group."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always @($(0,1)$).
     See the paper referenced in @(see twisted-edwards)."))
  (point-finite 0 1)
  ///

  (defrule point-on-twisted-edwards-p-of-twisted-edwards-zero
    (point-on-twisted-edwards-p (twisted-edwards-zero) curve)
    :enable point-on-twisted-edwards-p
    :prep-books
    ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

  (in-theory (disable (:e twisted-edwards-zero))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edwards-neg ((point pointp) (curve twisted-edwards-curvep))
  :guard (and (twisted-edwards-curve-completep curve)
              (point-on-twisted-edwards-p point curve))
  :returns (point1 pointp)
  :short "Negation of a point of the twisted Edwards curve group."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse with respect to the group addition operation.")
   (xdoc::p
    "It is obtained by negating the @($x$) coordinate.
     See the paper referenced in @(see twisted-edwards)."))
  (point-finite (neg (point-finite->x point)
                     (twisted-edwards-curve->p curve))
                (point-finite->y point))
  :guard-hints (("Goal" :in-theory (enable point-on-twisted-edwards-p fep)))
  :hooks (:fix)
  ///

  (defrule point-on-twisted-edwards-p-of-twisted-edwards-neg
    (implies (and (twisted-edwards-curvep curve)
                  (twisted-edwards-curve-completep curve)
                  (point-on-twisted-edwards-p point curve))
             (point-on-twisted-edwards-p (twisted-edwards-neg point curve)
                                         curve))
    :enable (point-on-twisted-edwards-p)
    :disable pfield::fep-of-neg
    :use (:instance pfield::fep-of-neg
          (x (point-finite->x point))
          (p (twisted-edwards-curve->p curve)))
    :prep-books
    ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edwards-sub ((point1 pointp)
                             (point2 pointp)
                             (curve twisted-edwards-curvep))
  :guard (and (twisted-edwards-curve-completep curve)
              (point-on-twisted-edwards-p point1 curve)
              (point-on-twisted-edwards-p point2 curve))
  :returns (point pointp)
  :short "Subtraction of two points of the twisted Edwards group."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is, as usual in groups, essentially an abbreviation for
     adding the first point to the negation of the second point."))
  (twisted-edwards-add point1
                       (twisted-edwards-neg point2 curve)
                       curve)
  :hooks (:fix)
  ///

  (defrule point-on-twisted-edwards-p-of-twisted-edwards-sub
    (implies (and (twisted-edwards-curvep curve)
                  (twisted-edwards-curve-completep curve)
                  (pointp point1)
                  (pointp point2)
                  (point-on-twisted-edwards-p point1 curve)
                  (point-on-twisted-edwards-p point2 curve))
             (point-on-twisted-edwards-p (twisted-edwards-sub point1
                                                              point2
                                                              curve)
                                         curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edwards-mul ((scalar integerp)
                             (point pointp)
                             (curve twisted-edwards-curvep))
  :guard (and (twisted-edwards-curve-completep curve)
              (point-on-twisted-edwards-p point curve))
  :returns (point1 pointp)
  :short "Scalar multiplication in the twisted Edwards group."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the group were multiplicative, this would be exponentiation.
     Since the twisted Edwards group is additive,
     here we talk about scalar multiplication instead.")
   (xdoc::p
    "We first define the operation for non-negative scalars,
     by simple recursion in the same manner as exponentiation:
     multiplication by 0 yields the neutral element;
     multiplication by a non-zero scalar yields the sum of the point and
     the scalar multiplication by the scalar minus one.
     Then we extend it to negative scalars,
     by negating the result of multiplying by the negated scalar.")
   (xdoc::p
    "For the recursive auxiliary function on non-negative scalars,
     we need to defer guard verification;
     we first need to prove that it returns a point on the curve."))
  (b* ((scalar (ifix scalar)))
    (if (>= scalar 0)
        (twisted-edwards-mul-nonneg scalar point curve)
      (twisted-edwards-neg
       (twisted-edwards-mul-nonneg (- scalar) point curve)
       curve)))
  :hooks (:fix)

  :prepwork
  ((define twisted-edwards-mul-nonneg ((scalar natp)
                                       (point pointp)
                                       (curve twisted-edwards-curvep))
     :guard (and (twisted-edwards-curve-completep curve)
                 (point-on-twisted-edwards-p point curve))
     :returns (point1 pointp)
     (if (zp scalar)
         (twisted-edwards-zero)
       (twisted-edwards-add point
                            (twisted-edwards-mul-nonneg (1- scalar) point curve)
                            curve))
     :hooks (:fix)
     :verify-guards nil ; done below
     ///
     (defrule point-on-twisted-edwards-p-of-twisted-edwards-mul-nonneg
       (implies (and (twisted-edwards-curvep curve)
                     (twisted-edwards-curve-completep curve)
                     (pointp point)
                     (point-on-twisted-edwards-p point curve))
                (point-on-twisted-edwards-p (twisted-edwards-mul-nonneg scalar
                                                                        point
                                                                        curve)
                                            curve)))
     (verify-guards twisted-edwards-mul-nonneg)))

  ///

  (defrule point-on-twisted-edwards-p-of-twisted-edwards-mul
    (implies (and (twisted-edwards-curvep curve)
                  (twisted-edwards-curve-completep curve)
                  (pointp point)
                  (point-on-twisted-edwards-p point curve))
             (point-on-twisted-edwards-p (twisted-edwards-mul scalar
                                                              point
                                                              curve)
                                         curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edwards-compress ((point pointp) (curve twisted-edwards-curvep))
  :guard (point-on-twisted-edwards-p point curve)
  :returns (mv (p bitp) (y natp))
  :short "Turn a point on a twisted Edwards curve into compressed form."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is based on Appendix A.3.3.2 of the "
    (xdoc::ahref "https://zips.z.cash/protocol/protocol.pdf"
                 "Zcash Protocol Specification (Version 2020.1.15)")
    ", but quite likely it is much more general than
     not only Zcash, but also twisted Edwards curves.")
   (xdoc::p
    "The compression consists in keeping the whole @($y$) coordinate
     but only the lowest bit (i.e. the parity) of the @($x$) coordinate.
     This, together with the information that the point is on the curve,
     should suffice to reconstruct the full @($x$) coordinate.
     Eventually we should prove this, and define a decompression function."))
  (declare (ignore curve)) ; only used in the guard
  (mv (mod (point-finite->x point) 2) (point-finite->y point))
  :hooks (:fix)
  :prepwork
  ((defrule returns-lemma
     (implies (and (natp x)
                   (not (equal (mod x 2) 0)))
              (equal (mod x 2) 1))
     :prep-books ((include-book "arithmetic-3/top" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edwards-point-orderp ((point pointp)
                                      (order natp)
                                      (curve twisted-edwards-curvep))
  :guard (and (twisted-edwards-curve-completep curve)
              (point-on-twisted-edwards-p point curve))
  :returns (yes/no booleanp)
  :short "Check if a point on a twisted Edwards curve has a certain order."
  :long
  (xdoc::topstring
   (xdoc::p
    "A point @($P$) has order @($n$) if and only if
     @($n > 0$),
     @($n P$) is the neutral element, and
     @($m P$) is not for every @($m < n$).")
   (xdoc::p
    "Every point on the curve has an order,
     so there should really be a function that returns that.
     However, defining that function requires some theorems
     that we do not have yet;
     thus, for now we define this predicate instead.
     We plan to define the function that returns the order eventually."))
  (b* ((order (nfix order)))
    (and (> order 0)
         (equal (twisted-edwards-mul order point curve)
                (twisted-edwards-zero))
         (twisted-edwards-point-order-leastp point order curve)))
  :hooks (:fix)

  :prepwork
  ((define-sk twisted-edwards-point-order-leastp
     ((point pointp)
      (order natp)
      (curve twisted-edwards-curvep))
     :guard (and (twisted-edwards-curve-completep curve)
                 (point-on-twisted-edwards-p point curve))
     (forall (order1)
             (implies (and (natp order1)
                           (< 0 order1)
                           (< order1 (nfix order)))
                      (not (equal (twisted-edwards-mul order1 point curve)
                                  (twisted-edwards-zero)))))
     ///
     (fty::deffixequiv-sk twisted-edwards-point-order-leastp
       :args ((point pointp) (order natp) (curve twisted-edwards-curvep))))))
