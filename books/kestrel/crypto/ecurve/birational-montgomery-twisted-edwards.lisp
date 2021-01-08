; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "montgomery")
(include-book "twisted-edwards")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ birational-montgomery-twisted-edwards
  :parents (elliptic-curves montgomery twisted-edwards)
  :short "Mapping between Montgomery curves and twisted Edwards curves."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is a birational equivalence between "
    (xdoc::seetopic "montgomery-curves" "Montgomery curves")
    " and "
    (xdoc::seetopic "twisted-edwards" "twisted Edwards curves")
    ", described in Section 3 of "
    (xdoc::ahref
     "https://eprint.iacr.org/2008/013.pdf"
     "Bernstein, Birkner, Joye, Lange, and Peters's ``Twisted Edwards Curves''")
    ". That is, there are:")
   (xdoc::ul
    (xdoc::li
     "An isomorphic mapping between
      the set of Montgomery curves
      and the set of twisted Edwards curves.")
    (xdoc::li
     "Given isomorphic Montgomery and twisted Edwards curves,
      there is an isomorphic mapping between
      the set of points of one curve
      and the set of points of the other curve."))
   (xdoc::p
    "Here `birational' means that the isomorphic mappings
     between the sets of points of two isomorphic curves
     are rational functions.
     Their denominators are 0 only for a finite number of points of the curves;
     the complete isomorphisms can be therefore defined with ease
     via the rational formulas plus a few special explicit cases.")
   (xdoc::p
    "Here we define all these isomorphic mappings.
     We plan to prove the isomorphism claims at some point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define montgomery-to-twisted-edwards ((mcurve montgomery-p))
  :guard (montgomery-primep mcurve)
  :returns (tecurve twisted-edwards-p)
  :short "Map a Montgomery curve to a twisted Edwards curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the Montgomery curve's coefficients @($A$) and @($B$),
     the twisted Edwards curve's coefficients are
     @($a = (A + 2) / B$) and @($d = (A - 2) B$),
     which are well-defined because @($B \\neq 0$).
     The prime is of course unchanged.")
   (xdoc::p
    "The guard proofs require to show that @($a$) and @($d$) are not 0,
     which follows from the conditions on @($A$).
     It also requires showing that @($a \\neq d$):
     this reduces (via locally included prime field rules)
     to @($A + 2 \\neq A - 2$) and thus to @($2 \\neq -2$),
     but this is not immediately obvious because it is modular,
     i.e. it really is @($2 \\neq p - 2$);
     so we use a local lemma to reduce this to @($p \\neq 4$),
     and another local lemma to show that 4 is not prime."))
  (b* (((montgomery mcurve) mcurve)
       (a (div (add mcurve.a 2 mcurve.p) mcurve.b mcurve.p))
       (d (div (sub mcurve.a 2 mcurve.p) mcurve.b mcurve.p)))
    (make-twisted-edwards :p mcurve.p :a a :d d))
  :guard-hints (("Goal" :in-theory (enable montgomery-primep)))
  :hooks (:fix)
  :prepwork
  ((local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
   (local (include-book "kestrel/prime-fields/equal-of-add-rules" :dir :system))
   (local (include-book "prime-field-extra-rules"))
   (defrulel verify-guards-lemma-1
     (implies (posp p)
              (equal (equal 2 (mod -2 p))
                     (equal p 4)))
     :prep-books ((include-book "arithmetic-3/top" :dir :system)))
   (defrulel verify-guards-lemma-2
     (not (rtl::primep 4))
     :enable rtl::primep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define twisted-edward-to-montgomery ((tecurve twisted-edwards-p))
  :guard (twisted-edwards-primep tecurve)
  :returns (mcurve montgomery-p)
  :short "Map a twisted Edwards curve to a Montgomery curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the twisted Edwards curve's coefficients @($a$) and @($d$),
     the Montgomery coefficients are
     @($A = 2 (a + d) / (a - d)$) and @($B = 4 / (a - d)$),
     which are well-defined because @($a \\neq d$).")
   (xdoc::p
    "The guard proofs require to show that
     @($A$) is neither 2 nor -2 and @($B$) is not 0.
     This is carried out via a number of rules from the prime fields library,
     along with a few specific lemmas that involve
     particular constants that appear in the formulas."))
  (b* (((twisted-edwards tecurve) tecurve)
       (a-d (sub tecurve.a tecurve.d tecurve.p))
       (a+d (add tecurve.a tecurve.d tecurve.p))
       (ma (mul 2 (div a+d a-d tecurve.p) tecurve.p))
       (mb (div (mod 4 tecurve.p) a-d tecurve.p)))
    (make-montgomery :p tecurve.p :a ma :b mb))
  :guard-hints (("Goal" :in-theory (enable twisted-edwards-primep)))
  :hooks (:fix)
  :prepwork
  ((local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
   (local (include-book "kestrel/prime-fields/equal-of-add-rules" :dir :system))
   (local (include-book "prime-field-extra-rules"))
   (defrulel verify-guards-lemma-1
     (implies (and (integerp p)
                   (> p 2))
              (equal (equal (mod 4 p) 0)
                     (equal p 4)))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))
   (defrulel verify-guards-lemma-2
     (not (rtl::primep 4))
     :enable rtl::primep)
   (defrulel verify-guards-3
     (implies (and (rtl::primep p)
                   (> p 2))
              (equal (div -2 2 p)
                     (pfield::minus1 p)))
     :enable div
     :disable mul-of-minus1-becomes-neg-2
     :use lemma
     :prep-books
     ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
     :prep-lemmas
     ((defruled lemma
        (implies (rtl::primep p)
                 (equal (mod -2 p)
                        (mul 2 (pfield::minus1 p) p)))
        :enable (mul pfield::minus1)
        :prep-books ((include-book "arithmetic-3/top" :dir :system)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: define mappings between points
