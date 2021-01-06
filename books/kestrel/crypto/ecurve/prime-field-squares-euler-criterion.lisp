; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Authors: Eric McCarthy (mccarthy@kestrel.edu)
;                       Nathan Guermond (guermond@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "prime-field-squares")

(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection prime-field-squares-euler-criterion
  :parents (pfield-squarep)
  :short "A weak formulation of Euler's criterion for prime field squares."
  :long
  (xdoc::topstring
   (xdoc::p
    "Euler's criterion serves to determine whether
     a number is a square or not modulo a prime.
     See "
    (xdoc::ahref "https://en.wikipedia.org/wiki/Euler's_criterion"
                 "this Wikipedia page")
    ".")
   (xdoc::p
    "Here we provide a weaker formulation.
     It only works for odd prime fields,
     and it only lets us conclude when a number is not a square.")
   (xdoc::p
    "The criterion is here formulated with respect to
     the @(tsee pfield-squarep) predicate.
     Like that predicate, this belongs to a more general library,
     probably the prime field library itself.
     It is currently in the elliptic curve library
     because that is where it is used.")
   (xdoc::p
    "The proof of the criterion relies on some existing libraries.
     It is explained in this file.
     It should be possibly to simplify and streamline the proof."))

  ;; The odd prime field library contains the key theorem used here.

  (local (include-book "odd-prime-fields"))

  ;; We define the concept of not being a square.
  ;; This is the same as in twisted-edwards-closure-core.lisp,
  ;; but with the sq macro expanded so we do not need to redefine it here.

  (local
   (defun-sk non-square (x)
     (forall n (implies (integerp n)
                        (not (=p (i* n n) x))))))

  ;; We prove the criterion, expressed using
  ;; non-square above, the constrained (prime), and the =p relation.

  (defruledl weak-euler-criterion-contrapositive-1
    (implies (and (integerp a)
                  (not (=p a 0))
                  (not (=p (expt a (/ (- (prime) 1) 2)) 1)))
             (non-square a))
    :use ((:instance weak-euler-criterion (sqrt{a} (non-square-witness a)))))

  ;; We introduce more general forms of non-square and =p,
  ;; in the sense that the prime is a parameter and not the constrained (prime),
  ;; the same as in the closure proof of twisted-edwards.lisp.
  ;; We prove them equivalent to the other ones.

  (local
   (defun-sk non-square-general (x p)
     (forall n (implies (integerp n)
                        (not (equal (mod (i* n n) p) (mod x p)))))))

  (local
   (defund mod-= (x y p)
     (equal (mod x p) (mod y p))))

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

  (defruledl rewrite-mod-=
    (implies (and (integerp x)
                  (integerp y))
             (equal (mod-= x y (prime))
                    (=p x y)))
    :hints (("Goal" :in-theory (e/d (=p modp mod-=) (mod)))))

  ;; Now we reformulate the criterion in terms of these more general functions.
  ;; We do that in two stages: first we use (prime) as the p parameter,
  ;; and then we do a functional instantiation.

  (defruledl weak-euler-criterion-contrapositive-general-2
    (implies (and (integerp a)
                  (not (mod-= a 0 (prime)))
                  (not (mod-= (expt a (/ (- (prime) 1) 2)) 1 (prime))))
             (non-square-general a (prime)))
    :enable (rewrite-mod-= rewrite-non-square-general)
    :disable (non-square-general non-square)
    :use ((:instance weak-euler-criterion-contrapositive-1) lemma)
    :prep-lemmas
    ((defruled lemma
       (implies (integerp a)
                (integerp (expt a (/ (- (prime) 1) 2))))
       :prep-books ((include-book "arithmetic-5/top" :dir :system)))))

  (defruledl weak-euler-criterion-contrapositive-general-3
    (implies (and (rtl::primep p)
                  (> p 2)
                  (integerp a)
                  (not (mod-= a 0 p))
                  (not (mod-= (expt a (/ (- p 1) 2)) 1 p)))
             (non-square-general a p))
    :enable rtl::primep
    :use ((:functional-instance
           weak-euler-criterion-contrapositive-general-2
           (prime (lambda () (if (and (rtl::primep p)
                                      (> p 2))
                                 p
                               3))))))

  ;; We prove the equivalence of pfield-squarep to non-square-general,
  ;; so that we can reformulate the criterion for pfield-squarep.

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

  ;; This is the final reformulation.

  (defruledl weak-euler-criterion-contrapositive
    (implies (and (rtl::primep p)
                  (> p 2)
                  (fep a p)
                  (not (equal a 0))
                  (not (equal (mod (expt a (/ (- p 1) 2)) p)
                              1)))
             (not (pfield-squarep a p)))
    :use weak-euler-criterion-contrapositive-general-3
    :enable (pfield-squarep-to-not-non-square-general fep mod-=)
    :disable non-square-general
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  ;; Exported version without hints.
  ;; This is the one that can be used to show that a number is not a square.

  (defruled weak-euler-criterion-contrapositive
    (implies (and (rtl::primep p)
                  (> p 2)
                  (fep a p)
                  (not (equal a 0))
                  (not (equal (mod (expt a (/ (- p 1) 2)) p)
                              1)))
             (not (pfield-squarep a p)))))
