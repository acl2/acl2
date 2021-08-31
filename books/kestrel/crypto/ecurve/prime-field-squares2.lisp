; Refinement of pfield-squarep
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/number-theory/quadratic-residue" :dir :system)
(include-book "prime-field-squares")

(defruled has-square-root?-satisfies-pfield-squarep
  :short "Show how pfield-squarep can be refined into has-square-root?"
  :long
  (xdoc::topstring
   (xdoc::p
    "@see('pfield-squarep') is a nonexecutable specification of what it means to
     check that a field element is a square of another field element.<br/>
     @see('primes::has-square-root?') is an executable specification that uses Euler's
     Criterion to determine if the field element has a square root.<br/>
     In order to use @(see apt::simplify) to refine a use of @('pfield-squarep')
     to @('has-square-root?'), we must show that they are equivalent under
     appropriate hypotheses that limit the domain.  That is the purpose of
     this  definition.")
   (xdoc::p
    "Implementation notes:")
   (xdoc::p
    "Use @('residue-meaning-backwards') to turn @('has-square-root?') into @('residue'),"
    "open it up to expose @('find-root'), use the theorem about @('find-root') to obtain"
    "that the square of @('find-root') is @('a'), and finally use that as witness to"
    "conclude @('pfield-squarep').")
   (xdoc::p
    "There is a case split on whether @('a') is @('0') or not,"
    "due to the definition of @('residue'). The enablement of @('mul') is so that"
    "@('pfield-squarep') is phrased as @('(mod (* ... ...) p)'), and enablement of"
    "@('fep') because some of the theorems used have @('natp') and @('< p') as hyps."))
  :parents (elliptic-curves)
  (implies (and (rtl::primep p)
		(not (equal p 2))
		(fep a p)
		(primes::has-square-root? a p))
	   (pfield-squarep a p))
  :cases ((equal a 0))
  :enable (mul fep rtl::residue primes::residue-meaning-backwards)
  :use ((:instance pfield-squarep-suff (r (rtl::find-root (- p 1) a p)) (x a))
	(:instance rtl::res-root1-lemma (n (- p 1)) (m a) (p p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The above is not sufficient for simplification.  What we really want is a rule that says
;; (implies <some-hyps>
;;          (equal (pfield-squarep a p) (primes::has-square-root? a p)))

;; Let's make sure the other direction is proved first

(defruled pfield-squarep-->has-square-root?
  (implies (and (rtl::primep p)
                (not (equal p 2))
                (fep a p)
                (pfield-squarep a p))
           (primes::has-square-root? a p))
  :enable ( ;fep  has-square-root?-satisfies-pfield-squarep
           mul pfield-squarep))

(local
 (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(defruled pfield-squarep<->has-square-root?
 (implies (and (rtl::primep p)
                (not (equal p 2))
                (fep a p))
         (equal (pfield-squarep a p)
                (primes::has-square-root? a p)))
  :enable (pfield-squarep-->has-square-root?
           has-square-root?-satisfies-pfield-squarep))

(defruled has-square-root?<->pfield-squarep
 (implies (and (rtl::primep p)
                (not (equal p 2))
                (fep a p))
         (equal (primes::has-square-root? a p)
                (pfield-squarep a p)))
  :enable (pfield-squarep-->has-square-root?
           has-square-root?-satisfies-pfield-squarep))

(theory-invariant (incompatible (:rewrite pfield-squarep<->has-square-root?)
                                (:rewrite has-square-root?<->pfield-squarep)))
