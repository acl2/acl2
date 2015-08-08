; quotient-remainder-lemmas.lisp  --  facts about FLOOR, MOD, TRUNCATE and REM
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    quotient-remainder-lemmas.lisp
;;;
;;;    This book includes facts about the functions FLOOR, MOD, TRUNCATE and
;;;    REM, and integer ratios.
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(deflabel quotient-remainder-lemmas

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
;
; A book of facts about FLOOR, MOD, TRUNCATE and REM, and integer ratios.
; Also enough of a theory of the Acl2 function NONNEGATIVE-INTEGER-QUOTIENT
; to prove the rules.
; ~/

; Since NONNEGATIVE-INTEGER-QUOTIENT is the only one of these functions that
; is recursive, the others must be DISABLEd for this library to be of any
; use.  This can easily be done by DISABLEing the QUOTIENT-REMAINDER-FUNCTIONS
; theory (defined by this book):

; (IN-THEORY (DISABLE QUOTIENT-REMAINDER-FUNCTIONS))

; ~/
; INTRODUCTION

; Common Lisp defines the quotient/remainder functions FLOOR/MOD and
; TRUNCATE/REM, which operate on any rational numbers (as long as the divisor
; is non-zero).  Both (TRUNCATE x y) and (FLOOR x y) are integers, and
; specify the `integer part' of the rational number x/y; they differ in the
; direction of rounding.

; TRUNCATE is the `FORTRAN-style' quotient operation, rounding towards 0,
; i.e., (TRUNCATE x y) = (TRUNCATE (ABS x) (ABS y)).  This book provides a
; selected theory of TRUNCATE and REM.

; (FLOOR x y) is identical to TRUNCATE if x/y > 0 or x/y is an integer,
; otherwise for negative non-integer ratios x/y,
; (FLOOR x y) = (TRUNCATE x y) - 1.  (FLOOR i (EXPT 2 j)) is the
; specification of an `arithmetic shift' of the integer i by -j bits.  Since
; FLOOR and MOD are the foundations for integer descriptions of hardware,
; this book contains a very extensive theory of FLOOR and MOD.

; The formal definitions of the Common Lisp functions are made in terms of
; the Acl2 function NONNEGATIVE-INTEGER-QUOTIENT, which is simple recursive
; specification of division of nonnegative integers by repeated subtraction.
; We provide only enough of a theory of NONNEGATIVE-INTEGER-QUOTIENT to prove
; the desired properties of the Common Lisp functions.

; DOCUMENTATION

; The documentation for this library is divided into a number of sections.
; There is a section for the rules that apply to each function.  Some of the
; rules will appear in more than 1 section.  If a rule is exported DISABLEd,
; then you will see `(D)' after the rule class in the `one-liner' for the
; rule.  Note that we often abbreviate NONNEGATIVE-INTEGER-QUOTIENT as NIQ.

; APPROACH

; We have tried to capture the properties of the quotient/remainder functions
; with the smallest number of the most general rules possible.  This approach
; takes advantage of Acl2 type reasoning, and the assumed existence of a
; basic mathematics simplification library.  Several lemmas contain the
; hypothesis (INTEGERP (/ x y)), which we consider to be the simplest
; statement of the fact that (<quotient> x y) = x/y, e.g.

; (INTEGERP (/ x y)) ==> (FLOOR x y) = (/ x y),
; (INTEGERP (/ x y)) ==> (MOD x y) = 0.

; Thus, the first fact above obviates the need for a specials lemmas like
; (FLOOR i 1) = i for integers i, since (/ i 1) = i by simplification.

; In general, at most 2 of the many possible commutative forms of the rules are
; exported from this library.  If they aren't the ones you need, simply prove
; the appropriate corollary, or :USE an :INSTANCE of the library rule.
; Also, lemmas are generally exported DISABLEd if they seemed to interfere
; with the proofs of other lemmas, or could easily lead to infinite looping.
; Be careful when ENABLEing these lemmas.

; Questions, comments, and sugestions are welcome.  Contact brock@cli.com.~/"
  )

(deflabel niq-lemmas

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
; Lemmas about nonnegative-integer-QUOTIENT (abbreviated NIQ).
; ~/~/~/"
  )

(deflabel floor-lemmas

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
; Lemmas about FLOOR.
; ~/~/~/"
  )

(deflabel truncate-lemmas

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
; Lemmas about TRUNCATE.
; ~/~/~/"
  )

(deflabel mod-lemmas

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
; Lemmas about MOD.
; ~/~/~/"
  )

(deflabel rem-lemmas

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
; Lemmas about REM.
; ~/~/~/"
  )

(deflabel integer-ratio-lemmas

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
; Lemmas about ratios x/y that are known to be INTEGERP.
; ~/~/~/"
  )


;;;****************************************************************************
;;;
;;;    ENVIRONMENT -- Load books and initialize the theory.
;;;
;;;****************************************************************************

;;;  Global rules.

(include-book "../../../../ihs/ihs-init")
(include-book "../../../../ihs/ihs-theories")
(local (include-book "../../../../ihs/math-lemmas"))
(local (in-theory nil))

(local (in-theory (enable basic-boot-strap ; From ihs-theories
			 ;; From math-lemmas
			  ihs-math
			  rationalp-algebra
			  ifix nfix)))


;;;****************************************************************************
;;;
;;;    DEFINITIONS and GUARD MACROS
;;;
;;;****************************************************************************

(deflabel qr-guard-macros

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
; Macro forms of the guards for the quotient/remainder functions.
; ~/
; Without these macros, fully 25% of the text of the
; \"quotient-remainder-lemmas\" book is given over simply to expressing
; the guards!~/~/"

  )

(defmacro niq-guard (i j)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; ":doc-section qr-guard-macros
; Macro form of the guard for NONNEGATIVE-INTEGER-QUOTIENT (forced).
; ~/~/~"

  (mlambda (i j)
    (and (force (integerp i))
	 (force (>= i 0))
	 (force (integerp j))
	 (force (> j 0)))))

(defmacro qr-guard (x y)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; ":doc-section qr-guard-macros
; Quotient/Remainder GUARD: Macro form of the guards for FLOOR, MOD, TRUNCATE,
; and REM., or any ratio x/y of rationals (forced).
; ~/~/~"

  (mlambda (x y)
    (and (force (rationalp x))
	 (force (rationalp y))
	 (force (not (equal 0 y))))))


;;;****************************************************************************
;;;
;;;    LOCAL LEMMAS --  A few special rules derived from the more general
;;;    rules included above.
;;;
;;;****************************************************************************

(local
 (defthm cancel-<-+-3
   (equal (< (+ x y z) y)
	  (< (+ x z) 0))
   :hints (("Goal" :in-theory (enable rewrite-linear-equalities-to-iff)))))

(local
 (defthm cancel-equal-+-3
   (implies (acl2-numberp y)
	    (equal (equal (+ x y z) y)
		   (equal (fix x) (- z))))))

(local
 (defthm cancel-equal-+-right
   (equal (equal (+ y x) (+ z x))
	  (equal (fix y) (fix z)))))

;  This theory is useful for proving certain types of bounds properties, but
;  will cause thrashing in linear arithmetic unless the hypotheses e.g.
;  x <= y can be relieved.

(local
 (defthm ratio-theory-of-1
   (and
    (implies
     (and (qr-guard x y) (<= 0 x) (< 0 y) (< x y))
     (< (/ x y) 1))
    (implies
     (and (qr-guard x y) (<= 0 x) (< 0 y) (<= y x))
     (<= 1 (/ x y)))
    (implies
     (and (qr-guard x y) (<= 0 x) (< y 0) (< x (- y)))
     (< -1 (/ x y)))
    (implies
     (and (qr-guard x y) (<= 0 x) (< y 0) (<= (- y) x))
     (<= (/ x y) -1))
    (implies
     (and (qr-guard x y) (<= 0 x) (< y 0) (<= x (- y)))
     (<= -1 (/ x y)))
    (implies
     (and (qr-guard x y) (<= x 0) (< 0 y) (< (- x) y))
     (< -1 (/ x y)))
    (implies
     (and (qr-guard x y) (<= x 0) (< 0 y) (<= y (- x)))
     (<= (/ x y) -1))
    (implies
     (and (qr-guard x y) (<= x 0) (< 0 y) (<= (- x) y))
     (<= -1 (/ x y)))
    (implies
     (and (qr-guard x y) (<= x 0) (< y 0) (< (- x) (- y)))
     (< (/ x y) 1))
    (implies
     (and (qr-guard x y) (<= x 0) (< y 0) (<= (- y) (- x)))
     (<= 1 (/ x y))))
   :rule-classes :linear
   :hints
   (("Goal"
     :in-theory (enable prefer-*-to-/
			rewrite-linear-equalities-to-iff)))))


;;;****************************************************************************
;;;
;;;    LEMMAS -- Begin proving lemmas.
;;;
;;;****************************************************************************

(deflabel begin-quotient-remainder-lemmas)

;;;****************************************************************************
;;;
;;;    NONNEGATIVE-INTEGER-QUOTIENT
;;;
;;;****************************************************************************

(local (defthm niq-bounds-help-1
	 (implies (and (rationalp i)
		       (< 0 j)
		       (rationalp j)
		       (rationalp x))
		  (equal (< (+ -1 (* i (/ j))) x)
			 (< i (+ j (* j x)))))
	 :hints (("Goal" :in-theory
		  (set-difference-theories
		   (enable rewrite-linear-equalities-to-iff)
		   '(<-*-left-cancel))
		  :use (:instance <-*-left-cancel
				  (z j) (y x) (x (/ (+ i (- j)) j)))))
	 :rule-classes nil))

(defthm niq-bounds
  (implies
   (niq-guard i j)
   (and (<= (nonnegative-integer-quotient i j) (/ i j))
	(< (- (/ i j) 1) (nonnegative-integer-quotient i j))))
  :rule-classes
  ((:linear :trigger-terms ((nonnegative-integer-quotient i j))))
  :hints
  (("Goal" :in-theory (enable ifix nfix nonnegative-integer-quotient
			      ratio-theory-of-1))
   ("Subgoal *1/2.2" :use
    (:instance niq-bounds-help-1
	       (i i) (j j)
	       (x (nonnegative-integer-quotient (+ i (- j))
						j)))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section niq-lemmas
; Linear (D): i/j - 1 < (NIQ i j) <= i/j.
; ~/

; This lemma serves as a :LINEAR definition of NONNEGATIVE-INTEGER-QUOTIENT,
; and allows us to derive interesting properties of FLOOR and TRUNCATE by
; linear arithmetic.  This lemma is stored as a :LINEAR rule under NIQ
; since we think of this as a property of NIQ, and not as a general property
; of (/ I J).~/~/"
  )

;< Although the following follows naturally from NIQ-BOUNDS, it can't be
;proved by linear alone, probably because (/ i j) is `too heavy'.

(defthm niq-type
  (implies
   (niq-guard i j)
   (and
    (equal (equal (nonnegative-integer-quotient i j) 0)
	   (< i j))
    (equal (< 0 (nonnegative-integer-quotient i j))
	   (>= i j))
    (equal (equal (nonnegative-integer-quotient i j) (/ i j))
	   (integerp (/ i j)))))
  :rule-classes
  ((:rewrite)
   (:linear
    :corollary
    (implies
     (and (>= i j)
	  (niq-guard i j))
     (< 0 (nonnegative-integer-quotient i j))))
   (:rewrite
    :corollary
    (implies
     (and (< i j)
	  (niq-guard i j))
     (equal (nonnegative-integer-quotient i j)
	    0)))
   (:rewrite
    :corollary
    (implies
     (and (equal r (/ i j))
	  (integerp r)
	  (niq-guard i j))
     (equal (nonnegative-integer-quotient i j) r))))
  :hints
  (("Goal"
    :in-theory (disable niq-bounds <-*-/-left)
    :use (niq-bounds)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section niq-lemmas
; Various : Decide (NIQ i j) = 0, (NIQ i j) > 0, and
; (NIQ i j) = i/j based on the inequalities of i and j, and the INTEGERP-ness
; of i/j.
; ~/~/~/"
  )


;;;****************************************************************************
;;;
;;;    TRUNCATE and REM
;;;
;;;  We begin with TRUNCATE and REM since we will sometimes prove properties of
;;;  FLOOR from a definition of FLOOR in terms of TRUNCATE.  Since TRUNCATE
;;;  doesn't figure into our hardware specification, however, it's theory is
;;;  somewhat TRUNCATEd!
;;;
;;;****************************************************************************

(defthm truncate-rem-elim
  (implies
   (qr-guard x y)
   (equal (+ (rem x y) (* y (truncate x y)))
	  x))
  :rule-classes (:rewrite :elim)
  :hints
  (("Goal"
    :in-theory (enable rem)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section truncate-lemmas
; Rewrite: (+ (REM x y) (* y (TRUNCATE x y))) = x.
; ~/
; NB: This rule is also stored as an :ELIM rule.~/~/
; :cited-by rem-lemmas"
  )

(defthm truncate-=-x/y
  (implies
   (qr-guard x y)
   (equal (equal (truncate x y) (/ x y))
	  (integerp (/ x y))))
  :hints
  (("Goal" :in-theory
    (set-difference-theories (enable truncate equal-*-x-y-x)
			     '(commutativity-of-*))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:rewrite
    :corollary
    (implies
     (and (equal r (/ x y))
	  (integerp r)
	  (qr-guard x y))
     (equal (truncate x y) r))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section truncate-lemmas
; Rewrite: (TRUNCATE x y) = x/y, when x/y is an integer.
; ~/
; This rule is a corollary of a more general equality, which is also stored
; as a :REWRITE and :GENERALIZE rule.~/~/
; :cited-by integer-ratio-lemmas"
  )

;<  This is a fast and beautiful proof, using the :LINEAR rule NIQ-BOUNDS.

(defthm truncate-bounds
  (and
   (implies
    (and (>= x 0) (> y 0) (qr-guard x y))
    (and (< (- (/ x y) 1) (truncate x y))
	 (<= (truncate x y) (/ x y))))
   (implies
    (and (<= x 0) (< y 0) (qr-guard x y))
    (and (< (- (/ x y) 1) (truncate x y))
	 (<= (truncate x y) (/ x y))))
   (implies
    (and (>= x 0) (< y 0) (qr-guard x y))
    (and (<= (/ x y) (truncate x y))
	 (< (truncate x y) (+ (/ x y) 1))))
   (implies
    (and (<= x 0) (> y 0) (qr-guard x y))
    (and (<= (/ x y) (truncate x y))
	 (< (truncate x y) (+ (/ x y) 1)))))
  :rule-classes
  ((:linear :trigger-terms ((truncate x y))))

  :hints
  (("Goal" :in-theory (set-difference-theories (enable truncate
						       rational-implies2)
					       '(<-*-/-left <-*-/-right))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section truncate-lemmas
; Linear (D) : x/y - 1 < (TRUNCATE x y) <= x/y, when x/y >= 0;
;              x/y <= (TRUNCATE x y) < x/y + 1, when x/y =< 0.
; ~/
; This lemma `defines' TRUNCATE as a set of inequalties.  Many of the
; properties of TRUNCATE will be derived from this theorem.  Unfortunately,
; this lemma is implicated in thrashing in the linear arithmetic procedure
; unless the inequalties of X and Y can be decided, so it may need to be
; DISABLEd at times.  This lemma is stored as a :LINEAR rule for TRUNCATE
; exclusively since we consider it to be a property of TRUNCATE, and not a
; general property of (/ x y).

; The statement of the hypotheses of this lemma is critical for its
; proper application.  It is necessary for each inequality of x and y to
; stand alone in order to be relieveable by linear arithemetic.  ~/~/"
  )

;<  Without the :CASES hint, the inequality conditions simplify to a form
;that doesn't allow us to decide the sign of X, and the proof fails.  With
;the :CASES hint, we can decide the sign of X and the proof is obvious from
;TRUNCATE-BOUNDS.

(defthm truncate-type
  (implies
   (qr-guard x y)
   (and
    (equal (< (truncate x y) 0)
	   (or (and (<= x 0) (> y 0) (<= y (- x)))
	       (and (>= x 0) (< y 0) (<= (- y) x))))
    (equal (> (truncate x y) 0)
	   (or (and (>= x 0) (> y 0) (<= y x))
	       (and (<= x 0) (< y 0) (>= y x))))
    (equal (equal (truncate x y) 0)
	   (< (abs x) (abs y)))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:linear
    :corollary
    (implies
     (and (<= x 0) (> y 0) (<= y (- x)) (qr-guard x y))
     (< (truncate x y) 0)))
   (:linear
    :corollary
    (implies
     (and (>= x 0) (< y 0) (<= (- y) x) (qr-guard x y))
     (< (truncate x y) 0)))
   (:linear
    :corollary
    (implies
     (and (>= x 0) (> y 0) (<= y x) (qr-guard x y))
     (> (truncate x y) 0)))
   (:linear
    :corollary
    (implies
     (and (<= x 0) (< y 0) (>= y x) (qr-guard x y))
     (> (truncate x y) 0)))
   (:rewrite
    :corollary
    (implies
     (and (< (abs x) (abs y)) (qr-guard x y))
     (equal (truncate x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (<= x 0) (> y 0) (qr-guard x y))
     (<= (truncate x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (>= x 0) (< y 0) (qr-guard x y))
     (<= (truncate x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (>= x 0) (> y 0) (qr-guard x y))
     (>= (truncate x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (<= x 0) (< y 0) (qr-guard x y))
     (>= (truncate x y) 0))))
  :hints
  (("Goal"
    :cases ((< x 0) (> x 0))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section truncate-lemmas
; Various : Decide (TRUNCATE x y) < 0, (TRUNCATE x y) > 0, and
; (TRUNCATE x y) = 0 based on inequalities of x and y.
; ~/
; This rule is available in various forms: :REWRITE, :LINEAR,
; :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
; can decide the inequalities of X and Y the :LINEAR forms may thrash.~/~/"
  )

;< These follow immediately from the definition of TRUNCATE.  If we enter
;these lemmas in a theory that includes the :LINEAR rules for TRUNCATE we will
;observe severe thrashing in linear arithmetic, since these rules are
;independent of the signs of x and y.  So, we'll just prove them in the theory
;that prevails at the beginning of this book.

(encapsulate ()

  (local (in-theory (current-theory 'begin-quotient-remainder-lemmas)))
  (local (in-theory (enable truncate)))

  (local (defthm foo (equal (rationalp (- x))
                            (or (rationalp x)
                                (not (acl2-numberp x))))))

  (defthm truncate-minus
    (and (equal (truncate (- x) y)
		(- (truncate x y)))
	 (equal (truncate x (- y))
		(- (truncate x y))))
    :hints (("Goal" :in-theory (enable denominator-unary-minus)
	     :expand
	     (nonnegative-integer-quotient 0
					   (denominator (- (* x (/ y)))))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section truncate-lemmas
; Rewrite: (TRUNCATE (- x) y) = (- (TRUNCATE x y));
;          (TRUNCATE x (- y)) = (- (TRUNCATE x y)).
; ~/~/~/"
    )

  (defthm rewrite-truncate-x*y-z-left
    (equal (truncate (* x y) z)
	   (truncate y (/ z x)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section truncate-lemmas
; Rewrite (D): (TRUNCATE (* x y) z) = (TRUNCATE y (/ z x)), when x /= 0.
; ~/
; Since we don't presume any rewriting strategy for / vis-a-vis *, this
; often useful rule is exported DISABLEd.~/~/"
    )

  (in-theory (disable rewrite-truncate-x*y-z-left))

  (defthm rewrite-truncate-x*y-z-right
    (equal (truncate (* x y) z)
	   (truncate x (/ z y)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section truncate-lemmas
; Rewrite (D): (TRUNCATE (* x y) z) = (TRUNCATE x (/ z y)), when y /= 0.
; ~/
; Since we don't presume any rewriting strategy for / vis-a-vis *, this
; often useful rule is exported DISABLEd.~/~/"
    )

  (in-theory (disable rewrite-truncate-x*y-z-right))

  (defthm truncate-cancel-*
    (implies
     (qr-guard x y)
     (and (equal (truncate (* x y) y)
		 (truncate x 1))
	  (equal (truncate (* y x) y)
		 (truncate x 1))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section truncate-lemmas
; Rewrite: (TRUNCATE (* x y) y) = (TRUNCATE x 1).
; ~/
; NB: You get the commutted form as well.~/~/"
    ))

;<  The linear rules refuse to fire on their own.  From TRUNCATE-BOUNDS and
;NIQ-BOUNDS it is obvious that these are the same integers.

(defthm integer-truncate-as-niq
  (implies
   (and (integerp i)
	(integerp j)
	(force (not (equal j 0))))
   (equal (truncate i j)
	  (* (signum i) (signum j)
	     (nonnegative-integer-quotient (abs i) (abs j)))))
  :hints
  (("Goal"
    :in-theory (disable truncate-bounds niq-bounds <-*-/-right <-*-/-left)
    :use ((:instance truncate-bounds (x i) (y j))
	  (:instance niq-bounds (i (abs i)) (j (abs j))))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section truncate-lemmas
; Rewrite (D) : (TRUNCATE i j) =
;               (SIGNUM i) * (SIGNUM j) * (NIQ i j), for integers i,j.
; ~/
; This rule shows that TRUNCATE is the \"usual\" (i.e., FORTRAN-style)
; integer quotient for both positive and negative integers.~/~/"
  )

(in-theory (disable integer-truncate-as-niq))

#|

(defthm truncate-truncate-integer
  (implies
   (and (integerp i)
	(integerp j)
	(integerp k)
	(force (not (equal j 0)))
	(force (not (equal k 0))))
   (equal (truncate (truncate i j) k)
	  (truncate i (* j k))))
  :hints
  (("Goal"
    :in-theory (enable truncate))))
  :hints
  (("Goal"
    :in-theory (e/d (integer-truncate-as-niq niq-type niq-i/j-<-k
					     prefer-*-to-/)
		    (x-<-y*z))
    :use ((:instance x-<-y*z (x (abs i)) (y (abs j)) (z (abs k))))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section truncate-lemmas
; Rewrite: (TRUNCATE (TRUNCATE i j) k) = (TRUNCATE i (* j k))
;          for integers i,j,k.~/~/~/"
)
|#


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    REM
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defthm linearize-rem
  (implies
   (and (qr-guard x y)
	(force (rationalp z)))
   (and
    (equal (< (rem x y) z)
	   (if (> y 0)
	       (< (- (/ x y) (truncate x y)) (/ z y))
	     (> (- (/ x y) (truncate x y)) (/ z y))))
    (equal (> (rem x y) z)
	   (if (> y 0)
	       (> (- (/ x y) (truncate x y)) (/ z y))
	     (< (- (/ x y) (truncate x y)) (/ z y))))
    (equal (equal (rem x y) z)
	   (equal (- (/ x y) (truncate x y)) (/ z y)))))
  :hints
  (("Goal"
    :in-theory (enable rem prefer-*-to-/)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section rem-lemmas
; Rewrite (D): Transform (REM x y) < z, (REM x y) > z, and (REM x y) = z
; into an equivalent TRUNCATE expression suitable for reasoning about with
; TRUNCATE-BOUNDS and other theorems about TRUNCATE.
; ~/
; Since this lemma can be considered a `definition' of REM, it is exported
; DISABLED.~/~/"
  )

(in-theory (disable linearize-rem))

(defthm rem-=-0
  (implies
   (qr-guard x y)
   (equal (equal (rem x y) 0)
	  (integerp (/ x y))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:rewrite
    :corollary
    (implies
     (and (integerp (/ x y))
	  (qr-guard x y))
     (equal (rem x y) 0))))
  :hints
  (("Goal"
    :in-theory (enable linearize-rem)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section rem-lemmas
; Rewrite: (REM x y) = 0, when x/y is an integer;
; ~/
; NB: This rule is a corollary of a more general equality.
; The equality is also stored as a :REWRITE and :GENERALIZE rule.~/~/
; :cited-by integer-ratio-lemmas"
  )

(defthm rem-x-y-=-x
  (implies
   (qr-guard x y)
   (equal (equal (rem x y) x)
	  (< (abs x) (abs y))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:rewrite
    :corollary
    (implies
     (and (< (abs x) (abs y))
	  (qr-guard x y))
     (equal (rem x y) x))))
  :hints
  (("Goal"
    :in-theory (enable linearize-rem)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section rem-lemmas
; Rewrite: (REM x y) = x, when |x| < |y|.
; ~/
; This rule is a corollary of a more general equality which is also stored as
; a :REWRITE and :GENERALIZE rule.~/~/"
  )

(defthm integerp-rem
  (implies
   (and (integerp i)
	(integerp j)
	(force (not (equal j 0))))
   (integerp (rem i j)))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable rem)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section rem-lemmas
; Type-Prescription: (REM i j) is an integer, when i and j are integers.
; ~/~/~/"
  )

;<  Again, this rule is an easy consequence of TRUNCATE-BOUNDS, but (/ x y)
;is too `heavy' to let it fire naturally, so we have to :USE it.

(defthm rem-bounds
  (and
   (implies
    (and (>= x 0)
	 (qr-guard x y))
    (< (rem x y) (abs y)))
   (implies
    (and (<= x 0)
	 (qr-guard x y))
    (> (rem x y) (- (abs y)))))
  :rule-classes
  ((:linear :trigger-terms ((rem x y)))
   (:generalize))
  :hints
  (("Goal"
    :in-theory (e/d (linearize-rem) (truncate-bounds))
    :use truncate-bounds))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section rem-lemmas
; Linear: Useful forms of the fact that |(REM x y)| < |y|.
; ~/
; This lemma is also stored as a :GENERALIZE rules.~/~/"
  )

(defthm rem-type
  (implies
   (qr-guard x y)
   (and
    (equal (< (rem x y) 0)
	   (and (< x 0)
		(not (integerp (/ x y)))))
    (equal (> (rem x y) 0)
	   (and (> x 0)
		(not (integerp (/ x y)))))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:linear
    :corollary
    (implies
     (and (< x 0) (not (integerp (/ x y))) (qr-guard x y))
     (< (rem x y) 0)))
   (:linear
    :corollary
    (implies
     (and (> x 0) (not (integerp (/ x y))) (qr-guard x y))
     (> (rem x y) 0)))
   (:linear
    :corollary
    (implies
     (and (<= x 0) (qr-guard x y))
     (<= (rem x y) 0)))
   (:linear
    :corollary
    (implies
     (and (>= x 0) (qr-guard x y))
     (>= (rem x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (< x 0) (not (integerp (/ x y))) (qr-guard x y))
     (< (rem x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (> x 0) (not (integerp (/ x y))) (qr-guard x y))
     (> (rem x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (<= x 0) (qr-guard x y))
     (<= (rem x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (>= x 0) (qr-guard x y))
     (>= (rem x y) 0))))
  :hints
  (("Goal"
    :in-theory (set-difference-theories
                (enable linearize-rem)
                '(<-*-/-right <-*-/-left))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section rem-lemmas
;  Various : Decide (REM x y) < 0 and (REM x y) > 0 based on the sign of
;  x and the INTEGERP-ness of x/y.
;  ~/
;  This rule is stored as appropriate :REWRITE, :LINEAR, :GENERALIZE, and
;  :TYPE-PRESCRIPTION rules.~/~/"
  )

(defthm rem-minus
  (implies
   (qr-guard x y)
   (and
    (equal (rem (- x) y)
	   (- (rem x y)))
    (equal (rem x (- y))
	   (* (signum y) (signum y) (rem x y)))))

  :hints
  (("Goal"
    :in-theory (enable linearize-rem)
    :expand (rem x y)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section rem-lemmas
; Rewrite: (REM (- x) y) = (- (REM x y));
;          (REM x (- y)) = (SIGNUM x) * (SIGNUM y) * (REM x y)).
; ~/~/~/"
  )



;;;****************************************************************************
;;;
;;;    FLOOR and MOD
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;  We'll sometimes use this lemma which allows us to prove properties of
;  FLOOR from properties of TRUNCATE.

(defthm floor-as-truncate
  (implies
   (qr-guard x y)
   (equal (floor x y)
	  (if (or (integerp (/ x y))
		  (> (/ x y) 0))
	      (truncate x y)
	    (- (truncate x y) 1))))
  :hints
  (("Goal" :in-theory (enable floor truncate)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Rewrite: Rewrite (FLOOR x y) to a function of (TRUNCATE x y).
; ~/~/~/"
  )

(in-theory (disable floor-as-truncate))

(defthm floor-mod-elim
  (implies (force (acl2-numberp x))
	   (equal (+ (mod x y) (* y (floor x y))) x))
  :rule-classes (:rewrite :elim)
  :hints (("Goal" :in-theory (enable mod)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Rewrite: (+ (MOD x y) (* y (FLOOR x y))) = x.
; ~/
; NB: This rule is also stored as an :ELIM rule.~/~/
; :cited-by mod-lemmas"
  )

(defthm floor-=-x/y
  (implies
   (qr-guard x y)
   (equal (equal (floor x y) (/ x y))
	  (integerp (/ x y))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:rewrite
    :corollary
    (implies
     (and (equal r (/ x y))
	  (integerp r)
	  (qr-guard x y))
     (equal (floor x y) r)))   )
  :hints (("Goal" :in-theory
	   (set-difference-theories (enable floor equal-*-x-y-x)
				    '(commutativity-of-*))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Rewrite: (FLOOR x y) = x/y, when x/y is an integer.
; ~/
; This rule is a corollary of a more general equality which is also stored as
; a :REWRITE and :GENERALIZE rule.~/~/"
  )

;< Another beautiful proof from NIQ-BOUNDS.

(defthm floor-bounds
  (implies
   (qr-guard x y)
   (and (< (- (/ x y) 1) (floor x y))
	(<= (floor x y) (/ x y))))
  :rule-classes
  ((:linear :trigger-terms ((floor x y)))
   (:generalize))
  :hints (("Goal" :in-theory
	   (set-difference-theories (enable floor rational-implies2)
				    '(<-*-/-left <-*-/-right))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Linear (D) : x/y - 1 < (FLOOR x y) <= x/y.
; ~/
; This lemma `defines' FLOOR as a set of inequalties.  Many of the properties
; of FLOOR will be derived from this theorem.  Unfortunately, this lemma is
; implicated in thrashing in the linear arithmetic procedure and must be
; DISABLEd at times.  This lemmas is stored as a :LINEAR rule for FLOOR
; exclusively since we consider it to be a property of FLOOR, and not a
; general property of (/ x y).~/~/"
  )

;< We need to consider the :CASES to get FLOOR-BOUNDS to do its job.  This
;proof does 2 eliminations (considering (FLOOR x y) = -1) but it goes
;through.  If we simply :USE FLOOR-BOUNDS with the same :CASES it also works
;and takes about the same amount of time.  I'll bet that it could get the
;(FLOOR x y) = -1 cases with FLOOR-BOUNDS if we let FLOOR-BOUNDS trigger on
;(/ x y).

;; The lemma FLOOR-TYPE had too many cases, so I split it in to 4 lemmas:
;; FLOOR-TYPE-1, FLOOR-TYPE-2, FLOOR-TYPE-3 and FLOOR-TYPE-4.
;; A. Flatau 17-Nov-1994

(defthm floor-type-1
  (implies (qr-guard x y)
	   (iff (< (floor x y) 0)
                (or (and (< x 0) (> y 0))
                    (and (> x 0) (< y 0)))))
  :hints (("Goal" :cases ((< (/ x y) 0) (> (/ x y) 0))
	   :in-theory (enable normalize-<-/-to-*-3)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (qr-guard x y)
                           (equal (< (floor x y) 0)
                                  (or (and (< x 0) (> y 0))
                                      (and (> x 0) (< y 0))))))
		 (:generalize
                  :corollary
                  (implies (qr-guard x y)
                           (equal (< (floor x y) 0)
                                  (or (and (< x 0) (> y 0))
                                      (and (> x 0) (< y 0))))))
		 (:linear
		  :corollary
		  (implies
		   (and (< x 0) (> y 0) (qr-guard x y))
		   (< (floor x y) 0)))
		 (:linear :corollary
			  (implies (and (> x 0) (< y 0) (qr-guard x y))
				   (< (floor x y) 0)))
		 (:type-prescription :corollary
				     (implies (and (< x 0)
						   (> y 0)
						   (qr-guard x y))
					      (< (floor x y) 0)))
		 (:type-prescription :corollary
				     (implies (and (> x 0)
						   (< y 0)
						   (qr-guard x y))
					      (< (floor x y) 0))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Decide (FLOOR x y) < 0  based on inequalities of x and y.~/
; This rule is available in various forms: :REWRITE, :LINEAR,
; :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
; can decide the inequalities of x and y the :LINEAR forms may thrash.~/~/"
  )


(defthm floor-type-2
  (implies (qr-guard x y)
	   (equal (> (floor x y) 0)
		  (or (and (>= x 0) (> y 0) (<= y x))
		      (and (<= x 0) (< y 0) (>= y x)))))
  :hints (("Subgoal 6" :cases ((<= x 0) (<= 0 x)))
          ("Subgoal 2" :cases ((<= x 0) (<= 0 x))))
  :rule-classes ((:rewrite)
		 (:generalize)
		 (:linear :corollary
			  (implies (and (>= x 0) (> y 0) (<= y x)
					(qr-guard x y))
				   (> (floor x y) 0)))
		 (:linear :corollary
			  (implies (and (<= x 0) (< y 0) (>= y x)
					(qr-guard x y))
				   (> (floor x y) 0))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Decide (FLOOR x y) > 0  based on inequalities of x and y. ~/
; This rule is available in various forms: :REWRITE, :LINEAR,
; :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
; can decide the inequalities of x and y the :LINEAR forms may thrash.~/~/"
  )

(defthm floor-type-3
  (implies (qr-guard x y)
	   (equal (equal (floor x y) 0)
		  (or (and (>= x 0) (> y 0) (< x y))
		      (and (<= x 0) (< y 0) (> x y)))))

  :hints (("Goal" :cases ((< (/ x y) 0) (> (/ x y) 0))))
  :rule-classes ((:rewrite)
		 (:generalize)
		 (:rewrite :corollary
			   (implies (and (>= x 0) (> y 0) (< x y)
					 (qr-guard x y))
				    (equal (floor x y) 0)))
		 (:rewrite :corollary
			   (implies (and (<= x 0) (< y 0) (> x y)
					 (qr-guard x y))
				    (equal (floor x y) 0)))
		 (:type-prescription :corollary
				     (implies (and (>= x 0) (> y 0)
						   (qr-guard x y))
					      (>= (floor x y) 0)))
		 (:type-prescription :corollary
				     (implies (and (<= x 0) (< y 0)
						   (qr-guard x y))
					      (>= (floor x y) 0))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Decide (FLOOR x y) > 0  based on inequalities of x and y. ~/
; This rule is available in various forms: :REWRITE, :LINEAR,
; :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
; can decide the inequalities of x and y the :LINEAR forms may thrash.~/~/"
  )

(defthm floor-type-4
  (implies (qr-guard x y)
	   (equal (equal (floor x y) -1)
		  (or (and (< x 0) (> y 0) (<= (- x) y))
		      (and (> x 0) (< y 0) (<= x (- y))))))
  :rule-classes ((:rewrite)
		 (:generalize)
		 (:rewrite :corollary
			   (implies (and (> x 0) (< y 0) (<= x (- y))
					 (qr-guard x y))
				    (equal (floor x y) -1)))
		 (:rewrite :corollary
			   (implies (and (< x 0) (> y 0) (<= (- x) y)
					 (qr-guard x y))
				    (equal (floor x y) -1))))
  :hints (("Goal" :cases ((< (/ x y) 0) (> (/ x y) 0)))
	  ("Subgoal 2"
	   :in-theory (set-difference-theories (enable <-+-negative-0-1
						       <-+-negative-0-2
						       normalize-<-/-to-*-3)
					       '(floor-bounds))
	   :use (:instance floor-bounds (x x) (y y))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Decide (FLOOR x y) = -1  based on inequalities of x and y.~/
; This rule is available in various forms: :REWRITE, :LINEAR,
; :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
; can decide the inequalities of x and y the :LINEAR forms may thrash.~/~/"
  )

(deftheory floor-type-linear
  '((:linear floor-type-1 . 1)
    (:linear floor-type-1 . 2)
    (:linear floor-type-2 . 1)
    (:linear floor-type-2 . 2))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; A theory of the :LINEAR rules created by the lemmas FLOOR-TYPE-1 and
; FLOOR-TYPE-2.~/
; These rules are implicated in thrashing linear arithmetic, so we provide
; this theory which can be DISABLED if it becomes a problem.~/~/"
  )

;< These follow immediately from the definition of FLOOR.  If we enter
;these lemmas in a theory that includes the :LINEAR rules for FLOOR we will
;observe severe thrashing in linear arithmetic, since these rules are
;independent of the signs of x and y.  So, we'll just prove them in the theory
;that prevails at the beginning of this book.

(encapsulate ()

  (local (in-theory (current-theory 'begin-quotient-remainder-lemmas)))
  (local (in-theory (enable floor)))

  (defthm floor-minus
    (and
     (implies
      (qr-guard x y)
      (equal (floor (- x) y)
	     (if (integerp (* x (/ y)))
		 (- (floor x y))
	       (- (- (floor x y)) 1))))
     (implies
      (qr-guard x y)
      (equal (floor x (- y))
	     (if (integerp (* x (/ y)))
		 (- (floor x y))
	       (- (- (floor x y)) 1)))))
    :hints (("Goal" :in-theory (enable DENOMINATOR-UNARY-MINUS)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section floor-lemmas
; Rewrite: (FLOOR (- x) y) =
;          (IF (INTEGERP (* x (/ y)))
;              (- (FLOOR x y))
;            (- (- (FLOOR x y)) 1)));
;          Rhs identical for -y.
; ~/~/~/"
    )

  (defthm rewrite-floor-x*y-z-left
    (implies
     (and (rationalp x)
	  (not (equal x 0))
	  (rationalp y)
	  (force (rationalp z))
	  (force (not (equal z 0))))
     (equal (floor (* x y) z)
	    (floor y (/ z x))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section floor-lemmas
; Rewrite (D): (FLOOR (* x y) z) = (FLOOR y (/ z x)), when x /= 0.
; ~/
; Since we don't presume any rewriting strategy for / vis-a-vis *, this
; often useful rule is exported DISABLEd.~/~/"
    )

  (in-theory (disable rewrite-floor-x*y-z-left))

  (defthm rewrite-floor-x*y-z-right
    (implies
     (and (rationalp x)
	  (rationalp y)
	  (not (equal y 0))
	  (force (rationalp z))
	  (force (not (equal z 0))))
     (equal (floor (* x y) z)
	    (floor x (/ z y))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section floor-lemmas
; Rewrite: (FLOOR (* x y) z) = (FLOOR x (/ z y)), when y /= 0.
; ~/
; Since we don't presume any rewriting strategy for / vis-a-vis *, this
; often useful rule is exported DISABLEd.~/~/"
    )

  (in-theory (disable rewrite-floor-x*y-z-right))

  (defthm floor-cancel-*
    (implies
     (qr-guard x y)
     (and (equal (floor (* x y) y)
		 (floor x 1))
	  (equal (floor (* y x) y)
		 (floor x 1))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section floor-lemmas
; Rewrite: (FLOOR (* x y) y) = (FLOOR x 1).
; ~/
; NB: You get the commuted form as well.~/~/"
    )

    (defthm floor-cancel-*-2
      (implies
       (and (rationalp x)
	    (not (equal x 0))
	    (rationalp y)
	    (rationalp z)
	    (not (equal z 0)))
       (equal (floor (* x y) (* x z))
	      (floor y z)))
      :hints
      (("Goal"
	:in-theory (enable rewrite-floor-x*y-z-left)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;     :doc
;     ":doc-section floor-lemmas
; Rewrite: (FLOOR (* x y) (* x z)) = (FLOOR y z).
; ~/~/~/"
      ))

;  This proof is only this complicated because I wanted to prove the most
;  general thing possible.

(encapsulate ()

  (local
   (defthm crock0
     (implies
      (and (< 1 y)
	   (< 0 x)
	   (qr-guard x y))
      (< (/ x y) x))
     :rule-classes :linear))

  (local
   (defthm crock1
     (implies
      (and (<= (+ 1 1) y)
	   (< x 0)
	   (qr-guard x y))
      (<= (* x y) (+ x x)))
     :rule-classes :linear
     :hints (("Goal" :in-theory (disable <-*-left-cancel (binary-+))
	      :use (:instance <-*-left-cancel (z x) (x 2) (y y))))))

  (local
   (defthm crock2
     (implies
      (and (<= 2 y)
	   (< x 0)
	   (< y (- x))
	   (qr-guard x y))
      (< x (- (/ x y) 1)))
     :rule-classes :linear
     :hints
     (("Goal"
       :in-theory (e/d (prefer-*-to-/) (<-*-left-cancel))
       :use (:instance <-*-left-cancel (z y) (x x) (y (- (/ x y) 1)))))))

  (defthm justify-floor-recursion
    (implies
     (qr-guard x y)
     (and
      (implies
       (and (< 0 x)
	    (< 1 y))
       (< (floor x y) x))
      (implies
       (and (< x -1)
	    (<= 2 y))
       (< x (floor x y)))))
    :hints
    (("Goal"
      :use ((:instance floor-bounds (x x) (y y))))
     ("Goal'"
      :cases ((< 0 x) (< y (- x)))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section floor-lemmas
; Rewrite: (FLOOR x y) < x, when x > 0 and y > 1;
;          x < (FLOOR x y), when x < -1 and y >= 2.
; ~/
; This theorem justifies recursion by FLOOR using the measure ACL2-COUNT,
; which for integers i is simply (ABS i).  Thus, this theorem won't justify
; a simple recursion by a negative y, since (FLOOR 1 y) = -1 for negative y,
; and (ABS -1) = (ABS 1).  For the most general case that includes negative
; y one would need to define a different measure that could handle this
; condition.~/~/"
    ))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    MOD
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defthm linearize-mod
  (implies
   (and (qr-guard x y)
	(force (rationalp z)))
   (and
    (equal (< (mod x y) z)
	   (if (> y 0)
	       (< (- (/ x y) (floor x y)) (/ z y))
	     (> (- (/ x y) (floor x y)) (/ z y))))
    (equal (> (mod x y) z)
	   (if (> y 0)
	       (> (- (/ x y) (floor x y)) (/ z y))
	     (< (- (/ x y) (floor x y)) (/ z y))))
    (equal (equal (mod x y) z)
	   (equal (- (/ x y) (floor x y)) (/ z y)))))
  :hints
  (("Goal"
    :in-theory (enable mod prefer-*-to-/)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Rewrite (D): Transform (MOD x y) < z, (MOD x y) > z, and (MOD x y) = z
; into an equivalent FLOOR expression suitable for reasoning about with
; FLOOR-BOUNDS and other theorems about FLOOR.
; ~/
; Since this lemma can be considered a `definition' of MOD, it is exported
; DISABLED.~/~/"
  )

(in-theory (disable linearize-mod))

(defthm mod-=-0
  (implies
   (qr-guard x y)
   (equal (equal (mod x y) 0)
	  (integerp (/ x y))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:rewrite
    :corollary
    (implies
     (and (integerp (/ x y))
	  (qr-guard x y))
     (equal (mod x y) 0))))
  :hints (("Goal" :in-theory (enable linearize-mod)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Rewrite: (MOD x y) = 0, when x/y is an integer;
; ~/
; This rule is a corollary of a more general equality.
; The equality is also stored as a :REWRITE and :GENERALIZE rule.~/~/
; :cited-by integer-ratio-lemmas"
  )

(defthm mod-x-y-=-x
  (implies
   (qr-guard x y)
   (equal (equal (mod x y) x)
	  (or (and (>= x 0) (> y 0) (< x y))
	      (and (<= x 0) (< y 0) (> x y)))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:rewrite
    :corollary
    (implies
     (and (>= x 0) (> y 0) (< x y) (qr-guard x y))
     (equal (mod x y) x)))
   (:rewrite
    :corollary
    (implies
     (and (<= x 0) (< y 0) (> x y) (qr-guard x y))
     (equal (mod x y) x))))
  :hints (("Goal" :in-theory (enable linearize-mod)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Rewrite: (MOD x y) = x, when |x| <= |y| and x and y have the same sign.
; ~/
; This rule is a corollary of a more general equality which is also stored as
; :REWRITE and :GENERALIZE rules.~/~/"
  )

;<  Again, we need to :USE FLOOR-BOUNDS to make this proof quick.

(encapsulate nil

   (local (defthm another-crock
	    (equal (equal (- x) 1) (equal x -1))))

   (defthm mod-x-y-=-x+y
     (implies
      (qr-guard x y)
      (equal (equal (mod x y) (+ x y))
	     (or (and (> x 0) (< y 0) (<= x (- y)))
		 (and (< x 0) (> y 0) (<= (- x) y)))))
     :rule-classes
     ((:rewrite)
      (:generalize)
      (:rewrite
       :corollary
       (implies
	(and (> x 0) (< y 0) (<= x y) (qr-guard x y))
	(equal (mod x y) (+ x y))))
      (:rewrite
       :corollary
       (implies
	(and (< x 0) (> y 0) (<= (- x) y) (qr-guard x y))
	(equal (mod x y) (+ x y)))))
     :hints
     (("Goal"
       :in-theory (e/d (linearize-mod) (floor-bounds))
       :use floor-bounds))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;    :doc
;    ":doc-section mod-lemmas
; Rewrite: (MOD x y) = x + y, when |x| <= |y| and x and y have different
; signs and x /= 0.
; ~/
; This rule is a corollary of a more general equality which is also stored as
; :REWRITE and :GENERALIZE rules.~/~/"
     ))

;; Added the :rule-classes :rewrite as this seems necessary at times.
;; A. Flatau  1-Dec-1994
(defthm integerp-mod
  (implies
   (and (integerp i)
	(integerp j))
   (integerp (mod i j)))
  :rule-classes (:type-prescription :rewrite)
  :hints
  (("Goal"
    :in-theory (enable mod)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Type-Prescription: (MOD i j) is an integer, when i and j are integers.
; ~/~/~/"
  )

(defthm mod-bounds
  (and
   (implies
    (and (> y 0)
	 (qr-guard x y))
    (< (mod x y) y))
   (implies
    (and (< y 0)
	 (qr-guard x y))
    (> (mod x y) y)))
  :rule-classes
  ((:linear :trigger-terms ((mod x y)))
   (:generalize))
  :hints
  (("Goal"
    :in-theory (e/d (linearize-mod) (floor-bounds))
    :use floor-bounds))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Linear: Useful forms of the fact that |(MOD x y)| < |y|.
; ~/
; This lemma is also stored as a :GENERALIZE rule.~/~/"
  )

(defthm mod-type
  (implies
   (qr-guard x y)
   (and
    (equal (< (mod x y) 0)
	   (and (< y 0)
		(not (integerp (/ x y)))))
    (equal (> (mod x y) 0)
	   (and (> y 0)
		(not (integerp (/ x y)))))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:linear
    :corollary
    (implies
     (and (< y 0) (not (integerp (/ x y))) (qr-guard x y))
     (< (mod x y) 0)))
   (:linear
    :corollary
    (implies
     (and (> y 0) (not (integerp (/ x y))) (qr-guard x y))
     (> (mod x y) 0)))
   (:linear
    :corollary
    (implies
     (and (<= y 0) (qr-guard x y))
     (<= (mod x y) 0)))
   (:linear
    :corollary
    (implies
     (and (>= y 0) (qr-guard x y))
     (>= (mod x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (< y 0) (not (integerp (/ x y))) (qr-guard x y))
     (< (mod x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (> y 0) (not (integerp (/ x y))) (qr-guard x y))
     (> (mod x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (<= y 0) (qr-guard x y))
     (<= (mod x y) 0)))
   (:type-prescription
    :corollary
    (implies
     (and (>= y 0) (qr-guard x y))
     (>= (mod x y) 0))))
  :hints
  (("Goal"
    :in-theory (enable linearize-mod)
    :use floor-bounds))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Various: Decide (MOD x y) < 0 and (MOD x y) > 0 based on the sign of
; y and the INTEGERP-ness of x/y.
; ~/
; This rule is also stored as appropriate :REWRITE, :LINEAR, :GENERALIZE,
; and :TYPE-PRESCRIPTION rules.~/~/"
  )

(deftheory mod-type-linear
  '((:linear mod-type . 1)
    (:linear mod-type . 2)
    (:linear mod-type . 3)
    (:linear mod-type . 4))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; A theory of the :LINEAR rules created by the lemma MOD-TYPE.
; ~/
; These rules are implicated in thrashing linear arithmetic, so we provide
; this theory which can be DISABLED if it becomes a problem.~/~/"
  )

(defthm mod-minus
  (implies
   (qr-guard x y)
   (and (equal (mod (- x) y)
	       (if (integerp (/ x y))
		   0
		 (- y (mod x y))))
	(equal (mod x (- y))
	       (if (integerp (/ x y))
		   0
		 (- (mod x y) y)))))
  :hints
  (("Goal"
    :in-theory (enable linearize-mod)
    :expand (mod x y)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Rewrite: (MOD (- x) y) =
;          (IF (INTEGERP (/ x y))
;              0
;            (- y (MOD x y)));
;          (MOD x (- y)) =
;          (IF (INTEGERP (/ x y))
;              0
;            (- (MOD x y) y)).
;  ~/~/~/
; :cited-by integer-ratio-lemmas"
  )

(encapsulate ()

  (local (in-theory (current-theory 'begin-quotient-remainder-lemmas)))

  (defthm simplify-mod-*
    (implies
     (and (integerp x)
	  (not (equal x 0))
	  (integerp y)
	  (integerp z)
	  (not (equal z 0)))
     (equal (mod (* x y) (* x z))
	    (* x (mod y z))))
  :hints
  (("Goal"
    :in-theory (enable mod floor-cancel-*-2)))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Addition Cancellation theory for FLOOR and MOD
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;< This next section of lemmas has nothing to do with the :LINEAR theory of
;FLOOR and MOD, so we DISABLE the key :LINEAR lemmas to avoid thrashing.

(local (in-theory (disable floor-bounds floor-type-1 floor-type-2
			   floor-type-3 floor-type-4 mod-bounds mod-type)))

;  These LOCAL theorems will be superceded by CANCEL-FLOOR-+,
;  CANCEL-FLOOR-+-3, CANCEL-MOD-+, and CANCEL-MOD-+-3.

(local
 (defthm floor-x+i*y-y
   (implies
    (and (integerp i)
	 (qr-guard x y))
    (and
     (equal (floor (+ x (* i y)) y)
	    (+ i (floor x y)))
     (equal (floor (+ x (* y i)) y)
	    (+ i (floor x y)))
     (equal (floor (- x (* i y)) y)
	    (- (floor x y) i))
     (equal (floor (- x (* y i)) y)
	    (- (floor x y) i))))
   :hints
   (("Goal"
     :use ((:instance floor-bounds (x (+ x (* i y))) (y y))
	   (:instance floor-bounds (x (- x (* i y))) (y y))
	   (:instance floor-bounds (x x) (y y)))))))

(local
 (defthm floor-x+y+i*z-z
   (implies
    (and (integerp i)
	 (force (rationalp x))
	 (qr-guard y z))
    (and
     (equal (floor (+ x y (* i z)) z)
	    (+ i (floor (+ x y) z)))
     (equal (floor (+ x y (* z i)) z)
	    (+ i (floor (+ x y) z)))
     (equal (floor (+ x y (- (* z i))) z)
	    (- (floor (+ x y) z) i))
     (equal (floor (+ x y (- (* i z))) z)
	    (- (floor (+ x y) z) i))))
   :hints
   (("Goal"
     :in-theory (disable floor-x+i*y-y)
     :use ((:instance floor-x+i*y-y (x (+ x y)) (y z)))))))

;;;(local  modified by PG to export thm

 (defthm mod-x+i*y-y
   (implies
    (and (integerp i)
	 (qr-guard x y))
    (and
     (equal (mod (+ x (* i y)) y)
	    (mod x y))
     (equal (mod (+ x (* y i)) y)
	    (mod x y))
     (equal (mod (+ x (- (* i y))) y)
	    (mod x y))
     (equal (mod (+ x (- (* y i))) y)
	    (mod x y))))
   :hints
   (("Goal"
     :in-theory (enable mod))))

;;; )

(local
 (defthm mod-x+y+i*z-z
   (implies
    (and (integerp i)
	 (force (rationalp x))
	 (qr-guard y z))
    (and
     (equal (mod (+ x y (* i z)) z)
	    (mod (+ x y) z))
     (equal (mod (+ x y (* z i)) z)
	    (mod (+ x y) z))
     (equal (mod (+ x y (- (* i z))) z)
	    (mod (+ x y) z))
     (equal (mod (+ x y (- (* z i))) z)
	    (mod (+ x y) z))))
   :hints
   (("Goal"
     :in-theory (disable mod-x+i*y-y)
     :use ((:instance mod-x+i*y-y (x (+ x y)) (y z)))))))

(encapsulate ()

  (local
   (defthm floor-+-crock
     (implies
      (and (rationalp x)
	   (rationalp y)
	   (rationalp z)
	   (syntaxp (and (eq x 'x) (eq y 'y) (eq z 'z))))
      (equal (floor (+ x y) z)
	     (floor (+ (+ (mod x z) (mod y z))
		       (* (+ (floor x z) (floor y z)) z)) z)))))

  (defthm floor-+
    (implies
     (and (force (rationalp x))
	  (force (rationalp y))
	  (force (rationalp z))
	  (force (not (equal z 0))))
     (equal (floor (+ x y) z)
	    (+ (floor (+ (mod x z) (mod y z)) z)
	       (+ (floor x z) (floor y z)))))
    :hints (("Goal" :in-theory (union-theories (disable associativity-of-+
							commutativity-2-of-+
							associativity-of-*
							commutativity-2-of-*
							distributivity)
					       '(rationalp-+ mod))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section floor-lemmas
;  Rewrite (D): (FLOOR (+ x y) z) =
;  (FLOOR x z) + (FLOOR y z) + (FLOOR (+ (MOD x z) (MOD y z)) z).
;  ~/

;  As this rule could easily loop it is exported DISABLEd.  Don't ENABLE this
;  lemma unless you are sure that the FLOOR/MOD term will simplify, or else
;  put SYNTAXP guards on the variables x, y, and/or z.~/~/"
    )

  (in-theory (disable floor-+)))

(encapsulate ()

  (local
   (defthm mod-+-crock
     (implies
      (and (rationalp x)
	   (rationalp y)
	   (rationalp z)
	   (not (equal z 0))
	   (syntaxp (and (eq x 'x) (eq y 'y) (eq z 'z))))
      (equal (mod (+ x y) z)
	     (mod (+ (+ (mod x z) (mod y z))
		     (* (+ (floor x z) (floor y z)) z)) z)))))

  (defthm mod-+
    (implies
     (and (force (rationalp x))
	  (force (rationalp y))
	  (force (rationalp z))
	  (force (not (equal z 0))))
     (equal (mod (+ x y) z)
	    (mod (+ (mod x z) (mod y z)) z)))
    :hints (("Goal" :in-theory (union-theories (disable associativity-of-+
							commutativity-2-of-+
							associativity-of-*
							commutativity-2-of-*
							distributivity)
					       '(rationalp-+ mod))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section mod-+
;    Rewrite (D): (MOD (+ x y) z) = (MOD (+ (MOD x z) (MOD y z)) z).
;  ~/

;  As this rule could easily loop it is exported DISABLEd.  Don't ENABLE this
;  lemma unless you are sure that the MOD/MOD term will simplify, or else
;  put SYNTAXP guards on the variables x, y, and/or z.~/~/"
    )

  (in-theory (disable mod-+)))

(encapsulate ()

  (local
   (defthm crock0
     (implies
      (and (integerp i)
	   (integerp (* x y)))
      (integerp (* x y i)))))

  (defthm rewrite-floor-mod
    (implies
     (and (equal i (/ y z))
	  (integerp i)
	  (qr-guard x y)
	  (qr-guard x z))
     (equal (floor (mod x y) z)
	    (- (floor x z) (* i (floor x y)))))
    :hints
    (("Goal"
      :in-theory (enable mod)
      :use ((:instance floor-+ (x x) (y (- (* y (floor x y)))) (z z)))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section floor-lemmas
; Rewrite: (FLOOR (MOD x y) z) = (FLOOR x z) - i*(FLOOR x y), when i = y/z
; is an integer.
; ~/~/~/
; :cited-by integer-ratio-lemmas"
    )

  (defthm rewrite-mod-mod
    (implies
     (and (equal i (/ y z))
	  (integerp i)
	  (qr-guard x y)
	  (qr-guard y z))
     (equal (mod (mod x y) z)
	    (mod x z)))
    :hints
    (("Goal"
      :expand ((mod x y) (mod x z))
      :use ((:instance mod-+ (x x) (y (- (* y (floor x y)))) (z z)))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section mod-lemmas
; Rewrite: (MOD (MOD x y) z) = (MOD x z), when y/z is an integer.
; ~/~/~/
; :cited-by integer-ratio-lemmas"
    ))

(defthm cancel-floor-+
  (implies
   (and (equal i (/ x z))
	(integerp i)
	(force (rationalp x))
	(force (rationalp y))
	(force (rationalp z))
	(force (not (equal z 0))))
   (and
    (equal (floor (+ x y) z)
	   (+ i (floor y z)))
    (equal (floor (+ y x) z)
	   (+ i (floor y z)))))
  :hints
  (("Goal"
    :in-theory (enable floor-+)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Rewrite: (FLOOR (+ x y) z) = x/z + (FLOOR y z), when x/z is an integer;
; also the commutative form.
; ~/~/~/
; :cited-by integer-ratio-lemmas"
  )

(defthm cancel-floor-+-3
  (implies
   (and (equal i (/ y z))
	(integerp i)
	(force (rationalp w))
	(force (rationalp x))
	(force (rationalp y))
	(force (rationalp z))
	(force (not (equal z 0))))
   (equal (floor (+ w x y) z)
	  (+ i (floor (+ w x) z))))
  :hints
  (("Goal"
    :in-theory (disable cancel-floor-+)
    :use ((:instance cancel-floor-+ (x y) (y (+ w x)) (z z)))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Rewrite: (FLOOR (+ w x y) z) = y/z + (FLOOR (+ w x) z), when y/z is an
; integer.
; ~/~/~/
; :cited-by integer-ratio-lemmas"
  )

(defthm cancel-mod-+
  (implies
   (and (equal i (/ x z))
	(integerp i)
	(force (rationalp x))
	(force (rationalp y))
	(force (rationalp z))
	(force (not (equal z 0))))
   (and
    (equal (mod (+ x y) z)
	   (mod y z))
    (equal (mod (+ y x) z)
	   (mod y z))))
  :hints
  (("Goal"
    :in-theory (enable mod-+)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Rewrite: (MOD (+ x y) z) = (MOD y z), when x/z is an integer;
; also the commutative form.
; ~/~/~/
; :cited-by integer-ratio-lemmas"
  )

(defthm cancel-mod-+-3
  (implies
   (and (equal i (/ y z))
	(integerp i)
	(force (rationalp w))
	(force (rationalp x))
	(force (rationalp y))
	(force (rationalp z))
	(force (not (equal z 0))))
   (equal (mod (+ w x y) z)
	  (mod (+ w x) z)))
  :hints
  (("Goal"
    :in-theory (disable cancel-mod-+)
    :use ((:instance cancel-mod-+ (x y) (y (+ w x)) (z z)))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Rewrite: (MOD (+ w x y) z) = (MOD (+ w x) z), when y/z is an integer.
; ~/~/~/
; :cited-by integer-ratio-lemmas"
  )

(defthm not-rationalp-rationalp-plus
 (implies (and (acl2-numberp x)
               (rationalp y)
               (not (rationalp x)))
          (not (rationalp (+ x y))))
 :hints (("Goal" :use ((:instance rationalp-+ (x (+ x y)) (y (- y)))))))

(defthm not-rationalp-rationalp-unary---plus
 (implies (and (acl2-numberp x)
               (rationalp y)
               (not (rationalp (- x))))
          (not (rationalp (+ x y))))
 :hints (("Goal" :use ((:instance rationalp-+ (x (+ x y)) (y (- y))))
	  :in-theory (enable rationalp-unary--))))

(encapsulate nil

   (local (defthm simplify-mod-+-mod-crock
	    (equal (equal (- (* i y)) y)
		   (and (acl2-numberp y)
			(or (equal y 0)
			    (equal i -1))))
	    :hints (("Goal" :in-theory (disable left-cancellation-for-*)
		     :use (:instance left-cancellation-for-*
				     (z y) (x -1) (y i))))))

   (local (defthm simplify-mod-+-mod-crock-2
            (equal (equal (* a b) (+ y z))
                   (equal (fix z) (- (* a b) y)))))

(defthm simplify-mod-+-mod
  (implies (and (equal i (/ y z))
		(integerp i)
		(qr-guard x y)
		(qr-guard w z))
	   (and (equal (mod (+ w (mod x y)) z)
		       (mod (+ w x) z))
		(equal (mod (+ (mod x y) w) z)
		       (mod (+ w x) z))
		(equal (mod (- w (mod x y)) z)
		       (mod (- w x) z))
		(equal (mod (- (mod x y) w) z)
		       (mod (- x w) z))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Rewrite: (MOD (+ w (MOD x y)) z) = (MOD (+ w x) z);
;          (MOD (+ (MOD x y) w) z) = (MOD (+ w x) z));
;          (MOD (- w (MOD x y)) z) = (MOD (- w x) z));
;          (MOD (- (MOD x y) w) z) = (MOD (- x w) z)),
; Provided that for each case y/z is an integer.
; ~/~/~/"
  ))

(defthm mod-+-cancel-0
  (implies
   (and (qr-guard x z)
	(qr-guard y z))
   (equal (equal (mod (+ x y) z) x)
	  (and (equal (mod y z) 0)
	       (equal (mod x z) x))))
  :hints (("Goal" :in-theory (disable left-cancellation-for-* equal-*-/-2)
	   :use ((:instance left-cancellation-for-*
			    (z (/ z)) (x y) (y (* z (floor (+ x y) z)))))
	   :expand ((mod (+ x y) z)))))

(local (in-theory (enable floor-type-1 floor-type-2 floor-type-3 floor-type-4
			  floor-bounds mod-type mod-bounds)))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Positive integer theory for FLOOR and MOD
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    The following is a proof of the theorem
;;;
;;;      (implies
;;;       (and (integerp i)
;;;            (integerp j)
;;;            (< 0 i)
;;;            (< 0 j)
;;;            (rationalp x))
;;;       (equal (floor (floor x i) j)
;;;      	 (floor x (* i j))))).
;;;
;;;    I believe that this is the most general, or at least the most
;;;    generally useful form of this result. E.g., it's not true for negative
;;;    J and K.  This theorem is used to justify a recursive definition of
;;;    "shifting" integers, i.e.,
;;;
;;;    (equal (floor i (expt 2 j)) (floor (floor i 2) (expt 2 (- j 1))))
;;;
;;;    for J > 0.

(defthm rationalp-mod
  (implies (and (rationalp x)
		(rationalp y))
	   (rationalp (mod x y)))
  :hints (("Goal" :in-theory (enable mod rationalp-+))))

(encapsulate ()

  ;;  This proof of FLOOR-FLOOR-INTEGER is an elaborate rewriting trick,
  ;;  which is spoiled by these 2 lemmas!

  (local (in-theory (disable rewrite-floor-mod rewrite-mod-mod)))

  ;;< These first 2 lemmas have nothing to do with the :LINEAR theory of
  ;;FLOOR and MOD, so we DISABLE the key :LINEAR lemmas to avoid thrashing.

  (local (in-theory (disable floor-type-1 floor-type-2 floor-type-3
			     floor-type-4 floor-bounds mod-type mod-bounds)))

  ;; First, write x as a quotient and remainder of i*j.

  (local
   (defthm floor-floor-integer-crock0
     (implies
      (and (rationalp x)
	   (integerp i)
	   (not (equal i 0))
	   (integerp j)
	   (not (equal j 0))
	   (syntaxp (and (eq x 'x) (eq i 'i) (eq j 'j))))
      (equal (floor (floor x i) j)
	     (floor (floor (+ (mod x (* i j))
			      (* (* i j) (floor x (* i j)))) i)
		    j)))
     :hints (("Goal" :in-theory (disable commutativity-2-of-+
					 commutativity-2-of-*
					 associativity-of-*)))))

  ;;  Next, divide out i and j through the sums.

  (local
   (defthm floor-floor-integer-crock1
     (implies
      (and (rationalp x)
	   (integerp i)
	   (not (equal i 0))
	   (integerp j)
	   (not (equal j 0))
	   (syntaxp (and (eq x 'x) (eq i 'i) (eq j 'j))))
      (equal (floor (floor x i) j)
	     (+ (floor x (* i j)) (floor (floor (mod x (* i j)) i) j))))
     :hints
     (("Goal"
       :in-theory (disable floor-mod-elim)))))

  ;;< This proof takes 20 sec. with no splitting. We need to re-ENABLE the
  ;;type lemmas to make it work. It could probably be speeded up by
  ;;DISABLEing selected parts of the :LINEAR theory of FLOOR and MOD.

  (local
   (defthm floor-floor-integer-crock2
     (implies
      (and (rationalp x)
	   (integerp i)
	   (< 0 i)
	   (integerp j)
	   (< 0 j))
      (equal (floor (floor (mod x (* i j)) i) j)
	     0))
     :hints (("Goal" :in-theory
	      (set-difference-theories (enable floor-type-1
					       floor-type-2
					       floor-type-3
					       mod-type)
				       '(floor-bounds mod-bounds
						      <-*-left-cancel
						      <-*-/-left-commuted))
       :use ((:instance floor-bounds (x (mod x (* i j))) (y i))
	     (:instance mod-bounds (x x) (y (* i j)))
	     (:instance <-*-left-cancel
			(z (/ i)) (x (mod x (* i j))) (y (* i j))))))))

  ;; Voila!

  (defthm floor-floor-integer
    (implies
     (and (integerp i)
	  (integerp j)
	  (< 0 i)
	  (< 0 j)
	  (rationalp x))
     (equal (floor (floor x i) j)
	    (floor x (* i j))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section floor-lemmas
;   Rewrite: (FLOOR (FLOOR x i) j) = (FLOOR x (* i j)) for integers i,j > 0.
;   ~/~/~/"
    ))

(defthm floor-x+i*k-i*j
  (implies
   (and (force (rationalp x))
	(force (integerp i))
	(force (integerp j))
	(force (integerp k))
	(< 0 i)
	(< 0 j)
	(<= 0 x)
	(< x i))
   (equal (floor (+ x (* i k)) (* i j))
	  (floor k j)))
  :hints
  (("Goal"
    :in-theory (disable floor-floor-integer floor-+)
    :use ((:instance floor-floor-integer (x (+ x (* i k))) (i i) (j j))
	  (:instance floor-+ (x x) (y (* i k)) (z i)))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section floor-lemmas
; Rewrite: (FLOOR (+ x (* i k)) (* i j)) = (FLOOR k j), when
; i,j > 0 and 0 <= x < i.
; ~/
; This is a crucial lemma for certain kinds of reasoning about hardware
; specifications, and is used to prove MOD-x+i*j-i*k.~/~/"
  )

(defthm mod-x+i*k-i*j
  (implies
   (and (force (rationalp x))
	(force (integerp i))
	(force (integerp j))
	(force (integerp k))
	(< 0 i)
	(< 0 j)
	(<= 0 x)
	(< x i))
  (equal (mod (+ x (* i k)) (* i j))
	 (+ x (* i (mod k j)))))
  :hints
  (("Goal"
    :in-theory (enable mod)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section mod-lemmas
; Rewrite: (MOD (+ x (* i k)) (* i j)) = (+ x (* i (MOD k j))), when
; i,j > 0 and 0 <= x < i.
; ~/
; This is a crucial lemma for certain kinds of reasoning about hardware
; specifications, for example, we can use this to prove that
; (MOD i (EXPT 2 n)) = (MOD i 2) + (MOD (FLOOR i 2) (EXPT 2 (1- n))), for
; n > 0, which justifies a recursive specification of hardware
; operations.~/~/"
  )

(encapsulate ()

  (local (in-theory (disable floor-type-1 floor-type-2 floor-type-3
			     floor-type-4 floor-bounds)))

  (local
   (defthm mod-x-i*j-crock
     (implies
      (and (> i 0)
	   (> j 0)
	   (force (integerp i))
	   (force (integerp j))
	   (force (rationalp x)))
      (equal (mod (+ (mod x i) (* i (floor x i))) (* i j))
	     (+ (mod x i) (* i (mod (floor x i) j)))))
     :rule-classes nil
     :hints
     (("Goal"
       :in-theory (disable floor-mod-elim)))))

  (defthm mod-x-i*j
    (implies
     (and (> i 0)
	  (> j 0)
	  (force (integerp i))
	  (force (integerp j))
	  (force (rationalp x)))
     (equal (mod x (* i j))
	    (+ (mod x i) (* i (mod (floor x i) j)))))
    :hints
    (("Goal"
      :use mod-x-i*j-crock))))


;;;****************************************************************************
;;;
;;;  Misc.
;;;
;;;****************************************************************************

;;  This is a nice "quotient" theorem -- If J is an integer and I/J is an
;;  integer, then I is also an integer, namely J*(FLOOR I J).  It was proved
;;  as part of en earlier pass at this book, and although it's not used
;;  anymore, I like it so I'm leaving it in.

(encapsulate ()

  (local
   (defthm crock0
     (implies
      (and (integerp (/ i j))
	   (rationalp i)
	   (integerp j)
	   (not (equal 0 j)))
      (integerp (+ (* j (floor i j)) (mod i j))))
     :rule-classes nil
     :hints
     (("Goal"
       :in-theory (disable floor-=-x/y)))))

  (defthm integerp-i/j-integerp-forward
    (implies
     (and (integerp (/ i j))
	  (rationalp i)
	  (integerp j)
	  (not (zerop j)))
     (integerp i))
    :hints
    (("Goal"
      :use ((:instance crock0))
      :in-theory (disable mod-=-0 floor-=-x/y)))
    :rule-classes
    ((:forward-chaining
      :corollary
      (implies
       (and (integerp (/ i j))
	    (force (rationalp i))
	    (integerp j)
	    (force (not (equal 0 j))))
       (integerp i)))
     (:forward-chaining
      :corollary
      (implies
       (and (integerp (* (/ j) i))
	    (force (rationalp i))
	    (integerp j)
	    (force (not (equal 0 j))))
       (integerp i))))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

;   :doc
;   ":doc-section integer-ratio-lemmas
;   Forward: If i/j is an integer and j is an integer, then i is an integer.
;   ~/
;   NB: The trigger-term is (INTEGERP (/ i j)).~/~/"
    ))


;;;****************************************************************************
;;;
;;;    THEORIES -- A couple of exported theories.
;;;
;;;****************************************************************************

(deflabel quotient-remainder-theories

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-lemmas
; Logical theories supplied by the QUOTIENT-REMAINDER book.~/~/

; The QUOTIENT-REMAINDER book exports 2 theories:
; QUOTIENT-REMAINDER-FUNCTIONS and QUOTIENT-REMAINDER-RULES.  The former is
; simply a theory of the functions characterized by the book.  Since
; these functions are all ENABLEd by default, and most are non-recursive, one
; should immediately:

; (IN-THEORY (DISABLE QUOTIENT-REMAINDER-FUNCTIONS))

; upon loading this book, or the lemmas may never be applied.

; QUOTIENT-REMAINDER-RULES is a theory of all of the lemmas exported by this
; book which are ENABLEd by default.  You can \"turn off\" this book
; after it is loaded by

; (IN-THEORY (DISABLE QUOTIENT-REMAINDER-RULES)).~/"
  )

(deftheory quotient-remainder-functions
  '(nonnegative-integer-quotient floor mod truncate rem)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-theories
; A theory of the function symbols characterized by
; \"quotient-remainder-lemmas\".
; ~/
; You should DISASBLE this theory immediately after loading this book.~/~/"
  )

(deftheory quotient-remainder-rules
  (union-theories
   (defun-type/exec-theory
     '(NONNEGATIVE-INTEGER-QUOTIENT FLOOR MOD TRUNCATE REM))
   (set-difference-theories (current-theory :here)
			    (current-theory 'begin-quotient-remainder-lemmas)))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.

; :doc
; ":doc-section quotient-remainder-theories
; A theory of all rules exported ENABLEd by the \"quotient-remainder-lemmas\"
; book.~/~/~/"
  )

; Documentation, auto-generated from legacy doc strings commented out above:

(include-book "xdoc/top" :dir :system)

(defxdoc cancel-floor-+
  :parents (floor-lemmas integer-ratio-lemmas)
  :short "Rewrite: (FLOOR (+ x y) z) = x/z + (FLOOR y z), when x/z is an integer;
also the commutative form."
  :long "")

(defxdoc cancel-floor-+-3
  :parents (floor-lemmas integer-ratio-lemmas)
  :short "Rewrite: (FLOOR (+ w x y) z) = y/z + (FLOOR (+ w x) z), when y/z is an
integer."
  :long "")

(defxdoc cancel-mod-+
  :parents (mod-lemmas integer-ratio-lemmas)
  :short "Rewrite: (MOD (+ x y) z) = (MOD y z), when x/z is an integer;
also the commutative form."
  :long "")

(defxdoc cancel-mod-+-3
  :parents (mod-lemmas integer-ratio-lemmas)
  :short "Rewrite: (MOD (+ w x y) z) = (MOD (+ w x) z), when y/z is an integer."
  :long "")

(defxdoc floor-+
  :parents (floor-lemmas)
  :short "Rewrite (D): (FLOOR (+ x y) z) =
(FLOOR x z) + (FLOOR y z) + (FLOOR (+ (MOD x z) (MOD y z)) z)."
  :long "<p>As this rule could easily loop it is exported DISABLEd.  Don't
 ENABLE this lemma unless you are sure that the FLOOR/MOD term will simplify,
 or else put SYNTAXP guards on the variables x, y, and/or z.</p>

 ")

(defxdoc floor-=-x/y
  :parents (floor-lemmas)
  :short "Rewrite: (FLOOR x y) = x/y, when x/y is an integer."
  :long "<p>This rule is a corollary of a more general equality which is also
 stored as a :REWRITE and :GENERALIZE rule.</p>

 ")

(defxdoc floor-as-truncate
  :parents (floor-lemmas)
  :short "Rewrite: Rewrite (FLOOR x y) to a function of (TRUNCATE x y)."
  :long "")

(defxdoc floor-bounds
  :parents (floor-lemmas)
  :short "Linear (D) : x/y - 1 &lt; (FLOOR x y) &lt;= x/y."
  :long "<p>This lemma `defines' FLOOR as a set of inequalties.  Many of the
 properties of FLOOR will be derived from this theorem.  Unfortunately, this
 lemma is implicated in thrashing in the linear arithmetic procedure and must
 be DISABLEd at times.  This lemmas is stored as a :LINEAR rule for FLOOR
 exclusively since we consider it to be a property of FLOOR, and not a general
 property of (/ x y).</p>

 ")

(defxdoc floor-cancel-*
  :parents (floor-lemmas)
  :short "Rewrite: (FLOOR (* x y) y) = (FLOOR x 1)."
  :long "<p>NB: You get the commuted form as well.</p>

 ")

(defxdoc floor-cancel-*-2
  :parents (floor-lemmas)
  :short "Rewrite: (FLOOR (* x y) (* x z)) = (FLOOR y z)."
  :long "")

(defxdoc floor-floor-integer
  :parents (floor-lemmas)
  :short "Rewrite: (FLOOR (FLOOR x i) j) = (FLOOR x (* i j)) for integers i,j &gt; 0."
  :long "")

(defxdoc floor-lemmas
  :parents (quotient-remainder-lemmas)
  :short "Lemmas about FLOOR."
  :long "")

(defxdoc floor-minus
  :parents (floor-lemmas)
  :short "Rewrite: (FLOOR (- x) y) =
         (IF (INTEGERP (* x (/ y)))
             (- (FLOOR x y))
           (- (- (FLOOR x y)) 1)));
         Rhs identical for -y."
  :long "")

(defxdoc floor-mod-elim
  :parents (floor-lemmas mod-lemmas)
  :short "Rewrite: (+ (MOD x y) (* y (FLOOR x y))) = x."
  :long "<p>NB: This rule is also stored as an :ELIM rule.</p>

 ")

(defxdoc floor-type-1
  :parents (floor-lemmas)
  :short "Decide (FLOOR x y) &lt; 0  based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
 :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we can
 decide the inequalities of x and y the :LINEAR forms may thrash.</p>

 ")

(defxdoc floor-type-2
  :parents (floor-lemmas)
  :short "Decide (FLOOR x y) &gt; 0  based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
 :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we can
 decide the inequalities of x and y the :LINEAR forms may thrash.</p>

 ")

(defxdoc floor-type-3
  :parents (floor-lemmas)
  :short "Decide (FLOOR x y) &gt; 0  based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
 :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we can
 decide the inequalities of x and y the :LINEAR forms may thrash.</p>

 ")

(defxdoc floor-type-4
  :parents (floor-lemmas)
  :short "Decide (FLOOR x y) = -1  based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
 :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we can
 decide the inequalities of x and y the :LINEAR forms may thrash.</p>

 ")

(defxdoc floor-type-linear
  :parents (floor-lemmas)
  :short "A theory of the :LINEAR rules created by the lemmas FLOOR-TYPE-1 and
FLOOR-TYPE-2."
  :long "<p>These rules are implicated in thrashing linear arithmetic, so we
 provide this theory which can be DISABLED if it becomes a problem.</p>

 ")

(defxdoc floor-x+i*k-i*j
  :parents (floor-lemmas)
  :short "Rewrite: (FLOOR (+ x (* i k)) (* i j)) = (FLOOR k j), when
i,j &gt; 0 and 0 &lt;= x &lt; i."
  :long "<p>This is a crucial lemma for certain kinds of reasoning about
 hardware specifications, and is used to prove MOD-x+i*j-i*k.</p>

 ")

(defxdoc integer-ratio-lemmas
  :parents (quotient-remainder-lemmas)
  :short "Lemmas about ratios x/y that are known to be INTEGERP."
  :long "")

(defxdoc integer-truncate-as-niq
  :parents (truncate-lemmas)
  :short "Rewrite (D) : (TRUNCATE i j) =
              (SIGNUM i) * (SIGNUM j) * (NIQ i j), for integers i,j."
  :long "<p>This rule shows that TRUNCATE is the \"usual\" (i.e.,
 FORTRAN-style) integer quotient for both positive and negative integers.</p>

 ")

(defxdoc integerp-i/j-integerp-forward
  :parents (integer-ratio-lemmas)
  :short "Forward: If i/j is an integer and j is an integer, then i is an integer."
  :long "<p>NB: The trigger-term is (INTEGERP (/ i j)).</p>

 ")

(defxdoc integerp-mod
  :parents (mod-lemmas)
  :short "Type-Prescription: (MOD i j) is an integer, when i and j are integers."
  :long "")

(defxdoc integerp-rem
  :parents (rem-lemmas)
  :short "Type-Prescription: (REM i j) is an integer, when i and j are integers."
  :long "")

(defxdoc justify-floor-recursion
  :parents (floor-lemmas)
  :short "Rewrite: (FLOOR x y) &lt; x, when x &gt; 0 and y &gt; 1;
         x &lt; (FLOOR x y), when x &lt; -1 and y &gt;= 2."
  :long "<p>This theorem justifies recursion by FLOOR using the measure
 ACL2-COUNT, which for integers i is simply (ABS i).  Thus, this theorem won't
 justify a simple recursion by a negative y, since (FLOOR 1 y) = -1 for
 negative y, and (ABS -1) = (ABS 1).  For the most general case that includes
 negative y one would need to define a different measure that could handle this
 condition.</p>

 ")

(defxdoc linearize-mod
  :parents (mod-lemmas)
  :short "Rewrite (D): Transform (MOD x y) &lt; z, (MOD x y) &gt; z, and (MOD x y) = z
into an equivalent FLOOR expression suitable for reasoning about with
FLOOR-BOUNDS and other theorems about FLOOR."
  :long "<p>Since this lemma can be considered a `definition' of MOD, it is
 exported DISABLED.</p>

 ")

(defxdoc linearize-rem
  :parents (rem-lemmas)
  :short "Rewrite (D): Transform (REM x y) &lt; z, (REM x y) &gt; z, and (REM x y) = z
into an equivalent TRUNCATE expression suitable for reasoning about with
TRUNCATE-BOUNDS and other theorems about TRUNCATE."
  :long "<p>Since this lemma can be considered a `definition' of REM, it is
 exported DISABLED.</p>

 ")

(defxdoc mod-+
  :parents (mod-+)
  :short "Rewrite (D): (MOD (+ x y) z) = (MOD (+ (MOD x z) (MOD y z)) z)."
  :long "<p>As this rule could easily loop it is exported DISABLEd.  Don't
 ENABLE this lemma unless you are sure that the MOD/MOD term will simplify, or
 else put SYNTAXP guards on the variables x, y, and/or z.</p>

 ")

(defxdoc mod-=-0
  :parents (mod-lemmas integer-ratio-lemmas)
  :short "Rewrite: (MOD x y) = 0, when x/y is an integer;"
  :long "<p>This rule is a corollary of a more general equality.  The equality
 is also stored as a :REWRITE and :GENERALIZE rule.</p>

 ")

(defxdoc mod-bounds
  :parents (mod-lemmas)
  :short "Linear: Useful forms of the fact that |(MOD x y)| &lt; |y|."
  :long "<p>This lemma is also stored as a :GENERALIZE rule.</p>

 ")

(defxdoc mod-lemmas
  :parents (quotient-remainder-lemmas)
  :short "Lemmas about MOD."
  :long "")

(defxdoc mod-minus
  :parents (mod-lemmas integer-ratio-lemmas)
  :short "Rewrite: (MOD (- x) y) =
         (IF (INTEGERP (/ x y))
             0
           (- y (MOD x y)));
         (MOD x (- y)) =
         (IF (INTEGERP (/ x y))
             0
           (- (MOD x y) y))."
  :long "")

(defxdoc mod-type
  :parents (mod-lemmas)
  :short "Various: Decide (MOD x y) &lt; 0 and (MOD x y) &gt; 0 based on the sign of
y and the INTEGERP-ness of x/y."
  :long "<p>This rule is also stored as
 appropriate :REWRITE, :LINEAR, :GENERALIZE, and :TYPE-PRESCRIPTION rules.</p>

 ")

(defxdoc mod-type-linear
  :parents (mod-lemmas)
  :short "A theory of the :LINEAR rules created by the lemma MOD-TYPE."
  :long "<p>These rules are implicated in thrashing linear arithmetic, so we
 provide this theory which can be DISABLED if it becomes a problem.</p>

 ")

(defxdoc mod-x+i*k-i*j
  :parents (mod-lemmas)
  :short "Rewrite: (MOD (+ x (* i k)) (* i j)) = (+ x (* i (MOD k j))), when
i,j &gt; 0 and 0 &lt;= x &lt; i."
  :long "<p>This is a crucial lemma for certain kinds of reasoning about
 hardware specifications, for example, we can use this to prove that
 (MOD i (EXPT 2 n)) = (MOD i 2) + (MOD (FLOOR i 2) (EXPT 2 (1- n))), for n &gt;
 0, which justifies a recursive specification of hardware operations.</p>

 ")

(defxdoc mod-x-y-=-x
  :parents (mod-lemmas)
  :short "Rewrite: (MOD x y) = x, when |x| &lt;= |y| and x and y have the same sign."
  :long "<p>This rule is a corollary of a more general equality which is also
 stored as
 :REWRITE and :GENERALIZE rules.</p>

 ")

(defxdoc mod-x-y-=-x+y
  :parents (mod-lemmas)
  :short "Rewrite: (MOD x y) = x + y, when |x| &lt;= |y| and x and y have different
signs and x /= 0."
  :long "<p>This rule is a corollary of a more general equality which is also
 stored as
 :REWRITE and :GENERALIZE rules.</p>

 ")

(defxdoc niq-bounds
  :parents (niq-lemmas)
  :short "Linear (D): i/j - 1 &lt; (NIQ i j) &lt;= i/j."
  :long "<p>This lemma serves as a :LINEAR definition of
 NONNEGATIVE-INTEGER-QUOTIENT, and allows us to derive interesting properties
 of FLOOR and TRUNCATE by linear arithmetic.  This lemma is stored as a :LINEAR
 rule under NIQ since we think of this as a property of NIQ, and not as a
 general property of (/ I J).</p>

 ")

(defxdoc niq-guard
  :parents (qr-guard-macros)
  :short "Macro form of the guard for NONNEGATIVE-INTEGER-QUOTIENT (forced)."
  :long "<p>~</p>")

(defxdoc niq-lemmas
  :parents (quotient-remainder-lemmas)
  :short "Lemmas about nonnegative-integer-QUOTIENT (abbreviated NIQ)."
  :long "")

(defxdoc niq-type
  :parents (niq-lemmas)
  :short "Various : Decide (NIQ i j) = 0, (NIQ i j) &gt; 0, and
(NIQ i j) = i/j based on the inequalities of i and j, and the INTEGERP-ness
of i/j."
  :long "")

(defxdoc qr-guard
  :parents (qr-guard-macros)
  :short "Quotient/Remainder GUARD: Macro form of the guards for FLOOR, MOD, TRUNCATE,
and REM., or any ratio x/y of rationals (forced)."
  :long "<p>~</p>")

(defxdoc qr-guard-macros
  :parents (quotient-remainder-lemmas)
  :short "Macro forms of the guards for the quotient/remainder functions."
  :long "<p>Without these macros, fully 25% of the text of the
 \"quotient-remainder-lemmas\" book is given over simply to expressing the
 guards!</p>

 ")

(defxdoc quotient-remainder-functions
  :parents (quotient-remainder-theories)
  :short "A theory of the function symbols characterized by
\"quotient-remainder-lemmas\"."
  :long "<p>You should DISASBLE this theory immediately after loading this
 book.</p>

 ")

(defxdoc quotient-remainder-lemmas
  :parents (quotient-remainder-lemmas)
  :short "A book of facts about FLOOR, MOD, TRUNCATE and REM, and integer ratios.
Also enough of a theory of the Acl2 function NONNEGATIVE-INTEGER-QUOTIENT
to prove the rules."
  :long "<p>Since NONNEGATIVE-INTEGER-QUOTIENT is the only one of these
 functions that is recursive, the others must be DISABLEd for this library to
 be of any use.  This can easily be done by DISABLEing the
 QUOTIENT-REMAINDER-FUNCTIONS theory (defined by this book):</p>

 <p>(IN-THEORY (DISABLE QUOTIENT-REMAINDER-FUNCTIONS))</p>

 <p>INTRODUCTION</p>

 <p>Common Lisp defines the quotient/remainder functions FLOOR/MOD and
 TRUNCATE/REM, which operate on any rational numbers (as long as the divisor is
 non-zero).  Both (TRUNCATE x y) and (FLOOR x y) are integers, and specify the
 `integer part' of the rational number x/y; they differ in the direction of
 rounding.</p>

 <p>TRUNCATE is the `FORTRAN-style' quotient operation, rounding towards 0,
 i.e., (TRUNCATE x y) = (TRUNCATE (ABS x) (ABS y)).  This book provides a
 selected theory of TRUNCATE and REM.</p>

 <p>(FLOOR x y) is identical to TRUNCATE if x/y &gt; 0 or x/y is an integer,
 otherwise for negative non-integer ratios x/y, (FLOOR x y) = (TRUNCATE x y) -
 1.  (FLOOR i (EXPT 2 j)) is the specification of an `arithmetic shift' of the
 integer i by -j bits.  Since FLOOR and MOD are the foundations for integer
 descriptions of hardware, this book contains a very extensive theory of FLOOR
 and MOD.</p>

 <p>The formal definitions of the Common Lisp functions are made in terms of
 the Acl2 function NONNEGATIVE-INTEGER-QUOTIENT, which is simple recursive
 specification of division of nonnegative integers by repeated subtraction.  We
 provide only enough of a theory of NONNEGATIVE-INTEGER-QUOTIENT to prove the
 desired properties of the Common Lisp functions.</p>

 <p>DOCUMENTATION</p>

 <p>The documentation for this library is divided into a number of sections.
 There is a section for the rules that apply to each function.  Some of the
 rules will appear in more than 1 section.  If a rule is exported DISABLEd,
 then you will see `(D)' after the rule class in the `one-liner' for the rule.
 Note that we often abbreviate NONNEGATIVE-INTEGER-QUOTIENT as NIQ.</p>

 <p>APPROACH</p>

 <p>We have tried to capture the properties of the quotient/remainder functions
 with the smallest number of the most general rules possible.  This approach
 takes advantage of Acl2 type reasoning, and the assumed existence of a basic
 mathematics simplification library.  Several lemmas contain the hypothesis
 (INTEGERP (/ x y)), which we consider to be the simplest statement of the fact
 that (&lt;quotient&gt; x y) = x/y, e.g.</p>

 <p>(INTEGERP (/ x y)) ==&gt; (FLOOR x y) = (/ x y), (INTEGERP (/ x y)) ==&gt;
 (MOD x y) = 0.</p>

 <p>Thus, the first fact above obviates the need for a specials lemmas like
 (FLOOR i 1) = i for integers i, since (/ i 1) = i by simplification.</p>

 <p>In general, at most 2 of the many possible commutative forms of the rules
 are exported from this library.  If they aren't the ones you need, simply
 prove the appropriate corollary, or :USE an :INSTANCE of the library rule.
 Also, lemmas are generally exported DISABLEd if they seemed to interfere with
 the proofs of other lemmas, or could easily lead to infinite looping.  Be
 careful when ENABLEing these lemmas.</p>

 <p>Questions, comments, and sugestions are welcome.  Contact
 brock@@cli.com.</p>")

(defxdoc quotient-remainder-rules
  :parents (quotient-remainder-theories)
  :short "A theory of all rules exported ENABLEd by the \"quotient-remainder-lemmas\"
book."
  :long "")

(defxdoc quotient-remainder-theories
  :parents (quotient-remainder-lemmas)
  :short "Logical theories supplied by the QUOTIENT-REMAINDER book."
  :long "<p>The QUOTIENT-REMAINDER book exports 2 theories:
 QUOTIENT-REMAINDER-FUNCTIONS and QUOTIENT-REMAINDER-RULES.  The former is
 simply a theory of the functions characterized by the book.  Since these
 functions are all ENABLEd by default, and most are non-recursive, one should
 immediately:</p>

 <p>(IN-THEORY (DISABLE QUOTIENT-REMAINDER-FUNCTIONS))</p>

 <p>upon loading this book, or the lemmas may never be applied.</p>

 <p>QUOTIENT-REMAINDER-RULES is a theory of all of the lemmas exported by this
 book which are ENABLEd by default.  You can \"turn off\" this book after it is
 loaded by</p>

 <p>(IN-THEORY (DISABLE QUOTIENT-REMAINDER-RULES)).</p>")

(defxdoc rem-=-0
  :parents (rem-lemmas integer-ratio-lemmas)
  :short "Rewrite: (REM x y) = 0, when x/y is an integer;"
  :long "<p>NB: This rule is a corollary of a more general equality.  The
 equality is also stored as a :REWRITE and :GENERALIZE rule.</p>

 ")

(defxdoc rem-bounds
  :parents (rem-lemmas)
  :short "Linear: Useful forms of the fact that |(REM x y)| &lt; |y|."
  :long "<p>This lemma is also stored as a :GENERALIZE rules.</p>

 ")

(defxdoc rem-lemmas
  :parents (quotient-remainder-lemmas)
  :short "Lemmas about REM."
  :long "")

(defxdoc rem-minus
  :parents (rem-lemmas)
  :short "Rewrite: (REM (- x) y) = (- (REM x y));
         (REM x (- y)) = (SIGNUM x) * (SIGNUM y) * (REM x y))."
  :long "")

(defxdoc rem-type
  :parents (rem-lemmas)
  :short "Various : Decide (REM x y) &lt; 0 and (REM x y) &gt; 0 based on the sign of
x and the INTEGERP-ness of x/y."
  :long "<p>This rule is stored as appropriate :REWRITE, :LINEAR, :GENERALIZE,
 and
 :TYPE-PRESCRIPTION rules.</p>

 ")

(defxdoc rem-x-y-=-x
  :parents (rem-lemmas)
  :short "Rewrite: (REM x y) = x, when |x| &lt; |y|."
  :long "<p>This rule is a corollary of a more general equality which is also
 stored as a :REWRITE and :GENERALIZE rule.</p>

 ")

(defxdoc rewrite-floor-mod
  :parents (floor-lemmas integer-ratio-lemmas)
  :short "Rewrite: (FLOOR (MOD x y) z) = (FLOOR x z) - i*(FLOOR x y), when i = y/z
is an integer."
  :long "")

(defxdoc rewrite-floor-x*y-z-left
  :parents (floor-lemmas)
  :short "Rewrite (D): (FLOOR (* x y) z) = (FLOOR y (/ z x)), when x /= 0."
  :long "<p>Since we don't presume any rewriting strategy for / vis-a-vis *,
 this often useful rule is exported DISABLEd.</p>

 ")

(defxdoc rewrite-floor-x*y-z-right
  :parents (floor-lemmas)
  :short "Rewrite: (FLOOR (* x y) z) = (FLOOR x (/ z y)), when y /= 0."
  :long "<p>Since we don't presume any rewriting strategy for / vis-a-vis *,
 this often useful rule is exported DISABLEd.</p>

 ")

(defxdoc rewrite-mod-mod
  :parents (mod-lemmas integer-ratio-lemmas)
  :short "Rewrite: (MOD (MOD x y) z) = (MOD x z), when y/z is an integer."
  :long "")

(defxdoc rewrite-truncate-x*y-z-left
  :parents (truncate-lemmas)
  :short "Rewrite (D): (TRUNCATE (* x y) z) = (TRUNCATE y (/ z x)), when x /= 0."
  :long "<p>Since we don't presume any rewriting strategy for / vis-a-vis *,
 this often useful rule is exported DISABLEd.</p>

 ")

(defxdoc rewrite-truncate-x*y-z-right
  :parents (truncate-lemmas)
  :short "Rewrite (D): (TRUNCATE (* x y) z) = (TRUNCATE x (/ z y)), when y /= 0."
  :long "<p>Since we don't presume any rewriting strategy for / vis-a-vis *,
 this often useful rule is exported DISABLEd.</p>

 ")

(defxdoc simplify-mod-+-mod
  :parents (mod-lemmas)
  :short "Rewrite: (MOD (+ w (MOD x y)) z) = (MOD (+ w x) z);
         (MOD (+ (MOD x y) w) z) = (MOD (+ w x) z));
         (MOD (- w (MOD x y)) z) = (MOD (- w x) z));
         (MOD (- (MOD x y) w) z) = (MOD (- x w) z)),
Provided that for each case y/z is an integer."
  :long "")

(defxdoc truncate-=-x/y
  :parents (truncate-lemmas integer-ratio-lemmas)
  :short "Rewrite: (TRUNCATE x y) = x/y, when x/y is an integer."
  :long "<p>This rule is a corollary of a more general equality, which is also
 stored as a :REWRITE and :GENERALIZE rule.</p>

 ")

(defxdoc truncate-bounds
  :parents (truncate-lemmas)
  :short "Linear (D) : x/y - 1 &lt; (TRUNCATE x y) &lt;= x/y, when x/y &gt;= 0;
             x/y &lt;= (TRUNCATE x y) &lt; x/y + 1, when x/y =&lt; 0."
  :long "<p>This lemma `defines' TRUNCATE as a set of inequalties.  Many of the
 properties of TRUNCATE will be derived from this theorem.  Unfortunately, this
 lemma is implicated in thrashing in the linear arithmetic procedure unless the
 inequalties of X and Y can be decided, so it may need to be DISABLEd at times.
 This lemma is stored as a :LINEAR rule for TRUNCATE exclusively since we
 consider it to be a property of TRUNCATE, and not a general property of (/ x
 y).</p>

 <p>The statement of the hypotheses of this lemma is critical for its proper
 application.  It is necessary for each inequality of x and y to stand alone in
 order to be relieveable by linear arithemetic.</p>

 ")

(defxdoc truncate-cancel-*
  :parents (truncate-lemmas)
  :short "Rewrite: (TRUNCATE (* x y) y) = (TRUNCATE x 1)."
  :long "<p>NB: You get the commutted form as well.</p>

 ")

(defxdoc truncate-lemmas
  :parents (quotient-remainder-lemmas)
  :short "Lemmas about TRUNCATE."
  :long "")

(defxdoc truncate-minus
  :parents (truncate-lemmas)
  :short "Rewrite: (TRUNCATE (- x) y) = (- (TRUNCATE x y));
         (TRUNCATE x (- y)) = (- (TRUNCATE x y))."
  :long "")

(defxdoc truncate-rem-elim
  :parents (truncate-lemmas rem-lemmas)
  :short "Rewrite: (+ (REM x y) (* y (TRUNCATE x y))) = x."
  :long "<p>NB: This rule is also stored as an :ELIM rule.</p>

 ")

(defxdoc truncate-type
  :parents (truncate-lemmas)
  :short "Various : Decide (TRUNCATE x y) &lt; 0, (TRUNCATE x y) &gt; 0, and
(TRUNCATE x y) = 0 based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
 :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we can
 decide the inequalities of X and Y the :LINEAR forms may thrash.</p>

 ")
