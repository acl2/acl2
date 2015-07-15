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
;;;    1717 West Sixth Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;
;;;    Modified for ACL2 Version_2.6 by:
;;;    Jun Sawada, IBM Austin Research Lab. sawada@us.ibm.com
;;;    Matt Kaufmann, kaufmann@cs.utexas.edu
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

; Modified by Jared Davis, October 2014, to port documentation to xdoc.

(in-package "ACL2")
(include-book "ihs-init")
(include-book "ihs-theories")
(include-book "std/util/defrule" :dir :system)
(local (include-book "math-lemmas"))
(local (in-theory nil))

(local (in-theory (enable basic-boot-strap ; From ihs-theories
			 ;; From math-lemmas
			  ihs-math
			  rationalp-algebra
			  ifix nfix)))

(defxdoc ihs/quotient-remainder-lemmas
  :parents (ihs)
  :short "A book of facts about FLOOR, MOD, TRUNCATE and REM, and integer
  ratios.  Also enough of a theory of the Acl2 function @(see
  nonnegative-integer-quotient) to prove the rules."

  :long "<p>Since @(see nonnegative-integer-quotient) is the only one of these
functions that is recursive, the others must be DISABLEd for this library to be
of any use.  This can easily be done by DISABLEing the
QUOTIENT-REMAINDER-FUNCTIONS theory (defined by this book):</p>

@({
  (IN-THEORY (DISABLE QUOTIENT-REMAINDER-FUNCTIONS))
})

<h3>Introduction</h3>

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

<p>The formal definitions of the Common Lisp functions are made in terms of the
Acl2 function NONNEGATIVE-INTEGER-QUOTIENT, which is simple recursive
specification of division of nonnegative integers by repeated subtraction.  We
provide only enough of a theory of NONNEGATIVE-INTEGER-QUOTIENT to prove the
desired properties of the Common Lisp functions.</p>

<h3>Documentation</h3>

<p>The documentation for this library is divided into a number of sections.
There is a section for the rules that apply to each function.  Some of the
rules will appear in more than 1 section.  If a rule is exported DISABLEd, then
you will see `(D)' after the rule class in the `one-liner' for the rule.  Note
that we often abbreviate NONNEGATIVE-INTEGER-QUOTIENT as NIQ.</p>

<h3>Approach</h3>

<p>We have tried to capture the properties of the quotient/remainder functions
with the smallest number of the most general rules possible.  This approach
takes advantage of Acl2 type reasoning, and the assumed existence of a basic
mathematics simplification library.  Several lemmas contain the
hypothesis (INTEGERP (/ x y)), which we consider to be the simplest statement
of the fact that @('(<quotient> x y)') = x/y, e.g.</p>

<ul>
<li>(INTEGERP (/ x y)) &rarr; (FLOOR x y) = (/ x y),</li>
<li>(INTEGERP (/ x y)) &rarr; (MOD x y) = 0.</li>
</ul>

<p>Thus, the first fact above obviates the need for a specials lemmas
like (FLOOR i 1) = i for integers i, since (/ i 1) = i by simplification.</p>

<p>In general, at most 2 of the many possible commutative forms of the rules
are exported from this library.  If they aren't the ones you need, simply prove
the appropriate corollary, or :USE an :INSTANCE of the library rule.  Also,
lemmas are generally exported DISABLEd if they seemed to interfere with the
proofs of other lemmas, or could easily lead to infinite looping.  Be careful
when ENABLEing these lemmas.</p>

<p>Questions, comments, and sugestions are welcome.  Contact
brock@cli.com.</p>")

(defsection niq-lemmas
  :parents (quotient-remainder-lemmas nonnegative-integer-quotient)
  :short "Lemmas about @(see nonnegative-integer-quotient) (abbreviated NIQ).")

(defsection floor-lemmas
  :parents (quotient-remainder-lemmas floor)
  :short "Lemmas about @(see FLOOR).")

(defsection truncate-lemmas
  :parents (quotient-remainder-lemmas truncate)
  :short "Lemmas about @(see TRUNCATE).")

(defsection mod-lemmas
  :parents (quotient-remainder-lemmas mod)
  :short "Lemmas about @(see MOD).")

(defsection rem-lemmas
  :parents (quotient-remainder-lemmas rem)
  :short "Lemmas about @(see REM).")

(defsection integer-ratio-lemmas
  :parents (quotient-remainder-lemmas /)
  :short "Lemmas about ratios @('x/y') that are known to be @(see integerp).")


;;;****************************************************************************
;;;
;;;    DEFINITIONS and GUARD MACROS
;;;
;;;****************************************************************************

(defsection qr-guard-macros
  :parents (quotient-remainder-lemmas)
  :short "Macro forms of the guards for the quotient/remainder functions."
  :long "<p>Without these macros, fully 25% of the text of the
\"quotient-remainder-lemmas\" book is given over simply to expressing the
guards!</p>")

(defsection niq-guard
  :parents (qr-guard-macros)
  :short "Macro form of the guard for @(see nonnegative-integer-quotient) (forced)."

  (defmacro niq-guard (i j)
    (mlambda (i j)
             (and (force (integerp i))
                  (force (>= i 0))
                  (force (integerp j))
                  (force (> j 0))))))

(defsection qr-guard
  :parents (qr-guard-macros)
  :short "Quotient/Remainder @(see GUARD): Macro form of the guards for @(see
FLOOR), @(see MOD), @(see TRUNCATE), and @(see REM), or any ratio @('x/y') of
rationals (forced)."
  (defmacro qr-guard (x y)
    (mlambda (x y)
             (and (force (real/rationalp x))
                  (force (real/rationalp y))
                  (force (not (equal 0 y)))))))


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
   (and (implies (and (qr-guard x y) (<= 0 x) (< 0 y) (< x y))
                 (< (/ x y) 1))
        (implies (and (qr-guard x y) (<= 0 x) (< 0 y) (<= y x))
                 (<= 1 (/ x y)))
        (implies (and (qr-guard x y) (<= 0 x) (< y 0) (< x (- y)))
                 (< -1 (/ x y)))
        (implies (and (qr-guard x y) (<= 0 x) (< y 0) (<= (- y) x))
                 (<= (/ x y) -1))
        (implies (and (qr-guard x y) (<= 0 x) (< y 0) (<= x (- y)))
                 (<= -1 (/ x y)))
        (implies (and (qr-guard x y) (<= x 0) (< 0 y) (< (- x) y))
                 (< -1 (/ x y)))
        (implies (and (qr-guard x y) (<= x 0) (< 0 y) (<= y (- x)))
                 (<= (/ x y) -1))
        (implies (and (qr-guard x y) (<= x 0) (< 0 y) (<= (- x) y))
                 (<= -1 (/ x y)))
        (implies (and (qr-guard x y) (<= x 0) (< y 0) (< (- x) (- y)))
                 (< (/ x y) 1))
        (implies (and (qr-guard x y) (<= x 0) (< y 0) (<= (- y) (- x)))
                 (<= 1 (/ x y))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable prefer-*-to-/
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
	 (implies (and (real/rationalp i)
		       (< 0 j)
		       (real/rationalp j)
		       (real/rationalp x))
		  (equal (< (+ -1 (* i (/ j))) x)
			 (< i (+ j (* j x)))))
	 :hints (("Goal" :in-theory (set-difference-theories
                                     (enable rewrite-linear-equalities-to-iff)
                                     '(<-*-left-cancel))
		  :use (:instance <-*-left-cancel
                        (z j) (y x) (x (/ (+ i (- j)) j)))))
	 :rule-classes nil))

(defrule niq-bounds
  :parents (niq-lemmas)
  :short "Linear (D): @('i/j - 1 < (NIQ i j) <= i/j')"
  :long "<p>This lemma serves as a :LINEAR definition of @(see
NONNEGATIVE-INTEGER-QUOTIENT), and allows us to derive interesting properties
of @(see FLOOR) and @(see TRUNCATE) by linear arithmetic.</p>

<p>This lemma is stored as a :LINEAR rule under NIQ since we think of this as a
property of NIQ, and not as a general property of (/ I J).</p>"

  (implies (niq-guard i j)
           (and (<= (nonnegative-integer-quotient i j) (/ i j))
                (< (- (/ i j) 1) (nonnegative-integer-quotient i j))))
  :rule-classes ((:linear :trigger-terms ((nonnegative-integer-quotient i j))))
  :hints
  (("Goal" :in-theory (enable ifix nfix nonnegative-integer-quotient
                              ratio-theory-of-1))
   ("Subgoal *1/2.2" :use (:instance niq-bounds-help-1
                           (i i) (j j)
                           (x (nonnegative-integer-quotient (+ i (- j)) j))))))

;< Although the following follows naturally from NIQ-BOUNDS, it can't be
;proved by linear alone, probably because (/ i j) is `too heavy'.

(defrule niq-type
  :parents (niq-lemmas)
  :short "Decide @('(NIQ i j) = 0'), @('(NIQ i j) > 0'), and @('(NIQ i j) =
i/j') based on the inequalities of i and j, and the INTEGERP-ness of i/j."

  (implies (niq-guard i j)
           (and (equal (equal (nonnegative-integer-quotient i j) 0)
                       (< i j))
                (equal (< 0 (nonnegative-integer-quotient i j))
                       (>= i j))
                (equal (equal (nonnegative-integer-quotient i j) (/ i j))
                       (integerp (/ i j)))))
  :rule-classes
  ((:rewrite)
   (:linear :corollary (implies (and (>= i j)
                                     (niq-guard i j))
                                (< 0 (nonnegative-integer-quotient i j))))
   (:rewrite :corollary (implies (and (< i j)
                                      (niq-guard i j))
                                 (equal (nonnegative-integer-quotient i j)
                                        0)))
   (:rewrite :corollary (implies (and (equal r (/ i j))
                                      (integerp r)
                                      (niq-guard i j))
                                 (equal (nonnegative-integer-quotient i j) r))))
  :disable (niq-bounds <-*-/-left)
  :use (niq-bounds))


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

(defrule truncate-rem-elim
  :parents (truncate-lemmas)
  :short "Rewrite: @('(+ (REM x y) (* y (TRUNCATE x y))) = x')."
  (implies
   ;; (qr-guard x y) ; changed for v2-9-2 at Jared Davis's suggestion
   (and (force (real/rationalp x))
        (force (real/rationalp y)))
   (equal (+ (rem x y) (* y (truncate x y)))
          x))
  :rule-classes (:rewrite :elim)
  :enable rem)

(defrule truncate-=-x/y
  :parents (truncate-lemmas)
  :short "Rewrite: @('(TRUNCATE x y) = x/y'), when x/y is an integer."
  :long "<p>This rule is a corollary of a more general equality, which is also
stored as a :REWRITE and :GENERALIZE rule.</p>"
  (implies (qr-guard x y)
           (equal (equal (truncate x y) (/ x y))
                  (integerp (/ x y))))
  :rule-classes ((:rewrite)
                 (:generalize)
                 (:rewrite :corollary (implies (and (equal r (/ x y))
                                                    (integerp r)
                                                    (qr-guard x y))
                                               (equal (truncate x y) r))))
  :in-theory (set-difference-theories (enable truncate equal-*-x-y-x)
                                      '(commutativity-of-*)))

;<  This is a fast and beautiful proof, using the :LINEAR rule NIQ-BOUNDS.

(defrule truncate-bounds
  :parents (truncate-lemmas)
  :short "Linear (D) : @('x/y - 1 < (TRUNCATE x y) <= x/y'), when @('x/y >= 0');
 @('x/y <= (TRUNCATE x y) < x/y + 1'), when @('x/y =< 0')."

  :long "<p>This lemma `defines' TRUNCATE as a set of inequalties.  Many of the
properties of TRUNCATE will be derived from this theorem.  Unfortunately, this
lemma is implicated in thrashing in the linear arithmetic procedure unless the
inequalities of X and Y can be decided, so it may need to be DISABLEd at times.
This lemma is stored as a :LINEAR rule for TRUNCATE exclusively since we
consider it to be a property of TRUNCATE, and not a general property of (/ x
y).</p>

<p>The statement of the hypotheses of this lemma is critical for its proper
application.  It is necessary for each inequality of x and y to stand alone in
order to be relieveable by linear arithmetic.</p>"

  (and (implies (and (>= x 0) (> y 0) (qr-guard x y))
                (and (< (- (/ x y) 1) (truncate x y))
                     (<= (truncate x y) (/ x y))))
       (implies (and (<= x 0) (< y 0) (qr-guard x y))
                (and (< (- (/ x y) 1) (truncate x y))
                     (<= (truncate x y) (/ x y))))
       (implies (and (>= x 0) (< y 0) (qr-guard x y))
                (and (<= (/ x y) (truncate x y))
                     (< (truncate x y) (+ (/ x y) 1))))
       (implies (and (<= x 0) (> y 0) (qr-guard x y))
                (and (<= (/ x y) (truncate x y))
                     (< (truncate x y) (+ (/ x y) 1)))))
  :rule-classes ((:linear :trigger-terms ((truncate x y))))
  :in-theory (set-difference-theories (enable truncate
                                              rational-implies2)
                                      '(<-*-/-left <-*-/-right)))

;<  Without the :CASES hint, the inequality conditions simplify to a form
;that doesn't allow us to decide the sign of X, and the proof fails.  With
;the :CASES hint, we can decide the sign of X and the proof is obvious from
;TRUNCATE-BOUNDS.

(defrule truncate-type
  :parents (truncate-lemmas)
  :short "Decide @('(TRUNCATE x y) < 0'), @('(TRUNCATE x y) > 0'), and
@('(TRUNCATE x y) = 0') based on inequalities of x and y."

  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
:TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we can
decide the inequalities of X and Y the :LINEAR forms may thrash.</p>"

  (implies (qr-guard x y)
           (and (equal (< (truncate x y) 0)
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
   (:linear :corollary (implies
                        (and (<= x 0) (> y 0) (<= y (- x)) (qr-guard x y))
                        (< (truncate x y) 0)))
   (:linear :corollary (implies
                        (and (>= x 0) (< y 0) (<= (- y) x) (qr-guard x y))
                        (< (truncate x y) 0)))
   (:linear :corollary (implies
                        (and (>= x 0) (> y 0) (<= y x) (qr-guard x y))
                        (> (truncate x y) 0)))
   (:linear :corollary (implies
                        (and (<= x 0) (< y 0) (>= y x) (qr-guard x y))
                        (> (truncate x y) 0)))
   (:rewrite :corollary (implies
                         (and (< (abs x) (abs y)) (qr-guard x y))
                         (equal (truncate x y) 0)))
   (:type-prescription :corollary (implies
                                   (and (<= x 0) (> y 0) (qr-guard x y))
                                   (<= (truncate x y) 0)))
   (:type-prescription :corollary (implies
                                   (and (>= x 0) (< y 0) (qr-guard x y))
                                   (<= (truncate x y) 0)))
   (:type-prescription :corollary (implies
                                   (and (>= x 0) (> y 0) (qr-guard x y))
                                   (>= (truncate x y) 0)))
   (:type-prescription :corollary (implies
                                   (and (<= x 0) (< y 0) (qr-guard x y))
                                   (>= (truncate x y) 0))))
  :cases ((< x 0) (> x 0)))

;< These follow immediately from the definition of TRUNCATE.  If we enter
;these lemmas in a theory that includes the :LINEAR rules for TRUNCATE we will
;observe severe thrashing in linear arithmetic, since these rules are
;independent of the signs of x and y.  So, we'll just prove them in the theory
;that prevails at the beginning of this book.

(encapsulate ()

  (local (in-theory (current-theory 'begin-quotient-remainder-lemmas)))
  (local (in-theory (enable truncate)))

  (local (defthm foo (equal (real/rationalp (- x))
                            (or (real/rationalp x)
                                (not (acl2-numberp x))))))

  (defrule truncate-minus
    :parents (truncate-lemmas)
    :short "Rewrite: @('(TRUNCATE (- x) y) = (- (TRUNCATE x y))') and
@('(TRUNCATE x (- y)) = (- (TRUNCATE x y))')."
    (and (equal (truncate (- x) y) (- (truncate x y)))
         (equal (truncate x (- y)) (- (truncate x y))))
    :in-theory (enable denominator-unary-minus)
    :expand (nonnegative-integer-quotient 0 (denominator (- (* x (/ y))))))

  (defruled rewrite-truncate-x*y-z-left
    :parents (truncate-lemmas)
    :short "Rewrite (D): @('(TRUNCATE (* x y) z) = (TRUNCATE y (/ z x))'), when x /= 0."
    :long "<p>Since we don't presume any rewriting strategy for @(see /)
  vis-a-vis @(see *), this often useful rule is exported DISABLEd.</p>"
    (equal (truncate (* x y) z)
           (truncate y (/ z x))))

  (defruled rewrite-truncate-x*y-z-right
    :parents (truncate-lemmas)
    :short "Rewrite (D): @('(TRUNCATE (* x y) z) = (TRUNCATE x (/ z y))'), when y /= 0."
    :long "<p>Since we don't presume any rewriting strategy for / vis-a-vis *, this
  often useful rule is exported DISABLEd.</p>"
    (equal (truncate (* x y) z)
           (truncate x (/ z y))))

  (defrule truncate-cancel-*
    :parents (truncate-lemmas)
    :short "Rewrite: @('(TRUNCATE (* x y) y) = (TRUNCATE x 1)')."
    (implies (qr-guard x y)
             (and (equal (truncate (* x y) y) (truncate x 1))
                  (equal (truncate (* y x) y) (truncate x 1))))))

;<  The linear rules refuse to fire on their own.  From TRUNCATE-BOUNDS and
;NIQ-BOUNDS it is obvious that these are the same integers.

(defruled integer-truncate-as-niq
  :parents (truncate-lemmas)
  :short "Rewrite (D) : @('(TRUNCATE i j) = (SIGNUM i) * (SIGNUM j) * (NIQ i
    j)'), for integers i,j."
  :long "<p>This rule shows that TRUNCATE is the \"usual\" (i.e., FORTRAN-style)
  integer quotient for both positive and negative integers.</p>"
  (implies (and (integerp i)
                (integerp j)
                (force (not (equal j 0))))
           (equal (truncate i j)
                  (* (signum i) (signum j)
                     (nonnegative-integer-quotient (abs i) (abs j)))))
  :in-theory (disable truncate-bounds niq-bounds <-*-/-right <-*-/-left
                      truncate-type default-<-1 default-<-2
                      integerp-+-minus-*)
  :use ((:instance truncate-bounds (x i) (y j))
        (:instance niq-bounds (i (abs i)) (j (abs j)))))

;; (defthm truncate-truncate-integer
;;   (implies
;;    (and (integerp i)
;; 	(integerp j)
;; 	(integerp k)
;; 	(force (not (equal j 0)))
;; 	(force (not (equal k 0))))
;;    (equal (truncate (truncate i j) k)
;; 	  (truncate i (* j k))))
;;   :hints
;;   (("Goal"
;;     :in-theory (enable truncate))))
;;   :hints
;;   (("Goal"
;;     :in-theory (e/d (integer-truncate-as-niq niq-type niq-i/j-<-k
;; 					     prefer-*-to-/)
;; 		    (x-<-y*z))
;;     :use ((:instance x-<-y*z (x (abs i)) (y (abs j)) (z (abs k))))))
;;     Rewrite: (TRUNCATE (TRUNCATE i j) k) = (TRUNCATE i (* j k))
;;     for integers i,j,k.~/~/~/")


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    REM
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defruled linearize-rem
  :parents (rem-lemmas)
  :short "Rewrite (D): Transform @('(REM x y) < z'), @('(REM x y) > z'), and
@('(REM x y) = z') into an equivalent @(see TRUNCATE) expression suitable for
reasoning about with @(see TRUNCATE-BOUNDS) and other @(see truncate-lemmas)."
  :long "<p>Since this lemma can be considered a \"definition\" of REM, it is
exported DISABLED.</p>"
  (implies (and (qr-guard x y)
                (force (real/rationalp z)))
           (and (equal (< (rem x y) z)
                       (if (> y 0)
                           (< (- (/ x y) (truncate x y)) (/ z y))
                         (> (- (/ x y) (truncate x y)) (/ z y))))
                (equal (> (rem x y) z)
                       (if (> y 0)
                           (> (- (/ x y) (truncate x y)) (/ z y))
                         (< (- (/ x y) (truncate x y)) (/ z y))))
                (equal (equal (rem x y) z)
                       (equal (- (/ x y) (truncate x y)) (/ z y)))))
  :enable (rem prefer-*-to-/))

(defrule rem-=-0
  :parents (rem-lemmas)
  :short "Rewrite: @('(REM x y) = 0'), when @('x/y') is an integer."
  :long "<p>This rule is a corollary of a more general equality.  The equality
  is also stored as a :REWRITE and :GENERALIZE rule.</p>"
  (implies (qr-guard x y)
           (equal (equal (rem x y) 0)
                  (integerp (/ x y))))
  :rule-classes ((:rewrite)
                 (:generalize)
                 (:rewrite :corollary (implies (and (integerp (/ x y))
                                                    (qr-guard x y))
                                               (equal (rem x y) 0))))
  :enable (linearize-rem))

(defrule rem-x-y-=-x
  :parents (rem-lemmas)
  :short "@('(REM x y) = x'), when @('|x| < |y|')."
  :long "<p>This rule is a corollary of a more general equality which is also
  stored as a :REWRITE and :GENERALIZE rule.</p>"
  (implies (qr-guard x y)
           (equal (equal (rem x y) x)
                  (< (abs x) (abs y))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:rewrite :corollary (implies (and (< (abs x) (abs y))
                                      (qr-guard x y))
                                 (equal (rem x y) x))))
  :enable (linearize-rem))

(defrule integerp-rem
  :parents (rem-lemmas)
  :short "Type-Prescription: (REM i j) is an integer, when i and j are integers."
  (implies (and (integerp i)
                (integerp j)
                (force (not (equal j 0))))
           (integerp (rem i j)))
  :rule-classes :type-prescription
  :enable rem)

;<  Again, this rule is an easy consequence of TRUNCATE-BOUNDS, but (/ x y)
;is too `heavy' to let it fire naturally, so we have to :USE it.

(defrule rem-bounds
  :parents (rem-lemmas)
  :short "Linear: Useful forms of the fact that @('(REM x y) < |y|')."
  :long "<p>This lemma is also stored as a :GENERALIZE rule.</p>"
  (and (implies (and (>= x 0)
                     (qr-guard x y))
                (< (rem x y) (abs y)))
       (implies (and (<= x 0)
                     (qr-guard x y))
                (> (rem x y) (- (abs y)))))
  :rule-classes ((:linear :trigger-terms ((rem x y)))
                 (:generalize))
  :enable linearize-rem
  :disable truncate-bounds
  :use truncate-bounds)

(defrule rem-type
  :parents (rem-lemmas)
  :short "Decide @('(REM x y) < 0') and @('(REM x y) > 0') based on the sign of
    x and the INTEGERP-ness of x/y."
  :long "<p>This rule is stored as appropriate :REWRITE, :LINEAR, :GENERALIZE,
  and :TYPE-PRESCRIPTION rules.</p>"
  (implies (qr-guard x y)
           (and (equal (< (rem x y) 0)
                       (and (< x 0)
                            (not (integerp (/ x y)))))
                (equal (> (rem x y) 0)
                       (and (> x 0)
                            (not (integerp (/ x y)))))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:linear :corollary (implies (and (< x 0)
                                     (not (integerp (/ x y)))
                                     (qr-guard x y))
                                (< (rem x y) 0)))
   (:linear :corollary (implies (and (> x 0)
                                     (not (integerp (/ x y)))
                                     (qr-guard x y))
                                (> (rem x y) 0)))
   (:linear :corollary (implies (and (<= x 0) (qr-guard x y))
                                (<= (rem x y) 0)))
   (:linear :corollary (implies (and (>= x 0)
                                     (qr-guard x y))
                                (>= (rem x y) 0)))
   (:type-prescription :corollary (implies (and (< x 0)
                                                (not (integerp (/ x y)))
                                                (qr-guard x y))
                                           (< (rem x y) 0)))
   (:type-prescription :corollary (implies (and (> x 0)
                                                (not (integerp (/ x y)))
                                                (qr-guard x y))
                                           (> (rem x y) 0)))
   (:type-prescription :corollary (implies (and (<= x 0)
                                                (qr-guard x y))
                                           (<= (rem x y) 0)))
   (:type-prescription :corollary (implies (and (>= x 0)
                                                (qr-guard x y))
                                           (>= (rem x y) 0))))
  :in-theory (set-difference-theories (enable linearize-rem)
                                      '(<-*-/-right <-*-/-left)))

(defrule rem-minus
  :parents (rem-lemmas)
  :short "Rewrite: @('(REM (- x) y) = (- (REM x y))');
   @('(REM x (- y)) = (SIGNUM x) * (SIGNUM y) * (REM x y)')."
  (implies (qr-guard x y)
           (and (equal (rem (- x) y)
                       (- (rem x y)))
                (equal (rem x (- y))
                       (* (signum y) (signum y) (rem x y)))))
  :enable linearize-rem
  :expand (rem x y))


;;;****************************************************************************
;;;
;;;    FLOOR and MOD
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;  We'll sometimes use this lemma which allows us to prove properties of
;  FLOOR from properties of TRUNCATE.

(defruled floor-as-truncate
  :parents (floor-lemmas)
  :short "Rewrite (FLOOR x y) to a function of (TRUNCATE x y)."
  (implies (qr-guard x y)
           (equal (floor x y)
                  (if (or (integerp (/ x y))
                          (> (/ x y) 0))
                      (truncate x y)
                    (- (truncate x y) 1))))
  :enable (floor truncate))

(defrule floor-mod-elim
  :parents (floor-lemmas)
  :short "Rewrite: @('(+ (MOD x y) (* y (FLOOR x y))) = x')."
  :long "<p>This rule is also stored as an :ELIM rule.</p>"
  ;; [Jared] modified on 2014-07-29 to not forcibly assume acl2-numberp, to
  ;; avoid name clash with arithmetic-5.
  (implies (acl2-numberp x)
	   (equal (+ (mod x y) (* y (floor x y))) x))
  :rule-classes (:rewrite :elim)
  :enable mod)

(defrule floor-=-x/y
  :parents (floor-lemmas)
  :short "Rewrite @('(FLOOR x y) = x/y'), when x/y is an integer."
  :long "<p>This rule is a corollary of a more general equality which is also
  stored as a :REWRITE and :GENERALIZE rule.</p>"
  ;; [Jared]: modified on 2014-07-29 to remove unnecessary (qr-guard x y)
  ;; hypothesis and for compatibility with arithmetic-5.
  (equal (equal (floor x y) (/ x y))
         (integerp (/ x y)))
  ;; The original IHS rule had the following rule classes:
  ;;
  ;; ((:rewrite)
  ;;  (:generalize)
  ;;  (:rewrite :corollary (implies (and (equal r (/ x y))
  ;;                                     (integerp r))
  ;;                                (equal (floor x y) r))))
  ;;
  ;; The original arithmetic-5 rule has the following rule-classes:
  ;;
  ;; (:rewrite :corollary (implies (integerp (/ x y))
  ;;                               (equal (floor x y)
  ;;                                      (/ x y))))
  ;; (:rewrite :corollary (implies (equal (* x (/ y)) z)
  ;;                               (equal (equal (floor x y) z)
  ;;                                      (integerp z))))
  ;;
  ;; Solution: DO ALL THE THINGS.
  :rule-classes ((:rewrite)
                 (:generalize)
                 (:rewrite :corollary (implies (and (equal r (/ x y))
                                                    (integerp r))
                                               (equal (floor x y) r)))
                 (:rewrite :corollary (implies (integerp (/ x y))
                                               (equal (floor x y)
                                                      (/ x y))))
		 (:rewrite :corollary (implies (equal (* x (/ y)) z)
                                               (equal (equal (floor x y) z)
                                                      (integerp z)))))
  :in-theory (set-difference-theories (enable floor equal-*-x-y-x)
                                      '(commutativity-of-*)))

;< Another beautiful proof from NIQ-BOUNDS.

(defrule floor-bounded-by-/
  :parents (floor-lemmas)
  :short "Linear (D) : @('x/y - 1 < (FLOOR x y) <= x/y')."
  :long "<p>This lemma \"defines\" FLOOR as a set of inequalties.  Many of the
properties of FLOOR will be derived from this theorem.  Unfortunately, this
lemma is implicated in thrashing in the linear arithmetic procedure and must be
DISABLEd at times.  This lemmas is stored as a :LINEAR rule for FLOOR
exclusively since we consider it to be a property of FLOOR, and not a general
property of @('(/ x y)').</p>"
  (implies (qr-guard x y)
           (and (< (- (/ x y) 1) (floor x y))
                (<= (floor x y) (/ x y))))
  :rule-classes ((:linear :trigger-terms ((floor x y)))
                 (:generalize))
  :in-theory (set-difference-theories (enable floor rational-implies2)
                                      '(<-*-/-left <-*-/-right)))

;< We need to consider the :CASES to get FLOOR-BOUNDED-BY-/ to do its job.  This
;proof does 2 eliminations (considering (FLOOR x y) = -1) but it goes
;through.  If we simply :USE FLOOR-BOUNDED-BY-/ with the same :CASES it also works
;and takes about the same amount of time.  I'll bet that it could get the
;(FLOOR x y) = -1 cases with FLOOR-BOUNDED-BY-/ if we let FLOOR-BOUNDED-BY-/ trigger on
;(/ x y).

;; The lemma FLOOR-TYPE had too many cases, so I split it in to 4 lemmas:
;; FLOOR-TYPE-1, FLOOR-TYPE-2, FLOOR-TYPE-3 and FLOOR-TYPE-4.
;; A. Flatau 17-Nov-1994

(defrule floor-type-1
  :parents (floor-lemmas)
  :short "Decide @('(FLOOR x y) < 0') based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
  :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
  can decide the inequalities of x and y the :LINEAR forms may thrash.</p>"
  (implies (qr-guard x y)
	   (iff (< (floor x y) 0)
                (or (and (< x 0) (> y 0))
                    (and (> x 0) (< y 0)))))
  :cases ((< (/ x y) 0) (> (/ x y) 0))
  :in-theory (enable normalize-<-/-to-*-3)
  :rule-classes
  ((:rewrite :corollary (implies (qr-guard x y)
                                 (equal (< (floor x y) 0)
                                        (or (and (< x 0) (> y 0))
                                            (and (> x 0) (< y 0))))))
   (:generalize :corollary (implies (qr-guard x y)
                                    (equal (< (floor x y) 0)
                                           (or (and (< x 0) (> y 0))
                                               (and (> x 0) (< y 0))))))
   (:linear :corollary (implies (and (< x 0) (> y 0) (qr-guard x y))
                                (< (floor x y) 0)))
   (:linear :corollary (implies (and (> x 0) (< y 0) (qr-guard x y))
                                (< (floor x y) 0)))
   (:type-prescription :corollary (implies (and (< x 0)
                                                (> y 0)
                                                (qr-guard x y))
                                           (< (floor x y) 0)))
   (:type-prescription :corollary (implies (and (> x 0)
                                                (< y 0)
                                                (qr-guard x y))
                                           (< (floor x y) 0)))))

(defrule floor-type-2
  :parents (floor-lemmas)
  :short "Decide @('(FLOOR x y) > 0') based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
  :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
  can decide the inequalities of x and y the :LINEAR forms may thrash.</p>"
  (implies (qr-guard x y)
	   (equal (> (floor x y) 0)
		  (or (and (>= x 0) (> y 0) (<= y x))
		      (and (<= x 0) (< y 0) (>= y x)))))
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
  :hints (("Subgoal 6" :cases ((<= x 0) (<= 0 x)))
          ("Subgoal 2" :cases ((<= x 0) (<= 0 x)))))

(defrule floor-type-3
  :parents (floor-lemmas)
  :short "Decide @('(FLOOR x y) > 0') based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
  :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
  can decide the inequalities of x and y the :LINEAR forms may thrash.</p>"
  (implies (qr-guard x y)
	   (equal (equal (floor x y) 0)
		  (or (and (>= x 0) (> y 0) (< x y))
		      (and (<= x 0) (< y 0) (> x y)))))
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
  :cases ((< (/ x y) 0) (> (/ x y) 0)))

(defrule floor-type-4
  :parents (floor-lemmas)
  :short "Decide @('(FLOOR x y) = -1') based on inequalities of x and y."
  :long "<p>This rule is available in various forms: :REWRITE, :LINEAR,
  :TYPE-PRESCRIPTION, and :GENERALIZE as appropriate.  Note that unless we
  can decide the inequalities of x and y the :LINEAR forms may thrash.</p>"
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
					       '(floor-bounded-by-/))
	   :use (:instance floor-bounded-by-/ (x x) (y y)))))

(defsection floor-type-linear
  :parents (floor-lemmas)
  :short "A theory of the :LINEAR rules created by the lemmas FLOOR-TYPE-1 and
  FLOOR-TYPE-2."
  :long "<p>These rules are implicated in thrashing linear arithmetic, so we
  provide this theory which can be DISABLED if it becomes a problem.</p>"

  (deftheory floor-type-linear
    '((:linear floor-type-1 . 1)
      (:linear floor-type-1 . 2)
      (:linear floor-type-2 . 1)
      (:linear floor-type-2 . 2))))

;< These follow immediately from the definition of FLOOR.  If we enter
;these lemmas in a theory that includes the :LINEAR rules for FLOOR we will
;observe severe thrashing in linear arithmetic, since these rules are
;independent of the signs of x and y.  So, we'll just prove them in the theory
;that prevails at the beginning of this book.

(encapsulate ()

  (local (in-theory (current-theory 'begin-quotient-remainder-lemmas)))
  (local (in-theory (enable floor)))

  (defrule floor-minus
    :parents (floor-lemmas)
    :short "Rewrite @('(FLOOR (- x) y)')."
    (and (implies (qr-guard x y)
                  (equal (floor (- x) y)
                         (if (integerp (* x (/ y)))
                             (- (floor x y))
                           (- (- (floor x y)) 1))))
         (implies (qr-guard x y)
                  (equal (floor x (- y))
                         (if (integerp (* x (/ y)))
                             (- (floor x y))
                           (- (- (floor x y)) 1)))))
    :enable denominator-unary-minus)

  (defruled rewrite-floor-x*y-z-left
    :parents (floor-lemmas)
    :short "Rewrite (D): @('(FLOOR (* x y) z) = (FLOOR y (/ z x))'), when x /= 0."
    :long "<p>Since we don't presume any rewriting strategy for / vis-a-vis *,
  this often useful rule is exported DISABLEd.</p>"
    (implies (and (real/rationalp x)
                  (not (equal x 0))
                  (real/rationalp y)
                  (force (real/rationalp z))
                  (force (not (equal z 0))))
             (equal (floor (* x y) z)
                    (floor y (/ z x)))))

  (defruled rewrite-floor-x*y-z-right
    :parents (floor-lemmas)
    :short "Rewrite: @('(FLOOR (* x y) z) = (FLOOR x (/ z y))'), when y /= 0."
    :long "<p>Since we don't presume any rewriting strategy for / vis-a-vis *,
  this often useful rule is exported DISABLEd.</p>"
    (implies (and (real/rationalp x)
                  (real/rationalp y)
                  (not (equal y 0))
                  (force (real/rationalp z))
                  (force (not (equal z 0))))
             (equal (floor (* x y) z)
                    (floor x (/ z y)))))

  (defrule floor-cancel-*
    :parents (floor-lemmas)
    :short "Rewrite: @('(FLOOR (* x y) y) = (FLOOR x 1)')."
    (implies (qr-guard x y)
             (and (equal (floor (* x y) y) (floor x 1))
                  (equal (floor (* y x) y) (floor x 1)))))

  (defrule floor-cancel-*-2
    :parents (floor-lemmas)
    :short "Rewrite: @('(FLOOR (* x y) (* x z)) = (FLOOR y z)')."
    (implies (and (real/rationalp x)
                  (not (equal x 0))
                  (real/rationalp y)
                  (real/rationalp z)
                  (not (equal z 0)))
             (equal (floor (* x y) (* x z))
                    (floor y z)))
    :enable rewrite-floor-x*y-z-left))

;  This proof is only this complicated because I wanted to prove the most
;  general thing possible.

(encapsulate ()

  (local
   (defthm crock0
     (implies (and (< 1 y)
                   (< 0 x)
                   (qr-guard x y))
              (< (/ x y) x))
     :rule-classes :linear))

  (local
   (defthm crock1
     (implies (and (<= (+ 1 1) y)
                   (< x 0)
                   (qr-guard x y))
              (<= (* x y) (+ x x)))
     :rule-classes :linear
     :hints (("Goal" :in-theory (disable <-*-left-cancel (binary-+))
	      :use (:instance <-*-left-cancel (z x) (x 2) (y y))))))

  (local
   (defthm crock2
     (implies (and (<= 2 y)
                   (< x 0)
                   (< y (- x))
                   (qr-guard x y))
              (< x (- (/ x y) 1)))
     :rule-classes :linear
     :hints
     (("Goal"
       :in-theory (e/d (prefer-*-to-/) (<-*-left-cancel))
       :use (:instance <-*-left-cancel (z y) (x x) (y (- (/ x y) 1)))))))

  (defrule floor-recursion
    :parents (floor-lemmas)
    :short "Rewrite: @('(FLOOR x y) < x'), when @('x > 0') and @('y > 1');
           @('x < (FLOOR x y)'), when @('x < -1') and @('y >= 2')."
    :long "<p>This theorem justifies recursion by FLOOR using the measure
  ACL2-COUNT, which for integers i is simply (ABS i).  Thus, this theorem won't
  justify a simple recursion by a negative y, since (FLOOR 1 y) = -1 for
  negative y, and (ABS -1) = (ABS 1).  For the most general case that includes
  negative y one would need to define a different measure that could handle
  this condition.</p>"
    ;; [Jared]: renamed from justify-floor-recursion to simply floor-recursion on
    ;; 2014-07-29, to avoid name conflict with arithmetic-5
    (implies (qr-guard x y)
             (and (implies (and (< 0 x)
                                (< 1 y))
                           (< (floor x y) x))
                  (implies (and (< x -1)
                                (<= 2 y))
                           (< x (floor x y)))))
    :hints (("Goal" :use ((:instance floor-bounded-by-/ (x x) (y y))))
            ("Goal'" :cases ((< 0 x) (< y (- x)))))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    MOD
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defruled linearize-mod
  :parents (mod-lemmas)
  :short "Rewrite (D): Transform @('(MOD x y) < z'), @('(MOD x y) > z'), and
  @('(MOD x y) = z') into an equivalent FLOOR expression suitable for reasoning
  about with FLOOR-BOUNDED-BY-/ and other theorems about FLOOR."
  :long "<p>Since this lemma can be considered a `definition' of MOD, it is
  exported DISABLED.</p>"
  (implies (and (qr-guard x y)
                (force (real/rationalp z)))
           (and (equal (< (mod x y) z)
                       (if (> y 0)
                           (< (- (/ x y) (floor x y)) (/ z y))
                         (> (- (/ x y) (floor x y)) (/ z y))))
                (equal (> (mod x y) z)
                       (if (> y 0)
                           (> (- (/ x y) (floor x y)) (/ z y))
                         (< (- (/ x y) (floor x y)) (/ z y))))
                (equal (equal (mod x y) z)
                       (equal (- (/ x y) (floor x y)) (/ z y)))))
  :enable (mod prefer-*-to-/))

(defrule mod-=-0
  :parents (mod-lemmas)
  :short "Rewrite: @('(MOD x y) = 0'), when x/y is an integer."
  :long "<p>This rule is a corollary of a more general equality.  The equality
  is also stored as a :REWRITE and :GENERALIZE rule.</p>"
  (implies (qr-guard x y)
           (equal (equal (mod x y) 0)
                  (integerp (/ x y))))
  :rule-classes ((:rewrite)
                 (:generalize)
                 (:rewrite :corollary (implies (and (integerp (/ x y))
                                                    (qr-guard x y))
                                               (equal (mod x y) 0))))
  :enable linearize-mod
  :disable commutativity-of-*)

(defrule mod-x-y-=-x-for-rationals
  :parents (mod-lemmas)
  :short "Rewrite: @('(MOD x y) = x'), when @('|x| <= |y|') and x and y have
  the same sign."
  :long "<p>This rule is a corollary of a more general equality which is also
  stored as :REWRITE and :GENERALIZE rules.</p>"
  (implies (qr-guard x y)
           (equal (equal (mod x y) x)
                  (or (and (>= x 0) (> y 0) (< x y))
                      (and (<= x 0) (< y 0) (> x y)))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:rewrite :corollary (implies (and (>= x 0) (> y 0) (< x y) (qr-guard x y))
                                 (equal (mod x y) x)))
   (:rewrite :corollary (implies (and (<= x 0) (< y 0) (> x y) (qr-guard x y))
                                 (equal (mod x y) x))))
  :enable linearize-mod)

;<  Again, we need to :USE FLOOR-BOUNDED-BY-/ to make this proof quick.

(encapsulate nil

   (local (defthm another-crock
	    (equal (equal (- x) 1) (equal x -1))))

   (defrule mod-x-y-=-x+y-for-rationals
     :parents (mod-lemmas)
     :short "Rewrite: @('(MOD x y) = x + y'), when @('|x| <= |y|') and x and y
  have different signs and x /= 0."
     :long "<p>This rule is a corollary of a more general equality which is
  also stored as :REWRITE and :GENERALIZE rules.</p>"
     (implies (qr-guard x y)
              (equal (equal (mod x y) (+ x y))
                     (or (and (> x 0) (< y 0) (<= x (- y)))
                         (and (< x 0) (> y 0) (<= (- x) y)))))
     :rule-classes
     ((:rewrite)
      (:generalize)
      (:rewrite :corollary (implies (and (> x 0) (< y 0) (<= x y) (qr-guard x y))
                                    (equal (mod x y) (+ x y))))
      (:rewrite :corollary (implies (and (< x 0) (> y 0) (<= (- x) y) (qr-guard x y))
                                    (equal (mod x y) (+ x y)))))
     :in-theory (e/d (linearize-mod) (floor-bounded-by-/))
     :use floor-bounded-by-/))

;; Added the :rule-classes :rewrite as this seems necessary at times.
;; A. Flatau  1-Dec-1994
;; Changed variable names from i, j to m, n to match RTL and arithmetic-5 --
;; Sol Swords 1/2011
(defrule integerp-mod
  :parents (mod-lemmas)
  :short "Type-Prescription: @('(MOD m n)') is an integer, when m and n are
  integers."
  (implies (and (integerp m)
                (integerp n))
           (integerp (mod m n)))
  :enable mod
  :rule-classes (:rewrite :type-prescription))

(defrule mod-bounded-by-modulus
  :parents (mod-lemmas)
  :short "Linear: Useful forms of the fact that @('|(MOD x y)| < |y|')."
  :long "<p>This lemma is also stored as a :GENERALIZE rule.</p>"
  (and (implies (and (> y 0)
                     (qr-guard x y))
                (< (mod x y) y))
       (implies (and (< y 0)
                     (qr-guard x y))
                (> (mod x y) y)))
  :rule-classes ((:linear :trigger-terms ((mod x y)))
                 (:generalize))
  :enable linearize-mod
  :disable floor-bounded-by-/
  :use floor-bounded-by-/)

(defrule mod-type
  :parents (mod-lemmas)
  :short "Decide @('(MOD x y) < 0') and @('(MOD x y) > 0') based on the sign of
  y and the INTEGERP-ness of x/y."
  (implies (qr-guard x y)
           (and (equal (< (mod x y) 0)
                       (and (< y 0)
                            (not (integerp (/ x y)))))
                (equal (> (mod x y) 0)
                       (and (> y 0)
                            (not (integerp (/ x y)))))))
  :rule-classes
  ((:rewrite)
   (:generalize)
   (:linear :corollary (implies (and (< y 0)
                                     (not (integerp (/ x y)))
                                     (qr-guard x y))
                                (< (mod x y) 0)))
   (:linear :corollary (implies (and (> y 0)
                                     (not (integerp (/ x y)))
                                     (qr-guard x y))
                                (> (mod x y) 0)))
   (:linear :corollary (implies (and (<= y 0)
                                     (qr-guard x y))
                                (<= (mod x y) 0)))
   (:linear :corollary (implies (and (>= y 0)
                                     (qr-guard x y))
                                (>= (mod x y) 0)))
   (:type-prescription :corollary (implies (and (< y 0)
                                                (not (integerp (/ x y)))
                                                (qr-guard x y))
                                           (< (mod x y) 0)))
   (:type-prescription :corollary (implies (and (> y 0)
                                                (not (integerp (/ x y)))
                                                (qr-guard x y))
                                           (> (mod x y) 0)))
   (:type-prescription :corollary (implies (and (<= y 0)
                                                (qr-guard x y))
                                           (<= (mod x y) 0)))
   (:type-prescription :corollary (implies (and (>= y 0)
                                                (qr-guard x y))
                                           (>= (mod x y) 0))))
  :enable linearize-mod
  :disable (floor-type-3 floor-type-1 (:type-prescription floor))
  :use floor-bounded-by-/)

(defsection mod-type-linear
  :parents (mod-lemmas)
  :short "A theory of the :LINEAR rules created by the lemma MOD-TYPE."
  :long "<p>These rules are implicated in thrashing linear arithmetic, so we
  provide this theory which can be DISABLED if it becomes a problem.</p>"

  (deftheory mod-type-linear
    '((:linear mod-type . 1)
      (:linear mod-type . 2)
      (:linear mod-type . 3)
      (:linear mod-type . 4))))

(defrule mod-minus
  :parents (mod-lemmas)
  :short "Rewrite: @('(MOD (- x) y)') and @('(MOD x (- y))')."
  (implies (qr-guard x y)
           (and (equal (mod (- x) y)
                       (if (integerp (/ x y))
                           0
                         (- y (mod x y))))
                (equal (mod x (- y))
                       (if (integerp (/ x y))
                           0
                         (- (mod x y) y)))))
  :enable linearize-mod
  :expand (mod x y))

(encapsulate ()

  (local (in-theory (current-theory 'begin-quotient-remainder-lemmas)))

  (defthm simplify-mod-*
    (implies (and (integerp x)
                  (not (equal x 0))
                  (integerp y)
                  (integerp z)
                  (not (equal z 0)))
             (equal (mod (* x y) (* x z))
                    (* x (mod y z))))
    :hints (("Goal" :in-theory (enable mod floor-cancel-*-2)))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Addition Cancellation theory for FLOOR and MOD
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;< This next section of lemmas has nothing to do with the :LINEAR theory of
;FLOOR and MOD, so we DISABLE the key :LINEAR lemmas to avoid thrashing.

(local (in-theory (disable floor-bounded-by-/ floor-type-1 floor-type-2
			   floor-type-3 floor-type-4 mod-bounded-by-modulus mod-type)))

;  These LOCAL theorems will be superceded by CANCEL-FLOOR-+-BASIC,
;  CANCEL-FLOOR-+-3, CANCEL-MOD-+-BASIC, and CANCEL-MOD-+-3.

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
     :use ((:instance floor-bounded-by-/ (x (+ x (* i y))) (y y))
	   (:instance floor-bounded-by-/ (x (- x (* i y))) (y y))
	   (:instance floor-bounded-by-/ (x x) (y y)))))))

(local
 (defthm floor-x+y+i*z-z
   (implies
    (and (integerp i)
	 (force (real/rationalp x))
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

(local
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
     :in-theory (enable mod)))))

(local
 (defthm mod-x+y+i*z-z
   (implies
    (and (integerp i)
	 (force (real/rationalp x))
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
      (and (real/rationalp x)
	   (real/rationalp y)
	   (real/rationalp z)
	   (syntaxp (and (eq x 'x) (eq y 'y) (eq z 'z))))
      (equal (floor (+ x y) z)
	     (floor (+ (+ (mod x z) (mod y z))
		       (* (+ (floor x z) (floor y z)) z)) z)))
     :hints(("Goal" :in-theory (disable mod-x-y-=-x+y-for-rationals
                                        mod-x-y-=-x-for-rationals)))))

  (defruled floor-+
    :parents (floor-lemmas)
    :short "Rewrite (D): @('(FLOOR (+ x y) z)')."
    :long "<p>As this rule could easily loop it is exported DISABLEd.  Don't
   ENABLE this lemma unless you are sure that the FLOOR/MOD term will simplify,
   or else put SYNTAXP guards on the variables x, y, and/or z.</p>"
    (implies (and (force (real/rationalp x))
                  (force (real/rationalp y))
                  (force (real/rationalp z))
                  (force (not (equal z 0))))
             (equal (floor (+ x y) z)
                    (+ (floor (+ (mod x z) (mod y z)) z)
                       (+ (floor x z) (floor y z)))))
    :in-theory (union-theories (disable associativity-of-+
                                        commutativity-2-of-+
                                        associativity-of-*
                                        commutativity-2-of-*
                                        distributivity)
                               '(rationalp-+
                                 #+non-standard-analysis
                                 realp-+
                                 mod))))

(encapsulate ()

  (local
   (defthm mod-+-crock
     (implies
      (and (real/rationalp x)
	   (real/rationalp y)
	   (real/rationalp z)
	   (not (equal z 0))
	   (syntaxp (and (eq x 'x) (eq y 'y) (eq z 'z))))
      (equal (mod (+ x y) z)
	     (mod (+ (+ (mod x z) (mod y z))
		     (* (+ (floor x z) (floor y z)) z)) z)))
     :hints(("Goal" :in-theory (disable mod-x-y-=-x+y-for-rationals
                                        mod-x-y-=-x-for-rationals)))))

  (defruled mod-+
    :parents (mod-lemmas)
    :short "Rewrite (D): @('(MOD (+ x y) z)')."
    :long "<p>As this rule could easily loop it is exported DISABLEd.  Don't
   ENABLE this lemma unless you are sure that the MOD/MOD term will simplify,
   or else put SYNTAXP guards on the variables x, y, and/or z.</p>"
    (implies (and (force (real/rationalp x))
                  (force (real/rationalp y))
                  (force (real/rationalp z))
                  (force (not (equal z 0))))
             (equal (mod (+ x y) z)
                    (mod (+ (mod x z) (mod y z)) z)))
    :in-theory (union-theories (disable associativity-of-+
                                        commutativity-2-of-+
                                        associativity-of-*
                                        commutativity-2-of-*
                                        distributivity)
                               '(rationalp-+
                                 #+non-standard-analysis
                                 realp-+
                                 mod))))

(encapsulate ()

  (local
   (defthm crock0
     (implies
      (and (integerp i)
	   (integerp (* x y)))
      (integerp (* x y i)))))

  (defrule rewrite-floor-mod
    :parents (floor-lemmas)
    :short "Rewrite: @('(FLOOR (MOD x y) z) = (FLOOR x z) - i*(FLOOR x y)'),
    when i = y/z is an integer."
    (implies (and (equal i (/ y z))
                  (integerp i)
                  (qr-guard x y)
                  (qr-guard x z))
             (equal (floor (mod x y) z)
                    (- (floor x z) (* i (floor x y)))))
    :enable mod
    :use ((:instance floor-+ (x x) (y (- (* y (floor x y)))) (z z))))

  (defrule rewrite-mod-mod
    :parents (mod-lemmas)
    :short "Rewrite: (MOD (MOD x y) z) = (MOD x z), when y/z is an integer."
    (implies (and (equal i (/ y z))
                  (integerp i)
                  (qr-guard x y)
                  (qr-guard y z))
             (equal (mod (mod x y) z)
                    (mod x z)))
    :expand ((mod x y) (mod x z))
    :use ((:instance mod-+ (x x) (y (- (* y (floor x y)))) (z z)))))

(defrule cancel-floor-+-basic
  :parents (floor-lemmas)
  :short "Rewrite: @('(FLOOR (+ x y) z) = x/z + (FLOOR y z)'), when x/z is an
  integer; also the commutative form."
  ;; [Jared] modified on 2014-07-29: this was originally called CANCEL-FLOOR-+
  ;; but that name clashes with an arithmetic-5 rule that appears to be more
  ;; sophisticated (it uses bind-free to find cancelling addends, etc.), so I
  ;; am renaming this to cancel-floor-+-basic.
  (implies (and (equal i (/ x z))
                (integerp i)
                (force (real/rationalp x))
                (force (real/rationalp y))
                (force (real/rationalp z))
                (force (not (equal z 0))))
           (and (equal (floor (+ x y) z) (+ i (floor y z)))
                (equal (floor (+ y x) z) (+ i (floor y z)))))
  :enable floor-+)

(defrule cancel-floor-+-3
  :parents (floor-lemmas)
  :short "Rewrite: @('(FLOOR (+ w x y) z) = y/z + (FLOOR (+ w x) z)'), when y/z
  is an integer."
  (implies (and (equal i (/ y z))
                (integerp i)
                (force (real/rationalp w))
                (force (real/rationalp x))
                (force (real/rationalp y))
                (force (real/rationalp z))
                (force (not (equal z 0))))
           (equal (floor (+ w x y) z)
                  (+ i (floor (+ w x) z))))
  :disable cancel-floor-+-basic
  :use ((:instance cancel-floor-+-basic (x y) (y (+ w x)) (z z))))

(defrule cancel-mod-+-basic
  :parents (mod-lemmas)
  :short "Rewrite: @('(MOD (+ x y) z) = (MOD y z)'), when x/z is an integer;
  also the commutative form."
  ;; [Jared] modified on 2014-07-29: this was originally called CANCEL-MOD-+
  ;; but that name clashes with an arithmetic-5 rule that appears to be more
  ;; sophisticated (it uses bind-free to find cancelling addends, etc.), so I
  ;; am renaming this to cancel-floor-+-basic.
  (implies (and (equal i (/ x z))
                (integerp i)
                (force (real/rationalp x))
                (force (real/rationalp y))
                (force (real/rationalp z))
                (force (not (equal z 0))))
           (and (equal (mod (+ x y) z) (mod y z))
                (equal (mod (+ y x) z) (mod y z))))
  :enable mod-+)

(defrule cancel-mod-+-3
  :parents (mod-lemmas)
  :short "Rewrite: @('(MOD (+ w x y) z) = (MOD (+ w x) z)'), when y/z is an
  integer."
  (implies (and (equal i (/ y z))
                (integerp i)
                (force (real/rationalp w))
                (force (real/rationalp x))
                (force (real/rationalp y))
                (force (real/rationalp z))
                (force (not (equal z 0))))
           (equal (mod (+ w x y) z)
                  (mod (+ w x) z)))
  :disable cancel-mod-+-basic
  :use ((:instance cancel-mod-+-basic (x y) (y (+ w x)) (z z))))

; [Jared] bozo this looks kind of expensive...

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

#+non-standard-analysis
(defthm not-realp-realp-plus
 (implies (and (acl2-numberp x)
               (realp y)
               (not (realp x)))
          (not (realp (+ x y))))
 :hints (("Goal" :use ((:instance realp-+ (x (+ x y)) (y (- y)))))))

#+non-standard-analysis
(defthm not-realp-realp-unary---plus
 (implies (and (acl2-numberp x)
               (realp y)
               (not (realp (- x))))
          (not (realp (+ x y))))
 :hints (("Goal" :use ((:instance realp-+ (x (+ x y)) (y (- y))))
	  :in-theory (enable realp-unary--))))

(encapsulate nil

  (local (defthm simplify-mod-+-mod-crock
           (equal (equal (* a b) (+ y z))
                  (equal (fix z) (- (* a b) y)))))

  (defrule simplify-mod-+-mod
    :parents (mod-lemmas)
    :short "Rewrite @('(MOD (+ w (MOD x y)) z)') and similar, where y/z is an integer."
    (implies (and (equal i (/ y z))
                  (integerp i)
                  (qr-guard x y)
                  (qr-guard w z))
             (and (equal (mod (+ w (mod x y)) z) (mod (+ w x) z))
                  (equal (mod (+ (mod x y) w) z) (mod (+ w x) z))
                  (equal (mod (- w (mod x y)) z) (mod (- w x) z))
                  (equal (mod (- (mod x y) w) z) (mod (- x w) z))))
    :hints(("Goal" :in-theory (disable mod-x-y-=-x+y-for-rationals
                                       mod-x-y-=-x-for-rationals
                                       integerp-mod
                                       integerp-+-minus-*
                                       mod-=-0)))))

(defrule mod-+-cancel-0
  :parents (mod-lemmas)
  :short "Rewrite @('(equal (mod (+ x y) z) x)')."
  (implies (and (qr-guard x z)
                (qr-guard y z))
           (equal (equal (mod (+ x y) z) x)
                  (and (equal (mod y z) 0)
                       (equal (mod x z) x))))
  :disable (left-cancellation-for-* equal-*-/-2)
  :use ((:instance left-cancellation-for-*
         (z (/ z)) (x y) (y (* z (floor (+ x y) z)))))
  :expand ((mod (+ x y) z)))

(local (in-theory (enable floor-type-1 floor-type-2 floor-type-3 floor-type-4
			  floor-bounded-by-/ mod-type mod-bounded-by-modulus)))


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
;;;            (real/rationalp x))
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

#-non-standard-analysis
(defthm rationalp-mod
  (implies (rationalp x)
           (rationalp (mod x y)))
  :rule-classes (:rewrite :type-prescription)
  :hints(("Goal"
          :cases ((rationalp y))
          :in-theory (enable mod floor))))

#+non-standard-analysis
(defthm rationalp-mod
  (implies (and (rationalp x)
		(rationalp y))
	   (rationalp (mod x y)))
  :hints (("Goal" :in-theory (enable mod rationalp-+)))
  :rule-classes (:rewrite :type-prescription))

#+non-standard-analysis
(defrule realp-mod
  (implies (real/rationalp x)
	   (real/rationalp (mod x y)))
  :cases ((not (acl2-numberp y))
          (real/rationalp y))
  :enable (mod floor realp-+)
  :rule-classes (:rewrite :type-prescription))

(encapsulate ()

  ;;  This proof of FLOOR-FLOOR-INTEGER is an elaborate rewriting trick,
  ;;  which is spoiled by these 2 lemmas!

  (local (in-theory (disable rewrite-floor-mod rewrite-mod-mod)))

  ;;< These first 2 lemmas have nothing to do with the :LINEAR theory of
  ;;FLOOR and MOD, so we DISABLE the key :LINEAR lemmas to avoid thrashing.

  (local (in-theory (disable floor-type-1 floor-type-2 floor-type-3
			     floor-type-4 floor-bounded-by-/ mod-type mod-bounded-by-modulus)))

  ;; First, write x as a quotient and remainder of i*j.

  (local
   (defthm floor-floor-integer-crock0
     (implies
      (and (real/rationalp x)
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
      (and (real/rationalp x)
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
      (and (real/rationalp x)
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
				       '(floor-bounded-by-/ mod-bounded-by-modulus
						      <-*-left-cancel
						      <-*-/-left-commuted))
       :use ((:instance floor-bounded-by-/ (x (mod x (* i j))) (y i))
	     (:instance mod-bounded-by-modulus (x x) (y (* i j)))
	     (:instance <-*-left-cancel
			(z (/ i)) (x (mod x (* i j))) (y (* i j))))))))

  ;; Voila!

  (defrule floor-floor-integer
    :parents (floor-lemmas)
    :short "Rewrite: @('(FLOOR (FLOOR x i) j) = (FLOOR x (* i j))') for integers i,j &gt; 0."
    (implies (and (integerp i)
                  (integerp j)
                  (< 0 i)
                  (< 0 j)
                  (real/rationalp x))
             (equal (floor (floor x i) j)
                    (floor x (* i j))))))

(defrule floor-x+i*k-i*j
  :parents (floor-lemmas)
  :short "Rewrite: @('(FLOOR (+ x (* i k)) (* i j)) = (FLOOR k j)'), when
  i,j &gt; 0 and 0 &lt;= x &lt; i."
  :long "<p>This is a crucial lemma for certain kinds of reasoning about hardware
  specifications, and is used to prove @(see MOD-x+i*j-i*k).</p>"
  (implies (and (force (real/rationalp x))
                (force (integerp i))
                (force (integerp j))
                (force (integerp k))
                (< 0 i)
                (< 0 j)
                (<= 0 x)
                (< x i))
           (equal (floor (+ x (* i k)) (* i j))
                  (floor k j)))
  :disable (floor-floor-integer floor-+)
  :use ((:instance floor-floor-integer (x (+ x (* i k))) (i i) (j j))
        (:instance floor-+ (x x) (y (* i k)) (z i))))

(defrule mod-x+i*k-i*j
  :parents (mod-lemmas)
  :short "Rewrite: @('(MOD (+ x (* i k)) (* i j)) = (+ x (* i (MOD k j)))'),
  when i,j &gt; 0 and 0 &lt;= x &lt; i."
  :long "<p>This is a crucial lemma for certain kinds of
  reasoning about hardware specifications, for example, we can use this to
  prove that</p>
  @({
       (MOD i (EXPT 2 n)) = (MOD i 2) + (MOD (FLOOR i 2) (EXPT 2 (1- n)))
  })
  <p>for @('n > 0'), which justifies a recursive specification of hardware
  operations.</p>"
  (implies (and (force (real/rationalp x))
                (force (integerp i))
                (force (integerp j))
                (force (integerp k))
                (< 0 i)
                (< 0 j)
                (<= 0 x)
                (< x i))
           (equal (mod (+ x (* i k)) (* i j))
                  (+ x (* i (mod k j)))))
  :enable mod)

(encapsulate ()

  (local (in-theory (disable floor-type-1 floor-type-2 floor-type-3
			     floor-type-4 floor-bounded-by-/)))

  (local
   (defthm mod-x-i*j-crock
     (implies
      (and (> i 0)
	   (> j 0)
	   (force (integerp i))
	   (force (integerp j))
	   (force (real/rationalp x)))
      (equal (mod (+ (mod x i) (* i (floor x i))) (* i j))
	     (+ (mod x i) (* i (mod (floor x i) j)))))
     :rule-classes nil
     :hints (("Goal" :in-theory (disable floor-mod-elim)))))

  (defthm mod-x-i*j-of-positives
    (implies (and (> i 0)
                  (> j 0)
                  (force (integerp i))
                  (force (integerp j))
                  (force (real/rationalp x)))
             (equal (mod x (* i j))
                    (+ (mod x i) (* i (mod (floor x i) j)))))
    :hints (("Goal" :use mod-x-i*j-crock))))


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
	   (real/rationalp i)
	   (integerp j)
	   (not (equal 0 j)))
      (integerp (+ (* j (floor i j)) (mod i j))))
     :rule-classes nil
     :hints
     (("Goal"
       :in-theory (disable floor-=-x/y)))))

  (defrule integerp-i/j-integerp-forward
    :parents (integer-ratio-lemmas)
    :short "Forward: If i/j is an integer and j is an integer, then i is an
    integer."
    (implies (and (integerp (/ i j))
                  (real/rationalp i)
                  (integerp j)
                  (not (zerop j)))
             (integerp i))
    :use ((:instance crock0))
    :disable (mod-=-0 floor-=-x/y)
    :rule-classes
    ((:forward-chaining :corollary (implies (and (integerp (/ i j))
                                                 (force (real/rationalp i))
                                                 (integerp j)
                                                 (force (not (equal 0 j))))
                                            (integerp i)))
     (:forward-chaining :corollary (implies (and (integerp (* (/ j) i))
                                                 (force (real/rationalp i))
                                                 (integerp j)
                                                 (force (not (equal 0 j))))
                                            (integerp i))))))


;;;****************************************************************************
;;;
;;;    THEORIES -- A couple of exported theories.
;;;
;;;****************************************************************************

(defxdoc quotient-remainder-theories
  :parents (quotient-remainder-lemmas)
  :short "Logical theories supplied by the QUOTIENT-REMAINDER book."

  :long "<p>The QUOTIENT-REMAINDER book exports 2 theories:
  QUOTIENT-REMAINDER-FUNCTIONS and QUOTIENT-REMAINDER-RULES.  The former is
  simply a theory of the functions characterized by the book.  Since these
  functions are all ENABLEd by default, and most are non-recursive, one should
  immediately:</p>

  @({
     (in-theory (disable quotient-remainder-functions))
  })

  <p>upon loading this book, or the lemmas may never be applied.</p>

  <p>QUOTIENT-REMAINDER-RULES is a theory of all of the lemmas exported by this
  book which are ENABLEd by default.  You can \"turn off\" this book after it
  is loaded by</p>

  @({
      (in-theory (disable quotient-remainder-rules))
  })")

(defsection quotient-remainder-functions
  :parents (quotient-remainder-theories)
  :short "A theory of the function symbols characterized by
  \"quotient-remainder-lemmas\"."
  :long "<p>You should DISABLE this theory immediately after loading this
  book.</p>"

  (deftheory quotient-remainder-functions
    '(nonnegative-integer-quotient floor mod truncate rem)))

(defsection quotient-remainder-rules
  :parents (quotient-remainder-theories)
  :short "A theory of all rules exported ENABLEd by the
  \"quotient-remainder-lemmas\" book."

  (deftheory quotient-remainder-rules
    (union-theories
     (defun-type/exec-theory
       '(NONNEGATIVE-INTEGER-QUOTIENT FLOOR MOD TRUNCATE REM))
     (set-difference-theories (current-theory :here)
                              (current-theory 'begin-quotient-remainder-lemmas)))))
