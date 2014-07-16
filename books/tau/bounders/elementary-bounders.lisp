; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore, December, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "elementary-bounders")

; Tau Interval Functions for Basic Arithmetic
; and Proofs of Their Correctness

; J Strother Moore
; Edinburgh, December, 2012

; Abstract

; Consider (+ x y) and suppose we know that the inputs, x and y, are contained
; in two intervals, int1 and int2.  We wish to compute from int1 and int2 an
; interval containing (+ x y).  For example, if x is known to be an INTEGERP
; such that 1 <= x <= 16 and y is a RATIONALP such that 0 < y (with no known
; upper bound), then (+ x y) is known to be in the RATIONALP interval such that
; 1 < (+ x y) (with no known upper bound).  I call the function that takes two
; intervals containing x and y respectively and that returns an interval
; containing (fn x y) a ``bounder'' for fn.
;
; I have developed a book that defines bounders for +, *, /, FLOOR, MOD,
; LOGAND, LOGNOT, LOGIOR, LOGORC1, LOGEQV, LOGXOR, EXPT2, and ASH.  The book
; proves the correctness of each bounder.  In future work I hope to extend ACL2
; so that users can define and verify bounders to improve the tau system.  The
; present work is an exploration of the shape and content of such bounder
; theorems.  Ideally, the present book would just become part of an arithmetic
; package and not be built into ACL2.

; Our bounder definitions (and hence their correctness proofs) fall into one of
; two different styles.  The first definitional style is just straightforward
; case analysis and arithmetic and so the proof follows the usual ACL2 style of
; definitional expansion and use of the arithmetic-5 library.  This first style
; of proof can generate a lot of cases.  For example, the proof that the
; bounder for products is correct generates over 40,000 subgoals.  This is due
; to a variety of issues including the myriad combinations of choices for the
; intervals containing the inputs x and y (e.g., are they open or closed,
; finite or not, over what domains?), as well as the case analysis necessary to
; compute the bounds.  See the definition of tau-bounder-* below.

; In the second style, the bounders are defined in terms of previously verified
; bounders.  For example,

; (LOGIOR X Y) = (LOGNOT (LOGAND (LOGNOT X) (LOGNOT Y)))

; Thus, we can bound LOGIOR by composing already verified bounders and we can
; verify the LOGIOR bounder by exploiting the proved properties of those
; earlier bounders.  However, making this second proof style work imposes
; additional constraints on the correctness theorems and how they are stored as
; rules.

; The book concludes with an essay On the Accuracy of the LOGAND Bounder.

; Some Technical Details

; In this work, an interval is a data structure, constructed by make-tau-interval,
; containing five fields that are named the ``domain,'' the ``lower bound
; relation,'' the ``lower bound,'' the ``upper bound relation,'' and the
; ``upper bound.''  These fields are accessed by interval-dom, interval-lo-rel,
; interval-lo, interval-hi-rel, and interval-hi.  The actual shape of the data
; structure is the same as for a tau-interval in the ACL2 source code:

; (defrec tau-interval (domain (lo-rel . lo) . (hi-rel . hi)) t).

; However, in the source code tau-intervals are constructed by the macro make
; and accessed by the macro access, which expand to raw conses, cars, and cdrs
; for efficiency.  I chose to introduce a named constructor and accessors to
; make it easier to hang lemmas on them during correctness proofs for bounders.
; But the named functions work on exactly the same data structures and can be
; applied to build and access ACL2's tau-intervals.

; An interval domain must be one of INTEGERP, RATIONALP, ACL2-NUMBERP, or nil,
; the last indicating that there is no restriction.  An interval relation is a
; Boolean, where nil means the relation is ``<='' and t means the relation is
; ``<.''  That is, nil means ``weak inequality'' and t means ``strong
; inequality.''  The upper and lower bounds are either nil, meaning no such
; bound is known, or an explicit rational.  Symbolic bounds are not allowed.
; For example,

; (make-tau-interval 'RATIONALP  t -1/2 nil 1)

; denotes the interval containing x such that

; (rationalp x) & -1/2 < x <= 1.

; There are two other constraints on well-formed interval.  First, if the two
; bounds, lo and hi, of an interval are non-nil, then lo <= hi.  Second, if the
; domain of an interval is INTEGERP then the relations must be weak and the
; bounds must be integers.  That is, if x is known to be an INTEGERP such that
; 1/2 < x < 11/2 then instead of creating the (illegal) interval

; (make-tau-interval 'INTEGERP T 1/2 T 11/2)

; one must create

; (make-tau-interval 'INTEGERP NIL 1 NIL 5)

; Of course, (make-tau-interval 'RATIONALP T 1/2 T 11/2) is a perfectly legal
; interval.

; These constraints are formalized in the predicate intervalp below.

; To say that x is ``in'' an interval, int, is (in-tau-intervalp x int), formalized
; below.

; The correctness theorem for the bounder function for addition, which is
; called tau-bounder-+, is given below and suggests the shape of all bounder
; correctness theorems here.

; (implies (and (tau-intervalp int1)
;               (tau-intervalp int2)
;               (or (equal (tau-interval-dom int1) 'integerp)
;                   (equal (tau-interval-dom int1) 'rationalp))
;               (or (equal (tau-interval-dom int2) 'integerp)
;                   (equal (tau-interval-dom int2) 'rationalp))
;               (in-tau-intervalp x int1)
;               (in-tau-intervalp y int2))
;          (and (tau-intervalp (tau-bounder-+ int1 int2))
;               (in-tau-intervalp (+ x y) (tau-bounder-+ int1 int2))
;               ))

; We envision this being used as follows: when ACL2 is asked to compute the tau
; of (+ x y) it first computes the tau of x and the tau of y.  These tau will
; include (possibly trivially unrestrictive) intervals, say int1 and int2.  An
; invariant of the ACL2 code is that the computed int1 and int2 are well-formed
; intervals that contain the values of x and y respectively.  Thus, the first
; two and last two hypotheses of the correctness theorem are assured.  Next,
; ACL2 should check that the domains of the two computed intervals are each
; either INTEGERP or RATIONALP, which if true satisfies the middle two
; hypotheses.  Thus, ACL2 can then run (tau-bounder-+ int1 int2) and know that
; it returns a well-formed interval that contains the value of (+ x y).  This
; allows it to include that newly computed interval into the tau being computed
; for (+ x y).

; In order to use such correctness theorems in the proofs of other such correctness
; theorems, it is necessary (a) to code the theorems (mainly) as :forward-chaining
; rules, and (b) include in the correctness theorem one additional conclusion, namely

;               (implies (not (equal (tau-interval-dom (tau-bounder-+ int1 int2)) 'integerp))
;                        (equal (tau-interval-dom (tau-bounder-+ int1 int2)) 'rationalp)).

; This additional conclusion, which is not necessary for the imagined use of
; TAU-BOUNDER-+, allows the facts proved about TAU-BOUNDER-+ to be sufficient
; to relieve the hypotheses of other correctness results.

; The reason we code these correctness results mainly as :forward-chaining
; rules has to do with free variables.  The bounder for LOGIOR is
; a composition of the bounders for LOGNOT and LOGAND because:

; (LOGIOR X Y) = (LOGNOT (LOGAND (LOGNOT X) (LOGNOT Y)))

; The correctness of the LOGIOR bounder will introduce:

; (TAU-BOUNDER-LOGNOT
;   (TAU-BOUNDER-LOGAND
;    (TAU-BOUNDER-LOGNOT INT1)
;    (TAU-BOUNDER-LOGNOT INT2)))

; and all we will know is that X is in INT1 and Y is INT2.  By forward chaining
; from those two facts, triggered by the presence in the goal of the trigger
; terms (TAU-BOUNDER-LOGNOT INT2) and (TAU-BOUNDER-LOGAND ...) we can infer:

; (IN-TAU-INTERVALP (LOGNOT X) (TAU-BOUNDER-LOGNOT INT1))

; (IN-TAU-INTERVALP (LOGNOT Y) (TAU-BOUNDER-LOGNOT INT2))

; from one round of forward chaining, and then:

; (IN-TAU-INTERVALP (LOGAND (LOGNOT X) (LOGNOT Y))
;               (TAU-BOUNDER-LOGAND
;                   (TAU-BOUNDER-LOGNOT INT1)
;                   (TAU-BOUNDER-LOGNOT INT2)))

; from a second and then

; (IN-TAU-INTERVALP (LOGNOT (LOGAND (LOGNOT X) (LOGNOT Y)))
;               (TAU-BOUNDER-LOGNOT
;                  (TAU-BOUNDER-LOGAND
;                      (TAU-BOUNDER-LOGNOT INT1)
;                      (TAU-BOUNDER-LOGNOT INT2))))

; from a third.  We discuss the decision to use forward-chaining further in the
; proof of tau-bounder-floor-correct.

; -----------------------------------------------------------------

(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

(local (deftheory jared-disables
         '(;; Things I think are slow in arith-5
           |(equal (if a b c) x)|
           |(equal x (if a b c))|
           |(+ x (if a b c))|

           SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<
           (:T EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
           (:T EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)
           (:T EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT)
           (:T EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT)
           (:T EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT)
           (:T EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT)
           (:T EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B)
           (:T EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE)
           (:T EXPT-TYPE-PRESCRIPTION-NON-0-BASE)
           (:T NOT-INTEGERP-3B)
           (:T NOT-INTEGERP-1B)
           (:T NOT-INTEGERP-2B)
           (:T NOT-INTEGERP-4E)
           (:T NOT-INTEGERP-4B)
           (:T NOT-INTEGERP-4B-EXPT)
           (:T NOT-INTEGERP-3B-EXPT)
           (:T NOT-INTEGERP-2B-EXPT)
           (:T NOT-INTEGERP-1B-EXPT)
           (:T RATIONALP-EXPT-TYPE-PRESCRIPTION)
           RATIONALP-X
           acl2-numberp-x

           not-integerp-1a
           not-integerp-2a
           not-integerp-3a
           not-integerp-4a
           not-integerp-1d
           not-integerp-2d
           not-integerp-3d
           not-integerp-4d
           not-integerp-1f
           not-integerp-2f
           not-integerp-3f
           not-integerp-4f

           default-times-1
           default-times-2
           default-less-than-1
           default-less-than-2
           default-car
           default-cdr

           )))

(local (in-theory (disable jared-disables)))

(local (SET-DEFAULT-HINTS
        '((NONLINEARP-DEFAULT-HINT++ ID
                                     STABLE-UNDER-SIMPLIFICATIONP HIST NIL)
          (and stable-under-simplificationp
               (not (cw "Jared-hint: re-enabling slow rules.~%"))
               '(:in-theory (enable jared-disables))))))


; Note:  I tried the simpler nonlinear hint:
; (set-default-hints '((nonlinearp-default-hint
;                       stable-under-simplificationp
;                       hist
;                       pspv)))
; but it didn't suffice for the tau-bounder-floor-correct theorem.


; -----------------------------------------------------------------
; Basic Abstract Properties of the Interval Functions


(local
 (defthm abstract-def-<?
   (implies (implies (and x y)
                     (or (real/rationalp x)
                         (real/rationalp y)))
            (iff (<? rel x y)
                 (if (or (null x)
                         (null y))
                     t
                     (if rel (< x y) (<= x y)))))
   :hints
   (("Goal"
     :use ((:instance completion-of-< (x x) (y y))
           (:instance completion-of-< (x y) (y x)))))
   :rule-classes
   ((:rewrite :corollary
              (implies (real/rationalp x)
                       (iff (<? rel x y)
                            (if (or (null x)
                                    (null y))
                                t
                                (if rel (< x y) (<= x y))))))
    (:rewrite :corollary
              (implies (real/rationalp y)
                       (iff (<? rel x y)
                            (if (or (null x)
                                    (null y))
                                t
                                (if rel (< x y) (<= x y))))))
    (:rewrite :corollary
              (implies (null x)
                       (iff (<? rel x y)
                            (if (or (null x)
                                    (null y))
                                t
                                (if rel (< x y) (<= x y))))))
    (:rewrite :corollary
              (implies (null y)
                       (iff (<? rel x y)
                            (if (or (null x)
                                    (null y))
                                t
                                (if rel (< x y) (<= x y)))))))))


(local
 (in-theory (disable <?)))

(local
 (defthm interval-accessors
   (and (equal (tau-interval-dom (make-tau-interval dom lo-rel lo hi-rel hi))
               dom)
        (equal (tau-interval-lo-rel (make-tau-interval dom lo-rel lo hi-rel hi))
               lo-rel)
        (equal (tau-interval-lo (make-tau-interval dom lo-rel lo hi-rel hi))
               lo)
        (equal (tau-interval-hi-rel (make-tau-interval dom lo-rel lo hi-rel hi))
               hi-rel)
        (equal (tau-interval-hi (make-tau-interval dom lo-rel lo hi-rel hi))
               hi))))

(local
 (defthm intervalp-rules
   (implies (tau-intervalp int)
            (and
             (implies (equal (tau-interval-dom int) 'integerp)
                      (and (equal (tau-interval-lo-rel int) nil)
                           (equal (tau-interval-hi-rel int) nil)
                           (equal (integerp (tau-interval-lo int))
                                  (if (tau-interval-lo int) t nil))
                           (equal (integerp (tau-interval-hi int))
                                  (if (tau-interval-hi int) t nil))
                           ))
             (booleanp (tau-interval-lo-rel int))
             (booleanp (tau-interval-hi-rel int))
             ;;(implies (tau-interval-lo int) (rationalp (tau-interval-lo int)))
             (equal (rationalp (tau-interval-lo int))
                    (if (tau-interval-lo int) t nil))
             ;; (implies (tau-interval-hi int) (rationalp (tau-interval-hi int)))
             (equal (rationalp (tau-interval-hi int))
                    (if (tau-interval-hi int) t nil))
             (implies (and (tau-interval-lo int)
                           (tau-interval-hi int))
                      (<= (tau-interval-lo int)
                          (tau-interval-hi int)))))
   :rule-classes
   ((:rewrite
     :corollary
     (implies (tau-intervalp int)
              (and (equal (rationalp (tau-interval-lo int))
                          (if (tau-interval-lo int) t nil))
                   (equal (rationalp (tau-interval-hi int))
                          (if (tau-interval-hi int) t nil)))))
    (:rewrite
     :corollary
     (implies (and (equal (tau-interval-dom int) 'integerp)
                   (tau-intervalp int))
              (and (equal (tau-interval-lo-rel int) nil)
                   (equal (tau-interval-hi-rel int) nil)
                   (equal (integerp (tau-interval-lo int))
                          (if (tau-interval-lo int) t nil))
                   (equal (integerp (tau-interval-hi int))
                          (if (tau-interval-hi int) t nil)))))
    (:forward-chaining
     :corollary
     (implies (and (tau-intervalp int)
                   (equal (tau-interval-dom int) 'integerp)
                   (tau-interval-lo int))
              (integerp (tau-interval-lo int))))
    (:forward-chaining
     :corollary
     (implies (and (tau-intervalp int)
                   (equal (tau-interval-dom int) 'integerp)
                   (tau-interval-hi int))
              (integerp (tau-interval-hi int))))
    (:forward-chaining
     :corollary
     (implies (and (tau-intervalp int)
                   (tau-interval-lo int))
              (rationalp (tau-interval-lo int))))
    (:forward-chaining
     :corollary
     (implies (and (tau-intervalp int)
                   (tau-interval-hi int))
              (rationalp (tau-interval-hi int))))

    ;; Jared: removing these since they seem expensive and bad
    ;; (:type-prescription
    ;;  :corollary
    ;;  (implies (tau-intervalp int) (booleanp (tau-interval-lo-rel int))))
    ;; (:type-prescription
    ;;  :corollary
    ;;  (implies (tau-intervalp int) (booleanp (tau-interval-hi-rel int))))

    (:linear
     :corollary
     (implies (and (tau-intervalp int)
                   (tau-interval-lo int)
                   (tau-interval-hi int))
              (<= (tau-interval-lo int)
                  (tau-interval-hi int)))))))

(local
 (defthm in-tau-intervalp-rules
   (and
    (implies (and (tau-intervalp int)
                  (in-tau-intervalp x int)
                  (eq (tau-interval-dom int) 'integerp))
             (integerp x))
    (implies (and (tau-intervalp int)
                  (in-tau-intervalp x int)
                  (eq (tau-interval-dom int) 'rationalp))
             (rationalp x))
    (implies (and (tau-intervalp int)
                  (in-tau-intervalp x int)
                  (eq (tau-interval-dom int) 'acl2-numberp))
             (acl2-numberp x))
    (implies (and (tau-intervalp int)
                  (in-tau-intervalp x int)
                  x
                  (tau-interval-lo-rel int)
                  (tau-interval-lo int))
             (< (tau-interval-lo int) x))
    (implies (and (tau-intervalp int)
                  (in-tau-intervalp x int)
                  x
                  (not (tau-interval-lo-rel int))
                  (tau-interval-lo int))
             (<= (tau-interval-lo int) x))
    (implies (and (tau-intervalp int)
                  (in-tau-intervalp x int)
                  x
                  (tau-interval-hi-rel int)
                  (tau-interval-hi int))
             (< x (tau-interval-hi int)))
    (implies (and (tau-intervalp int)
                  (in-tau-intervalp x int)
                  (not (tau-interval-hi-rel int))
                  x
                  (tau-interval-hi int))
             (<= x (tau-interval-hi int))))
   :rule-classes
   ((:forward-chaining
     :corollary
     (implies (and (in-tau-intervalp x int)
                   (tau-intervalp int)
                   (eq (tau-interval-dom int) 'integerp))
              (integerp x)))
    (:forward-chaining
     :corollary
     (implies (and (in-tau-intervalp x int)
                   (tau-intervalp int)
                   (eq (tau-interval-dom int) 'rationalp))
              (rationalp x)))
    (:forward-chaining
     :corollary
     (implies (and (in-tau-intervalp x int)
                   (tau-intervalp int)
                   (eq (tau-interval-dom int) 'acl2-numberp))
              (acl2-numberp x)))
    (:linear
     :corollary
     (implies (and (in-tau-intervalp x int)
                   x
                   (tau-intervalp int)
                   (tau-interval-lo-rel int)
                   (tau-interval-lo int))
              (< (tau-interval-lo int) x)))
    (:linear ; forward-chaining
     :corollary
     (implies (and (in-tau-intervalp x int)
                   x
                   (tau-intervalp int)
                   (tau-interval-lo int))
              (<= (tau-interval-lo int) x)))
    (:linear ; forward-chaining
     :corollary
     (implies (and (in-tau-intervalp x int)
                   x
                   (tau-intervalp int)
                   (tau-interval-hi-rel int)
                   (tau-interval-hi int))
              (< x (tau-interval-hi int))))
    (:linear ; forward-chaining
     :corollary
     (implies (and (in-tau-intervalp x int)
                   x
                   (tau-intervalp int)
                   (tau-interval-hi int))
              (<= x (tau-interval-hi int)))))))

(local
 (defthm intervalp-make-tau-interval
   (equal (tau-intervalp (make-tau-interval dom lo-rel lo hi-rel hi))
          (cond ((eq dom 'integerp)
                 (and (null lo-rel)
                      (null hi-rel)
                      (if lo
                          (and (integerp lo)
                               (if hi (and (integerp hi) (<= lo hi))
                                   t))
                          (if hi (integerp hi) t))))
                (t (and (member dom '(rationalp acl2-numberp nil))
                        (booleanp lo-rel)
                        (booleanp hi-rel)
                        (if lo
                            (and (rationalp lo)
                                 (if hi (and (rationalp hi) (<= lo hi))
                                     t))
                            (if hi (rationalp hi) t))))))))

(local
 (defthm in-tau-intervalp-make-tau-interval
   (equal (in-tau-intervalp x (make-tau-interval dom lo-rel lo hi-rel hi))
          (and (tau-interval-domainp dom x)
               (<? lo-rel lo (fix x))
               (<? hi-rel (fix x) hi)))))

(local
 (in-theory (disable make-tau-interval
                     tau-interval-dom tau-interval-lo-rel tau-interval-lo
                     tau-interval-hi-rel tau-interval-hi)))



; -----------------------------------------------------------------
; BINARY-+

(defun domain-of-binary-arithmetic-function (domx domy)

; In this function, domx and domy are domain names as found in tau-bounders,
; e.g., INTEGERP, RATIONALP, ACL2-NUMBERP, or NIL.  The function returns the
; the domain of such generic binary arithmetic functions as sum, product, or
; mod.  Note that arithmetic functions always return (at least) ACL2-NUMBERPs.
; So we never return NIL.

  (cond ((eq domx 'integerp)
         (cond ((eq domy 'integerp) 'integerp)
               ((eq domy 'rationalp) 'rationalp)
               (t 'acl2-numberp)))
        ((eq domx 'rationalp)
         (cond ((or (eq domy 'integerp)
                    (eq domy 'rationalp))
                'rationalp)
               (t 'acl2-numberp)))
        (t 'acl2-numberp)))

(defun bounds-of-sum (lo-rel1 lo1 hi-rel1 hi1 lo-rel2 lo2 hi-rel2 hi2)

; Suppose x and y are terms and that it is known that lo1 <? x <? hi1 and lo2
; <? y <? hi2, where the relations denoted by ``<?'' are controlled by the four
; respective ``rel'' flags.  We seek bounds (mv lo lo-rel hi hi-rel) on the sum
; (+ x y).  In the ideal case where all the intervals are bounded by finite
; rationals, the answer would be:

; (mv (or lo-rel1 lo-rel2) (+ lo1 lo2) (or hi-rel1 hi-rel2) (+ hi1 hi2)).

; In the case of sum, the upper and lower bounds can be computed independently.
; But to make this function similar to the function for computing the bounds of
; a product -- where, for example, the lower bounds of the factors can
; influence the upper bound of the product -- we take all eight parameters and
; compute all four results in one function.

; Complicating this function is the requirement that we must allow for
; infinities.  Thus, for example, if lo2 is nil, we have ``-infinity <= y''.
; With no lower bound on y, there can be no lower bound on (+ x y).  Finally,
; recall our convention that when the bound is infinite, we use the weak
; relation (rel = nil) by default.

  (mv-let
   (lo-rel lo)
   (if (and lo1 lo2)
       (mv (or lo-rel1 lo-rel2) (+ lo1 lo2))
       (mv nil nil))
   (mv-let
    (hi-rel hi)
    (if (and hi1 hi2)
        (mv (or hi-rel1 hi-rel2) (+ hi1 hi2))
        (mv nil nil))
    (mv lo-rel lo hi-rel hi))))

(defun tau-bounder-+ (int1 int2)
  (let ((dom (domain-of-binary-arithmetic-function
              (tau-interval-dom int1)
              (tau-interval-dom int2))))
    (mv-let (lo-rel lo hi-rel hi)
            (bounds-of-sum (tau-interval-lo-rel int1)
                           (tau-interval-lo int1)
                           (tau-interval-hi-rel int1)
                           (tau-interval-hi int1)
                           (tau-interval-lo-rel int2)
                           (tau-interval-lo int2)
                           (tau-interval-hi-rel int2)
                           (tau-interval-hi int2))
            (make-tau-interval dom lo-rel lo hi-rel hi))))

(defthm tau-bounder-+-correct
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-+ int1 int2))
                (in-tau-intervalp (+ x y) (tau-bounder-+ int1 int2))
                ))
  :rule-classes
  ((:rewrite)
   (:forward-chaining
    :corollary
    (implies (and (tau-intervalp int1)
                  (tau-intervalp int2)
                  (in-tau-intervalp x int1)
                  (in-tau-intervalp y int2))
             (and (tau-intervalp (tau-bounder-+ int1 int2))
                  (in-tau-intervalp (+ x y) (tau-bounder-+ int1 int2))))
    :trigger-terms ((tau-bounder-+ int1 int2)))
   ))

; -----------------------------------------------------------------
; BINARY-*

; I now implement ``the bounds of the product are the products of the bounds.''
; But this is INSANELY more complicated and depends on the signs of the
; intervals, whether they are strict or non-strict, and whether they contain
; zero.  For example, if both intervals are strictly negative (the upper bounds
; are negative), then the product of their lower bounds is the upper bound of
; their product, and vice versa.  And if one of the intervals is negative and
; the other is positive, the product of the positive upper bound and the
; negative lower bound is the lower bound of the product, and vice versa.
; After working out a few cases, we asked Robert Krug for an exhaustive case
; analysis which he provided in the form of a theorem for products akin to that
; shown above for sums, except instead of dealing with intervals as objects it
; just returned the two bounding rationals and the two relations.  I believe
; Robert worked most of this out while developing the non-linear features of
; the community books in arithmetic-5/.  Thank you Robert!

(defun bounds-of-product-< (x y)

; X and y are either rationals or nil or t, where nil represents negative
; infinity and t represents positive infinity.  We determine whether x < y, and
; we (rather oddly) say that x < x, when x is either infinity.

  (if (null x)
      t
      (if (eq x t)
          (if (eq y t)
              t
              nil)
          (if (null y)
              nil
              (if (eq y t)
                  t
                  (< x y))))))

(defun bounds-of-product-<= (x y)

; X and y are either rationals or nil or t, where nil represents negative
; infinity and t represents positive infinity.  We determine whether x <= y.

  (if (null x)
      t
      (if (eq x t)
          (if (eq y t)
              t
              nil)
          (if (null y)
              nil
              (if (eq y t)
                  t
                  (<= x y))))))

(defun bounds-of-product-* (x y)

; X and y are either rationals or nil or t, where nil represents negative
; infinity and t represents positive infinity.  We compute (* x y).

  (if (or (eql x 0)
          (eql y 0))
      0
      (if (or (null x)
              (eq x t)
              (null y)
              (eq y t))
          (let ((signx (cond ((null x) nil)
                             ((eq x t) t)
                             ((< x 0) nil)
                             (t t)))
                (signy (cond ((null y) nil)
                             ((eq y t) t)
                             ((< y 0) nil)
                             (t t))))
            (eq signx signy))
          (* x y))))

(defun bounds-of-product1 (lo-rel1 lo1 hi-rel1 hi1 lo-rel2 lo2 hi-rel2 hi2)

; Warning: This function uses nil and t respectively to represent negative and
; positive infinity.  Except for this function and the three extended
; arithmetic operators above, all other functions in the tau system obey the
; convention that both infinities are represented by nil.

; Given the different representations of the infinities, assume that lo1 <? x
; <? hi1 and lo2 <? y <? hi2, where the ``<?'' relations are controlled,
; respectively, by lo-rel1, hi-rel1, lo-rel2, and hi-rel2.  We wish to
; determine bounds on (* x y).  We return (mv lo-rel lo hi-rel hi).

; If you replace bounds-of-product-<, bounds-of-product-<=, and
; bounds-of-product-* by <, <=, and * respectively below, you get a version of
; this function that works when all the bounds are finite.  Inspection shows
; that this is still a very messy function!  Trying to handle the infinities by
; case splitting is daunting.  (Abstractly, one could specialize the code below
; for each of the 2^8 cases -- each bound is either a finite rational or is
; infinite and each relation is either strict or not -- although one can cut it
; in half by exploiting the commutativity of multiplication.)  That's why we
; extended the basic operations to handle infinities.

; The intellectual bulk of the following definition was derived by Robert
; Krug's, who worked out and verified an exhaustive case analysis.  The proof
; of correctness of his original involved only about 5,000 subgoals whereas the
; proof of correctness of the full-fledged interval-based version involves
; about 40,000.  But the case analysis and bounds is due to Robert.  Thank you
; Robert!

  (cond
   ((equal lo1 hi1)
    (cond ((bounds-of-product-< 0 lo1)
           (mv lo-rel2
               (bounds-of-product-* lo1 lo2)
               hi-rel2
               (bounds-of-product-* lo1 hi2)))
          ((equal lo1 0)
           (mv nil
               0
               nil
               0))
          (t
           ;; (bounds-of-product-< lo1 0)
           (mv hi-rel2
               (bounds-of-product-* lo1 hi2)
               lo-rel2
               (bounds-of-product-* lo1 lo2)))))
   ((equal lo2 hi2)
    (cond ((bounds-of-product-< 0 lo2)
           (mv lo-rel1
               (bounds-of-product-* lo1 lo2)
               hi-rel1
               (bounds-of-product-* hi1 hi2)))
          ((equal lo2 0)
           (mv nil
               0
               nil
               0))
          (t
           ;; (bounds-of-product-< lo2 0)
           (mv hi-rel1
               (bounds-of-product-* hi1 lo2)
               lo-rel1
               (bounds-of-product-* lo1 lo2)))))

   ((and (bounds-of-product-<= 0 lo1)
         (bounds-of-product-<= 0 lo2))
    (mv (and (or lo-rel1 lo-rel2)
             (or lo-rel1 (not (equal lo1 0)))
             (or lo-rel2 (not (equal lo2 0))))
        (bounds-of-product-* lo1 lo2)
        (or hi-rel1 hi-rel2)
        (bounds-of-product-* hi1 hi2)
        ))
   ((and (bounds-of-product-<= hi1 0)
         (bounds-of-product-<= hi2 0))
    (mv (and (or hi-rel1 hi-rel2)
             (or hi-rel1 (not (equal hi1 0)))
             (or hi-rel2 (not (equal hi2 0))))
        (bounds-of-product-* hi1 hi2)
        (or lo-rel1 lo-rel2)
        (bounds-of-product-* lo1 lo2)
        ))
   ((and (bounds-of-product-<= 0 lo1)
         (bounds-of-product-<= hi2 0))
    (mv (or hi-rel1 lo-rel2)
        (bounds-of-product-* hi1 lo2)
        (and (or lo-rel1 hi-rel2)
             (or lo-rel1 (not (equal lo1 0)))
             (or hi-rel2 (not (equal hi2 0))))
        (bounds-of-product-* lo1 hi2)
        ))
   ((and (bounds-of-product-<= hi1 0)
         (bounds-of-product-<= 0 lo2))
    (mv (or lo-rel1 hi-rel2)
        (bounds-of-product-* lo1 hi2)
        (and (or hi-rel1 lo-rel2)
             (or hi-rel1 (not (equal hi1 0)))
             (or lo-rel2 (not (equal lo2 0))))
        (bounds-of-product-* hi1 lo2)
        ))

   ((and (bounds-of-product-< lo1 0)
         (bounds-of-product-< 0 hi1)
         (bounds-of-product-<= 0 lo2))
    (mv (or lo-rel1 hi-rel2)
        (bounds-of-product-* lo1 hi2)
        (or hi-rel1 hi-rel2)
        (bounds-of-product-* hi1 hi2)
        ))
   ((and (bounds-of-product-< lo1 0)
         (bounds-of-product-< 0 hi1)
         (bounds-of-product-<= hi2 0))
    (mv (or hi-rel1 lo-rel2)
        (bounds-of-product-* hi1 lo2)
        (or lo-rel1 lo-rel2)
        (bounds-of-product-* lo1 lo2)
        ))

   ((and (bounds-of-product-<= 0 lo1)
         (bounds-of-product-< lo2 0)
         (bounds-of-product-< 0 hi2))
    (mv (or hi-rel1 lo-rel2)
        (bounds-of-product-* hi1 lo2)
        (or hi-rel1 hi-rel2)
        (bounds-of-product-* hi1 hi2)
        ))
   ((and (bounds-of-product-<= hi1 0)
         (bounds-of-product-< lo2 0)
         (bounds-of-product-< 0 hi2))
    (mv (or lo-rel1 hi-rel2)
        (bounds-of-product-* lo1 hi2)
        (or lo-rel1 lo-rel2)
        (bounds-of-product-* lo1 lo2)
        ))

   (t
    (cond ((and (bounds-of-product-< (bounds-of-product-* lo1 hi2)
                                     (bounds-of-product-* hi1 lo2))
                (bounds-of-product-< (bounds-of-product-* lo1 lo2)
                                     (bounds-of-product-* hi1 hi2)))
           (mv (or lo-rel1 hi-rel2)
               (bounds-of-product-* lo1 hi2)
               (or hi-rel1 hi-rel2)
               (bounds-of-product-* hi1 hi2)
               ))
          ((and (bounds-of-product-< (bounds-of-product-* lo1 hi2)
                                     (bounds-of-product-* hi1 lo2))
                (equal (bounds-of-product-* lo1 lo2)
                       (bounds-of-product-* hi1 hi2)))
           (mv (or lo-rel1 hi-rel2)
               (bounds-of-product-* lo1 hi2)
               (and (or lo-rel1 lo-rel2)
                    (or hi-rel1 hi-rel2))
               (bounds-of-product-* lo1 lo2)
               ))
          ((and (bounds-of-product-< (bounds-of-product-* lo1 hi2)
                                     (bounds-of-product-* hi1 lo2))
                (bounds-of-product-< (bounds-of-product-* hi1 hi2)
                                     (bounds-of-product-* lo1 lo2)))
           (mv (or lo-rel1 hi-rel2)
               (bounds-of-product-* lo1 hi2)
               (or lo-rel1 lo-rel2)
               (bounds-of-product-* lo1 lo2)
               ))

          ((and (equal (bounds-of-product-* lo1 hi2)
                       (bounds-of-product-* hi1 lo2))
                (bounds-of-product-< (bounds-of-product-* lo1 lo2)
                                     (bounds-of-product-* hi1 hi2)))
           (mv (and (or lo-rel1 hi-rel2)
                    (or hi-rel1 lo-rel2))
               (bounds-of-product-* lo1 hi2)
               (or hi-rel1 hi-rel2)
               (bounds-of-product-* hi1 hi2)
               ))
          ((and (equal (bounds-of-product-* lo1 hi2)
                       (bounds-of-product-* hi1 lo2))
                (equal (bounds-of-product-* lo1 lo2)
                       (bounds-of-product-* hi1 hi2)))
           (mv (and (or lo-rel1 hi-rel2)
                    (or hi-rel1 lo-rel2))
               (bounds-of-product-* lo1 hi2)
               (and (or lo-rel1 lo-rel2)
                    (or hi-rel1 hi-rel2))
               (bounds-of-product-* lo1 lo2)
               ))
          ((and (equal (bounds-of-product-* lo1 hi2)
                       (bounds-of-product-* hi1 lo2))
                (bounds-of-product-< (bounds-of-product-* hi1 hi2)
                                     (bounds-of-product-* lo1 lo2)))
           (mv (and (or lo-rel1 hi-rel2)
                    (or hi-rel1 lo-rel2))
               (bounds-of-product-* lo1 hi2)
               (or lo-rel1 lo-rel2)
               (bounds-of-product-* lo1 lo2)
               ))

          ((and (bounds-of-product-< (bounds-of-product-* hi1 lo2)
                                     (bounds-of-product-* lo1 hi2))
                (bounds-of-product-< (bounds-of-product-* lo1 lo2)
                                     (bounds-of-product-* hi1 hi2)))
           (mv (or hi-rel1 lo-rel2)
               (bounds-of-product-* hi1 lo2)
               (or hi-rel1 hi-rel2)
               (bounds-of-product-* hi1 hi2)
               ))
          ((and (bounds-of-product-< (bounds-of-product-* hi1 lo2)
                                     (bounds-of-product-* lo1 hi2))
                (equal (bounds-of-product-* lo1 lo2)
                       (bounds-of-product-* hi1 hi2)))
           (mv (or hi-rel1 lo-rel2)
               (bounds-of-product-* hi1 lo2)
               (and (or lo-rel1 lo-rel2)
                    (or hi-rel1 hi-rel2))
               (bounds-of-product-* lo1 lo2)
               ))
          (t
           ;; (and (bounds-of-product-< (bounds-of-product-* hi1 lo2)
           ;;                  (bounds-of-product-* lo1 hi2))
           ;;      (bounds-of-product-< (bounds-of-product-* hi1 hi2)
           ;;                  (bounds-of-product-* lo1 lo2)))
           (mv (or hi-rel1 lo-rel2)
               (bounds-of-product-* hi1 lo2)
               (or lo-rel1 lo-rel2)
               (bounds-of-product-* lo1 lo2)
               ))))))

(defun bounds-of-product (lo-rel1 lo1 hi-rel1 hi1 lo-rel2 lo2 hi-rel2 hi2)

; We coerce positive infinities to t, use the workhorse function, and then
; coerce positive infinities back to nil.  We also insure that weak
; inequalities are used with the infinities.  (The workhorse can return a
; strong inequality with an infinity, as happens with: (bounds-of-product1 10
; t nil nil 100 t 100 t) where we get back the lower bound of nil with the
; relation t.)

  (let ((hi1 (if (null hi1) t hi1))
        (hi2 (if (null hi2) t hi2)))
    (mv-let (lo-rel lo hi-rel hi)
            (bounds-of-product1 lo-rel1 lo1 hi-rel1 hi1
                                lo-rel2 lo2 hi-rel2 hi2)
            (mv (if (null lo) nil lo-rel)
                lo
                (if (eq hi t) nil hi-rel)
                (if (eq hi t) nil hi)))))

; Here is a theorem (and proof hint) establishing the correctness of the
; bounds-of-product function.  The version of this theorem in which all bounds
; are finite is due to Robert Krug although we have changed some function names
; and introduced our conventional rel flag (of opposite parity than Robert's
; closedp).

; This theorem is a good application for ACL2(p).  If you are running ACL2(p) the
; following two commands are helpful (and are no-ops in ordinary ACL2).

; (set-waterfall-parallelism t)
; (set-waterfall-printing :limited)

; We break the usual theorem into two parts: one theorem about the domain and
; the other about the bounds.  The reason is that the bounds theorem breaks in
; the special cases that x and/or y is INTEGERP instead of just RATIONALP.
; This is because of some idiosyncracies of arithmetic-5's handling of
; non-linear.

(defun tau-bounder-* (int1 int2)
  (let ((dom (domain-of-binary-arithmetic-function
              (tau-interval-dom int1)
              (tau-interval-dom int2))))
    (mv-let (lo-rel lo hi-rel hi)
            (bounds-of-product (tau-interval-lo-rel int1)
                                   (tau-interval-lo int1)
                                   (tau-interval-hi-rel int1)
                                   (tau-interval-hi int1)
                                   (tau-interval-lo-rel int2)
                                   (tau-interval-lo int2)
                                   (tau-interval-hi-rel int2)
                                   (tau-interval-hi int2))
            (make-tau-interval dom lo-rel lo hi-rel hi))))

; Weakness: The following theorem could be strengthened by concluding, in
; addition, that if int1 and int2 have INTEGERP domains then the tau-bounder-*
; has an INTEGERP domain.  As it stands below, we do not break out the cases
; and concluded only that if both int1 and int2 are either INTEGERP or
; RATIONALP then so is the product.

(encapsulate
  ()
  (local (in-theory (disable
                     ;; Horrible godawful hack.
                     the-floor-below
                     the-floor-above
                     REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<
                     REDUCE-MULTIPLICATIVE-CONSTANT-<
                     REDUCE-ADDITIVE-CONSTANT-<
                     INTEGERP-<-CONSTANT
                     CONSTANT-<-INTEGERP
                     remove-strict-inequalities
                     remove-weak-inequalities
                     prefer-positive-addends-<
                     |(< c (/ x)) positive c --- present in goal|
                     |(< c (/ x)) positive c --- obj t or nil|
                     |(< c (/ x)) negative c --- present in goal|
                     |(< c (/ x)) negative c --- obj t or nil|
                     |(< c (- x))|
                     |(< (/ x) c) positive c --- present in goal|
                     |(< (/ x) c) positive c --- obj t or nil|
                     |(< (/ x) c) negative c --- present in goal|
                     |(< (/ x) c) negative c --- obj t or nil|
                     |(< (/ x) (/ y))|
                     |(< (- x) c)|
                     |(< (- x) (- y))|
                     intervalp-rules
                     REDUCE-RATIONALP-+
                     REDUCE-RATIONALP-*
                     RATIONALP-MINUS-X
                     META-RATIONALP-CORRECT
                     SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL
                     REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL
                     REDUCE-ADDITIVE-CONSTANT-EQUAL
                     PREFER-POSITIVE-ADDENDS-EQUAL
                     EQUAL-OF-PREDICATES-REWRITE
                     |(equal c (/ x))|
                     |(equal c (- x))|
                     |(equal (/ x) c)|
                     |(equal (/ x) (/ y))|
                     |(equal (- x) c)|
                     |(equal (- x) (- y))|
                     |(< (/ x) 0)|
                     |(< (* x y) 0)|
                     (:TYPE-PRESCRIPTION IN-TAU-INTERVALP)
                     (:TYPE-PRESCRIPTION TAU-INTERVALP)
                     (:TYPE-PRESCRIPTION TAU-INTERVAL-DOMAINP)
                     NORMALIZE-FACTORS-GATHER-EXPONENTS
                     SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER
                     SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON
                     SIMPLIFY-SUMS-EQUAL
                     |(< 0 (/ x))|
                     |(< 0 (* x y))|
                     INTEGERP-MINUS-X
                     (:TYPE-PRESCRIPTION BOOLEANP)
                     |(< 0 (* x y)) rationalp (* x y)|
                     META-INTEGERP-CORRECT
                     default-plus-1
                     default-plus-2
                     default-divide
                     member
                     )))

  (local (SET-DEFAULT-HINTS
          '((and stable-under-simplificationp
                 '(:nonlinearp t))
            (and stable-under-simplificationp
                 (not (cw "Jared-hint: re-enabling slow rules.~%"))
                 '(:in-theory (enable jared-disables)))
            (and stable-under-simplificationp
                 (not (cw "Jared-hint: splitting into cases.~%"))
                 '(:cases ((and (< 0 x) (< 0 y))
                           (and (< 0 x) (equal 0 y))
                           (and (< 0 x) (< y 0))
                           (and (equal 0 x) (< 0 y))
                           (and (equal 0 x) (equal 0 y))
                           (and (equal 0 x) (< y 0))
                           (and (< x 0) (< 0 y))
                           (and (< x 0) (equal 0 y))
                           (and (< x 0) (< y 0)))))
            (and stable-under-simplificationp
                 (NONLINEARP-DEFAULT-HINT++
                  ID STABLE-UNDER-SIMPLIFICATIONP HIST NIL)))))

  (defthm tau-bounder-*-correct
    (implies (and (tau-intervalp int1)
                  (tau-intervalp int2)
                  (or (equal (tau-interval-dom int1) 'integerp)
                      (equal (tau-interval-dom int1) 'rationalp))
                  (or (equal (tau-interval-dom int2) 'integerp)
                      (equal (tau-interval-dom int2) 'rationalp))
                  (in-tau-intervalp x int1)
                  (in-tau-intervalp y int2))
             (and (tau-intervalp (tau-bounder-* int1 int2))
                  (in-tau-intervalp (* x y) (tau-bounder-* int1 int2))

                  (implies (not (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'integerp))
                           (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'rationalp))))

; Robert Krug first defined the function (akin to our tau-bounder-*) that
; computed the upper and lower bounds on a product given the bounds on the two
; factors.  He proved it correct and used the hint below, which he said was
; necessary only for some of the cases but which he said was more convenient to
; provide at the top.  Robert also points out that tau-bounder-*-correct
; theorem is a good example for David Rager's work on parallelism.  One might
; try it with:

; (set-waterfall-parallelism t)
; (set-waterfall-printing :limited)

    :rule-classes
    ((:rewrite)
     (:forward-chaining
      :corollary
      (implies (and (tau-intervalp int1)
                    (tau-intervalp int2)
                    (equal (tau-interval-dom int1) 'integerp)
                    (equal (tau-interval-dom int2) 'integerp)
                    (in-tau-intervalp x int1)
                    (in-tau-intervalp y int2))
               (and (tau-intervalp (tau-bounder-* int1 int2))
                    (implies (not (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'integerp))
                             (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'rationalp))
                    (in-tau-intervalp (* x y) (tau-bounder-* int1 int2))))
      :trigger-terms ((tau-bounder-* int1 int2)))
     (:forward-chaining
      :corollary
      (implies (and (tau-intervalp int1)
                    (tau-intervalp int2)
                    (equal (tau-interval-dom int1) 'integerp)
                    (equal (tau-interval-dom int2) 'rationalp)
                    (in-tau-intervalp x int1)
                    (in-tau-intervalp y int2))
               (and (tau-intervalp (tau-bounder-* int1 int2))
                    (implies (not (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'integerp))
                             (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'rationalp))
                    (in-tau-intervalp (* x y) (tau-bounder-* int1 int2))))
      :trigger-terms ((tau-bounder-* int1 int2)))
     (:forward-chaining
      :corollary
      (implies (and (tau-intervalp int1)
                    (tau-intervalp int2)
                    (equal (tau-interval-dom int1) 'rationalp)
                    (equal (tau-interval-dom int2) 'integerp)
                    (in-tau-intervalp x int1)
                    (in-tau-intervalp y int2))
               (and (tau-intervalp (tau-bounder-* int1 int2))
                    (implies (not (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'integerp))
                             (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'rationalp))
                    (in-tau-intervalp (* x y) (tau-bounder-* int1 int2))))
      :trigger-terms ((tau-bounder-* int1 int2)))
     (:forward-chaining
      :corollary
      (implies (and (tau-intervalp int1)
                    (tau-intervalp int2)
                    (equal (tau-interval-dom int1) 'rationalp)
                    (equal (tau-interval-dom int2) 'rationalp)
                    (in-tau-intervalp x int1)
                    (in-tau-intervalp y int2))
               (and (tau-intervalp (tau-bounder-* int1 int2))
                    (implies (not (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'integerp))
                             (equal (tau-interval-dom (tau-bounder-* int1 int2)) 'rationalp))
                    (in-tau-intervalp (* x y) (tau-bounder-* int1 int2))))
      :trigger-terms ((tau-bounder-* int1 int2)))
     )))


; The proof above takes 15 minutes and generates a lot of subgoals.

; [Jared]: I got it down to 180 seconds with stupid AP hacking.  (I think this
; could be significantly improved by not just brute forcing the proof,
; eventually).

; Subgoals: 40,661
; Time:  920.78 seconds (prove: 917.26, print: 3.49, other: 0.02)
; Prover steps counted:  53057929

; The restrictions on the domains of int1 and int2 are necessary.  The theorem
; does not hold for complex numbers.  The imaginary number i, i.e., #c(0 1), is
; in the interval beteen 0 and 10 shown for int1 and int2 below, but (* i i) =
; -1 is not in the product interval, 0 to 100.

; (set-guard-checking :none)
;
; (let ((int1 (make-tau-interval 'acl2-numberp nil 0 nil 10))
;       (int2 (make-tau-interval 'acl2-numberp nil 0 nil 10))
;       (x #c(0 1))
;       (y #c(0 1)))
;   (implies (and (tau-intervalp int1)
;                 (tau-intervalp int2)
; ;               (or (equal (tau-interval-dom int1) 'integerp)    ; delete these hyps
; ;                   (equal (tau-interval-dom int1) 'rationalp))
; ;               (or (equal (tau-interval-dom int2) 'integerp)
; ;                   (equal (tau-interval-dom int2) 'rationalp))
;                 (in-tau-intervalp x int1)
;                 (in-tau-intervalp y int2))
;            (in-tau-intervalp (* x y) (tau-bounder-* int1 int2))))
; NIL

; -----------------------------------------------------------------
; / -- the reciprocal operator

; The reason we care about this case is that we wish to bound (floor x y).  We
; know (floor x y) <= x/y which is (* x (/ y)), and we know how to bound a
; product.  So what remains is how to bound the reciprocal of y given the
; bounds on y.

; If x occupies a finite rational interval that lies STRICTLY above or below 0,
; e.g.,
;                     0 < lo <? x <? hi
; or
;     lo <? x <? hi < 0

; then we can bound (/ x) by inverting and switching the bounds of x:

;  (/ hi) <? (/ x) <? (/ lo)

; However, things are more complicated if x can take on the value 0, either
; because it is bounded weakly above or below 0 or because the interval spans
; 0.  If a rational interval includes 0 then (/ x) cannot be bounded in either
; direction: as x approaches 0 from above, (/ x) becomes infinitely positive;
; as x approaches 0 from below, (/ x) becomes infinitely negative.  (These
; observations depend on x being allowed to take on any rational value.)  What
; happens if one of the endpoints of the interval is 0?  For example what is
; the range of (/ x) if 0 <= x <= 7?  One might think it is 1/7 <= (/ x) <=
; infinity.  But in fact it is 0 <= (/ x) <= infinity because when x = 0, (/ x)
; is (unfortunately) 0 rather than infinity.

; If x is limited to the integers, the situation is more interesting:
; -1 <= (/ x) <= 1 for integral values of x.

(defun bounds-of-reciprocal (x dom lo-rel lo hi-rel hi)
  (declare (ignore x))
; This function returns the bounds on (/ x) given bounds on x.  It is assumed x
; and the bounds, lo and hi, are in the domain specified by dom, which is
; either INTEGERP or RATIONALP.  Furthermore, when dom is INTEGERP, the two
; relations are weak (nil).

; The following table summarizes this definition.  We use -oo and +oo for the
; two infinities. However, when dom is INTEGERP we can't get an infinity out of
; reciprocal.  That is, the biggest thing we can get is 1, because (/ 1) = 1,
; and the smallest is -1.

; Lines [2,5,8,11] are irrelevant when dom is INTEGERP because the relations
; are weak and those lines involve strong relations.

; [1] -oo <= x <=      0            -oo    <= (/ x) <= 0
; [2] -oo <= x <       0            -oo    <= (/ x) <  0
; [3] -oo <= x <? hi < 0            (/ hi) <? (/ x) <  0
; [4]  lo <? x <? hi < 0            (/ hi) <? (/ x) <? (/ lo)
; [5]  lo <? x <       0            -oo    <= (/ x) <? (/ lo)
; [6]  lo <? x <=      0            -oo    <= (/ x) <= 0

; [7]  0        <= x <= +oo         0      <= (/ x) <= +oo
; [8]  0        <  x <= +oo         0      <  (/ x) <= +oo
; [9]  0  <  lo <? x <= +oo         0      <  (/ x) <? (/ lo)
;[10]  0  <  lo <? x <? hi          (/ hi) <? (/ x) <? (/ lo)
;[11]  0        <  x <? hi          (/ hi) <? (/ x) <= +oo
;[12]  0        <= x <? hi          0      <= (/ x) <= +oo

; [*]  all other cases              -oo    <= (/ x) <= +oo


  (let ((-oo (if (eq dom 'integerp) -1 nil))
        (+oo (if (eq dom 'integerp) +1 nil)))
    (cond
     ((null lo)
      (cond ((null hi)
             (mv nil -oo nil +oo))          ; [*]
            ((< hi 0)
             (mv hi-rel (/ hi) t 0))        ; [3]
            ((equal hi 0)
             (mv nil -oo hi-rel 0))         ; [1,2]
            (t
             (mv nil -oo nil +oo))))        ; [*]
     ((< 0 lo)
      (cond
       ((null hi)
        (mv t 0 lo-rel (/ lo)))             ; [9]
       (t
        (mv hi-rel (/ hi) lo-rel (/ lo))))) ; [10]
     ((equal 0 lo)
      (cond ((null hi)
             (mv lo-rel 0 nil +oo))         ; [7,8]
            (lo-rel
             (mv hi-rel (/ hi) nil +oo))    ; [11]
            (t
             (mv nil 0 nil +oo))))          ; [12]
     ((or (null hi)
          (< 0 hi))
      (mv nil -oo nil +oo))                 ; [*]
     ((equal 0 hi)
      (cond
       (hi-rel
        (mv nil -oo lo-rel (/ lo)))         ; [5]
       (t
        (mv nil -oo nil 0))))               ; [6]
     (t
      (mv hi-rel (/ hi) lo-rel (/ lo))))))  ; [4]

(defun tau-bounder-/ (int)
  (mv-let (lo-rel lo hi-rel hi)
          (bounds-of-reciprocal 0
                                (tau-interval-dom int)
                                (tau-interval-lo-rel int)
                                (tau-interval-lo int)
                                (tau-interval-hi-rel int)
                                (tau-interval-hi int))
          (make-tau-interval 'rationalp lo-rel lo hi-rel hi)))

(defthm tau-bounder-/-correct
  (implies (and (tau-intervalp int1)
                (or (equal (tau-interval-dom int1) 'integerp)
                    (equal (tau-interval-dom int1) 'rationalp))
                (in-tau-intervalp x int1))
           (and (tau-intervalp (tau-bounder-/ int1))
                (in-tau-intervalp (/ x) (tau-bounder-/ int1))

                (equal (tau-interval-dom (tau-bounder-/ int1)) 'rationalp)))
  :rule-classes
  ((:rewrite)
   (:forward-chaining
    :corollary
    (implies (and (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (in-tau-intervalp x int1))
             (and (tau-intervalp (tau-bounder-/ int1))
                  (equal (tau-interval-dom (tau-bounder-/ int1)) 'rationalp)
                  (in-tau-intervalp (/ x) (tau-bounder-/ int1))))
    :trigger-terms ((tau-bounder-/ int1)))
   (:forward-chaining
    :corollary
    (implies (and (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'rationalp)
                  (in-tau-intervalp x int1))
             (and (tau-intervalp (tau-bounder-/ int1))
                  (equal (tau-interval-dom (tau-bounder-/ int1)) 'rationalp)
                  (in-tau-intervalp (/ x) (tau-bounder-/ int1))))
    :trigger-terms ((tau-bounder-/ int1)))
   ))

; -----------------------------------------------------------------
; FLOOR

; Intuitively the smallest value of (floor x y) is gotten by taking the
; smallest value of x and flooring it with the biggest value of y, and the
; biggest value of floor is gotten by taking the biggest value of x and
; flooring it with the smallest value of y.  But what about signs, 0, etc?
; Certainly the naive idea above is wrong: suppose 2 <= x <= 25 and -3 <= y <=
; 7, then the actual range of (floor x y) is -25 <= (floor x y) <= +25.  But
; the naive idea says that the smallest value of (floor x y) is (floor 2 25),
; which is 0.  Wrong.  Rather than think it through, we just use the fact that
; (floor x y) is the integer under (/ x y) = (* x (/ y)) and compute the
; integer bounds on the latter expression.

(local
 (defthm floor-tau-bounder-domain
   (integerp (floor x y))))

(defun tau-bounder-floor (int1 int2)
  (let ((int
         (tau-bounder-* int1 (tau-bounder-/ int2))))
    (make-tau-interval 'integerp
                   nil
                   (if (tau-interval-lo int)
                       (floor (tau-interval-lo int) 1)
                       nil)
                   nil
                   (if (tau-interval-hi int)
                       (floor (tau-interval-hi int) 1)
                       nil))))

; This is the first of our proofs in the ``second style.''  The idea is not to
; re-expose the (horrendous) details of tau-bounder-* or any of the other
; pre-verified bounders.  We want the proof to appeal to their correctness
; proofs.  With that in mind, we disable the functions concerned (see the e/d
; below).  We disable the executable-counterpart of make-tau-interval so that
; constant intervals, like (make-tau-interval 'integerp nil nil nil nil) which
; arises in one case above), don't block our use of the intervalp-make-tau-interval
; and in-tau-intervalp-make-tau-interval rules.

; The idea in these second style proofs is that the new bounder,
; tau-bounder-floor expands to expose a composition of old bounders and/or
; make-tau-intervals.  Then the previously proved results apply to the resulting
; intervalp, in-tau-intervalp, and interval-dom expressions which are now applied
; to previously verified bounders.

; However, there is a problem.  The (in-tau-intervalp (make-tau-interval ...))
; exposed by the expansion of tau-bounder-floor below will lead us to the
; goal (among others):

; (FLOOR X Y) <= (TAU-INTERVAL-LO (TAU-BOUNDER-* INT1 (TAU-BOUNDER-/ INT2))).

; This particular goal is a bit tricky because it involves an ``extra step,'' namely
; knowing that (floor x y) <= (* x (/ y)), which is known to arithmetic-5.  So let's
; simplify the discussion by assuming that step is taken care of.  How do we prove
; the resulting:

; (* X (/ Y)) <= (TAU-INTERVAL-LO (TAU-BOUNDER-* INT1 (TAU-BOUNDER-/ INT2))).

; where we know that X is in INT1 and Y is in INT2.

; The relevant lemma about tau-bounder-* concludes with:

; (in-tau-intervalp (* x y) (tau-bounder-* int1 int2))

; From this fact we could conclude

; (IN-TAU-INTERVALP (* X (/ Y)) (TAU-BOUNDER-* INT1 (TAU-BOUNDER-/ INT2))) [1]

; and from there we could get an inequality relating (* X (/ Y)) to the
; INTERVAL-LO of the TAU-BOUNDER-*.  But since [1] isn't in the theorem
; and isn't a subgoal, we have to somehow create it and the only way I can
; think of to do that is forward-chain triggered by a term that will be in
; the problem, namely:

; (TAU-BOUNDER-* INT1 (TAU-BOUNDER-/ INT2)).

; But that requires finding choices for the free variables x and y.

; So the general strategy of the ``second style'' of proof is to do everything
; by forward chaining.  From the presence of (TAU-BOUNDER-/ INT2) we forward
; chain to (IN-TAU-INTERVALP (/ Y) (TAU-BOUNDER-/ INT2)), guessing Y by the presence
; of (IN-TAU-INTERVALP Y INT2) given in the problem.  From the presence of
; (TAU-BOUNDER-* INT1 (TAU-BOUNDER-/ INT2)) we forward chain to
; (IN-TAU-INTERVALP (* X (/ Y)) INT1 (TAU-BOUNDER-/ INT2)), guessing X from
; (IN-TAU-INTERVALP X INT1) given in the problem and guessing (/ Y) from the just
; derived IN-TAU-INTERVALP.

; Once these basic IN-TAU-INTERVALP conditions are derived, we can use :LINEAR lemmas
; like that in IN-TAU-INTERVALP-RULES:

; (implies (and (in-tau-intervalp x int)
;               x
;               (tau-intervalp int)
;               (tau-interval-lo int))
;          (<= (tau-interval-lo int) x))

; which, note, have a free x in them.  That free x is selected via the first
; hyp above, which is present because of forward-chaining.

(defthm tau-bounder-floor-correct
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (or (equal (tau-interval-dom int1) 'integerp)
                    (equal (tau-interval-dom int1) 'rationalp))
                (or (equal (tau-interval-dom int2) 'integerp)
                    (equal (tau-interval-dom int2) 'rationalp))
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-floor int1 int2))
                (in-tau-intervalp (floor x y) (tau-bounder-floor int1 int2))

                (equal (tau-interval-dom (tau-bounder-floor int1 int2)) 'integerp)
                ))
  :hints (("Goal"
           :in-theory
           (disable tau-intervalp
                    in-tau-intervalp
                    tau-bounder-*
                    tau-bounder-/
                    (:executable-counterpart make-tau-interval))))
  :rule-classes
  ((:rewrite)
   (:forward-chaining
    :corollary
    (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'integerp)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-floor int1 int2))
                (equal (tau-interval-dom (tau-bounder-floor int1 int2)) 'integerp)
                (in-tau-intervalp (floor x y) (tau-bounder-floor int1 int2))
                ))
    :trigger-terms ((tau-bounder-floor int1 int2)))
   (:forward-chaining
    :corollary
    (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'integerp)
                (equal (tau-interval-dom int2) 'rationalp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-floor int1 int2))
                (equal (tau-interval-dom (tau-bounder-floor int1 int2)) 'integerp)
                (in-tau-intervalp (floor x y) (tau-bounder-floor int1 int2))
                ))
    :trigger-terms ((tau-bounder-floor int1 int2)))
   (:forward-chaining
    :corollary
    (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'rationalp)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-floor int1 int2))
                (equal (tau-interval-dom (tau-bounder-floor int1 int2)) 'integerp)
                (in-tau-intervalp (floor x y) (tau-bounder-floor int1 int2))
                ))
    :trigger-terms ((tau-bounder-floor int1 int2)))
   (:forward-chaining
    :corollary
    (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'rationalp)
                (equal (tau-interval-dom int2) 'rationalp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-floor int1 int2))
                (equal (tau-interval-dom (tau-bounder-floor int1 int2)) 'integerp)
                (in-tau-intervalp (floor x y) (tau-bounder-floor int1 int2))
                ))
    :trigger-terms ((tau-bounder-floor int1 int2)))
   ))

; -----------------------------------------------------------------
; MOD

; Since (mod x y) = (- x (* (floor x y) y)), the domain of MOD is given
; by domain-of-binary-arithmetic-function:

(defun lower-bound-> (a-rel a b-rel b)

; See Specification of Bound Comparisons, above.

  (if (null a)
      nil
      (if (null b)
          t
          (if (and a-rel (not b-rel))
              (>= a b)
              (> a b)))))

(defun upper-bound-< (a-rel a b-rel b)

; See Specification of Bound Comparisons, above.

  (if (null a)
      nil
      (if (null b)
          t
          (if (and a-rel (not b-rel))
              (<= a b)
              (< a b)))))

(defun combine-intervals1 (dom1 lo-rel1 lo1 hi-rel1 hi1
                                dom2 lo-rel2 lo2 hi-rel2 hi2)
  (mv-let
   (lo-rel lo)
   (if (lower-bound-> lo-rel1 lo1 lo-rel2 lo2)
       (mv lo-rel2 lo2)
       (mv lo-rel1 lo1))
   (mv-let
    (hi-rel hi)
    (if (upper-bound-< hi-rel1 hi1 hi-rel2 hi2)
        (mv hi-rel2 hi2)
        (mv hi-rel1 hi1))
    (make-tau-interval (domain-of-binary-arithmetic-function dom1 dom2)
                   lo-rel lo hi-rel hi))))

(defun squeeze-k (upper-boundp rel k)

; K is either NIL (the appopriate infinity) or a rational.  Consider some
; interval with INTEGERP domain bounded (above or below as per upper-boundp) by
; rel and k.  If k is non-nil, we squeeze the given bound as per:

; Table A:
; upper-boundp  rel   meaning    squeezed        k'
; t             t     (<  x k)   (<= x k')       (- (ceiling k 1) 1)
; t             nil   (<= x k)   (<= x k')       (floor k 1)
; nil           t     (<  k x)   (<= k' x)       (+ (floor k 1) 1)
; nil           nil   (<= k x)   (<= k' x)       (ceiling k 1)

; Programming Note: When k is a non-integer rational,
; (- (ceiling k 1) 1) = (floor k 1), and thus
; (+ (floor k 1) 1)   = (ceiling k 1)
; so the table would be:

; Table B: Non-Integer Rational k:
; upper-boundp  rel   meaning    squeezed        k'
; t             t     (<  x k)   (<= x k')       (floor k 1)
; t             nil   (<= x k)   (<= x k')       (floor k 1)
; nil           t     (<  k x)   (<= k' x)       (ceiling k 1)
; nil           nil   (<= k x)   (<= k' x)       (ceiling k 1)

; But when k is an integer, the table is:

; Table C: Integer k:
; upper-boundp  rel   meaning    squeezed        k'
; t             t     (<  x k)   (<= x k')       (- k 1)
; t             nil   (<= x k)   (<= x k')       k
; nil           t     (<  k x)   (<= k' x)       (+ k 1)
; nil           nil   (<= k x)   (<= k' x)       k

; We actually code Tables B and C and test which to use with (integerp k),
; because we believe it is faster than Table A because whenever k is an integer
; we avoid calls of floor or ceiling.

  (if k
      (if (integerp k)
          (if rel
              (if upper-boundp (- k 1) (+ k 1))
              k)
          (if upper-boundp
              (floor k 1)
              (ceiling k 1)))
      nil))

(defun fix-integerp-interval (int)
  (cond ((eq (tau-interval-dom int) 'integerp)
         (cond ((and (null (tau-interval-lo-rel int))
                     (or (null (tau-interval-lo int))
                         (integerp (tau-interval-lo int)))
                     (null (tau-interval-hi-rel int))
                     (or (null (tau-interval-hi int))
                         (integerp (tau-interval-hi int))))
                int)
               (t (let ((lo (squeeze-k nil (tau-interval-lo-rel int) (tau-interval-lo int)))
                        (hi (squeeze-k  t (tau-interval-hi-rel int) (tau-interval-hi int))))
                    (make-tau-interval 'integerp nil lo nil hi)))))
        (t int)))

(defun tau-bounder-mod (int1 int2)
  (let ((domx (tau-interval-dom int1))
        (lo-relx (tau-interval-lo-rel int1))
        (lox (tau-interval-lo int1))
        (hi-relx (tau-interval-hi-rel int1))
        (hix (tau-interval-hi int1))
        (domy (tau-interval-dom int2))
        (lo-rely (tau-interval-lo-rel int2))
        (loy (tau-interval-lo int2))
        (hi-rely (tau-interval-hi-rel int2))
        (hiy (tau-interval-hi int2)))
    (fix-integerp-interval
     (cond
      ((and (rationalp loy)
            (if lo-rely
                (<= 0 loy)
                (< 0 loy)))

; If y is strictly positive, then (mod x y) lies in the interval between 0 and
; y, which means it is bound above (strictly) by hiy.

       (make-tau-interval (domain-of-binary-arithmetic-function domx domy)
                      nil 0 t hiy))
      ((and (rationalp hiy)
            (if hi-rely
                (<= hiy 0)
                (< hiy 0)))

; If y is strictly negative, then (mod x y) lies in the interval
; between y and 0 which means it is bound below (strictly) by loy.

       (make-tau-interval (domain-of-binary-arithmetic-function domx domy)
                      t loy nil 0))

      (t

; Otherwise, y is not strictly positive and it is not strictly negative, which
; means that y is sometimes 0.  Thus, (mod x y) might return x and hence the
; bounds must include those for the interval containing x, and y might be
; negative or positive, in which case (mod x y) is bound below (strictly) by
; loy and above (strictly) by hiy.  So we combine the two intervals.

       (combine-intervals1 domx lo-relx lox hi-relx hix
                           domy lo-rely loy hi-rely hiy))))))

; Note that (mod x y) can return a complex-rational when its arguments are
; complex-rationals.  The conclusion of the theorem would compare that
; complex-rational to two rationals.  But I don't want to think about that!
; So, we restrict our attention to intervals over the rationals (or integers).
; As a result of this restriction, the domain returned by the general purpose
; bounds-of-mod is the same as that computed by domain-of-sum-or-product, as
; noted in our theorem below.

(encapsulate
  ()
  (local (in-theory (disable jared-disables)))
  (local (in-theory (disable (:t not-integerp-4b)
                             (:t not-integerp-3b)
                             (:t not-integerp-2b)
                             (:t not-integerp-1b)
                             ;; integerp-mod-1
                             ;; integerp-mod-2
                             ;; rationalp-mod
                             mod-nonnegative
                             mod-nonpositive
                             mod-zero
                             mod-positive
                             mod-negative
                             MOD-X-Y-=-X
                             MOD-X-Y-=-X+Y
                             MOD-X-Y-=-X-Y
                             ;; mod-bounds-1
                             ;; mod-bounds-2
                             the-floor-below
                             the-floor-above
                             default-times-1
                             default-times-2
                             default-plus-1
                             default-plus-2
                             REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<
                             |(< c (/ x)) positive c --- present in goal|
                             |(< c (/ x)) positive c --- obj t or nil|
                             |(< c (/ x)) negative c --- present in goal|
                             |(< c (/ x)) negative c --- obj t or nil|
                             |(< c (- x))|
                             |(< (/ x) c) positive c --- present in goal|
                             |(< (/ x) c) positive c --- obj t or nil|
                             |(< (/ x) c) negative c --- present in goal|
                             |(< (/ x) c) negative c --- obj t or nil|
                             |(< (/ x) (/ y))|
                             |(< (- x) c)|
                             |(< (- x) (- y))|
                             rationalp-x
                             PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2
                             PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL
                             default-car
                             default-cdr
                             cancel-mod-+
                             meta-integerp-correct
                             meta-rationalp-correct
                             acl2-numberp-x

                             in-tau-intervalp-rules
                             intervalp-rules
                             )))

  (local (set-default-hints
          '((and stable-under-simplificationp
                 '(:nonlinearp t))
            (and stable-under-simplificationp
                 (NONLINEARP-DEFAULT-HINT++
                  ID STABLE-UNDER-SIMPLIFICATIONP HIST NIL))
            (and stable-under-simplificationp
                 (not (cw "Jared-hint: re-enabling slower rules.~%"))
                 '(:in-theory (enable jared-disables))))))

  (defthm tau-bounder-mod-correct
    (implies (and (tau-intervalp int1)
                  (tau-intervalp int2)
                  (or (equal (tau-interval-dom int1) 'integerp)
                      (equal (tau-interval-dom int1) 'rationalp))
                  (or (equal (tau-interval-dom int2) 'integerp)
                      (equal (tau-interval-dom int2) 'rationalp))
                  (in-tau-intervalp x int1)
                  (in-tau-intervalp y int2))
             (and (tau-intervalp (tau-bounder-mod int1 int2))
                  (in-tau-intervalp (mod x y) (tau-bounder-mod int1 int2))

                  (implies (not (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'integerp))
                           (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'rationalp))
                  ))
    :rule-classes
    ((:rewrite)
     (:forward-chaining
      :corollary
      (implies (and (tau-intervalp int1)
                    (tau-intervalp int2)
                    (equal (tau-interval-dom int1) 'integerp)
                    (equal (tau-interval-dom int2) 'integerp)
                    (in-tau-intervalp x int1)
                    (in-tau-intervalp y int2))
               (and (tau-intervalp (tau-bounder-mod int1 int2))
                    (implies (not (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'integerp))
                             (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'rationalp))
                    (in-tau-intervalp (mod x y) (tau-bounder-mod int1 int2))
                    ))
      :trigger-terms ((tau-bounder-mod int1 int2)))
     (:forward-chaining
      :corollary
      (implies (and (tau-intervalp int1)
                    (tau-intervalp int2)
                    (equal (tau-interval-dom int1) 'integerp)
                    (equal (tau-interval-dom int2) 'rationalp)
                    (in-tau-intervalp x int1)
                    (in-tau-intervalp y int2))
               (and (tau-intervalp (tau-bounder-mod int1 int2))
                    (implies (not (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'integerp))
                             (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'rationalp))
                    (in-tau-intervalp (mod x y) (tau-bounder-mod int1 int2))
                    ))
      :trigger-terms ((tau-bounder-mod int1 int2)))
     (:forward-chaining
      :corollary
      (implies (and (tau-intervalp int1)
                    (tau-intervalp int2)
                    (equal (tau-interval-dom int1) 'rational)
                    (equal (tau-interval-dom int2) 'integerp)
                    (in-tau-intervalp x int1)
                    (in-tau-intervalp y int2))
               (and (tau-intervalp (tau-bounder-mod int1 int2))
                    (implies (not (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'integerp))
                             (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'rationalp))
                    (in-tau-intervalp (mod x y) (tau-bounder-mod int1 int2))
                    ))
      :trigger-terms ((tau-bounder-mod int1 int2)))
     (:forward-chaining
      :corollary
      (implies (and (tau-intervalp int1)
                    (tau-intervalp int2)
                    (equal (tau-interval-dom int1) 'rationalp)
                    (equal (tau-interval-dom int2) 'rationalp)
                    (in-tau-intervalp x int1)
                    (in-tau-intervalp y int2))
               (and (tau-intervalp (tau-bounder-mod int1 int2))
                    (implies (not (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'integerp))
                             (equal (tau-interval-dom (tau-bounder-mod int1 int2)) 'rationalp))
                    (in-tau-intervalp (mod x y) (tau-bounder-mod int1 int2))
                    ))
      :trigger-terms ((tau-bounder-mod int1 int2)))
     )))


; -----------------------------------------------------------------
; The Arithmetic-Logical Functions

; The logical functions always take and return integers.  Our theorems require
; this.  We thus know that the relations, e.g., ``lo-rel'' and ``hi-rel'',
; bounding the various quantities are always weak.  Hence, our functions for
; computing bounds and our theorems about those functions don't traffic in
; relations.  For example, ``bounds-of-logand'' takes four argument, the bounds
; on x and y, not eight; it returns two results, not four.  (However, the
; theorems still use (<? nil lo ...), for example, rather than (<= lo ...)
; because lo might be a nil representing negative infinity.)

; To help us keep track of these reduced signatures, we add an ``i'' for
; ``integer'' to the bounds functions and theorem names, e.g.,
; ibounds-for-logand and logand-tau-bounder-ibounds.  The functions concerned
; are:

; LOGAND
; LOGNOT
; LOGIOR
; LOGORC1
; LOGEQV
; LOGXOR
; EXPT2
; ASH

; If others are added, make sure they traffic only in integers!

; -----------------------------------------------------------------
; LOGAND

; We first prove a variety of lemmas to handle special cases.  Some of these
; lemmas restrict the domains of x and y to INTEGERP and some don't.  But our
; main result will apply only to INTEGERP domains, INTEGERP bounds, and weak
; relations.

; By the way, it is known that INTEGERP (logand x y), no matter what x and y
; are.

; If x is in the interval 0 <= minx <= x <= maxx and
;    y is in the interval 0 <= miny <= y <= maxy, then
; then (logand x y) is in
; the interval 0 <= (logand x y) <= (min maxx maxy).

; Note that we can't raise the lower bound because if x and y have no bits in
; common (as in x=4 and y=8), their logand is in fact 0.

(local
 (defthm LOGAND-tau-bounder-both-nonnegative
   (implies (and (<= 0 minx) (<= minx x) (<= x maxx)
                 (<= 0 miny) (<= miny y) (<= y maxy))
            (and (<= 0
                     (logand x y))
                 (<= (logand x y)
                     (min maxx maxy))))
   :rule-classes (:rewrite :linear)))

; If both x and y are negative integers, then x+y < (logand x y) <= (min x y).

(defun shifts-to-all-ones (x)

; Assuming x < 0, how many times must we shift x to make it -1?  This turns out
; to be either (log2 (- x)) or (+ 1 (log2 (- x))), depending on whether (- x)
; is a power of 2 -- but I haven't proved that and don't need it.

  (if (and (integerp x)
           (< x 0))
      (if (equal x -1)
          0
          (+ 1 (shifts-to-all-ones (ash x -1))))
      0))

(local
 (encapsulate
  nil
  (local
   (defthm expt-2-shifts-to-all-ones
     (implies (and (integerp x) (< x 0))
              (<= (- (expt 2 (shifts-to-all-ones x)))
                  x))
     :rule-classes :linear))

  (local
   (defthm logand-both-negative-lower-bound
     (implies (and (integerp x)
                   (integerp y)
                   (< x 0)
                   (< y 0))
              (<= (- (expt 2 (max (shifts-to-all-ones x)
                                  (shifts-to-all-ones y))))
                  (logand x y)))
     :hints
     (("Goal" :in-theory (e/d (logand)(|(logand (floor x 2) (floor y 2))| ))))
     :rule-classes nil))

  (local
   (defthm logand-both-negative
     (implies (and (integerp x)
                   (integerp y)
                   (< x 0)
                   (< y 0))
              (and (<= (- (expt 2 (max (shifts-to-all-ones x)
                                       (shifts-to-all-ones y))))
                       (logand x y))
                   (<= (logand x y) (min x y))))
     :hints (("Goal" :use logand-both-negative-lower-bound))
     :rule-classes nil))


  (local
   (defun shifts-to-all-ones-monotonic-hint (x y)
     (if (and (integerp x)
              (< x 0)
              (integerp y)
              (< y 0))
         (if (equal x -1)
             0
             (if (equal y -1)
                 0
                 (shifts-to-all-ones-monotonic-hint (ash x -1) (ash y -1))))
         0)))
  (local
   (defthm shifts-to-all-ones-monotic
     (implies (and (integerp x)
                   (integerp y)
                   (< y 0)
                   (<= x y))
              (<= (shifts-to-all-ones y)
                  (shifts-to-all-ones x)))
     :hints (("Goal" :induct (shifts-to-all-ones-monotonic-hint x y)))
     :rule-classes nil))

  (defthm logand-tau-bounder-both-negative
    (implies (and (integerp x)
                  (integerp y)
                  (integerp minx)
                  (integerp miny)
                  (integerp maxx)
                  (integerp maxy)
                  (<= minx x) (<= x maxx) (< maxx 0)
                  (<= miny y) (<= y maxy) (< maxy 0))
             (and (<= (- (expt 2 (max (shifts-to-all-ones minx)
                                      (shifts-to-all-ones miny))))
                      (logand x y))
                  (<= (logand x y) (min maxx maxy))))
    :hints (("Goal" :use ((:instance logand-both-negative)
                          (:instance shifts-to-all-ones-monotic
                                     (x minx)
                                     (y x))
                          (:instance shifts-to-all-ones-monotic
                                     (x miny)
                                     (y y)))))
    :rule-classes (:rewrite :linear))
  ))

(local
 (defthm logand-tau-bounder-both-either-lower-bound
   (implies (and (integerp x)
                 (integerp y)
                 (integerp minx)
                 (integerp miny)
                 (<= minx x)
                 (<= miny y))
            (<= (min 0 (- (expt 2 (max (shifts-to-all-ones minx)
                                       (shifts-to-all-ones miny)))))
                (logand x y)))
   :hints (("Goal"
            :in-theory (disable max)
            :cases ((and (< x 0)(< y 0)))))
   :rule-classes (:rewrite :linear)))

; The following bound is not very good.  Intuitively it ought to be (min maxx
; maxy).  But suppose x is -1 and maxx is 2 and y is 8 and maxy is 10: Then the
; (logand x y) = y = 8, but (min maxx maxy) = 2.  Oops.  The problem is that if
; x and y are allowed to range all over, then (logand x y) might be x or y as
; the other takes on the value -1.  But if we have to describe the bounds in
; terms of maxx and maxy, then the best we can do is be ready for either x or
; y, e.g., (max maxx maxy).

(local
 (defthm logand-tau-bounder-both-either-upper-bound
   (implies (and (integerp x)
                 (integerp y)
                 (<= x maxx)
                 (<= y maxy))
            (<= (logand x y) (max maxx maxy)))
   :hints (("Goal"
            :cases ((and (< x 0)(< y 0)))))
   :rule-classes (:rewrite :linear)))

; Unfortunately, the analytical bounds derived above are sometimes not very
; good.  We therefore use an empirical method to compute the bounds for logand
; over small intervals.

(local (include-book "find-minimal-2d"))

(defun find-minimal-logand2 (x loy hiy min)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hiy)) (ifix loy)))
                  :guard (and (integerp x)
                              (integerp loy)
                              (integerp hiy)
                              (or (null min) (integerp min)))
                  :verify-guards nil))
  (cond
   ((mbe :logic (not (and (integerp loy)
                          (integerp hiy)))
         :exec nil)
    min)
   ((> loy hiy) min)
   (t (find-minimal-logand2
       x
       (+ 1 loy) hiy
       (if (or (null min)
               (< (logand x loy) min))
           (logand x loy)
           min)))))

(defun find-minimal-logand1 (lox hix loy hiy min)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hix)) (ifix lox)))
                  :guard (and (integerp lox)
                              (integerp hix)
                              (integerp loy)
                              (integerp hiy)
                              (or (null min) (integerp min)))
                  :verify-guards nil))
  (cond
   ((mbe :logic (not (and (integerp lox)
                          (integerp hix)))
         :exec nil)
    min)
   ((> lox hix) min)
   (t (find-minimal-logand1
       (+ 1 lox) hix
       loy hiy
       (find-minimal-logand2 lox loy hiy min)))))

; This is the wrapper that initializes the running minimal, min, to nil.  But
; all our lemmas except the last will be about the two recursive functions
; above.

(defun find-minimal-logand (lox hix loy hiy)
  (declare (xargs :guard (and (integerp lox)
                              (integerp hix)
                              (integerp loy)
                              (integerp hiy))
                  :verify-guards nil))
  (find-minimal-logand1 lox hix loy hiy nil))

(local
 (defthm find-minimal-logand-correct
   (implies (and (integerp lox)
                 (integerp hix)
                 (integerp loy)
                 (integerp hiy)
                 (integerp x)
                 (<= lox x)
                 (<= x hix)
                 (integerp y)
                 (<= loy y)
                 (<= y hiy))
            (and (integerp (find-minimal-logand lox hix loy hiy))
                 (<= (find-minimal-logand lox hix loy hiy)
                     (logand x y))))
   :hints (("Goal" :use (:functional-instance
                         find-minimal-correct
                         (fmla (lambda (x y) (logand x y)))
                         (find-minimal2 find-minimal-logand2)
                         (find-minimal1 find-minimal-logand1)
                         (find-minimal find-minimal-logand))))))


(in-theory (disable find-minimal-logand))

(local (include-book "find-maximal-2d"))

(defun find-maximal-logand2 (x loy hiy max)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hiy)) (ifix loy)))
                  :guard (and (integerp x)
                              (integerp loy)
                              (integerp hiy)
                              (or (null max) (integerp max)))
                  :verify-guards nil))
  (cond
   ((mbe :logic (not (and (integerp loy)
                          (integerp hiy)))
         :exec nil)
    max)
   ((> loy hiy) max)
   (t (find-maximal-logand2
       x
       (+ 1 loy) hiy
       (if (or (null max)
               (> (logand x loy) max))
           (logand x loy)
           max)))))

(defun find-maximal-logand1 (lox hix loy hiy max)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hix)) (ifix lox)))
                  :guard (and (integerp lox)
                              (integerp hix)
                              (integerp loy)
                              (integerp hiy)
                              (or (null max) (integerp max)))
                  :verify-guards nil))
  (cond
   ((mbe :logic (not (and (integerp lox)
                          (integerp hix)))
         :exec nil)
    max)
   ((> lox hix) max)
   (t (find-maximal-logand1
       (+ 1 lox) hix
       loy hiy
       (find-maximal-logand2 lox loy hiy max)))))

; This is the wrapper that initializes the running maximal, max, to nil.  But
; all our lemmas except the last will be about the two recursive functions
; above.

(defun find-maximal-logand (lox hix loy hiy)
  (declare (xargs :guard (and (integerp lox)
                              (integerp hix)
                              (integerp loy)
                              (integerp hiy))
                  :verify-guards nil))
  (find-maximal-logand1 lox hix loy hiy nil))

; A nice way to demo the effectiveness of guard verification is to admit these
; functions with :verify-guards nil and run

; (time$ (find-minimal-logand 0 1023 0 1023))

; then do the verify-guards below and repeat the timing.  You get about a 14x
; speed up.

(verify-guards find-minimal-logand2)
(verify-guards find-minimal-logand1)
(verify-guards find-minimal-logand)
(verify-guards find-maximal-logand2)
(verify-guards find-maximal-logand1)
(verify-guards find-maximal-logand)

(local
 (defthm find-maximal-logand-correct
   (implies (and (integerp lox)
                 (integerp hix)
                 (integerp loy)
                 (integerp hiy)
                 (integerp x)
                 (<= lox x)
                 (<= x hix)
                 (integerp y)
                 (<= loy y)
                 (<= y hiy))
            (and (integerp (find-maximal-logand lox hix loy hiy))
                 (>= (find-maximal-logand lox hix loy hiy)
                     (logand x y))))
   :hints (("Goal" :use (:functional-instance
                         find-maximal-correct
                         (fmla (lambda (x y) (logand x y)))
                         (find-maximal2 find-maximal-logand2)
                         (find-maximal1 find-maximal-logand1)
                         (find-maximal find-maximal-logand))))))

(in-theory (disable find-maximal-logand))

(defthm find-minimal-logand-below-find-maximal-logand
  (implies (and (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy)
                (<= lox hix)
                (<= loy hiy))
           (<= (find-minimal-logand lox hix loy hiy)
	       (find-maximal-logand lox hix loy hiy)))
  :hints (("Goal"
           :use
           ((:instance find-minimal-logand-correct
                       (x lox)
                       (y loy))
            (:instance find-maximal-logand-correct
             (x lox)
             (y loy)))
           :in-theory (disable find-minimal-logand-correct
                               find-maximal-logand-correct)))
  :rule-classes :linear)

(defconst *logand-empirical-threshhold* (* 1024 1024))

(defun worth-computingp (lox hix loy hiy)

; This function is for heuristic purposes only.  It determines whether we
; compute the exact minimal and maximal of logand over a pair of intervals by
; computing logand for each combination.  The threshhold chosen above just
; allows us to compute the bounds on 10-bit x 10-bit logands.  It takes a total
; of 0.066123 seconds to compute the two bounds on intervals of this size,
; running on a 2.6 GHz Intel Core i7 Macbook Pro in CCL.  Note also that the
; way we actually compute the minimal and maximal (see bounds-of-logand below)
; is to compute them separately in two passes over the matrix.  We could
; presumably save a little overhead by computing them in one pass.

  (< (* (if (<= lox hix) (+ 1 (- hix lox)) 0)
        (if (<= loy hiy) (+ 1 (- hiy loy)) 0))
     *logand-empirical-threshhold*))

(in-theory (disable worth-computingp))

; This function assumes both domains are INTEGERp.

(defun tau-bounder-logand (int1 int2)
  (let ((lox (tau-interval-lo int1))
        (hix (tau-interval-hi int1))
        (loy (tau-interval-lo int2))
        (hiy (tau-interval-hi int2)))
      (cond
       ((and lox hix loy hiy (worth-computingp lox hix loy hiy))
        (make-tau-interval
         'integerp
         nil
         (find-minimal-logand lox hix loy hiy)
         nil
         (find-maximal-logand lox hix loy hiy)))
       ((and lox (<= 0 lox) ; x nonnegative
             loy (<= 0 loy)) ; y nonnegative
        (make-tau-interval 'integerp nil 0 nil (and hix hiy (min hix hiy))))
       ((and hix (< hix 0)  ; x negative
             hiy (< hiy 0)) ; y negative
        (make-tau-interval
         'integerp
         nil
         (and lox loy
              (- (expt 2 (max (shifts-to-all-ones lox)
                              (shifts-to-all-ones loy)))))
         nil
         (min hix hiy)))
       ((and hix (<= hix 0) ; x negative
             loy (<= 0 loy)) ; y nonnegative
        (make-tau-interval 'integerp nil 0 nil hiy))
       ((and hiy (<= hiy 0) ; x nonnegative
             lox (<= 0 lox)) ; y negative
        (make-tau-interval 'integerp nil 0 nil hix))
       ((and lox (<= 0 lox)) ; x nonnegative, y is either
        (make-tau-interval 'integerp nil 0 nil (and hix hiy (max hix hiy))))
       ((and loy (<= 0 loy)) ; y nonnegative, x is either
        (make-tau-interval 'integerp nil 0 nil (and hix hiy (max hix hiy))))
       (t
        (make-tau-interval
         'integerp
         nil
         (and lox loy (min 0 (- (expt 2 (max (shifts-to-all-ones lox)
                                             (shifts-to-all-ones loy))))))
         nil
         (and hix hiy (max hix hiy)))))))

(local
 (defthm min-max-properties
   (and (<= (min x y) x)
        (<= (min x y) y)
        (<= x (max x y))
        (<= y (max x y)))
   :rule-classes :linear))

(defthm tau-bounder-logand-correct
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'integerp)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-logand int1 int2))
                (in-tau-intervalp (logand x y) (tau-bounder-logand int1 int2))

                (equal (tau-interval-dom (tau-bounder-logand int1 int2)) 'integerp)
            ))
  :hints (("Goal" :in-theory (disable min max)))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-logand int1 int2)))
   ))

; These bounds aren't always very tight.  See the essay On the Accuracy of the
; LOGAND Bounder at the end of this book.

; -----------------------------------------------------------------
; LOGNOT

(defun tau-bounder-lognot (int)
  (let ((lo (tau-interval-lo int))
        (hi (tau-interval-hi int)))
    (make-tau-interval 'integerp
                   nil (if hi (- (- hi) 1) nil)
                   nil (if lo (- (- lo) 1) nil))))

(defthm tau-bounder-lognot-correct
  (implies (and (tau-intervalp int1)
                (equal (tau-interval-dom int1) 'integerp)
                (in-tau-intervalp x int1))
           (and (tau-intervalp (tau-bounder-lognot int1))
                (in-tau-intervalp (lognot x) (tau-bounder-lognot int1))

                (equal (tau-interval-dom (tau-bounder-lognot int1)) 'integerp)
            ))
  :hints (("Goal" :in-theory (enable lognot)))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-lognot int1)))
   ))

; -----------------------------------------------------------------
; LOGIOR

; (Logior x y) = (lognot (logand (lognot x) (lognot y)))

; Therefore, we'll first try bounding it by composing our existing bounds functions.
; My old bound theorem for logior only worked for natp x and y.  It was:
; (MIN MINX MINY) <= (LOGIOR X Y) <= (EXPT 2 (LOG2 (MAX MAXX MAXY))).

(defun tau-bounder-logior (int1 int2)
  (tau-bounder-lognot
   (tau-bounder-logand
    (tau-bounder-lognot int1)
    (tau-bounder-lognot int2))))

(defthm tau-bounder-logior-correct
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'integerp)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-logior int1 int2))
                (in-tau-intervalp (logior x y) (tau-bounder-logior int1 int2))

                (equal (tau-interval-dom (tau-bounder-logior int1 int2)) 'integerp)
                ))
  :hints
  (("Goal"
    :in-theory
    (e/d (logior)
         (tau-intervalp
          in-tau-intervalp
          tau-bounder-logand
          tau-bounder-lognot
          lognot-logand ; rewrite rule in arithmetic-5 that folds logior
          (:executable-counterpart make-tau-interval)))))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-logior int1 int2)))
   ))

; -----------------------------------------------------------------
; LOGORC1

; (logorc1 x y) = (logior (lognot x) y)

(defun tau-bounder-logorc1 (int1 int2)
  (tau-bounder-logior
   (tau-bounder-lognot int1)
   int2))

(defthm tau-bounder-logorc1-correct
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'integerp)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-logorc1 int1 int2))
                (in-tau-intervalp (logorc1 x y) (tau-bounder-logorc1 int1 int2))

                (equal (tau-interval-dom (tau-bounder-logorc1 int1 int2)) 'integerp)
                ))
  :hints
  (("Goal"
    :in-theory
    (e/d (logorc1)
         (tau-intervalp
          in-tau-intervalp
          tau-bounder-logior
          tau-bounder-lognot
          |(logior y x)| ; commutative rule for logior
          (:executable-counterpart make-tau-interval)))))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-logorc1 int1 int2)))
   ))

; -----------------------------------------------------------------
; LOGEQV

; (logeqv x y) = (logand (logorc1 x y) (logorc1 y x))

(defun tau-bounder-logeqv (int1 int2)
  (tau-bounder-logand
   (tau-bounder-logorc1 int1 int2)
   (tau-bounder-logorc1 int2 int1)))

(defthm tau-bounder-logeqv-correct
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'integerp)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-logeqv int1 int2))
                (in-tau-intervalp (logeqv x y) (tau-bounder-logeqv int1 int2))

                (equal (tau-interval-dom (tau-bounder-logeqv int1 int2)) 'integerp)
                ))
  :hints
  (("Goal"
    :in-theory
    (e/d (logeqv)
         (tau-intervalp
          in-tau-intervalp
          logorc1
          tau-bounder-logand
          tau-bounder-logorc1
          (:executable-counterpart make-tau-interval)))))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-logeqv int1 int2)))
   ))

; -----------------------------------------------------------------
; LOGXOR

; (logxor x y) = (lognot (logeqv x y))

(defun tau-bounder-logxor (int1 int2)
  (tau-bounder-lognot
   (tau-bounder-logeqv int1 int2)))

(defthm tau-bounder-logxor-correct
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'integerp)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-logxor int1 int2))
                (in-tau-intervalp (logxor x y) (tau-bounder-logxor int1 int2))

                (equal (tau-interval-dom (tau-bounder-logxor int1 int2)) 'integerp)
                ))
  :hints
  (("Goal"
    :in-theory
    (e/d (logxor)
         (tau-intervalp
          in-tau-intervalp
          logeqv
          tau-bounder-lognot
          tau-bounder-logeqv
          (:executable-counterpart make-tau-interval)))))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-logxor int1 int2)))
   ))

; -----------------------------------------------------------------
; (EXPT 2 y)

; While we could bound (EXPT x y), we choose for the moment to focus on just
; what we need for ASH, which is (EXPT 2 y).  The situations for x < 0 and (not
; (integerp x)) are messy.  We assume y is an INTEGERP.

; Note that this ``i''-bounds function uncharacteristically returns the domain
; pair of (expt 2 y) as well.  The trouble is that while y must be an integer
; and (expt 2 y) is an integer for non-negative y, (expt 2 y) is a rational for
; negative y.

(defun tau-bounder-expt2 (int2)
  (let ((loy (tau-interval-lo int2))
        (hiy (tau-interval-hi int2)))
    (if loy
        (if (<= 0 loy)
            (if hiy
                (make-tau-interval 'integerp nil (expt 2 loy) nil (expt 2 hiy))
                (make-tau-interval 'integerp nil (expt 2 loy) nil nil))
            (if hiy
                (make-tau-interval 'rationalp nil (expt 2 loy) nil (expt 2 hiy))
                (make-tau-interval 'rationalp nil (expt 2 loy) nil nil)))
        (if hiy
            (make-tau-interval 'rationalp t 0 nil (expt 2 hiy))
            (make-tau-interval 'rationalp t 0 nil nil)))))

; Warning:  We only deal with (EXPT 2 y), for integerp y!

(defthm tau-bounder-expt2-correct
  (implies (and (tau-intervalp int2)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-expt2 int2))
                (in-tau-intervalp (expt 2 y) (tau-bounder-expt2 int2))

                (implies (not (equal (tau-interval-dom (tau-bounder-expt2 int2)) 'integerp))
                         (equal (tau-interval-dom (tau-bounder-expt2 int2)) 'rationalp))
                ))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-expt2 int2)))
   ))

; -----------------------------------------------------------------
; (EXPT r i)

; Both parameters of this tau-bounder are intervals. So tau-system can accept
; it.  It recognizes specific case r=2 and delegates it to the previous bounder
; and returns the entire rational set in the general case.

(defun tau-bounder-expt (intr inti)
  (if
    (and
      (equal (tau-interval-lo intr) 2)
      (equal (tau-interval-hi intr) 2))
    (tau-bounder-expt2 inti)
    (make-tau-interval 'rationalp nil nil nil nil)))

; Warning:  We only deal with (EXPT 2 i), for integerp i!

(defthm tau-bounder-expt-correct
  (implies (and (tau-intervalp intr)
                (equal (tau-interval-dom intr) 'integerp)
                (in-tau-intervalp r intr)
                (tau-intervalp inti)
                (equal (tau-interval-dom inti) 'integerp)
                (in-tau-intervalp i inti))
           (and (tau-intervalp (tau-bounder-expt intr inti))
                (in-tau-intervalp (expt r i) (tau-bounder-expt intr inti))

                (implies (not (equal (tau-interval-dom (tau-bounder-expt intr inti)) 'integerp))
                         (equal (tau-interval-dom (tau-bounder-expt intr inti)) 'rationalp))
                ))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-expt intr inti)))
   ))

; -----------------------------------------------------------------
; ASH

; (ash x y) = (floor (* (ifix x) (expt 2 y)) 1)

(defun tau-bounder-ash (int1 int2)
  (tau-bounder-floor
   (tau-bounder-* int1
                   (tau-bounder-expt2 int2))
   (make-tau-interval 'integerp nil 1 nil 1)))

; Weakness: See the little essay immediately below on why I need the :use hint!
; It opens a raft of difficulties.

(defthm tau-bounder-ash-correct
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (equal (tau-interval-dom int1) 'integerp)
                (equal (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2))
           (and (tau-intervalp (tau-bounder-ash int1 int2))
                (in-tau-intervalp (ash x y) (tau-bounder-ash int1 int2))

                (equal (tau-interval-dom (tau-bounder-ash int1 int2)) 'integerp)
                ))
  :hints
  (("Goal"
    :use ((:instance tau-bounder-floor-correct
                     (x (* x (expt 2 y)))
                     (int1 (TAU-BOUNDER-* INT1 (TAU-BOUNDER-EXPT2 INT2)))
                     (y 1)
                     (int2 (MAKE-TAU-INTERVAL 'INTEGERP NIL 1 NIL 1))))
    :in-theory
    (e/d (ash)
         (tau-intervalp
          in-tau-intervalp
          tau-bounder-floor
          tau-bounder-*
          tau-bounder-expt2
          tau-bounder-floor-correct ; <--- since I :use it above
          (:executable-counterpart make-tau-interval)))))
  :rule-classes
  ((:rewrite)
   (:forward-chaining :trigger-terms ((tau-bounder-ash int1 int2)))
   ))

; On Why We Need the :USE Hint in the Proof of that the ASH Bounder is Correct

; Consider just the proof of the first concluding conjunct above,

; (TAU-INTERVALP (TAU-BOUNDER-ASH INT1 INT2)).

; After opening up, this is:

;  (TAU-INTERVALP (TAU-BOUNDER-FLOOR
;              (TAU-BOUNDER-* INT1
;                              (TAU-BOUNDER-EXPT2 INT2))
;              (MAKE-TAU-INTERVAL 'INTEGERP NIL 1 NIL 1)))

; We mean to prove this by :forward-chaining from the three correctness lemmas
; for FLOOR, *, and EXPT2.  To use the TAU-BOUNDER-FLOOR-CORRECT theorem, we
; need to have derived:

; [1] (tau-intervalp (TAU-BOUNDER-* INT1 (TAU-BOUNDER-EXPT2 INT2)))

; [2] (tau-intervalp (MAKE-TAU-INTERVAL 'INTEGERP NIL 1 NIL 1))

; We could get [2] in one of several ways but we don't pursue those
; improvements because we'd still be blocked from our ultimate ASH goal by the
; problems raised by [1].  But to elaborate slightly on fixing [2], one
; solution would be to add the :forward-chaining rule:

; (defthm make-tau-interval-x-x
;   (implies (integerp x)
;            (and (equal (tau-interval-dom (make-tau-interval 'integerp nil x nil x)) 'integerp)
;                 (tau-intervalp (make-tau-interval 'integerp nil x nil x))
;                 (in-tau-intervalp x (make-tau-interval 'integerp nil x nil x))))
;   :rule-classes ((:forward-chaining :trigger-terms ((make-tau-interval 'integerp nil x nil x)))))

; Alternatively we could rely on the fact that forward-chaining evaluates
; ground terms and [2] is a ground term, but we have (:executable-counterpart
; make-tau-interval) disabled in these ``second style'' proofs so as to simplify
; the application of our basic rules for tearing apart IN-TAU-INTERVALP and
; INTERVALP of MAKE-TAU-INTERVAL expressions.  (If ground MAKE-TAU-INTERVALs are
; evaluated, we'd have to recode some of those rules so that, for example
; (in-tau-intervalp x (cons dom (cons (cons lo-rel lo) (cons hi-rel hi)))) is
; expanded appropriately.)

; But as noted, we don't try to fix [2] because we're still blocked by [1].

; What does it take to get [1]?  To apply tau-bounder-*-correct we need to
; know that its second argument, (TAU-BOUNDER-EXPT2 INT2), is an intervalp
; [which we can get via tau-bounder-expt2-correct] and we need to know that
; the domain of (TAU-BOUNDER-EXPT2 INT2) is either 'INTEGERP or 'RATIONALP.
; Now in fact the domain of (TAU-BOUNDER-EXPT2 INT2) is one of those two, but
; we don't know which.  (If Y is non-negative, the domain is INTEGERP and if Y
; is negative it is RATIONALP -- but this fact, like the fact that
; tau-bounder-* is weak because it doesn't tell us when the product is an
; INTEGERP -- is not proved here.)  But even we had proved this fact, it
; wouldn't help us because we don't know the sign of Y, forward-chaining
; doesn't do case analysis, and forward-chaining cannot propagage disjunctions.
; The only way to win here is to :USE some rule that puts the necessary
; conditions into the theorem and let the simplifier consider the cases.

; This perhaps calls into question the whole ``second style'' of proof, based
; on forward-chaining from previously proved correctness theorems.  However,
; revisit the discussion on the role of forward-chaining in the comment
; preceding tau-bounder-floor-correct.

; -----------------------------------------------------------------
; There are no events beyond this point
; -----------------------------------------------------------------

; On the Accuracy of the LOGAND Bounder
;
; [This essay was written to be somewhat self-contained and so repeats some basic
; facts before getting to the gist of the matter.]
;
; Tau is capable of tracking finite intervals.  For example, suppose x is known
; to be an integer that lies between two known integer constants, e.g., 0 <= x <= 15.
; This information is treated by tau as a ``type'' in the sense that it can
; be propagated by signatures and other rules available to the system.
;
; Suppose the lower and upper bounds of the interval on x are given by the
; integers lox (``low x'') and hix (``high x''), and the bounds on y are
; loy and hiy.  Obviously then, the bounds on (+ x y) are lox+loy and hix+hiy.
; Note that the bounds on (+ x y) are constants, computed by summing the constant
; bounds on the inputs x and y.
;
; In the same fashion, we wish to bound (logand x y).
;
; A little bit of analysis can provide some rough bounds.  For example, if both
; input intervals are non-negative (i.e., 0 <= lox and 0 <= loy), then
; (logand x y) can be no smaller than 0 and no larger than the minimum of hix and
; hiy.  If both input intervals are strictly negative, (logand x y) is negative
; and can be no smaller than
;
; (- (expt 2 (max (shifts-to-all-ones lox)
;                 (shifts-to-all-ones loy))))
;
; and no greater than the minimum of hix and hiy.  Here, shifts-to-all-ones is
; the function that determines how many times its argument must be right
; shifted to produce -1 (and is thus ceiling of the log base 2 of the negative
; of its argument; e.g., (shifts-to-all-ones -9) = 4).
;
; Using this analysis, if -7 <= x <= -1 and -6 <= y <= -2, then
; -8 <= (logand x y) <= -2.
;
; One can similarly work out analytical bounds for when one of the inputs is
; strictly negative and the other is non-negative, and for when both can range
; over both the negatives and non-negatives.
;
; I have worked out such analytical bounds and proved that they are sufficient
; to actually contain all values of the relevant logand expressions.  However,
; my analytical bounds of logand can be quite inaccurate.  [Footnote: I say
; ``my analytical bounds'' because one could probably work out more accurate
; ones and, indeed, I illustrate the approach below but don't pursue it.]
;
; To give an example of the inaccuracy of my bounds, consider a simple case
; where both x and y range over non-negative values.  Analytically we say that
; (logand x y) in this cases ranges from 0 to the minimal of the upper bounds of
; x and y.  This is obvious since logand will only turn some bits off.
;
; But now consider this example:
;
; lox = (+ (expt 2 31) 8)
; hix = (+ (expt 2 31) 8 7)
; loy = (+ (expt 2 30) 8)
; hiy = (+ (expt 2 30) 8 7)  = 1073741839
;
; The analytical answer says 0 <= (logand x y) <= 1073741839.  But actually, we
; can see that 8 <= (logand x y) <= 15.  Thus both our lower analytical bound and
; our upper analytical bound can be wildly inaccurate.
;
; Part of the project of computing bounds for logand was to address the
; inaccuracy of this analysis.  Notice that despite the magnitude of the bounds
; above, there are only 8 possible values of x and 8 possible values of y.
; Hence, there are only 64 combinations and it is straightforward to evaluate
; logand on those 64 combinations to compute the actual bounds.  I call this the
; ``empirical'' method instead of the (my) ``analytical'' method.
;
; Of course, the empirical method cannot be applied to problems beyond a certain
; small size (as measured by the product of the widths of the two input
; intervals).  This size, called the ``empirical threshhold,'' is set currently
; at 1024^2 or 1,048,576.  This allows us to bound 10-bit by 10-bit logands
; perfectly.  The time it takes to compute both the upper and lower bounds for an
; interval of this size is 0.066123 seconds on a Macbook Pro running CCL on an
; 2.6 GHz Intel Core i7.  Of course, we might wish to lower the threshhold to
; avoid the empirical computation if we decide that it is just too expensive in
; actual proofs.  My gut feeling is that since this only happens when we
; encounter LOGANDs, we can probably afford the 10-bit by 10-bit test.
;
; The approach we adopted in tau-bounder-logand is to first determine the size
; of the problem.  If it is small enough, we use the empirical method.
; Otherwise, we use the analytic method.  We call this combined scheme the
; ``heuristic method.''
;
; In tau-bounder-logand-correct, above, I prove that the heuristic bounds are
; logically sufficient:  they are always wide enough to include the right answer.
;
; Two ill-formed questions swirl in my mind.  It would be nice if someone with a
; more analytical mindset (or a sense of having more time!) made the two
; questions more precise so they could actually be answered.  One question is:
; if we didn't use the empirical method to make some of our bounds perfect,
; how bad would it be?  Of course, the example above shows that the error can be
; about as bad as you can imagine.  Indeed, if the two inputs have exactly one
; bit in common, that bit determines both the upper and lower bounds of the interval
; (they're equal) and all the other bits in the two inputs contribute only to the
; size of the error!  But really, how often do these bad cases happen over random
; input intervals?  This clearly has a precise, abstract answer but I haven't
; pursued it.
;
; The second question is: how much more accurate do it get if we use the
; empirical method on the small problems?  This could help us decide whether the
; empirical method is worth its cost.
;
; Of course, the more meaningful cost/benefit question is: how many more
; theorems (that we're likely to run into) would we prove due to the use of the
; empirical method on small problems?  In the absence of an answer to that more
; meaningful question, an accuracy analysis of tau-bounder-logand is sort of
; irrelevant or, at least to me, of secondary importance.  That's why I'm
; satisfied with a proof of correctness and a half-baked experimental
; determination that the empirical methods sort of seems to probably improve
; accuracy by a meaningful amount.
;
; With these apologies, let me now present my experimental setup and results.
;
; Let k be some natural number.  In the tests below, I use k=5, 10, 15, ..., 50.
; I call k the ``radius'' of a test.  In a test of radius k, I consider all
; combinations of two intervals whose upper and lower bounds are between -k and
; k.  I call this the test set.  More precisely, the test set for radius k is the
;
;  {(make-tau-interval 'integerp nil lo nil hi) : (-k <= lo <= k) & (lo <= hi <= k)}
;
; Note: hi must be at least lo for the interval to be legal.
;
; The test for radius k then chooses every possible combination of intervals from
; the test set and assesses the accuracy of the logand bounder, with and without
; the empirical method.
;
; But how do I ``assess accuracy?''  The only way I know is to use the empirical
; method to determine the true bounds of each combination.
;
; Since the number of combinations in a test set increases exponentially with k,
; this experiment gets computationally expensive.  I therefore limit my tests to
; radii below 50. However, if every interval in every test set is small, then
; they'd all fall below the threshhold for using the empirical method and every
; single result of tau-bounder-logand would be perfect.
;
; To deal with this, I set the thresshold artificially low: 100.  That is,
; tau-bounder-logand uses the empirical method only when product of the size of
; the two intervals is less than 10 * 10.  (To run tau-bounder-logand without it
; using the empirical method at all, I set the threshhold to 0.)
;
; My hypothesis is that even with a relatively low threshhold (so that the number
; of combinations handled correctly ``by definition'' becomes increasiningly
; small compared to the number of combinations), the empirical method improves
; accuracy significantly.  Here are my results.  See the Appendix A for the code
; and resulting raw data from which this table is extracted.
;
;  k   A      H  (E coverage)
;
;  5   65    100 (99)
; 10   60     87 (80)
; 15   61     87 (58)
; 20   57     77 (43)
; 25   58     75 (32)
; 30   60     73 (25)
; 35   57     68 (20)
; 40   56     65 (17)
; 45   56     65 (14)
; 50   57     65 (12)
;
; In column A I show the percentage of the combinations bounded perfectly by the
; analytical method (i.e., with the threshhold set to 0 so that the empirical
; method is not employed).  Note that it seems to hold steady at about 57% as k
; increases.
;
; In column H I show the percentage of the combinations bounded perfectly by the
; heuristic method (which augments the analytical method with the empirical
; method for combinations under the size threshhold of 100).
;
; In parenthesis I show the percentage of the cases covered by the empirical
; method.  For example, when k=50, the heuristic method is perfect 65 percent of
; the time but only 12% of the cases were handled by the empirical method.
;
; What this shows is that the empirical method increases the accuracy even as it
; addresses a smaller percentage of the cases.  Since the empirical method is
; limited to small cases, I suspect this means that the small cases are handled
; inaccurately by the analytical method a disproportionate number of times.
;
; -----------------------------------------------------------------
; Appendix A.
;
; In this section I show the raw Lisp code and raw data behind the table above.
;
; ; These bounds aren't always very tight.  Let k be some natural number.
; ; Consider every combination of:
;
; ; -k <= lox <= hix <= k and -k <= loy <= hiy <= k
;
; ; and then compute the predicted bounds of logand.  Then, for every x and y in
; ; the given two intervals, compute the actual lo and the actual hi of (logand x
; ; y).  Let dlo be the distances between the actual lo and the predicted lo, and
; ; let dhi be the comparable hi distance.  Sum dlo and dhi to get a measure how
; ; accurate the interval is.  Sum all the measures across all combinations of
; ; input intervals.
;
; (include-book "elementary-bounders")
;
; (value :q)
;
; ; This test, which should return T, confirms that we can rebind the threshhold
; ; to control whether the empirical method is used by tau-bounder-logand:
;
; (not (equal (worth-computingp 0 100 0 100)
;             (let ((*logand-empirical-threshhold* 100))
;               (worth-computingp 0 100 0 100))))
;
; (defun score-logand-prediction (k)
; ; Given a max radius of k, compute the
;   (let ((combinations 0)
;         (perfect 0)
;         (perfect-by-def 0)
;         (worst-miss-on-lo nil)
;         (worst-miss-on-hi nil)
;         (score nil))
; ; When non-nil, the two ``worst-miss'' values are:
; ; (miss-magnitude (lox hix loy hiy) (predicted-lo predicted-hi) (alo ahi))
;     (setq score
;           (loop for lox from (- k) to k
;                 sum
;                 (loop for hix from lox to k
;                       sum
;                       (let ((int1 (make-tau-interval 'integerp nil lox nil hix)))
;                         (loop for loy from (- k) to k
;                               sum
;                               (loop for hiy from loy to k
;                                     sum
;                                     (let* ((int2 (make-tau-interval 'integerp nil loy nil hiy))
;                                            (int (tau-bounder-logand int1 int2))
;                                            (lo (tau-interval-lo int))
;                                            (hi (tau-interval-hi int))
;
; ; Warning: Even though we construct the input intervals int1 and int2, we still
; ; exploit the fact that the variables lox, hix, loy, and hiy are bound to the
; ; respective bounds of those intervals.
;
;                                            (alo (find-minimal-logand lox hix loy hiy))
;                                            (ahi (find-maximal-logand lox hix loy hiy)))
;                                       (setq combinations (+ 1 combinations))
;                                       (if (worth-computingp lox hix loy hiy)
;                                           (setq perfect-by-def (+ 1 perfect-by-def)))
;                                       (if (and (equal lo alo)
;                                                (equal hi ahi))
;                                           (setq perfect (+ 1 perfect)))
;                                       (if (or (null worst-miss-on-lo)
;                                               (< (car worst-miss-on-lo)
;                                                  (abs (- lo alo))))
;                                           (setq worst-miss-on-lo
;                                                 `(,(abs (- lo alo))
;                                                   (,lox ,hix ,loy ,hiy)
;                                                   (,lo ,hi)
;                                                   (,alo ,ahi))))
;                                       (if (or (null worst-miss-on-hi)
;                                               (< (car worst-miss-on-hi)
;                                                  (abs (- hi ahi))))
;                                           (setq worst-miss-on-hi
;                                                 `(,(abs (- hi ahi))
;                                                   (,lox ,hix ,loy ,hiy)
;                                                   (,lo ,hi)
;                                                   (,alo ,ahi))))
;                                       (+ (abs (- lo alo))
;                                          (abs (- hi ahi))))))))))
;     `((combinations ,combinations)
;       (perfect ,perfect)
;       (perfect-percentage ,(floor (* 100 (/ perfect combinations)) 1) %)
;       (perfect-by-def ,perfect-by-def)
;       (perfect-by-def-percentage ,(floor (* 100 (/ perfect-by-def combinations)) 1) %)
;       (perfect-otherwise ,(- perfect perfect-by-def))
;       (perfect-otherwise-percentage ,(floor (* 100 (/ (- perfect perfect-by-def) combinations)) 1) %)
;       (score ,score)
;       (average-error ,(float (/ score combinations)))
;       (worst-miss-on-lo ,worst-miss-on-lo)
;       (worst-miss-on-hi ,worst-miss-on-hi))))
;
; ; The test:
;
; (let ((*logand-empirical-threshhold* *logand-empirical-threshhold*))
;   (progn
;     (print (setq *logand-empirical-threshhold* 100))
;     (print (list '(score-logand-prediction  5) (score-logand-prediction  5)))
;     (print (list '(score-logand-prediction 10) (score-logand-prediction 10)))
;     (print (list '(score-logand-prediction 15) (score-logand-prediction 15)))
;     (print (list '(score-logand-prediction 20) (score-logand-prediction 20)))
;     (print (list '(score-logand-prediction 25) (score-logand-prediction 25)))
;     (print (list '(score-logand-prediction 30) (score-logand-prediction 30)))
;     (print (list '(score-logand-prediction 35) (score-logand-prediction 35)))
;     (print (list '(score-logand-prediction 40) (score-logand-prediction 40)))
;     (print (list '(score-logand-prediction 45) (score-logand-prediction 45)))
;     (print (list '(score-logand-prediction 50) (score-logand-prediction 50)))
;     (print (setq *logand-empirical-threshhold* 0))
;     (print (list '(score-logand-prediction  5) (score-logand-prediction  5)))
;     (print (list '(score-logand-prediction 10) (score-logand-prediction 10)))
;     (print (list '(score-logand-prediction 15) (score-logand-prediction 15)))
;     (print (list '(score-logand-prediction 20) (score-logand-prediction 20)))
;     (print (list '(score-logand-prediction 25) (score-logand-prediction 25)))
;     (print (list '(score-logand-prediction 30) (score-logand-prediction 30)))
;     (print (list '(score-logand-prediction 35) (score-logand-prediction 35)))
;     (print (list '(score-logand-prediction 40) (score-logand-prediction 40)))
;     (print (list '(score-logand-prediction 45) (score-logand-prediction 45)))
;     (print (list '(score-logand-prediction 50) (score-logand-prediction 50)))
;     nil
;     ))
;
; ; Output:
;
; 100
; ((SCORE-LOGAND-PREDICTION 5)
;  ((COMBINATIONS 4356) (PERFECT 4356) (PERFECT-PERCENTAGE 100 %)
;   (PERFECT-BY-DEF 4347) (PERFECT-BY-DEF-PERCENTAGE 99 %) (PERFECT-OTHERWISE 9)
;   (PERFECT-OTHERWISE-PERCENTAGE 0 %) (SCORE 0) (AVERAGE-ERROR 0.0)
;   (WORST-MISS-ON-LO (0 (-5 -5 -5 -5) (-5 -5) (-5 -5)))
;   (WORST-MISS-ON-HI (0 (-5 -5 -5 -5) (-5 -5) (-5 -5)))))
; ((SCORE-LOGAND-PREDICTION 10)
;  ((COMBINATIONS 53361) (PERFECT 49621) (PERFECT-PERCENTAGE 92 %)
;   (PERFECT-BY-DEF 43165) (PERFECT-BY-DEF-PERCENTAGE 80 %) (PERFECT-OTHERWISE 6456)
;   (PERFECT-OTHERWISE-PERCENTAGE 12 %) (SCORE 11498) (AVERAGE-ERROR 0.21547572)
;   (WORST-MISS-ON-LO (7 (-9 -1 -1 10) (-16 10) (-9 10)))
;   (WORST-MISS-ON-HI (6 (-10 10 0 4) (0 10) (0 4)))))
; ((SCORE-LOGAND-PREDICTION 15)
;  ((COMBINATIONS 246016) (PERFECT 214784) (PERFECT-PERCENTAGE 87 %)
;   (PERFECT-BY-DEF 143557) (PERFECT-BY-DEF-PERCENTAGE 58 %)
;   (PERFECT-OTHERWISE 71227) (PERFECT-OTHERWISE-PERCENTAGE 28 %) (SCORE 105010)
;   (AVERAGE-ERROR 0.42684215) (WORST-MISS-ON-LO (7 (-9 -4 -1 15) (-16 15) (-9 12)))
;   (WORST-MISS-ON-HI (12 (-15 15 0 3) (0 15) (0 3)))))
; ((SCORE-LOGAND-PREDICTION 20)
;  ((COMBINATIONS 741321) (PERFECT 574847) (PERFECT-PERCENTAGE 77 %)
;   (PERFECT-BY-DEF 319249) (PERFECT-BY-DEF-PERCENTAGE 43 %)
;   (PERFECT-OTHERWISE 255598) (PERFECT-OTHERWISE-PERCENTAGE 34 %) (SCORE 967170)
;   (AVERAGE-ERROR 1.3046575)
;   (WORST-MISS-ON-LO (15 (-17 -13 -1 18) (-32 18) (-17 18)))
;   (WORST-MISS-ON-HI (18 (-20 20 0 2) (0 20) (0 2)))))
; ((SCORE-LOGAND-PREDICTION 25)
;  ((COMBINATIONS 1758276) (PERFECT 1321323) (PERFECT-PERCENTAGE 75 %)
;   (PERFECT-BY-DEF 579499) (PERFECT-BY-DEF-PERCENTAGE 32 %)
;   (PERFECT-OTHERWISE 741824) (PERFECT-OTHERWISE-PERCENTAGE 42 %) (SCORE 2743968)
;   (AVERAGE-ERROR 1.5606014) (WORST-MISS-ON-LO (16 (-16 -7 16 25) (0 25) (16 25)))
;   (WORST-MISS-ON-HI (24 (-25 25 0 1) (0 25) (0 1)))))
; ((SCORE-LOGAND-PREDICTION 30)
;  ((COMBINATIONS 3575881) (PERFECT 2634466) (PERFECT-PERCENTAGE 73 %)
;   (PERFECT-BY-DEF 927789) (PERFECT-BY-DEF-PERCENTAGE 25 %)
;   (PERFECT-OTHERWISE 1706677) (PERFECT-OTHERWISE-PERCENTAGE 47 %) (SCORE 6587188)
;   (AVERAGE-ERROR 1.8421161) (WORST-MISS-ON-LO (16 (-16 -10 16 30) (0 30) (16 22)))
;   (WORST-MISS-ON-HI (29 (-30 30 0 1) (0 30) (0 1)))))
; ((SCORE-LOGAND-PREDICTION 35)
;  ((COMBINATIONS 6533136) (PERFECT 4502512) (PERFECT-PERCENTAGE 68 %)
;   (PERFECT-BY-DEF 1367879) (PERFECT-BY-DEF-PERCENTAGE 20 %)
;   (PERFECT-OTHERWISE 3134633) (PERFECT-OTHERWISE-PERCENTAGE 47 %) (SCORE 19708780)
;   (AVERAGE-ERROR 3.016741) (WORST-MISS-ON-LO (32 (-32 -8 32 35) (0 35) (32 35)))
;   (WORST-MISS-ON-HI (34 (-35 35 0 1) (0 35) (0 1)))))
; ((SCORE-LOGAND-PREDICTION 40)
;  ((COMBINATIONS 11029041) (PERFECT 7251983) (PERFECT-PERCENTAGE 65 %)
;   (PERFECT-BY-DEF 1905769) (PERFECT-BY-DEF-PERCENTAGE 17 %)
;   (PERFECT-OTHERWISE 5346214) (PERFECT-OTHERWISE-PERCENTAGE 48 %) (SCORE 42591220)
;   (AVERAGE-ERROR 3.8617337) (WORST-MISS-ON-LO (32 (-32 -21 32 40) (0 40) (32 40)))
;   (WORST-MISS-ON-HI (39 (-40 40 0 1) (0 40) (0 1)))))
; ((SCORE-LOGAND-PREDICTION 45)
;  ((COMBINATIONS 17522596) (PERFECT 11407801) (PERFECT-PERCENTAGE 65 %)
;   (PERFECT-BY-DEF 2547459) (PERFECT-BY-DEF-PERCENTAGE 14 %)
;   (PERFECT-OTHERWISE 8860342) (PERFECT-OTHERWISE-PERCENTAGE 50 %) (SCORE 72472530)
;   (AVERAGE-ERROR 4.135947) (WORST-MISS-ON-LO (32 (-32 -25 32 44) (0 44) (32 39)))
;   (WORST-MISS-ON-HI (44 (-45 45 0 1) (0 45) (0 1)))))
; ((SCORE-LOGAND-PREDICTION 50)
;  ((COMBINATIONS 26532801) (PERFECT 17294676) (PERFECT-PERCENTAGE 65 %)
;   (PERFECT-BY-DEF 3298343) (PERFECT-BY-DEF-PERCENTAGE 12 %)
;   (PERFECT-OTHERWISE 13996333) (PERFECT-OTHERWISE-PERCENTAGE 52 %)
;   (SCORE 114203530) (AVERAGE-ERROR 4.3042397)
;   (WORST-MISS-ON-LO (32 (-32 -27 32 48) (0 48) (32 37)))
;   (WORST-MISS-ON-HI (50 (-50 50 0 0) (0 50) (0 0)))))
; 0
; ((SCORE-LOGAND-PREDICTION 5)
;  ((COMBINATIONS 4356) (PERFECT 2873) (PERFECT-PERCENTAGE 65 %) (PERFECT-BY-DEF 0)
;   (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 2873)
;   (PERFECT-OTHERWISE-PERCENTAGE 65 %) (SCORE 2845) (AVERAGE-ERROR 0.6531221)
;   (WORST-MISS-ON-LO (5 (-3 -3 5 5) (0 5) (5 5)))
;   (WORST-MISS-ON-HI (5 (-5 5 0 0) (0 5) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 10)
;  ((COMBINATIONS 53361) (PERFECT 32499) (PERFECT-PERCENTAGE 60 %) (PERFECT-BY-DEF 0)
;   (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 32499)
;   (PERFECT-OTHERWISE-PERCENTAGE 60 %) (SCORE 68793) (AVERAGE-ERROR 1.2892)
;   (WORST-MISS-ON-LO (10 (-6 -6 10 10) (0 10) (10 10)))
;   (WORST-MISS-ON-HI (10 (-10 10 0 0) (0 10) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 15)
;  ((COMBINATIONS 246016) (PERFECT 150727) (PERFECT-PERCENTAGE 61 %)
;   (PERFECT-BY-DEF 0) (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 150727)
;   (PERFECT-OTHERWISE-PERCENTAGE 61 %) (SCORE 405365) (AVERAGE-ERROR 1.6477181)
;   (WORST-MISS-ON-LO (15 (-1 -1 15 15) (0 15) (15 15)))
;   (WORST-MISS-ON-HI (15 (-15 15 0 0) (0 15) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 20)
;  ((COMBINATIONS 741321) (PERFECT 429599) (PERFECT-PERCENTAGE 57 %)
;   (PERFECT-BY-DEF 0) (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 429599)
;   (PERFECT-OTHERWISE-PERCENTAGE 57 %) (SCORE 1889899) (AVERAGE-ERROR 2.5493667)
;   (WORST-MISS-ON-LO (20 (-12 -12 20 20) (0 20) (20 20)))
;   (WORST-MISS-ON-HI (20 (-20 20 0 0) (0 20) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 25)
;  ((COMBINATIONS 1758276) (PERFECT 1034743) (PERFECT-PERCENTAGE 58 %)
;   (PERFECT-BY-DEF 0) (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 1034743)
;   (PERFECT-OTHERWISE-PERCENTAGE 58 %) (SCORE 4887045) (AVERAGE-ERROR 2.7794528)
;   (WORST-MISS-ON-LO (25 (-7 -7 25 25) (0 25) (25 25)))
;   (WORST-MISS-ON-HI (25 (-25 25 0 0) (0 25) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 30)
;  ((COMBINATIONS 3575881) (PERFECT 2146211) (PERFECT-PERCENTAGE 60 %)
;   (PERFECT-BY-DEF 0) (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 2146211)
;   (PERFECT-OTHERWISE-PERCENTAGE 60 %) (SCORE 11087983) (AVERAGE-ERROR 3.1007695)
;   (WORST-MISS-ON-LO (30 (-2 -2 30 30) (0 30) (30 30)))
;   (WORST-MISS-ON-HI (30 (-30 30 0 0) (0 30) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 35)
;  ((COMBINATIONS 6533136) (PERFECT 3786285) (PERFECT-PERCENTAGE 57 %)
;   (PERFECT-BY-DEF 0) (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 3786285)
;   (PERFECT-OTHERWISE-PERCENTAGE 57 %) (SCORE 27677205) (AVERAGE-ERROR 4.236435)
;   (WORST-MISS-ON-LO (35 (-29 -29 35 35) (0 35) (35 35)))
;   (WORST-MISS-ON-HI (35 (-35 35 0 0) (0 35) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 40)
;  ((COMBINATIONS 11029041) (PERFECT 6215779) (PERFECT-PERCENTAGE 56 %)
;   (PERFECT-BY-DEF 0) (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 6215779)
;   (PERFECT-OTHERWISE-PERCENTAGE 56 %) (SCORE 55769581) (AVERAGE-ERROR 5.056612)
;   (WORST-MISS-ON-LO (40 (-24 -24 40 40) (0 40) (40 40)))
;   (WORST-MISS-ON-HI (40 (-40 40 0 0) (0 40) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 45)
;  ((COMBINATIONS 17522596) (PERFECT 9959663) (PERFECT-PERCENTAGE 56 %)
;   (PERFECT-BY-DEF 0) (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 9959663)
;   (PERFECT-OTHERWISE-PERCENTAGE 56 %) (SCORE 92758101) (AVERAGE-ERROR 5.2936277)
;   (WORST-MISS-ON-LO (45 (-19 -19 45 45) (0 45) (45 45)))
;   (WORST-MISS-ON-HI (45 (-45 45 0 0) (0 45) (0 0)))))
; ((SCORE-LOGAND-PREDICTION 50)
;  ((COMBINATIONS 26532801) (PERFECT 15351489) (PERFECT-PERCENTAGE 57 %)
;   (PERFECT-BY-DEF 0) (PERFECT-BY-DEF-PERCENTAGE 0 %) (PERFECT-OTHERWISE 15351489)
;   (PERFECT-OTHERWISE-PERCENTAGE 57 %) (SCORE 144236691) (AVERAGE-ERROR 5.4361653)
;   (WORST-MISS-ON-LO (50 (-14 -14 50 50) (0 50) (50 50)))
;   (WORST-MISS-ON-HI (50 (-50 50 0 0) (0 50) (0 0)))))
;
;
; -----------------------------------------------------------------
; Appendix B.
;
; I now discuss briefly the prospects of refining my analysis so that it is
; inherently more accurate.  I am not optimistic but record my thoughts for
; posterity in case somebody wants to pursue it.
;
; Here is an example of a bad case.  The x interval contains only one element.
; The y interval contains 64 elements, so it is easy to compute the empirical
; answer.  The analytical range is 0 to 3392, but the actual range is 3072 to
; 3104.  Furthermore, there are only two points in the actual range: 3072 and
; 3104.  Here is some Common Lisp code to confirm these statements:
;
; (let* ((lox #b10110000100000)
;        (loy #b00110100000000)
;        (hiy #b00110101000000)
;        (hix lox))
;   (mv-let (rel1 lo rel2 hi)
;           (ibounds-of-logand nil lox nil hix nil loy nil hiy)
;           `((lox ,lox)
; 	    (hix ,hix)
; 	    (loy ,loy)
; 	    (hiy ,hiy)
; 	    (,lo --- ,hi)
; 	    (,(find-minimal-logand lox hix loy hiy) ---
; 	      ,(find-maximal-logand lox hix loy hiy))
; 	    (all ,(let ((ans nil))
; 		    (loop for x from lox to hix
; 			  do (loop for y from loy to hiy
; 				   do (or (member-equal (logand x y) ans)
; 					  (setq ans (cons (logand x y) ans)))))
; 		    ans)))))
; This produces:
;
; ((LOX 11296)
;  (HIX 11296)
;  (LOY 3328)
;  (HIY 3392)
;  (0 --- 3392)       ; analytical interval
;  (3072 --- 3104)    ; actual interval
;  (ALL (3104 3072))) ; all possible actual values of (logand x y)
;
; Let's blow up this example to see why the prediction is so hard.  I discuss
; the example in the text below and, in the ``footnotes'', discuss the
; generalization of the example to whole classes of problems.
;
; bits            a  b  c  d  e  f  g  h  i  j  k  l  m  n
; pwr            13 12 11 10  9  8  7  6  5  4  3  2  1  0
;
; lox = hix = #b  1  0  1  1  0  0  0  0  1  0  0  0  0  0
; loy       = #b  0  0  1  1  0  1  0  0  0  0  0  0  0  0
; hiy       = #b  0  0  1  1  0  1  0  1  0  0  0  0  0  0
;
; Note that as y ranges from loy to hiy, we will generate all possible 6-bit
; patterns in bits i through n, stopping when we finally set bit h.  [Footnote:
; In general we won't generate all h-bit patterns, since we start with the
; pattern given by the low h bits of loy and end with the pattern given by the
; low h+1 bits of hiy, but since in this example, loy and hiy both have all 0s
; below bit h, we will generate all patterns.]  Thus, all the y's in the range
; share the same bits above bit h.  Thus, every logand of x and y will be
; non-zero, because x and every y will always share whatever bits all three
; share above bit h.  In this case that is bits c and d, which is 2^11 + 2^10 =
; 3072.  [Footnote: Clearly we could have an arbitrary number of shared bits
; contributing to this lower bound.]  Furthermore, since there is only one x
; and it has only one bit set below bit h, as y varies it the low order h bits
; of (logand x y) will will either be all 0 or all 0 except for 1 in bit i.
; This will mean that the low order h bits of the logand either contribute 0 or
; 2^5 to the value.  This is how the empirical hi is achieved: lo + 2^5 = 3104.
; This accounts for all (both) of the values of the logand.  [Footnote: By
; choosing an x with multiple bits set below bit h we can arrange for multiple
; values to be generated by the logand.  Precisely which values can only be
; determined, I think, by generating each of the h-bit numbers between the low
; h bits of loy and the low h bits of hiy and loganding those patterns with the
; low h bits of x.]
;
; One could over estimate the maximal amount by which lo will be incremented by
; supposing that there exists a combination in y that will select all of the
; lower h bits of x.
;
; But I've decided that trying to get more accurate analytical bounds is not
; worth the effort.  Instead, I'll just go with the empirical approach.  We'll
; see if this is helpful enough.
