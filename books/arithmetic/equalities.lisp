; ACL2 books on arithmetic
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:
; Matt Kaufmann, Bishop Brock, and John Cowles, with help from Art Flatau
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

#-:non-standard-analysis
(defmacro real-listp (l)
  `(rational-listp ,l))

(include-book "xdoc/top" :dir :system)
(local (include-book "cowles/acl2-crg" :dir :system))

(defsection fc
  :parents (arithmetic-1)
  :short "Identity macro &mdash; does nothing, you can safely ignore this."

  :long "<p>@(call fc) just expands to @('x').  This macro is a historic
artifact that was originally used in the @('arithmetic') library as a way to
experiment with using @(see force).</p>

@(def fc)"

  #|
  (defmacro fc (x)
    (list 'force x))
  |#

  (defmacro fc (x)
    x))


(defsection basic-sum-normalization
  :parents (arithmetic-1)
  :short "Trivial normalization and cancellation rules for sums."

  (defthm commutativity-2-of-+
    (equal (+ x (+ y z))
           (+ y (+ x z))))

  (defthm functional-self-inversion-of-minus
    (equal (- (- x))
           (fix x)))

  (defthm distributivity-of-minus-over-+
    (equal (- (+ x y))
           (+ (- x) (- y))))

  (defthm minus-cancellation-on-right
    (equal (+ x y (- x))
           (fix y)))

  (defthm minus-cancellation-on-left
    (equal (+ x (- x) y)
           (fix y)))

; Note that the cancellation rules below (and similarly for *) aren't
; complete, in the sense that the element to cancel could be on the
; left side of one expression and the right side of the other.  But
; perhaps those situations rarely arise in practice.  (?)

  (defthm right-cancellation-for-+
    (equal (equal (+ x z)
                  (+ y z))
           (equal (fix x) (fix y))))

  (defthm left-cancellation-for-+
    (equal (equal (+ x y)
                  (+ x z))
         (equal (fix y) (fix z))))

  (defthm equal-minus-0
    (equal (equal 0 (- x))
           (equal 0 (fix x))))

  (defthm inverse-of-+-as=0
    (equal (equal (- a b) 0)
           (equal (fix a) (fix b))))

  (defthm equal-minus-minus
    (equal (equal (- a) (- b))
           (equal (fix a) (fix b))))

  (defthm fold-consts-in-+
    (implies (and (syntaxp (quotep x))
                  (syntaxp (quotep y)))
             (equal (+ x (+ y z))
                    (+ (+ x y) z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Facts about * (and /)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The same as Inverse-of-*, from axioms.lisp, but with force.
#|
(defaxiom right-inverse-of-*
  (implies (and (acl2-numberp x)
                (not (equal x 0)))
           (equal (* x (/ x)) 1)))
|#

#| The following proof of commutativity-2-of-* was originally obtained by using
   John Cowles's macro acl2-asg::add-commutativity-2 as follows, and
   then editing out package references in the statement of the final
   theorem.
(acl2-asg::add-commutativity-2 equal
			       acl2-numberp
			       *
			       commutativity-of-*
			       commutativity-2-of-*)
|#

(defsection basic-product-normalization
  :parents (arithmetic-1)
  :short "Trivial normalization and cancellation rules for products."

  (defthm commutativity-2-of-*
    (equal (* x (* y z))
           (* y (* x z)))
    :hints (("Goal" :use (:functional-instance acl2-asg::commutativity-2-of-op
                                               (acl2-asg::equiv equal)
                                               (acl2-asg::pred (lambda (x) t))
                                               (acl2-asg::op binary-*)))))

  (defthm functional-self-inversion-of-/
    (equal (/ (/ x)) (fix x))
    :hints (("Goal" :use (:functional-instance
                          acl2-agp::Involution-of-inv
                          (acl2-agp::equiv equal)
                          (acl2-agp::pred (lambda (x)
                                            (and (acl2-numberp x)
                                                 (not (equal x 0)))))
                          (acl2-agp::op binary-*)
                          (acl2-agp::id (lambda () 1))
                          (acl2-agp::inv unary-/)))))

  (defthm distributivity-of-/-over-*
    (equal (/ (* x y))
           (* (/ x) (/ y)))
    :hints (("Goal" :use (:functional-instance
                          acl2-agp::Distributivity-of-inv-over-op
                          (acl2-agp::equiv equal)
                          (acl2-agp::pred (lambda (x)
                                            (and (acl2-numberp x)
                                                 (not (equal x 0)))))
                          (acl2-agp::op binary-*)
                          (acl2-agp::id (lambda () 1))
                          (acl2-agp::inv unary-/)))))

  (defthm /-cancellation-on-right
    (implies (and (fc (acl2-numberp x))
                  (fc (not (equal x 0))))
             (equal (* x y (/ x))
                    (fix y)))
    :hints (("Goal" :use (:functional-instance
                          acl2-agp::inv-cancellation-on-right
                          (acl2-agp::equiv equal)
                          (acl2-agp::pred (lambda (x)
                                            (and (acl2-numberp x)
                                                 (not (equal x 0)))))
                          (acl2-agp::op binary-*)
                          (acl2-agp::id (lambda () 1))
                          (acl2-agp::inv unary-/)))))

  (defthm /-cancellation-on-left
    (implies (and (fc (acl2-numberp x))
                  (fc (not (equal 0 x))))
             (equal (* x (/ x) y)
                    (fix y)))
    :hints (("Goal" :use /-cancellation-on-right)))

  (local
   (defthm right-cancellation-for-*-lemma
     (implies (and (equal (* x z) (* y z))
                   (acl2-numberp z)
                   (not (equal 0 z))
                   (acl2-numberp x)
                   (acl2-numberp y))
              (equal (equal x y) t))
     :hints (("Goal" :use (:functional-instance
                           acl2-agp::Right-cancellation-for-op
                           (acl2-agp::equiv equal)
                           (acl2-agp::pred (lambda (x)
                                             (and (acl2-numberp x)
                                                  (not (equal x 0)))))
                           (acl2-agp::op binary-*)
                           (acl2-agp::id (lambda () 1))
                           (acl2-agp::inv unary-/))))))

  (defthm right-cancellation-for-*
    (equal (equal (* x z) (* y z))
           (or (equal 0 (fix z))
               (equal (fix x) (fix y)))))

  (defthm left-cancellation-for-*
    (equal (equal (* z x) (* z y))
           (or (equal 0 (fix z))
               (equal (fix x) (fix y)))))

  (defthm Zero-is-only-zero-divisor
    (equal (equal (* x y) 0)
           (or (equal (fix x) 0)
               (equal (fix y) 0))))

  (defthm equal-*-x-y-x
    (equal (equal (* x y) x)
           (or (equal x 0)
               (and (equal y 1)
                    (acl2-numberp x))))
    :hints (("Goal" :use ((:instance right-cancellation-for-*
                                     (z x)
                                     (x y)
                                     (y 1))))))

  (defthm equal-*-x-y-y
    (equal (equal (* x y) y)
           (or (equal y 0)
               (and (equal x 1)
                    (acl2-numberp y))))
    :hints (("Goal" :use ((:instance right-cancellation-for-*
                                     (z y)
                                     (x x)
                                     (y 1))))))

  (local (defthm equal-/-lemma
           (implies (and (acl2-numberp x)
                         (acl2-numberp y)
                         (equal (* x y) 1))
                    (equal y (/ x)))
           :rule-classes nil
           :hints (("Goal" :use (:functional-instance
                                 acl2-agp::Uniqueness-of-op-inverses
                                 (acl2-agp::equiv equal)
                                 (acl2-agp::pred (lambda (x)
                                                   (and (acl2-numberp x)
                                                        (not (equal x 0)))))
                                 (acl2-agp::op binary-*)
                                 (acl2-agp::id (lambda () 1))
                                 (acl2-agp::inv unary-/))))))

  (defthm equal-/
    (implies (and (fc (acl2-numberp x))
                  (fc (not (equal 0 x))))
             (equal (equal (/ x) y)
                    (equal 1 (* x y))))
    :hints (("Goal" :use equal-/-lemma)))

; The following hack helps in the application of equal-/ when forcing is
; turned off.

  (defthm numerator-nonzero-forward
    (implies (not (equal (numerator r) 0))
             (and (not (equal r 0))
                  (acl2-numberp r)))
    :rule-classes
    ((:forward-chaining :trigger-terms
                        ((numerator r)))))

; The following loops with the lemma equal-/ just proved but is
; sometimes useful.

  (encapsulate
    ()
    (local (defthm Uniqueness-of-*-inverses-lemma
             (equal (equal (* x y) 1)
                    (and (not (equal x 0))
                         (acl2-numberp x)
                         (equal y (/ x))))))

    (defthm Uniqueness-of-*-inverses
      (equal (equal (* x y) 1)
             (and (not (equal (fix x) 0))
                  (equal y (/ x))))
      :hints (("Goal" :in-theory (disable equal-/)))))

  (in-theory (disable Uniqueness-of-*-inverses))

  (theory-invariant
   (not (and (active-runep '(:rewrite Uniqueness-of-*-inverses))
             (active-runep '(:rewrite equal-/)))))

  (encapsulate
    ()
    (local (defthm equal-/-/-lemma
             (implies (and (fc (acl2-numberp a))
                           (fc (acl2-numberp b))
                           (fc (not (equal a 0)))
                           (fc (not (equal b 0))))
                      (equal (equal (/ a) (/ b))
                             (equal a b)))
             :hints
             (("Goal" :use ((:instance (:theorem (implies
                                                  (and (fc (acl2-numberp a))
                                                       (fc (acl2-numberp b))
                                                       (fc (not (equal a 0)))
                                                       (fc (not (equal b 0))))
                                                  (implies (equal a b)
                                                           (equal (/ a) (/ b)))))
                                       (a (/ a)) (b (/ b))))))
             :rule-classes nil))

    (defthm equal-/-/
      (equal (equal (/ a) (/ b))
             (equal (fix a) (fix b)))
      :hints (("Goal" :use equal-/-/-lemma
               :in-theory (disable equal-/)))))

  (defthm equal-*-/-1
    (implies (and (acl2-numberp x)
                  (not (equal x 0)))
             (equal (equal (* (/ x) y) z)
                    (and (acl2-numberp z)
                         (equal (fix y) (* x z))))))

  (defthm equal-*-/-2
    (implies (and (acl2-numberp x)
                  (not (equal x 0)))
             (equal (equal (* y (/ x)) z)
                    (and (acl2-numberp z)
                         (equal (fix y) (* z x))))))

  (defthm fold-consts-in-*
    (implies (and (syntaxp (quotep x))
                  (syntaxp (quotep y)))
             (equal (* x (* y z))
                    (* (* x y) z))))

  (defthm times-zero
    ;; We could prove an analogous rule about non-numeric coefficients, but
    ;; this one has efficiency advantages:  it doesn't match too often, it has
    ;; no hypothesis, and also we know that the 0 is the first argument so we
    ;; don't need two versions.  Besides, we won't need this too often; it's
    ;; a type-reasoning fact.  But it did seem useful in the proof of a meta
    ;; lemma about times cancellation, so we include it here.
    (equal (* 0 x) 0)))


(defsection basic-products-with-negations
  :parents (arithmetic-1)
  :short "Rules for normalizing products with negative factors, and reciprocals
of negations."

  (local (defthm functional-commutativity-of-minus-*-right-lemma
           (implies (and (fc (acl2-numberp x))
                         (fc (acl2-numberp y)))
                    (equal (* x (- y))
                           (- (* x y))))
           :hints (("Goal" :use (:functional-instance
                                 acl2-crg::functional-commutativity-of-minus-times-right
                                 (acl2-crg::equiv equal)
                                 (acl2-crg::pred acl2-numberp)
                                 (acl2-crg::plus binary-+)
                                 (acl2-crg::times binary-*)
                                 (acl2-crg::zero (lambda () 0))
                                 (acl2-crg::minus unary--))))
           :rule-classes nil))

  (defthm functional-commutativity-of-minus-*-right
    (equal (* x (- y))
           (- (* x y)))
    :hints (("Goal" :use functional-commutativity-of-minus-*-right-lemma)))

  (defthm functional-commutativity-of-minus-*-left
    (equal (* (- x) y)
           (- (* x y))))

  (defthm reciprocal-minus
    (equal (/ (- x))
           (- (/ x)))
    :hints (("Goal" :cases
             ((and (fc (acl2-numberp x))
                   (fc (not (equal x 0)))))))))


(defsection basic-rational-identities
  :parents (arithmetic-1 numerator denominator)
  :short "Basic cancellation rules for @('numerator') and @('denominator') terms."
  :long "<p>See also @(see more-rational-identities) for additional reductions
involving @('numerator') and @('denominator') terms.</p>"

  (local (defthm numerator-integerp-lemma-1
           (implies (rationalp x)
                    (equal (* (* (numerator x) (/ (denominator x))) (denominator x))
                           (numerator x)))
           :rule-classes nil
           :hints (("Goal" :in-theory (disable rational-implies2)))))

  (local (defthm numerator-integerp-lemma
           (implies (and (rationalp x)
                         (equal (* (numerator x) (/ (denominator x)))
                                x))
                    (equal (numerator x)
                           (* x (denominator x))))
           :rule-classes nil
           :hints (("Goal" :use (numerator-integerp-lemma-1)
                    :in-theory (disable rational-implies2)))))

  (defthm numerator-when-integerp
    (implies (integerp x)
             (equal (numerator x)
                    x))
    :hints (("Goal" :in-theory (disable rational-implies2)
             :use ((:instance lowest-terms (r x)
                              (q 1)
                              (n (denominator x)))
                   rational-implies2
                   numerator-integerp-lemma))))

  (defthm integerp==>denominator=1
    (implies (integerp x)
             (equal (denominator x) 1))
    :hints (("Goal" :use (rational-implies2 numerator-when-integerp)
             :in-theory (disable rational-implies2))))

  (defthm equal-denominator-1
    (equal (equal (denominator x) 1)
           (or (integerp x)
               (not (rationalp x))))
    :hints (("Goal" :use (rational-implies2 completion-of-denominator)
             :in-theory (disable rational-implies2))))

  (defthm *-r-denominator-r
    (equal (* r (denominator r))
           (if (rationalp r)
               (numerator r)
             (fix r)))
    :hints (("Goal" :use ((:instance rational-implies2 (x r)))
             :in-theory (disable rational-implies2))))

  (defthm /r-when-abs-numerator=1
    (and (implies (equal (numerator r) 1)
                  (equal (/ r) (denominator r)))
         (implies (equal (numerator r) -1)
                  (equal (/ r) (- (denominator r)))))
    :hints (("Goal" :use ((:instance rational-implies2 (x r)))
             :in-theory (disable rational-implies2)))))



;; Much of this is adapted from John Cowles's @('acl2-exp.lisp') book.  There
;; are various modifications, however, including some by Ruben Gamboa to
;; support non-standard analysis in the non-standard version of ACL2, ACL2(r);
;; see :doc real.

(defsection basic-expt-type-rules
  :parents (arithmetic-1 expt)
  :short "Rules about when @('expt') produces integers, positive numbers, etc."

  #+:non-standard-analysis
  (defthm expt-type-prescription-realp
    (implies (realp r)
             (realp (expt r i)))
    :rule-classes (:type-prescription :generalize))

  (defthm expt-type-prescription-rationalp
    (implies (rationalp r)
             (rationalp (expt r i)))
    :rule-classes (:type-prescription :generalize))

  ;; This theorem was strengthened to allow all real numbers (but reduces to
  ;; the version with a rationalp hypothesis in for ACL2, as opposed to
  ;; ACL2(r)).

  (defthm expt-type-prescription-positive
    (implies (and (< 0 r)
                  (real/rationalp r))
             (< 0 (expt r i)))
    :rule-classes (:type-prescription :generalize))

  (defthm expt-type-prescription-nonzero
    (implies (and (fc (acl2-numberp r))
                  (not (equal r 0)))
             (not (equal 0 (expt r i))))
    :rule-classes (:type-prescription :generalize))

  (defthm expt-type-prescription-integerp
    (implies (and (<= 0 i)
                  (integerp r))
             (integerp (expt r i)))
    :rule-classes (:type-prescription :generalize))

  (in-theory
   ;; [Jared] Some of these type-prescription rules for expt, above, are
   ;; duplicates of built-in ACL2 rules:
   ;;
   ;;    new rule                                duplicates
   ;;  ---------------------------------------------------------------------------------
   ;;    EXPT-TYPE-PRESCRIPTION-RATIONALP        RATIONALP-EXPT-TYPE-PRESCRIPTION
   ;;    EXPT-TYPE-PRESCRIPTION-NONZERO          EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE
   ;;
   ;; Since the new rules above have :generalize rule-classes as well, I'm going to
   ;; disable the built-in ACL2 rules.
   (disable RATIONALP-EXPT-TYPE-PRESCRIPTION
            EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE)))



(defsection basic-expt-normalization
  :parents (arithmetic-1 expt)
  :short "Basic rules for normalizing and simplifying exponents."

  ;; [Jared] removing since it is redundant with expt-1, below
  ;; (defthm Left-nullity-of-1-for-expt
  ;;   (equal (expt 1 i) 1))

  (defthm Right-unicity-of-1-for-expt
    (equal (expt r 1)
           (fix r))
    :hints (("Goal" :expand (expt r 1))))

  (defthm expt-minus
    (equal (expt r (- i))
           (/ (expt r i))))

  ;; The following is superseded by exponents-add below, except for the case
  ;; that r = 0.  But I'll leave it here; in fact it's quite natural to have
  ;; (roughly speaking) two versions of each rule about expt, based on the
  ;; disjunction in the guard for expt.

  (defthm Exponents-add-for-nonneg-exponents
    ;; We don't need that r is non-zero for this one.
    (implies (and (<= 0 i)
                  (<= 0 j)
                  (fc (integerp i))
                  (fc (integerp j)))
             (equal (expt r (+ i j))
                    (* (expt r i)
                       (expt r j)))))

  (encapsulate
    ()
    (local (defthm Exponents-add-negative-negative
             (implies (and (integerp i)
                           (integerp j)
                           (< i 0)
                           (< j 0))
                      (equal (expt r (+ i j))
                             (* (expt r i)
                                (expt r j))))
             :rule-classes nil))

    (local (defthm Exponents-add-positive-negative
             (implies (and (integerp i)
                           (integerp j)
                           (acl2-numberp r)
                           (not (equal r 0))
                           (< 0 i)
                           (< j 0))
                      (equal (expt r (+ i j))
                             (* (expt r i)
                                (expt r j))))
             :hints (("Goal" :expand (expt r (+ i j))))
             :rule-classes nil))

    (defthm Exponents-add

; The first two (syntaxp) hypotheses below are new for Version_2.6.  Without
; this change there can be looping with the definition of expt, for example on
; the following (thanks to Eric Smith for reporting the problem from which this
; example was culled).  (By the way, this example is probably not a theorem;
; the point here is to avoid looping.)  But see also
; Exponents-add-unrestricted.

      #|
      (thm (IMPLIES (AND (NOT (ZIP P))
      (< 0 P)
      (< (* 2 (+ P -1) (/ (EXPT 2 (+ P -1))))
      1)
      (INTEGERP P)
      (< 1 P)
      (INTEGERP Q)
      (< 0 Q))
      (< (* 2 P (/ (EXPT 2 P))) 1)))
      |#

   (implies (and (syntaxp (not (and (quotep i) (integerp (cadr i))
                                    (or (equal (cadr i) 1)
                                        (equal (cadr i) -1)))))
                 (syntaxp (not (and (quotep j) (integerp (cadr j))
                                    (or (equal (cadr j) 1)
                                        (equal (cadr j) -1)))))
                 (not (equal 0 r))
                 (fc (acl2-numberp r))
                 (fc (integerp i))
                 (fc (integerp j)))
            (equal (expt r (+ i j))
                   (* (expt r i)
                      (expt r j))))
   :hints (("Goal" :use
            (Exponents-add-negative-negative
             Exponents-add-positive-negative
             (:instance Exponents-add-positive-negative
                        (i j) (j i)))))))

  (defthm Exponents-add-unrestricted

; The comment above in Exponents-add explains why we do not leave this rule
; enabled.  But we include it in case it is of use.  For example, Exponents-add
; is not sufficient for the proof of expt-is-increasing-for-base>1 in
; inequalities.lisp.

    (implies (and (not (equal 0 r))
                  (fc (acl2-numberp r))
                  (fc (integerp i))
                  (fc (integerp j)))
             (equal (expt r (+ i j))
                    (* (expt r i)
                       (expt r j)))))

  (in-theory (disable Exponents-add-unrestricted))

  (defthm Distributivity-of-expt-over-*
    (equal (expt (* a b) i)
           (* (expt a i)
              (expt b i))))

  ;; It's not clear to me whether the following rule belongs this way or the
  ;; other way around, but I'll leave it this way -- mk.

  (defthm expt-1
    (equal (expt 1 x) 1))

  (defthm Exponents-multiply
    (implies (and (fc (integerp i))
                  (fc (integerp j)))
             (equal (expt (expt r i) j)
                    (expt r (* i j))))
    :hints (("Goal" :cases
             ((not (acl2-numberp r))
              (equal r 0)))))

  (defthm Functional-commutativity-of-expt-/-base
    (equal (expt (/ r) i)
           (/ (expt r i))))

  ;; Added 6/01 by Matt Kaufmann in response to an example sent by John Cowles
  ;; that cannot be proved without it, shown below.  Actually this rule was
  ;; suggested by J Moore.
  (defthm equal-constant-+
    (implies (syntaxp (and (quotep c1)
                           (quotep c2)))
             (equal (equal (+ c1 x) c2)
                    (if (acl2-numberp c2)
                        (if (acl2-numberp x)
                            (equal x (- c2 c1))
                          (equal (fix c1) c2))
                      nil)))))

#| John Cowles's example (see rule above); without the rule above the following
      hint is needed for the thm form below:

;    :hints (("Goal"
;	      :use (:theorem
;		    (implies (equal (+ -1 x) 3)
;			     (equal x 4)))))

      (include-book
       "/meru1/cowles/acl2/ver2.5/acl2-sources/books/arithmetic/top-with-meta")

      (defun  ;; compute 2^n ; ; ;
        pow (n)
        (if (zp n)
            1
          (* 2 (pow (- n 1)))))

      (defun e (x) ;; product from i=1 to x of 2^i - 1 ; ; ;
        (if (zp x)
            1
          (* (- (pow x) 1)(e (- x 1)))))

      (defun
        e1 (x)
        (if (zp x)
            1
          (* (pow x)(e1 (- x 1)))))

      (thm
     ;; some complicated hyps removed ; ; ;
       (IMPLIES (EQUAL (+ -1 X) 3)
                (EQUAL (+ (* 384 (POW (+ -4 X)))
                          (- (* 768 (POW (+ -4 X)) (POW (+ -4 X))))
                          (* 3456
                             (/ (+ (- (* 2 (E (+ -4 X))
                                         (E1 (+ -4 X))
                                         (POW (+ -4 X))))
                                   (* 4 (E (+ -4 X))
                                      (E1 (+ -4 X))
                                      (POW (+ -4 X))
                                      (POW (+ -4 X)))))))
                       (+ (- (* 64 (E (+ -4 X))
                                (E1 (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))))
                          (* 128 (E (+ -4 X))
                             (E1 (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X)))
                          (* 256 (E (+ -4 X))
                             (E1 (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X)))
                          (* 512 (E (+ -4 X))
                             (E1 (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X)))
                          (- (* 512 (E (+ -4 X))
                                (E1 (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))))
                          (- (* 1024 (E (+ -4 X))
                                (E1 (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))))
                          (- (* 2048 (E (+ -4 X))
                                (E1 (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))
                                (POW (+ -4 X))))
                          (* 4096 (E (+ -4 X))
                             (E1 (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X))
                             (POW (+ -4 X)))))))

      |#
