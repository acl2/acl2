; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; expt.lisp
;;;
;;; This book contains rules for reasoning about expt.
;;;
;;; It contains the following sections:
;;;
;;; 1. Type-prescription rules for expt.
;;; 2. Simple rules about expt.
;;; 3. Normalizing expt expressions
;;; 4. Some miscelaneous rules about expt.
;;; 5. Linear rules about expt.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local
 (include-book "../../support/top"))

(local
 (include-book "expt-helper"))

(local
 (include-book "types"))

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 1. Type-prescription rules for expt.

(defthm expt-type-prescription-rationalp-base
  (implies (rationalp x)
           (rationalp (expt x n)))
  :rule-classes (:type-prescription :generalize))

#+non-standard-analysis
(defthm expt-type-prescription-realp-base
  (implies (real/rationalp x)
           (real/rationalp (expt x n)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-integerp-base
  (implies (and (<= 0 n)
                (integerp x))
           (integerp (expt x n)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-integerp-base-a
  (implies (and (integerp n)
		(< n 0)
                (integerp x)
		(< 1 x))
           (and (rationalp (expt x n))
		(not (integerp (expt x n)))))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-integerp-base-b
  (implies (and (integerp n)
		(< n 0)
                (integerp x)
		(< x -1))
           (and (rationalp (expt x n))
		(not (integerp (expt x n)))))
  :rule-classes (:type-prescription :generalize))

#|
;;; I would really like to not need the following rewrite rule.
;;; However, type-reasoning is not particularly good at
;;; determining the truth of inequalities.

;;; Type reasoning should now (v2-8) be a little better at determining
;;; the truth of inequalities and I believe that the following rule is
;;; no longer neccesary.  I keep it around, but commented out, just in
;;; case this is wrong.

(defthm integerp-expt
    (implies (and (integerp x)
                  (<= 0 n))
             (integerp (expt x n))))
|#

;;; Note the form of the conclusion of these rules.  It is important
;;; to write type-prescription rules such that their conclusions
;;; actually specify a type-set.  Due to the presence of complex
;;; numbers and the fact that they are linearly ordered,
;;; (< 0 (expt x n)) does not encode a type-set.  This makes me
;;; unhappy at times.

;;; NOTE: Should the next 3 rules be :linear rules also?
;;; Since they compare to zero, probably not.  On the other hand, as
;;; noted above, type-reasoning is not always as good at
;;; determining the truth of inequalities as one might desire.  This is
;;; still true even with the improvement to type-set mentioned
;;; above.

(defthm expt-type-prescription-non-0-base
  (implies (and (acl2-numberp x)
                (not (equal x 0)))
           (and (acl2-numberp (expt x n))
		(not (equal (expt x n) 0))))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-positive-base
  (implies (and (< 0 x)
                (rationalp x))
           (and (rationalp (expt x n))
		(< 0 (expt x n))))
  :rule-classes (:type-prescription :generalize))

#+non-standard-analysis
(defthm expt-type-prescription-positive-base-real-case
  (implies (and (< 0 x)
                (real/rationalp x))
           (and (real/rationalp (expt x n))
		(< 0 (expt x n))))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-nonnegative-base
  (implies (and (<= 0 x)
                (rationalp x))
	   (and (rationalp (expt x n))
		(<= 0 (expt x n))))
  :rule-classes (:type-prescription :generalize))

#+non-standard-analysis
(defthm expt-type-prescription-nonnegative-base-real-case
  (implies (and (<= 0 x)
                (real/rationalp x))
	   (and (real/rationalp (expt x n))
		(<= 0 (expt x n))))
  :rule-classes (:type-prescription :generalize))

(defthm integerp-/-expt-1
  (implies (and (integerp x)
		(< 1 x)
		(integerp n))
	   (equal (integerp (/ (expt x n)))
		  (<= n 0)))
  :rule-classes (:rewrite
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(< 1 x)
				(integerp n)
				(<= n 0))
			   (integerp (/ (expt x n)))))
		 (:generalize
		  :corollary
		  (implies (and (integerp x)
				(< 1 x)
				(integerp n)
				(<= n 0))
			   (integerp (/ (expt x n)))))))

(defthm integerp-/-expt-2
  (implies (and (integerp x)
		(< x -1)
		(integerp n))
	   (equal (integerp (/ (expt x n)))
		  (<= n 0)))
  :rule-classes (:rewrite
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(< x -1)
				(integerp n)
				(<= n 0))
			   (integerp (/ (expt x n)))))
		 (:generalize
		  :corollary
		  (implies (and (integerp x)
				(< x -1)
				(integerp n)
				(<= n 0))
			   (integerp (/ (expt x n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 2. Simple rules about expt

;;; Since expt will be disabled, I provide some rules to take care of
;;; the ``simple'' cases.

(defthm |(expt x 0)|
 (equal (expt x 0)
        1))

(defthm |(expt 0 n)|
    (equal (expt 0 n)
           (if (zip n)
               1
             0)))

(defthm |(expt x 1)|
  (implies (acl2-numberp x)
	   (equal (expt x 1)
		  x)))

(defthm |(expt 1 n)|
    (equal (expt 1 n)
           1))

(defthm |(expt x -1)|
  (equal (expt x -1)
	 (/ x)))

;;; Do we want a rule like the following?  I have neither tried to
;;; prove it, nor tested its effects.
#|
(defthm |equal (expt x n) -c|
  (implies (and (syntaxp (negative-numeric-constant-p c))
		(integerp c)
		(integerp n)
		(rationalp x))
	   (equal (equal (expt x n) c)
		  (and (equal (expt (- x) n) (- c))
		       (oddp n)))))
|#
;;; There would be issues with |(expt (- x) n)|, at the least.
;;; Maybe a forward-chaining rule with concl (oddp n)?

(defthm |(equal (expt x n) -1)|
  (implies (and (integerp n)
		(real/rationalp x))
	   (equal (equal (expt x n) -1)
		  (and (equal x -1)
		       (oddp n)))))

(defthm |(equal (expt x n) 0)|
  (implies (and (integerp n)
		(real/rationalp x))
	   (equal (equal (expt x n) 0)
		  (and (equal x 0)
		       (not (equal n 0))))))

;;; Should we restrict this to present-in-goal?  Introducing case-splits
;;; like the below can be expensive.

(defthm |(equal (expt x n) 1)|
  (implies  (and (integerp n)
		 (real/rationalp x)
		 (syntaxp (rewriting-goal-literal x mfc state)))
	   (equal (equal (expt x n) 1)
		  (or (zip n)
		      (equal x 1)
		      (and (equal x -1)
			   (evenp n))))))

;;; Do we want something like this?  I have not tried to prove it yet,
;;; but I think it will require reasoning about prime numbers and
;;; factorization.  Given that, should we generalize it to any prime,
;;; not just 2?
#|
(defthm |(equal (expt x n) 2)|
  (implies (syntaxp (rewriting-goal-literal x mfc state))
	   (equal (equal (expt x n) 2)
		  (or (and (equal x 1/2)
			   (equal n -1))
		      (and (equal x 2)
			   (equal n 1))))))
|#

;;; Could we generalize this to other bases than two easily?

;;; Two is an important number

(defun p-o-2-g-fn (c)
  (let ((x (power-of-2-generalized c)))
    (if x
	(list (cons 'x (kwote x)))
      nil)))

(defthm |(equal (expt 2 n) c)|
  (implies (and (bind-free (p-o-2-g-fn c) (x))
		(integerp x)
		(equal (expt 2 x) c)
		(integerp n))
	   (equal (equal (expt 2 n) c)
		  (equal n x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Should we expand (expt (+ c x) d), whenever c and d are constants?
;;; What about (expt (+ x y) 256)?  Where should we draw the line?

(defthm |(expt (+ x y) 2)|
    (implies (syntaxp (rewriting-goal-literal x mfc state))
             (equal (expt (+ x y) 2)
                    (+ (expt x 2)
                       (* 2 x y)
                       (expt y 2))))
  :hints (("Goal" :expand (expt (+ x y) 2))))

(defthm |(expt (+ x y) 3)|
    (implies (syntaxp (rewriting-goal-literal x mfc state))
             (equal (expt (+ x y) 3)
                    (+ (expt x 3)
                       (* 3 (expt x 2) y)
                       (* 3 x (expt y 2))
                       (expt y 3))))
  :hints (("Goal" :expand ((expt (+ x y) 3)
			   (expt (+ x y) 2)))))

(defthm |(expt c (* d n))|
  (implies (and (syntaxp (quotep c))
                (integerp c)
		(syntaxp (quotep d))
                (integerp d)
		(integerp n))
	   (equal (expt c (* d n))
		  (expt (expt c d) n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 3. Normalizing expt expressions

;;; In these next sections we define a couple of rules for
;;; normalizing expressions involving expt.  See top.lisp for a couple
;;; of theories which use some or all of these.

;;; The next six rules come in three pairs, one for general terms, one
;;; for constants.  If you change or disable any of these rules, you
;;; may break the assumptions in collect.lisp for collect-* rules.
;;; Also, see invert-match.

;;; I keep going back and forth on what is the proper treatment of
;;; expt and unary-/.  I originally preferred (expt (/ x) n),
;;; next I tried the below, and now I am trying (expt x (- n)).

#|
;;; I used to push / inside expt, but I now believe that was wrong.

;;; Note that the use of negative-addends-p means that we are not
;;; introducing negation into the exponent below, rather we are
;;; undoing it.

(defthm |(expt x (- n))|
    (implies (syntaxp (mostly-negative-addends-p n mfc state))
             (equal (expt x n)
                    (/ (expt x (- n))))))

(defthm |(expt x (- c))|
    (implies (syntaxp (numeric-constant-p c))
             (equal (expt x (- c))
                    (/ (expt x c)))))

;;; If you change |(expt (/ x) n)| below, see nintergerp-extra in
;;; integerp.lisp.

(defthm |(expt (/ x) n)|
  (equal (expt (/ x) n)
	 (/ (expt x n))))
|#

(defthm |(expt (/ x) n)|
  (equal (expt (/ x) n)
	 (expt x (- n))))

(defthm |(/ (expt x n))|
  (equal (/ (expt x n))
	 (expt x (- n))))

(defthm |(expt 1/c n)|
    (implies (and (syntaxp (quotep x))
                  (syntaxp (rationalp (unquote x)))
                  (syntaxp (not (integerp (unquote x))))
                  ;(syntaxp (equal (numerator x) 1))
		  (syntaxp (< (abs x) 1))
		  )
             (equal (expt x n)
                    (expt (/ x) (- n)))))

(defthm |(expt (- x) n)|
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		  (syntaxp (mostly-negative-addends-p x mfc state))
                  (integerp n))
             (equal (expt x n)
                    (if (evenp n)
                        (expt (- x) n)
                      (- (expt (- x) n)))))
  :hints (("Goal" :use ((:instance expt-negative-base-even-exponent-a
                                   (i n)
                                   (r x))
                        (:instance expt-negative-base-odd-exponent-a
                                   (i n)
                                   (r x))))))

(defthm |(expt (- c) n)|
    (implies (and (syntaxp (rewriting-goal-literal c mfc state))
		  (syntaxp (rational-constant-p c))
                  (integerp n))
             (equal (expt (- c) n)
                    (if (evenp n)
                        (expt c n)
                      (- (expt c n))))))

(theory-invariant (if (active-runep '(:definition arith-5-active-flag))
                      (and ;(active-runep '(:rewrite |(expt x (- n))|))
                           ;(active-runep '(:rewrite |(expt x (- c))|))
                           (active-runep '(:rewrite |(expt (/ x) n)|))
                           (active-runep '(:rewrite |(/ (expt x n))|))
                           (active-runep '(:rewrite |(expt 1/c n)|))
                           (active-runep '(:rewrite |(expt (- x) n)|))
                           (active-runep '(:rewrite |(expt (- c) n)|)))
                    t)
                  :error nil)

(defthm |(expt (* x y) n)|
  (equal (expt (* x y) n)
         (* (expt x n)
            (expt y n))))

(defthm |(expt (expt x m) n)|
  (implies (and (integerp m)
                (integerp n))
           (equal (expt (expt x m) n)
                  (expt x (* m n)))))

;;; The following will be disabled for gather-exponents.

;;; Force the scattering of the exponents even at the cost of introducing a
;;; case-split only when we are back-chaining.

(defthm |(expt x (+ m n))|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (if (equal (+ m n) 0)
		      1
		      (* (expt x m)
			 (expt x n))))))

;;; The following will be disabled for gather-exponents.

(defthm |(expt x (+ m n)) non-zero (+ m n)|
  (implies (and (integerp m)
		(integerp n)
		(not (equal (+ m n) 0)))
	   (equal (expt x (+ m n))
		  (* (expt x m)
		     (expt x n)))))

;;; The following will be disabled for gather-exponents.

(defthm |(expt x (+ m n)) non-zero x|
  (implies (and (acl2-numberp x)
		(not (equal x 0))
		(integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (* (expt x m)
		     (expt x n)))))
#|
;;; I don't think we want these next two.  I leave them here for
;;; referance purposes only.  If you reinstate them, be sure to
;;; uncomment any references to them in top.

(defthm |(expt x (+ m n)) non-pos m and n|
  (implies (and (<= m 0)
		(<= n 0)
		(integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (* (expt x m)
		     (expt x n)))))

(defthm |(expt x (+ m n))) non-neg m and n|
  (implies (and (<= 0 m)
		(<= 0 n)
		(integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (* (expt x m)
		     (expt x n)))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 4. Some miscelaneous rules about expt.

;;; NOTE: There are several rules in this book which have (< 1 x)
;;; as a hypothesis.  There probably should be rules with
;;; (< 0 x) (< x 1) also.

(defthm |(integerp (expt x n))|
  (implies (and (integerp n)
		(integerp x)
		(< 1 x))
	   (equal (integerp (expt x n))
		  (<= 0 n))))

(defthm |(< (expt x n) (expt x m))|
   (implies (and (real/rationalp x)
		 (< 1 x)
		 (integerp m)
		 (integerp n))
	    (equal (< (expt x m) (expt x n))
		   (< m n))))

 (defthm |(equal (expt x m) (expt x n))|
   (implies (and (real/rationalp x)
		 (not (equal x -1))
		 (not (equal x 0))
		 (not (equal x 1))
		 (integerp m)
		 (integerp n))
	    (equal (equal (expt x m) (expt x n))
		   (equal m n))))

;;; I do not particularly like the form of the next rule, but I do
;;; not see how to do better.  Also, something like this would
;;; be a nifty linear rule if we could guess the correct m or n but,
;;; again, I do not see how.

(defthm expt-exceeds-another-by-more-than-y
  (implies (and (real/rationalp x)
		(< 1 x)
                (integerp m)
                (integerp n)
		(<= 0 m)
                (<= 0 n)
                (< m n)
		(real/rationalp y)
		(< (+ y 1) x))
	   (< (+ y (expt x m)) (expt x n))))

(defthm expt-2-n-is-even
  (implies (and (integerp n)
		(integerp m))
	   (equal (equal (expt 2 n)
			 (+ 1 (expt 2 m)))
		  (and (equal n 1)
		       (equal m 0)))))

(defthm odd-expt-thm
  (implies (and (integerp man)
		(integerp exp)
		(<= exp 0))
	   (equal (< man (expt 2 exp))
		  (<= man 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 5. Linear rules about expt.

;;; We include two sets of linear rules for expt.  The first set
;;; consists of rules which are both linear and rewrite rules.  Both
;;; types are needed because of the free variable problem.  The second
;;; set are linear rules only.

(defthm expt-x->-x
  (implies (and (< 1 x)
		(< 1 n)
		(real/rationalp x)
		(integerp n))
	   (< x (expt x n)))
  :rule-classes (:rewrite :linear))

(defthm expt-x->=-x
  (implies (and (<= 1 x)
		(< 1 n)
		(real/rationalp x)
		(integerp n))
	   (<= x (expt x n)))
  :rule-classes (:rewrite :linear))

(defthm expt-is-increasing-for-base->-1
  (implies (and (< m n)
		(< 1 x)
		(integerp m)
		(integerp n)
		(real/rationalp x))
	   (< (expt x m)
	      (expt x n)))
  :rule-classes ((:rewrite)
                 (:linear :match-free :once)))

(defthm expt-is-decreasing-for-pos-base-<-1
  (implies (and (< m n)
                (< 0 x)
                (< x 1)
                (integerp m)
                (integerp n)
                (real/rationalp x))
           (< (expt x n)
              (expt x m)))
  :rule-classes ((:rewrite)
                 (:linear :match-free :once)))

(defthm expt-is-weakly-increasing-for-base->-1
  (implies (and (<= m n)
                (<= 1 x)
                (integerp m)
                (integerp n)
                (real/rationalp x))
           (<= (expt x m)
               (expt x n)))
  :rule-classes ((:rewrite)
                 (:linear :match-free :once)))

(defthm expt-is-weakly-decreasing-for-pos-base-<-1
  (implies (and (<= m n)
                (< 0 x)
                (<= x 1)
                (integerp m)
                (integerp n)
                (real/rationalp x))
           (<= (expt x n)
               (expt x m)))
  :rule-classes ((:rewrite)
                 (:linear :match-free :once)))

;; Should these be rewrite rules also? Probably not.

(defthm expt->-1-one
  (implies (and (< 1 x)
		(< 0 n)
		(real/rationalp x)
		(integerp n))
	   (< 1 (expt x n)))
  :rule-classes :linear)

(defthm expt->=-1-one
  (implies (and (<= 1 x)
		(<= 0 n)
		(real/rationalp x)
		(integerp n))
	   (<= 1 (expt x n)))
  :rule-classes :linear)

(defthm expt->-1-two
  (implies (and (< 0 x)
		(< x 1)
		(< n 0)
		(real/rationalp x)
		(integerp n))
	   (< 1 (expt x n)))
  :rule-classes :linear)

(defthm expt->=-1-two
  (implies (and (< 0 x)
		(<= x 1)
		(<= n 0)
		(real/rationalp x)
		(integerp n))
	   (<= 1 (expt x n)))
  :rule-classes :linear)

(defthm expt-<-1-one
  (implies (and (< 0 x)
		(< x 1)
		(< 0 n)
		(real/rationalp x)
		(integerp n))
	   (< (expt x n) 1))
  :rule-classes :linear)

(defthm expt-<=-1-one
  (implies (and (<= 0 x)
		(<= x 1)
		(<= 0 n)
		(real/rationalp x)
		(integerp n))
	   (<= (expt x n) 1))
  :hints (("Goal" :cases ((equal x 0)
			  (equal x 1))))
  :rule-classes :linear)

(defthm expt-<-1-two
  (implies (and (< 1 x)
		(< n 0)
		(real/rationalp x)
		(integerp n))
	   (< (expt x n) 1))
  :rule-classes :linear)

(defthm expt-<=-1-two
  (implies (and (<= 1 x)
		(<= n 0)
		(real/rationalp x)
		(integerp n))
	   (<= (expt x n) 1))
  :rule-classes :linear)


;;; So, we now try replacing the six rules below with four rules using
;;; bind-free.  I really wish ACL2 would let me do the work once, and
;;; to somehow construct the (either one or two) inequalities (including
;;; the relation) on the fly.
#|
;;; RBK: Maybe use bind-free to find the best match for d in the six
;;; rules below?  This could also eliminate the neccesity for -aaa and
;;; -bbb.

;;; Note that I limit these to when c and d are constants.  Thus,
;;; (expt c d) or (expt c (+ 1 d)) are constants being fed into
;;; linear arithemtic as bounds.

(defthm expt-linear-a
  (implies (and (syntaxp (rational-constant-p c))
		(< d n)
		(syntaxp (rational-constant-p d))
		(integerp d)
		(rationalp c)
		(< 1 c)
		(integerp n))
	   (<= (expt c (+ 1 d)) (expt c n)))
  :hints (("Goal" :in-theory (disable expt
				      EXPONENTS-ADD-1
				      EXPONENTS-ADD-2
				      |(expt x (+ m n))|
				      |(expt x (+ m n)) non-zero x|)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))

(defthm expt-linear-aa
  (implies (and (syntaxp (rational-constant-p c))
		(<= d n)
		(syntaxp (rational-constant-p d))
		(integerp d)
		(real/rationalp c)
		(< 1 c)
		(integerp n))
	   (<= (expt c d) (expt c n)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))

;;; We need this one because of weaknesses in free variable matching.

(defthm expt-linear-aaa
  (implies (and (syntaxp (rational-constant-p c))
		(<= d n)
		(syntaxp (rational-constant-p d))
		(not (equal n d))
		(integerp d)
		(real/rationalp c)
		(< 1 c)
		(integerp n))
	   (<= (expt c (+ 1 d)) (expt c n)))
  :hints (("Goal" :in-theory (disable expt
				      EXPONENTS-ADD-1
				      EXPONENTS-ADD-2
				      |(expt x (+ m n))|
				      |(expt x (+ m n)) non-zero x|)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))

(defthm expt-linear--b
  (implies (and (syntaxp (rational-constant-p c))
		(< n d)
		(syntaxp (rational-constant-p d))
		(integerp d)
		(real/rationalp c)
		(< 1 c)
		(integerp n))
	   (<= (expt c n) (expt c (+ -1 d))))
  :hints (("Goal" :in-theory (disable expt
				      EXPONENTS-ADD-1
				      EXPONENTS-ADD-2
				      |(expt x (+ m n))|
				      |(expt x (+ m n)) non-zero x|)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))

(defthm expt-linear-bb
  (implies (and (syntaxp (rational-constant-p c))
		(<= n d)
		(syntaxp (rational-constant-p d))
		(integerp d)
		(real/rationalp c)
		(< 1 c)
		(integerp n))
	   (<= (expt c n) (expt c d)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))

(defthm expt-linear-bbb
  (implies (and (syntaxp (rational-constant-p c))
		(<= n d)
		(syntaxp (rational-constant-p d))
		(not (equal n d))
		(integerp d)
		(real/rationalp c)
		(< 1 c)
		(integerp n))
	   (<= (expt c n) (expt c (+ -1 d))))
  :hints (("Goal" :in-theory (disable expt
				      EXPONENTS-ADD-1
				      EXPONENTS-ADD-2
				      |(expt x (+ m n))|
				      |(expt x (+ m n)) non-zero x|)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))
|#

;;; This should really be put in axioms.lisp.
(defun mfc-pot-lst (mfc)
  (car (cddddr (cddddr mfc))))

;;; This should really be put in axioms.lisp.
(defun mfc-pt (mfc)
  (let ((rcnst (cadr (cddddr (cddddr mfc)))))
    (caaddr rcnst)))

(defun bounds-for-expt-linear-fns-1 (n mfc state)
  ;; See extract-bounds in non-linear for details.
  (declare (xargs :mode :program))
  (declare (ignore state))
  (if (equal (fn-symb n) 'UNARY--)
      (let ((bounds-polys (bounds-polys-with-var n
						 (mfc-pot-lst mfc)
						 (mfc-pt mfc))))
	(mv-let (lbd lbd-rel lbd-ttree
		 ubd ubd-rel ubd-ttree)
	  (extract-bounds bounds-polys)
	  (declare (ignore lbd-ttree ubd-ttree))
	  (mv lbd lbd-rel ubd ubd-rel)))
    (let ((bounds-polys (bounds-polys-with-var n
					       (mfc-pot-lst mfc)
					       (mfc-pt mfc))))
      (mv-let (lbd lbd-rel lbd-ttree
	       ubd ubd-rel ubd-ttree)
	(extract-bounds bounds-polys)
	(declare (ignore lbd-ttree ubd-ttree))
	(mv lbd lbd-rel ubd ubd-rel)))))

;;; RBK: I am pretty sure that this is what I want, but I really should
;;; do some proper testing.
(defun bounds-for-expt-linear-fns (n mfc state)
  ;; We are about to try to extract bounds for n from the linear-pot.
  ;; So, we make sure waht we pass on is a legitimate pot-label
  (declare (xargs :mode :program))
  (cond ((quotep n)
	 ;; Shouldn't happen, raise error or warning?
	 (mv nil nil nil nil))
	((symbolp n)
	 (bounds-for-expt-linear-fns-1 n mfc state))
	((equal (fn-symb n) 'BINARY-+)
	 ;; Shouldn't happen (given the use of arithmetic-theory),
	 ;; raise error or warning?
	 (mv nil nil nil nil))
	((equal (fn-symb n) 'UNARY--)
	 (mv-let (lbd lbd-rel ubd ubd-rel)
	   (bounds-for-expt-linear-fns-1 (arg1 n) mfc state)
	   (mv (if ubd
		   (- ubd)
		 nil)
	       ubd-rel
	       (if lbd
		   (- lbd)
		 nil)
	       lbd-rel)))
	((and (equal (fn-symb n) 'BINARY-*)
	      (quotep (arg1 n))
	      (equal (unquote (arg1 n)) 0))
	 ;; Shouldn't happen, raise error or warning?
	 (mv nil nil nil nil))
	((and (equal (fn-symb n) 'BINARY-*)
	      (quotep (arg1 n))
	      (rationalp (unquote (arg1 n)))
	      (< 0 (unquote (arg1 n))))
	 (mv-let (lbd lbd-rel ubd ubd-rel)
	   (bounds-for-expt-linear-fns-1 (arg2 n) mfc state)
	   (let ((x (/ (unquote (arg1 n)))))
	     (mv (if lbd
		     (/ lbd x)
		   nil)
		 lbd-rel
		 (if ubd
		     (/ ubd x)
		   nil)
		 ubd-rel))))
	((and (equal (fn-symb n) 'BINARY-*)
	      (quotep (arg1 n))
	      (rationalp (unquote (arg1 n)))
	      (< (unquote (arg1 n)) 0))
	 (mv-let (lbd lbd-rel ubd ubd-rel)
	   (bounds-for-expt-linear-fns-1 (arg2 n) mfc state)
	   (let ((x (/ (unquote (arg1 n)))))
	     (mv (if ubd
		     (- (/ ubd x))
		   nil)
		 ubd-rel
		 (if lbd
		     (- (/ lbd x))
		   nil)
		 lbd-rel))))
	(t
	 (bounds-for-expt-linear-fns-1 n mfc state))))

;;; RBK: I always get horribly confused when I try to think abut the
;;; various permutations of relations and constants with respect to
;;; the strength of the final concls in the linear rules.  It is very
;;; likely that this could be done better.

(defun expt-linear-upper-<-fn (n mfc state)
  (declare (xargs :mode :program))
  (mv-let (lbd lbd-rel ubd ubd-rel)
    (bounds-for-expt-linear-fns n mfc state)
    (declare (ignore lbd lbd-rel))
    (cond ((and (equal ubd-rel '<)
		(integerp ubd))
	   (list (cons 'd (kwote ubd))))
	  (t
	   nil))))

(defun expt-linear-upper-<=-fn (n mfc state)
  (declare (xargs :mode :program))
  (mv-let (lbd lbd-rel ubd ubd-rel)
    (bounds-for-expt-linear-fns n mfc state)
    (declare (ignore lbd lbd-rel))
    (cond ((and (equal ubd-rel '<=)
		(integerp ubd))
	   (list (cons 'd (kwote ubd))))
	  ((and (equal ubd-rel '<)
		(integerp ubd))
	   ;; Caught in expt-linear-upper-<-fn
	   nil)
	  ((real/rationalp ubd)
	   (list (cons 'd (kwote (floor ubd 1)))))
	  (t
	   nil))))

(defun expt-linear-lower-<-fn (n mfc state)
  (declare (xargs :mode :program))
  (mv-let (lbd lbd-rel ubd ubd-rel)
    (bounds-for-expt-linear-fns n mfc state)
    (declare (ignore ubd ubd-rel))
    (cond ((and (equal lbd-rel '<)
		(integerp lbd))
	   (list (cons 'd (kwote lbd))))
	  (t
	   nil))))

(defun expt-linear-lower-<=-fn (n mfc state)
  (declare (xargs :mode :program))
  (mv-let (lbd lbd-rel ubd ubd-rel)
    (bounds-for-expt-linear-fns n mfc state)
    (declare (ignore ubd ubd-rel))
    (cond ((and (equal lbd-rel '<=)
		(integerp lbd))
	   (list (cons 'd (kwote lbd))))
	  ((and (equal lbd-rel '<)
		(integerp lbd))
	   nil)
	  ((real/rationalp lbd)
	   (list (cons 'd (kwote (+ 1 (floor lbd 1))))))
	  (t
	   nil))))

(defthm expt-linear-upper-<
  (implies (and (syntaxp (rational-constant-p c))
		(real/rationalp c)
		(< 1 c)
		(bind-free (expt-linear-upper-<-fn n mfc state)
			   (d))
		(integerp d)
		(< n d)
		(integerp n))
	   (< (expt c n) (expt c d)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))

(defthm expt-linear-upper-<=
  (implies (and (syntaxp (rational-constant-p c))
		(real/rationalp c)
		(< 1 c)
		(bind-free (expt-linear-upper-<=-fn n mfc state)
			   (d))
		(integerp d)
		(<= n d)
		(integerp n))
	   (<= (expt c n) (expt c d)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))

(defthm expt-linear-lower-<
  (implies (and (syntaxp (rational-constant-p c))
		(real/rationalp c)
		(< 1 c)
		(bind-free (expt-linear-lower-<-fn n mfc state)
			   (d))
		(integerp d)
		(< d n)
		(integerp n))
	   (< (expt c d) (expt c n)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))

(defthm expt-linear-lower-<=
  (implies (and (syntaxp (rational-constant-p c))
		(real/rationalp c)
		(< 1 c)
		(bind-free (expt-linear-lower-<=-fn n mfc state)
			   (d))
		(integerp d)
		(<= d n)
		(integerp n))
	   (<= (expt c d) (expt c n)))
  :rule-classes ((:linear :trigger-terms ((expt c n)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some rules about expt with a negative base.

(defthm expt-type-prescription-negative-base-even-exponent
  (implies (and (< x 0)
		(rationalp x)
		(integerp n)
		(integerp (* 1/2 n)))
	   (and (rationalp (expt x n))
		(< 0 (expt x n))))
  :rule-classes (:type-prescription :generalize))

#+non-standard-analysis
(defthm expt-type-prescription-negative-base-even-exponent-real-case
  (implies (and (< x 0)
		(real/rationalp x)
		(integerp n)
		(integerp (* 1/2 n)))
	   (and (real/rationalp (expt x n))
		(< 0 (expt x n))))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-negative-base-odd-exponent
  (implies (and (< x 0)
		(rationalp x)
		(integerp n)
		(not (integerp (* 1/2 n))))
	   (and (rationalp (expt x n))
		(< (expt x n) 0)))
  :rule-classes (:type-prescription :generalize))

#+non-standard-analysis
(defthm expt-type-prescription-negative-base-odd-exponent-real-case
  (implies (and (< x 0)
		(real/rationalp x)
		(integerp n)
		(not (integerp (* 1/2 n))))
	   (and (real/rationalp (expt x n))
		(< (expt x n) 0)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-nonpositive-base-even-exponent
  (implies (and (<= x 0)
                (rationalp x)
		(integerp n)
		(integerp (* 1/2 n)))
	   (and (rationalp (expt x n))
		(<= 0 (expt x n))))
  :rule-classes (:type-prescription :generalize)
  :hints (("Goal" :use ((:instance
			 expt-type-prescription-negative-base-even-exponent-a)))))

#+non-standard-analysis
(defthm expt-type-prescription-nonpositive-base-even-exponent-real-case
  (implies (and (<= x 0)
                (real/rationalp x)
		(integerp n)
		(integerp (* 1/2 n)))
	   (and (real/rationalp (expt x n))
		(<= 0 (expt x n))))
  :rule-classes (:type-prescription :generalize)
  :hints (("Goal" :use ((:instance
			 expt-type-prescription-negative-base-even-exponent-a)))))

(defthm expt-type-prescription-nonpositive-base-odd-exponent
  (implies (and (<= x 0)
                (rationalp x)
		(integerp n)
		(not (integerp (* 1/2 n))))
	   (and (rationalp (expt x n))
		(<= (expt x n) 0)))
  :rule-classes (:type-prescription :generalize)
  :hints (("Goal" :use ((:instance
			 expt-type-prescription-negative-base-odd-exponent-a)))))

#+non-standard-analysis
(defthm expt-type-prescription-nonpositive-base-odd-exponent-real-case
  (implies (and (<= x 0)
                (real/rationalp x)
		(integerp n)
		(not (integerp (* 1/2 n))))
	   (and (real/rationalp (expt x n))
		(<= (expt x n) 0)))
  :rule-classes (:type-prescription :generalize)
  :hints (("Goal" :use ((:instance
			 expt-type-prescription-negative-base-odd-exponent-a)))))

