; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; basic.lisp
;;;
;;; This book contains the basic rules used to enforce a functional
;;; nesting order we have found useful as well as a few other small
;;; rules.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

(local (include-book "basic-helper"))

(include-book "building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Since expt will be disabled, we create a couple of rules
;;; similar to default-+-1 and default-+-2.

(defthm default-expt-1
    (implies (not (acl2-numberp x))
             (equal (expt x n)
                    (if (zip n)
                        1
                      0))))

(defthm default-expt-2
    (implies (case-split (not (integerp n)))
             (equal (expt x n)
                    1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The following three sets of rules enforce the functional nesting
;;; order + - * / as well as commutative and associative rules for
;;; + and *.

(defthm |(+ y x)|
    (equal (+ y x)
           (+ x y)))

(defthm |(+ y (+ x z))|
  (equal (+ y (+ x z))
         (+ x (+ y z))))

(defthm |(+ (+ x y) z)|
    (equal (+ (+ x y) z)
           (+ x (+ y z))))

;;; A ``base case'' rule.

(defthm |(+ 0 x)|
  (implies (acl2-numberp x)
           (equal (+ 0 x)
                  x)))

;;; Unary-- is idempotent.

(defthm |(- (- x))|
  (implies (acl2-numberp x)
           (equal (- (- x))
                  x)))

;;; We regard - as a unary operation (unary-- is the internal
;;; representation), and hence push it inside the binary
;;; operation + (or binary-+).

(defthm |(- (+ x y))|
  (equal (- (+ x y))
         (+ (- x) (- y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(* y x)|
    (equal (* y x)
           (* x y)))

(defthm |(* y (* x z))|
   (equal (* y (* x z))
          (* x (* y z))))

(defthm |(* (* x y) z)|
    (equal (* (* x y) z)
           (* x (* y z))))

(defthm |(* 1 x)|
  (implies (acl2-numberp x)
           (equal (* 1 x)
                  x)))

(defthm |(* 0 x)|
  (equal (* 0 x)
         0))

;;; This rule conflicts with AMD's preferances.  See |(- x)|
;;; in mini-theories.lisp

(defthm |(* -1 x)|
  (equal (* -1 x)
         (- x)))

;;; Unary-/ is idempotent.

(defthm |(/ (/ x))|
  (implies (acl2-numberp x)
           (equal (/ (/ x))
                  x)))

;;; We regard / as a unary operation (unary-/ is the internal
;;; representation), and hence push it inside the binary
;;; operation * (or binary-*).

(defthm |(/ (* x y))|
  (equal (/ (* x y))
	 (* (/ x) (/ y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Two distributivity rules.  Note that we disable the
;;; ``built-in'' rule Distributivity in top.lisp.

(defthm |(* x (+ y z))|
  (equal (* x (+ y z))
         (+ (* x y) (* x z))))

(local
 (in-theory (disable Distributivity)))

(defthm |(* (+ x y) z)|
  (equal (* (+ x y) z)
	 (+ (* x z) (* y z))))

;;; These rules might seem out of place in that they deal with
;;; cancelling like terms --- something otherwise handled
;;; elsewhere.  However, by coming after (in this file)  the two
;;; distributivity rules above they will help catch such forms
;;; as  (* (+ a b) (/ (+ a b))) here, rather than letting it get
;;; distributed out and then having to deal with it afterwards.
;;; We place this comment here as a reminder of how the
;;; occasional ''extra'' rule can be a good thing.

;;; I believe that these two rules are sufficient to handle the
;;; general case, since x and (/ x) will be placed next to each
;;; other in term-order.

;;; Note that these rules does not catch such terms as
;;; (* (expt x y) (expt x (- y))) or
;;; (* (expt x y) (expt (/ x) y)).
;;; Should we try to handle these also?  Or is it reasonable to
;;; assume that |(expt x (- n))| and |(expt (/ x) n)| will
;;; obviate the need?

(defthm |(* a (/ a))|
    (implies (acl2-numberp x)
             (equal (* x (/ x))
                    (if (equal x 0)
                        0
                      1))))

(defthm |(* a (/ a) b)|
    (implies (and (acl2-numberp x)
                  (acl2-numberp y))
             (equal (* x (/ x) y)
                    (if (equal x 0)
                        0
                      y))))

;;; We pull - outside of *.  These two rules are sufficient to
;;; handle the general case since ACL2 rewrites from the inside
;;; out.  Note that we specificly exclude negative constants
;;; from these rules.

(defthm |(* x (- y))|
  (implies (syntaxp (not (quotep y)))
	   (equal (* x (- y))
		  (- (* x y)))))

(defthm |(* (- x) y)|
  (implies (syntaxp (not (quotep x)))
	   (equal (* (- x) y)
		  (- (* x y)))))

;;; In the case of a product involving a constant, we prefer the
;;; constant to be negative.

(defthm |(- (* c x))|
  (implies (syntaxp (quotep c))
	   (equal (- (* c x))
		  (* (- c) x))))

;;; We pull - outside of / also.  Note that we do not need a rule
;;; analogous to |(- (* c x))| since ``execution'' will ensure
;;; that this is done automatically in that case.

(defthm |(/ (- x))|
  (implies (syntaxp (not (quotep x)))
  (equal (/ (- x))
         (- (/ x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some type-prescription rules for expt.

(defthm expt-type-prescription-rationalp-base
  (implies (rationalp x)
           (rationalp (expt x n)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-integerp-base
  (implies (and (<= 0 n)
                (integerp x))
           (integerp (expt x n)))
  :rule-classes (:type-prescription :generalize))

;;; Type reasoning should now (v2-8) be a little better at
;;; determining the truth of inequalities and I believe that
;;; the following rule is no longer neccesary.  I keep it
;;; around, but commented out, just in case this is wrong.

#|
;;; I would really like to not need the following rewrite rule.
;;; However, type-reasoning is not particularly good at
;;; determining the truth of inequalities.

(defthm integerp-expt
    (implies (and (integerp x)
                  (<= 0 n))
             (integerp (expt x n))))
|#

;;; Note the form of the conclusion of these rules.  It is
;;; important to write type-prescription rules such that
;;; their conclusions actually specify a type-set.  Due to
;;; the presence of complex numbers and the fact that they
;;; are linearly ordered, (< 0 (expt x n)) does not encode a
;;; type-set.  This makes me unhappy at times.

;;; NOTE: Should the next 3 rules be :linear rules also?
;;; Since they compare to zero, probably not.  On the other hand,
;;; as noted above, type-reasoning is not particularly good at
;;; determining the truth of inequalities.

(defthm expt-type-prescription-non-0-base
  (implies (and (acl2-numberp x)
                (not (equal x 0)))
           (not (equal (expt x n) 0)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-positive-base
  (implies (and (< 0 x)
                (rationalp x))
           (< 0 (expt x n)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-nonnegative-base
  (implies (and (<= 0 x)
                (rationalp x))
           (<= 0 (expt x n)))
  :rule-classes (:type-prescription :generalize))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Since expt will be disabled, I provide some rules to take care
;;; of the ``simple'' cases.


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

;;; This rule conflicts with AMD's preferances.  See |(/ x)|
;;; in mini-theories.lisp

(defthm |(expt x -1)|
  (equal (expt x -1)
	 (/ x)))

(defthm |(equal (expt x n) 0)|
  (implies (and (acl2-numberp x)
                  (integerp n))
             (equal (equal (expt x n) 0)
                    (and (equal x 0)
                         (not (equal n 0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Should we expand (expt (+ c x) d), whenever c and d are
;;; constants?  What about (expt (+ x y) 256)?  Where should we draw
;;; the line?

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

;;; The following will be disabled for gather-exponents.

(defthm |(expt x c)|
  (implies (and (syntaxp (quotep c))
                (integerp c)
                (not (equal c 0)))
           (equal (expt x c)
                  (cond ((< c 0)
                         (* (/ x) (expt x (+ c 1))))
                        (t  ; (< 0 c)
                         (* x (expt x (- c 1)))))))
  :hints (("Goal" :in-theory (disable expt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; In these next two sections we define a couple of rules for
;;; normalizing expressions involving expt.  See top.lisp for a couple
;;; of theories which use some or all of these.

;;; I used to push / inside expt, but I now believe that was
;;; wrong.  This form was in conflict with the desireable
;;; |(expt 1/c n)| below.

(defthm |(expt x (- n))|
    (implies (syntaxp (negative-addends-p n))
             (equal (expt x n)
                    (/ (expt x (- n))))))

(defthm |(expt (/ x) n)|
  (equal (expt (/ x) n)
         (/ (expt x n))))

(defthm |(expt (- (/ x)) n)|
  (equal (expt (- (/ x)) n)
         (/ (expt (- x) n))))

;;; The syntaxp hyps recognize terms of the form 1/c,
;;; where c is a constant.  Note that since x is a
;;; constant, we are NOT introducing a / inside the
;;; expt since ACL2 will ``execute'' (/ x).  For
;;; example, (expt 1/4 n) will get rewritten to
;;; (/ (expt (/ 1/4) n)) and thence to (/ (expt 4 n)).

(defthm |(expt 1/c n)|
    (implies (and (syntaxp (quotep x))
                  (syntaxp (rationalp (unquote x)))
                  (syntaxp (not (integerp (unquote x))))
                  (syntaxp (equal (numerator x) 1)))
             (equal (expt x n)
                    (/ (expt (/ x) n)))))

(defthm |(expt (- x) n)|
    (implies (and (syntaxp (negative-addends-p x))
                  (integerp n))
             (equal (expt x n)
                    (if (evenp n)
                        (expt (- x) n)
                      (- (expt (- x) n)))))
  :hints (("Goal" :use ((:instance expt-negative-base-even-exponent
                                   (i n)
                                   (r x))
                        (:instance expt-negative-base-odd-exponent
                                   (i n)
                                   (r x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Two is an important number.

;;; 2 is an important number in hardware and software proofs and
;;; we treat it specially here.  The basic idea is to recognize
;;; powers of 2 inside an expt, and to rewrite appropriately.
;;; For example, we transform (expt 16 n) to (expt 2 (* 4 n)).
;;; Note that in combination with |(expt 1/c n)| we will also
;;; catch terms such as (expt 1/4 n).

(defun power-of-2-helper (x)
  (declare (xargs :mode :program))
  (cond ((not (integerp x))
         0)
        ((<= x 2)
         1)
        (t
         (1+ (power-of-2-helper (/ x 2))))))

(defun power-of-2 (x)
  (declare (xargs :mode :program))
  ;; if x is a power of 2 (other than 2 itself), we return its
  ;; ``exponent''; Egg., the exponent of 4 is 2 and that of
  ;; 32 is 5.  We make no claims about the value returned
  ;; otherwise.
  (list (cons 'c (kwote (power-of-2-helper (unquote x))))))

(defthm |(expt 2^i n)|
    ;; I should document this rule better.
    (implies (and (integerp n)
                  (syntaxp (quotep x))
                  (syntaxp (not (equal x ''1)))
                  (syntaxp (not (equal x ''2)))
                  (bind-free (power-of-2 x) (c))
                  (integerp c)
                  (equal (expt 2 c) x))
             (equal (expt x n)
                    (expt 2 (* c n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(expt (* x y) n)|
  (equal (expt (* x y) n)
         (* (expt x n)
            (expt y n))))

(defthm |(expt (expt x m) n)|
  (implies (and (integerp m)
                (integerp n))
           (equal (expt (expt x m) n)
                  (expt x (* m n)))))


(defthm |(expt x (+ m n))|
  (implies (and (integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (if (equal (+ m n) 0)
		      1
		      (* (expt x m)
			 (expt x n))))))
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
(defthm |(expt x (+ m n)) non-zero x|
  (implies (and (not (equal 0 x))
		(acl2-numberp x)
		(integerp m)
		(integerp n))
	   (equal (expt x (+ m n))
		  (* (expt x m)
		     (expt x n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We take care of a few of the simple, and exceptional, cases
;;; here, rather than worry about them elsewhere.

(defthm |(equal (/ x) 0)|
  (implies (acl2-numberp x)
           (equal (equal (/ x) 0)
                  (equal x 0))))

(defthm |(equal (- x) 0)|
    (implies (and (syntaxp (negative-addends-p x))
                  (acl2-numberp x))
             (equal (equal x 0)
                    (equal (- x) 0))))

(defthm |(equal (/ x) (/ y))|
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (equal (/ x) (/ y))
                  (equal x y))))

(defthm |(equal (- x) (- y))|
    (implies (and (syntaxp (negative-addends-p x))
                  (syntaxp (negative-addends-p y))
                  (acl2-numberp x)
                  (acl2-numberp y))
             (equal (equal x y)
                    (equal (- x) (- y)))))

(defthm |(< (/ x) 0)|
  (implies (rationalp x)
	   (equal (< (/ x) 0)
		  (< x 0))))

(defthm |(< 0 (/ x))|
  (implies (rationalp x)
	   (equal (< 0 (/ x))
		  (< 0 x))))

(defthm |(< (- x) 0)|
    (implies (syntaxp (negative-addends-p x))
             (equal (< x 0)
                    (< 0 (- x)))))

(defthm |(< 0 (- x))|
    (implies (syntaxp (negative-addends-p x))
             (equal (< 0 x)
                    (< (- x) 0))))

(defthm |(< (- x) (- y))|
    (implies (and (syntaxp (negative-addends-p x))
                  (syntaxp (negative-addends-p y)))
             (equal (< x y)
                    (< (- y) (- x)))))

(defthm |(equal (+ c x) d)|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (acl2-numberp d)
                (syntaxp (not (equal (fn-symb x) 'BINARY-+))))
           (equal (equal (+ c x) d)
                  (equal x (- d c)))))

(defthm |(equal (+ c x y) d)|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (syntaxp (not (equal (unquote d) 0)))
                (acl2-numberp d))
           (equal (equal (+ c x y) d)
                  (equal (+ x y) (- d c)))))

(defthm |(equal (+ c x) (+ d y))|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (acl2-numberp d)
                (acl2-numberp y)
                (< c d))
           (equal (equal (+ c x) (+ d y))
                  (equal x (+ (- d c) y)))))

(defthm |(equal (+ d x) (+ c y))|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (acl2-numberp d)
                (acl2-numberp y)
                (< c d))
           (equal (equal (+ d x) (+ c y))
                  (equal (+ (- d c) x) y))))

(local
 (defthm equal-to-iff
   (equal (equal (< a b)
                 (< x y))
          (iff (< a b)
               (< x y)))))

(defthm |(< (+ c x) d)|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (acl2-numberp d)
                (syntaxp (not (equal (fn-symb x) 'BINARY-+))))
           (equal (< (+ c x) d)
                  (< x (- d c)))))

(defthm |(< (+ c x y) d)|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (syntaxp (not (equal (unquote d) 0)))
                (acl2-numberp d))
           (equal (< (+ c x y) d)
                  (< (+ x y) (- d c)))))

(defthm |(< (+ c x) (+ d y))|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (acl2-numberp d)
                (acl2-numberp y)
                (< c d))
           (equal (< (+ c x) (+ d y))
                  (< x (+ (- d c) y)))))

(defthm |(< (+ d x) (+ c y))|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (acl2-numberp d)
                (acl2-numberp y)
                (< c d))
           (equal (< (+ d x) (+ c y))
                  (< (+ (- d c) x) y))))

(defthm |(< d (+ c x))|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (acl2-numberp d)
                (syntaxp (not (equal (fn-symb x) 'BINARY-+))))
           (equal (< d (+ c x))
                  (< (- d c) x))))

(defthm |(< d (+ c x y))|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
                (acl2-numberp x)
                (syntaxp (quotep d))
                (syntaxp (not (equal (unquote d) 0)))
                (acl2-numberp d))
           (equal (< d (+ c x y))
                  (< (- d c) (+ x y)))))

(defthm |(equal (* x y) 0)|
  (implies (and (rationalp x)
                (rationalp y))
           (equal (equal (* x y) 0)
                  (or (equal x 0)
                      (equal y 0)))))

(defthm |(< (* x y) 0)|
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (rationalp x)
                  (rationalp y))
             (equal (< (* x y) 0)
                    (cond ((equal x 0)
                           nil)
                          ((equal y 0)
                           nil)
                          ((< x 0)
                           (< 0 y))
                          ((< 0 x)
                           (< y 0))))))

(defthm |(< 0 (* x y))|
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (rationalp x)
                  (rationalp y))
             (equal (< 0 (* x y))
                    (cond ((equal x 0)
                           nil)
                          ((equal y 0)
                           nil)
                          ((< x 0)
                           (< y 0))
                          ((< 0 x)
                           (< 0 y))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; !!! This next batch of lemmatta should be eliminated by my
;;; free-var-hack. !!!

;;; We conclude this book with two sets of linear rules for expt.
;;; The first set consists of rules which are both linear and
;;; rewrite rules.  Both types are needed because of the free
;;; variable problem.  The second set are linear rules only.

(defthm expt-x->-x
  (implies (and (< 1 x)
		(< 1 n)
		(rationalp x)
		(integerp n))
	   (< x (expt x n)))
  :rule-classes (:rewrite :linear))

(defthm expt-x->=-x
  (implies (and (<= 1 x)
		(< 1 n)
		(rationalp x)
		(integerp n))
	   (<= x (expt x n)))
  :rule-classes (:rewrite :linear))

(defthm expt-is-increasing-for-base->-1
  (implies (and (< m n)
		(< 1 x)
		(integerp m)
		(integerp n)
		(rationalp x))
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
                (rationalp x))
           (< (expt x n)
              (expt x m)))
  :rule-classes ((:rewrite)
                 (:linear :match-free :once)))

(defthm expt-is-weakly-increasing-for-base->-1
  (implies (and (<= m n)
                (<= 1 x)
                (integerp m)
                (integerp n)
                (rationalp x))
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
                (rationalp x))
           (<= (expt x n)
               (expt x m)))
  :rule-classes ((:rewrite)
                 (:linear :match-free :once)))

;; Should these be rewrite rules also? Probably not.

(defthm expt->-1-one
  (implies (and (< 1 x)
		(< 0 n)
		(rationalp x)
		(integerp n))
	   (< 1 (expt x n)))
  :rule-classes :linear)

(defthm expt->-1-two
  (implies (and (< 0 x)
		(< x 1)
		(< n 0)
		(rationalp x)
		(integerp n))
	   (< 1 (expt x n)))
  :rule-classes :linear)

(defthm expt-<-1-one
  (implies (and (< 0 x)
		(< x 1)
		(< 0 n)
		(rationalp x)
		(integerp n))
	   (< (expt x n) 1))
  :rule-classes :linear)

(defthm expt-<-1-two
  (implies (and (< 1 x)
		(< n 0)
		(rationalp x)
		(integerp n))
	   (< (expt x n) 1))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Finally, a few if normalization rules.

(defthm |(+ (if a b c) x)|
  (equal (+ (if a b c) x)
	 (if a (+ b x) (+ c x))))

(defthm |(+ x (if a b c))|
  (equal (+ x (if a b c))
	 (if a (+ x b) (+ x c))))

(defthm |(- (if a b c))|
  (equal (- (if a b c))
	 (if a (- b) (- c))))

(defthm |(* (if a b c) x)|
  (equal (* (if a b c) x)
	 (if a (* b x) (* c x))))

(defthm |(* x (if a b c))|
  (equal (* x (if a b c))
	 (if a (* x b) (* x c))))

(defthm |(/ (if a b c))|
  (equal (/ (if a b c))
	 (if a (/ b) (/ c))))

(defthm |(expt (if a b c) x)|
  (equal (expt (if a b c) x)
	 (if a (expt b x) (expt c x))))

(defthm |(expt x (if a b c))|
  (equal (expt x (if a b c))
	 (if a (expt x b) (expt x c))))

(defthm |(equal x (if a b c))|
  (equal (equal x (if a b c))
	 (if a (equal x b) (equal x c))))

(defthm |(equal (if a b c) x)|
  (equal (equal (if a b c) x)
	 (if a (equal b x) (equal c x))))

(defthm |(< x (if a b c))|
  (equal (< x (if a b c))
	 (if a (< x b) (< x c))))

(defthm |(< (if a b c) x)|
  (equal (< (if a b c) x)
	 (if a (< b x) (< c x))))
