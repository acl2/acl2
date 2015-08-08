(in-package "ACL2")

;; This book establishes some facts about real differentiable
;; functions.  It shows that differentiable functions are continuous.
;; Also, it proves Rolle's theorem and from that the mean value
;; theorem.

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "continuity")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; The theorem i-close-reflexive in nsa.lisp forces ACL2 to back-chain
;; on acl2-numberp x.  But, there's probably no need for that, since
;; we only use i-close in hypotheses when x is a number.  So, it
;; should be safe the acl2-numberp hypothesis.  We do that here.  This
;; "improvement" should probably be migrated to axioms.lisp.

(local
 (defthm i-close-reflexive-force
   (implies (force (acl2-numberp x))
	    (i-close x x))
   :hints (("Goal" :use (:instance i-close-reflexive)))))

;; First, we introduce rdfn - a Real Differentiable FunctioN of a
;; single argument.  It is assumed to return standard values for
;; standard arguments, and to satisfy the differentiability criterion.

(encapsulate
 ((rdfn (x) t)
  (rdfn-domain () t))

 ;; Our witness continuous function is the identity function.

 (local (defun rdfn (x) (realfix x)))
 (local (defun rdfn-domain () (interval 0 1)))

 ;; The interval really is an interval

 (defthm intervalp-rdfn-domain
     (interval-p (rdfn-domain))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is real

 (defthm rdfn-domain-real
     (implies (inside-interval-p x (rdfn-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm rdfn-domain-non-trivial
     (or (null (interval-left-endpoint (rdfn-domain)))
	 (null (interval-right-endpoint (rdfn-domain)))
	 (< (interval-left-endpoint (rdfn-domain))
	    (interval-right-endpoint (rdfn-domain))))
   :rule-classes nil)

 ;; The function returns real values (even for improper arguments).

 (defthm rdfn-real
     (realp (rdfn x))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y1 and y2 are two arbitrary reals
 ;; close to x, then (rdfn(x)-rdfn(y1))/(x-y1) is close to
 ;; (rdfn(x)-rdfn(y2))/(x-y2).  Also, (rdfn(x)-rdfn(y1))/(x-y1) is
 ;; limited.  What this means is that the standard-part of that is a
 ;; standard number, and we'll call that the derivative of rdfn at x.

 (defthm rdfn-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-domain))
		 (inside-interval-p y1 (rdfn-domain))
		 (inside-interval-p y2 (rdfn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (rdfn x) (rdfn y1)) (- x y1)))
		 (i-close (/ (- (rdfn x) (rdfn y1)) (- x y1))
			  (/ (- (rdfn x) (rdfn y2)) (- x y2))))))

 )

;; We want to prove the mean-value theorem.  This states that there is
;; a point x in [a,b] so that the derivitate of rdfn at x is equal to
;; the slope of the line from (a, (rdfn a)) to (b, (rdfn b)).  To
;; prove this, we first establish Rolle's theorem.  This is a special
;; case of the mean-value theorem when (rdfn a) = (rdfn b) = 0.  In
;; this case, we find an x in [a,b] so that the derivative of rdfn at
;; x is 0.  This point x is easy to find.  Simply look for the maximum
;; value of rdfn on [a,b].  If the maximum point is either a or b,
;; then that means rdfn is identically zero, so the derivative at any
;; point in (a,b) must be zero.  Otherwise, we're talking about the
;; derivative of a local maximum (or minimum), and that is clearly
;; zero since the differentials at x swap signs coming from the left
;; and right.

;; The first major theorem is that rdfn is also continuous.

(encapsulate
 ()

 ;; Here is a simple lemma.  If y is small and x/y is limited, then x
 ;; must be small (actually "smaller" than y).

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (realp y)
		  (i-small y)
		  (not (= y 0))
		  (i-limited (/ x y)))
	     (i-small x))
    :hints (("Goal"
	     :use ((:instance limited*large->large (y (/ y))))
	     :in-theory (disable limited*large->large)))))


 ;; Where this lemma comes in handy is that we know that ((rdfn x) -
 ;; (rdfn y))/(x - y) is limited for y close to x.  From that, we can
 ;; conclude that (rdfn x) is close to (rdfn y) -- i.e., that rdfn is
 ;; continuous.

 (defthm rdfn-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-domain))
		 (i-close x y)
		 (inside-interval-p y (rdfn-domain)))
	    (i-close (rdfn x) (rdfn y)))
   :hints (("Goal"
	    :use ((:instance rdfn-differentiable (y1 y) (y2 y))
		  (:instance lemma-1
			     (x (+ (rdfn x) (- (rdfn y))))
			     (y (+ x (- y)))))
	    :in-theory (enable-disable (i-close)
				       (rdfn-differentiable
					lemma-1)))))
 )

;; So now, we want to find the maximum of rdfn.  We do this by
;; defining the functions of find-max-x from the rcfn case.

(defun find-max-rdfn-x-n (a max-x i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (> (rdfn (+ a (* i eps))) (rdfn max-x))
	  (find-max-rdfn-x-n a (+ a (* i eps)) (1+ i) n eps)
	(find-max-rdfn-x-n a max-x (1+ i) n eps))
    max-x))

;; To use defun-std, we need to establish that the max-x-n function is
;; limited.  We can do that by functional instantiation.

(defthm find-max-rdfn-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-max-rdfn-x-n a a
				    0 (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b)))))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x-n-limited
				       (find-max-rcfn-x-n find-max-rdfn-x-n)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable find-max-rcfn-x-n-limited))
	  ("Subgoal 2"
	   :use ((:instance rdfn-domain-non-trivial))
	   )))

;; And so, we can use defun-std to get the maximum of rdfn on [a,b].

(defun-std find-max-rdfn-x (a b)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-max-rdfn-x-n a
					a
					0
					(i-large-integer)
					(/ (- b a) (i-large-integer))))
    0))

;; Of course, we have to prove that it *is* the maximum, and we can do
;; that by functional instantiation.

(defthm find-max-rdfn-is-maximum
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rdfn x) (rdfn (find-max-rdfn-x a b))))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-is-maximum
				       (find-max-rcfn-x-n find-max-rdfn-x-n)
				       (find-max-rcfn-x find-max-rdfn-x)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable find-max-rcfn-is-maximum))))

;; We also need to prove that the maximum value is in the range
;; [a,b].  First, we find that it is >= a....again, by functional
;; instantiation.

(defthm find-max-rdfn-x->=-a
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= a (find-max-rdfn-x a b)))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x->=-a
				       (find-max-rcfn-x-n find-max-rdfn-x-n)
				       (find-max-rcfn-x find-max-rdfn-x)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable find-max-rcfn-x->=-a))))

;; And it's <= b....by functional instantiation.

(defthm find-max-rdfn-x-<=-b
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= (find-max-rdfn-x a b) b))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x-<=-b
				       (find-max-rcfn-x-n find-max-rdfn-x-n)
				       (find-max-rcfn-x find-max-rdfn-x)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable find-max-rcfn-x-<=-b))))

;; Arrrgh!  Now we have to do it all over again for minimums!  Here's
;; the definition of the minimum function.

(defun find-min-rdfn-x-n (a min-x i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (< (rdfn (+ a (* i eps))) (rdfn min-x))
	  (find-min-rdfn-x-n a (+ a (* i eps)) (1+ i) n eps)
	(find-min-rdfn-x-n a min-x (1+ i) n eps))
    min-x))

;; Of course, it's limited.

(defthm find-min-rdfn-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-min-rdfn-x-n a a
				    0 (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b)))))
  :hints (("Goal"
	   :use ((:functional-instance find-min-rcfn-x-n-limited
				       (find-min-rcfn-x-n find-min-rdfn-x-n)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable find-min-rcfn-x-n-limited))))

;; And so we can use defun-std to get the "real" minimum value.

(defun-std find-min-rdfn-x (a b)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-min-rdfn-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))))
    0))

;; And we can prove that it is the minimum, by functional instantiation.

(defthm find-min-rdfn-is-minimum
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rdfn (find-min-rdfn-x a b)) (rdfn x)))
  :hints (("Goal"
	   :use ((:functional-instance find-min-rcfn-is-minimum
				       (find-min-rcfn-x-n find-min-rdfn-x-n)
				       (find-min-rcfn-x find-min-rdfn-x)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable find-min-rcfn-is-minimum))))

;; And it's >= a.....

(defthm find-min-rdfn-x->=-a
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= a (find-min-rdfn-x a b)))
  :hints (("Goal"
	   :use ((:functional-instance find-min-rcfn-x->=-a
				       (find-min-rcfn-x-n find-min-rdfn-x-n)
				       (find-min-rcfn-x find-min-rdfn-x)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable find-min-rcfn-x->=-a))))

;; ....and <= b.

(defthm find-min-rdfn-x-<=-b
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= (find-min-rdfn-x a b) b))
  :hints (("Goal"
	   :use ((:functional-instance find-min-rcfn-x-<=-b
				       (find-min-rcfn-x-n find-min-rdfn-x-n)
				       (find-min-rcfn-x find-min-rdfn-x)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable find-min-rcfn-x-<=-b))))

;; Now, here's an important theorem.  If the minimum is equal to the
;; maximum, then rdfn is constant throughout [a,b].  We prove this for
;; arbitrary continuous functions.

(defthm min=max->-constant-rcfn
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(realp x)
		(< a b)
		(<= a x)
		(<= x b)
		(= (rcfn (find-min-rcfn-x a b))
		   (rcfn (find-max-rcfn-x a b))))
	   (equal (equal (rcfn (find-min-rcfn-x a b)) (rcfn x)) t))
  :hints (("Goal"
	   :use ((:instance find-min-rcfn-is-minimum)
		 (:instance find-max-rcfn-is-maximum))
	   :in-theory (disable find-min-rcfn-is-minimum
			       find-max-rcfn-is-maximum))))

;; So of course it's true for rdfn, our differentiable (and hence
;; continuous!) function.

(defthm min=max->-constant-rdfn
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(realp x)
		(< a b)
		(<= a x)
		(<= x b)
		(= (rdfn (find-min-rdfn-x a b))
		   (rdfn (find-max-rdfn-x a b))))
	   (equal (equal (rdfn (find-min-rdfn-x a b)) (rdfn x)) t))
  :hints (("Goal"
	   :use ((:functional-instance min=max->-constant-rcfn
				       (find-min-rcfn-x-n find-min-rdfn-x-n)
				       (find-min-rcfn-x find-min-rdfn-x)
				       (find-max-rcfn-x-n find-max-rdfn-x-n)
				       (find-max-rcfn-x find-max-rdfn-x)
				       (rcfn rdfn)
				       (rcfn-domain rdfn-domain)))
	   :in-theory (disable min=max->-constant-rcfn))))

;; Now, let's define the differential of rdfn.

(encapsulate
 ( ((differential-rdfn * *) => * ) )

 (local
  (defun differential-rdfn (x eps)
    (/ (- (rdfn (+ x eps)) (rdfn x)) eps)))

 (defthm differential-rdfn-definition
   (implies (and (force (inside-interval-p x (rdfn-domain)))
		 (force (inside-interval-p (+ x eps) (rdfn-domain))))
	    (equal (differential-rdfn x eps)
		   (/ (- (rdfn (+ x eps)) (rdfn x)) eps)))))

;; An obvious fact is that the differential is a real number.

(defthm realp-differential-rdfn
  (implies (and (inside-interval-p x (rdfn-domain))
		(inside-interval-p (+ x eps) (rdfn-domain))
		(realp eps))
	   (realp (differential-rdfn x eps))))

;; Differential-rdfn is limited when x and eps are in the right range

(defthm differential-rdfn-limited
    (implies (and (standardp x)
		  (inside-interval-p x (rdfn-domain))
		  (inside-interval-p (+ x eps) (rdfn-domain))
		  (i-small eps))
	     (i-limited (differential-rdfn x eps)))
  :hints (("Goal"
	   :use ((:instance rdfn-differentiable
			    (x x)
			    (y1 (+ x eps))
			    (y2 (+ x eps)))
		 (:instance i-close-to-small-sum))
	   :in-theory (disable rdfn-differentiable i-close-to-small-sum))))

(in-theory (disable find-min-rdfn-x find-max-rdfn-x))

;; We need to show that when a and b are in the domain of rdfn,
;; so are (a+b)/2 and (a+b)/2 + eps.  This follows, because
;; the domain is an interval (and we're assuming eps is small).
(defthm midpoint-in-interval
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain)))
	   (inside-interval-p (+ (* 1/2 a) (* 1/2 b))
			      (rdfn-domain)))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (+ (* 1/2 a) (* 1/2 b)))
			    (interval (rdfn-domain)))
		 (:instance inside-interval-p-squeeze
			    (a b)
			    (b a)
			    (c (+ (* 1/2 a) (* 1/2 b)))
			    (interval (rdfn-domain))))
	   :in-theory (disable inside-interval-p-squeeze))))

(defthm midpoint+eps-in-interval-1
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(<= 0 eps)
		(realp eps)
		(< eps (+ (- (* 1/2 a)) (* 1/2 b))))
	   (inside-interval-p (+ eps (* 1/2 a) (* 1/2 b))
			      (rdfn-domain)))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (+ eps (* 1/2 a) (* 1/2 b)))
			    (interval (rdfn-domain)))
		 (:instance inside-interval-p-squeeze
			    (a b)
			    (b a)
			    (c (+ eps (* 1/2 a) (* 1/2 b)))
			    (interval (rdfn-domain))))
	   :in-theory (disable inside-interval-p-squeeze))))

(defthm midpoint+eps-in-interval-2
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(< eps 0)
		(realp eps)
		(< (- eps) (+ (- (* 1/2 a)) (* 1/2 b))))
	   (inside-interval-p (+ eps (* 1/2 a) (* 1/2 b))
			      (rdfn-domain)))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (+ eps (* 1/2 a) (* 1/2 b)))
			    (interval (rdfn-domain)))
		 (:instance inside-interval-p-squeeze
			    (a b)
			    (b a)
			    (c (+ eps (* 1/2 a) (* 1/2 b)))
			    (interval (rdfn-domain))))
	   :in-theory (disable inside-interval-p-squeeze))))

(defthm inner-point-in-interval
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(realp x)
		(< a x)
		(< x b))
	   (inside-interval-p x (rdfn-domain)))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c x)
			    (interval (rdfn-domain))))
	   :in-theory (disable inside-interval-p-squeeze))))

(defthm inner-point+eps-in-interval
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(realp x)
		(realp eps)
		(< 0 eps)
		(< a (+ (- eps) x))
		(< (+ eps x) b))
	   (and (inside-interval-p x (rdfn-domain))
		(inside-interval-p (+ eps x) (rdfn-domain))
		(inside-interval-p (+ (- eps) x) (rdfn-domain))))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c x)
			    (interval (rdfn-domain)))
		 (:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (+ eps x))
			    (interval (rdfn-domain)))
		 (:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (+ (- eps) x))
			    (interval (rdfn-domain))))
	   :in-theory (disable inside-interval-p-squeeze))))

;; OK now, if the minimum value of rdfn on [a,b] is equal to its
;; maximum value, then the differential of the midpoint of [a,b]
;; (actually of any point in (a,b)) must be zero.  This is because the
;; function is constant.

(defthm rolles-theorem-lemma-1
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(realp eps)
		(< (abs eps) (/ (- b a) 2))
		(= (rdfn (find-min-rdfn-x a b))
		   (rdfn (find-max-rdfn-x a b))))
	   (equal (differential-rdfn (/ (+ a b) 2) eps) 0))
  :hints (("Goal"
	   :use ((:instance min=max->-constant-rdfn
			    (x (+ (* 1/2 a) (* 1/2 b))))
		 (:instance min=max->-constant-rdfn
			    (x (+ eps (* 1/2 a) (* 1/2 b)))))
	   :in-theory (disable min=max->-constant-rdfn))))

;; Otherwise, if max-x is in (a,b), then it's derivative must be
;; zero.  This follows because for a positive eps, the differential of
;; max-x using eps is non-positive -- since rdfn at x+eps is <= rdfn
;; at x, since x is a maximum.  I.e., rdfn is falling from x to x+eps.

(defthm rolles-theorem-lemma-2a
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(realp eps)
		(< 0 eps)
		(< a (- (find-max-rdfn-x a b) eps))
		(< (+ (find-max-rdfn-x a b) eps) b))
	   (<= (differential-rdfn (find-max-rdfn-x a b) eps) 0))
  :hints (("Goal"
	   :use ((:instance inner-point+eps-in-interval
			    (x (find-max-rdfn-x a b))))
	   :in-theory (disable inner-point+eps-in-interval)))
  )

;; Similarly, for a negative eps, rdfn is rising from x+eps to x, so
;; the eps-differential of x is non-negative.

(defthm rolles-theorem-lemma-2b
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(realp eps)
		(< 0 eps)
		(< a (- (find-max-rdfn-x a b) eps))
		(< (+ (find-max-rdfn-x a b) eps) b))
	   (<= 0 (differential-rdfn (find-max-rdfn-x a b) (- eps))))
  :hints (("Goal"
	   :use ((:instance inner-point+eps-in-interval
			    (x (find-max-rdfn-x a b))))
	   :in-theory (disable inner-point+eps-in-interval)))
  )

;; Of course, the same claims follow for an internal minimum, min-x.
;; For a positive epsilon, the differential is non-positive.

(defthm rolles-theorem-lemma-2c
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(realp eps)
		(< 0 eps)
		(< a (- (find-min-rdfn-x a b) eps))
		(< (+ (find-min-rdfn-x a b) eps) b))
	   (<= 0 (differential-rdfn (find-min-rdfn-x a b) eps)))
  :hints (("Goal"
	   :use ((:instance inner-point+eps-in-interval
			    (x (find-min-rdfn-x a b))))
	   :in-theory (disable inner-point+eps-in-interval)))
  )

;; And for a negative epsilon it is non-negative.

(defthm rolles-theorem-lemma-2d
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(realp eps)
		(< 0 eps)
		(< a (- (find-min-rdfn-x a b) eps))
		(< (+ (find-min-rdfn-x a b) eps) b))
	   (<= (differential-rdfn (find-min-rdfn-x a b) (- eps)) 0))
    :hints (("Goal"
	   :use ((:instance inner-point+eps-in-interval
			    (x (find-min-rdfn-x a b))))
	   :in-theory (disable inner-point+eps-in-interval)))
    )

;; This is clearly something that belongs in nsa.lisp.  The
;; standard-part of a small number is zero.

(local
 (defthm standard-part-of-small
   (implies (i-small eps)
	    (equal (standard-part eps) 0))
   :hints (("Goal"
	    :in-theory (enable i-small)))))

;; Now, if a standard x is in (a,b) and eps is small, x-eps is in
;; (a,b).  This is only true because x and a are standard!

(local
 (defthm small-squeeze-standard-1
   (implies (and (realp a) (standardp a)
		 (realp x) (standardp x)
		 (< a x)
		 (realp eps)
		 (< 0 eps)
		 (i-small eps))
	    (< a (- x eps)))
   :hints (("Goal"
	    :use ((:instance standard-part-<-2 (x a) (y (- x eps))))))))

;; Similarly, x+eps is in (a,b).

(local
 (defthm small-squeeze-standard-2
   (implies (and (realp b) (standardp b)
		 (realp x) (standardp x)
		 (< x b)
		 (realp eps)
		 (< 0 eps)
		 (i-small eps))
	    (< (+ x eps) b))
   :hints (("Goal"
	    :use ((:instance standard-part-<-2 (x (+ x eps)) (y b)))))))

;; We're particularly interested in when the internal point x is max-x
;; or min-x.  So, we establish immediately that these points are
;; standard.

(defthm standard-find-min-max-rdfn
  (implies (and (realp a) (standardp a)
		(realp b) (standardp b))
	   (and (standardp (find-min-rdfn-x a b))
		(standardp (find-max-rdfn-x a b))))
  :hints (("Goal"
	   :in-theory (enable find-min-rdfn-x find-max-rdfn-x))))

;; So what this means is that if max-x is in (a,b), so are max-x+eps
;; and max-x-eps.

(defthm rolles-theorem-lemma-2e
  (implies (and (inside-interval-p a (rdfn-domain)) (standardp a)
		(inside-interval-p b (rdfn-domain)) (standardp b)
		(< a b)
		(< a (find-max-rdfn-x a b))
		(< (find-max-rdfn-x a b) b)
		(realp eps)
		(< 0 eps)
		(i-small eps))
	   (and (< a (- (find-max-rdfn-x a b) eps))
		(< (+ (find-max-rdfn-x a b) eps) b)))
  :hints (("Goal"
	   :use ((:instance small-squeeze-standard-1
			    (x (find-max-rdfn-x a b)))
		 (:instance small-squeeze-standard-2
			    (x (find-max-rdfn-x a b))))
	   :in-theory (disable small-squeeze-standard-1
			       small-squeeze-standard-2))))

;; And the same holds for min-x.

(defthm rolles-theorem-lemma-2f
  (implies (and (inside-interval-p a (rdfn-domain)) (standardp a)
		(inside-interval-p b (rdfn-domain)) (standardp b)
		(< a b)
		(< a (find-min-rdfn-x a b))
		(< (find-min-rdfn-x a b) b)
		(realp eps)
		(< 0 eps)
		(i-small eps))
	   (and (< a (- (find-min-rdfn-x a b) eps))
		(< (+ (find-min-rdfn-x a b) eps) b)))
  :hints (("Goal"
	   :use ((:instance small-squeeze-standard-1
			    (x (find-min-rdfn-x a b)))
		 (:instance small-squeeze-standard-2
			    (x (find-min-rdfn-x a b))))
	   :in-theory (disable small-squeeze-standard-1
			       small-squeeze-standard-2))))

;; Now, we define the critical point of rdfn on [a,b].  If min-x is
;; equal to max-x, then we arbitrarily pick the midpoint of a and b,
;; since that'll be an interior point.  Otherwise, we pick whichever
;; of min-x or max-x is interior.

(defun rolles-critical-point (a b)
  (if (equal (rdfn (find-min-rdfn-x a b)) (rdfn (find-max-rdfn-x a b)))
      (/ (+ a b) 2)
    (if (equal (rdfn (find-min-rdfn-x a b)) (rdfn a))
	(find-max-rdfn-x a b)
      (find-min-rdfn-x a b))))

;; OK now, if rdfn achieves its minimum at a, then the maximum is an
;; interior point.

(defthm rolles-theorem-lemma-3a
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(= (rdfn a) (rdfn b))
		(not (= (rdfn (find-min-rdfn-x a b))
			(rdfn (find-max-rdfn-x a b))))
		(= (rdfn (find-min-rdfn-x a b)) (rdfn a)))
	   (and (< a (find-max-rdfn-x a b))
		(< (find-max-rdfn-x a b) b)))
  :hints (("Goal"
	   :use ((:instance find-max-rdfn-x->=-a)
		 (:instance find-max-rdfn-x-<=-b))
	   :in-theory (disable find-max-rdfn-x->=-a
			       find-max-rdfn-x-<=-b))))

;; If rdfn does not achieve its minimum at a, then the minimum itself
;; is an interior point.

(defthm rolles-theorem-lemma-3b
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(< a b)
		(= (rdfn a) (rdfn b))
		(not (= (rdfn (find-min-rdfn-x a b))
			(rdfn (find-max-rdfn-x a b))))
		(not (= (rdfn (find-min-rdfn-x a b)) (rdfn a))))
	   (and (< a (find-min-rdfn-x a b))
		(< (find-min-rdfn-x a b) b)))
  :hints (("Goal"
	   :use ((:instance find-min-rdfn-x->=-a)
		 (:instance find-min-rdfn-x-<=-b))
	   :in-theory (disable find-min-rdfn-x->=-a
			       find-min-rdfn-x-<=-b))))

;; If eps is a small number, then |eps| < midpoint(a,b).  This key
;; fact means that the differentials at midpoint(a,b) are using
;; numbers inside the range (a,b).

(defthm rolles-theorem-lemma-4
  (implies (and (inside-interval-p a (rdfn-domain)) (standardp a)
		(inside-interval-p b (rdfn-domain)) (standardp b)
		(< a b)
		(realp eps)
		(i-small eps))
	   (< (abs eps) (* (+ b (- a)) 1/2)))
  :hints (("Goal"
	   :use ((:instance small-<-non-small
			    (x eps)
			    (y (* (+ b (- a)) 1/2)))
		 (:instance standard-small-is-zero
			    (x (* (+ b (- a)) 1/2))))
	   :in-theory (disable small-<-non-small))))

(in-theory (disable differential-rdfn-definition))

;; This (or something like it) is another theorem that should be in
;; nsa.lisp.

(local
 (defthm small+limited-close
   (implies (and (i-limited x)
		 (i-small eps))
	    (i-close x (+ eps x)))
   :hints (("Goal" :in-theory (enable nsa-theory)))))

;; We now take a detour to reason about interval boundaries.  When a standard
;; x belongs to a standard interval, it does not necessarily follow that
;; x+eps also belongs to the interval.  But if it does not, then x must be
;; the right endpoint.  Similarly for x-eps.

(defthm non-standard-between-standards
    (implies (and (realp x) (standardp x)
		  (realp b) (standardp b)
		  (< x b)
		  (realp x+eps)
		  (i-close x x+eps)
		  (< x x+eps))
	     (< x+eps b))
  :hints (("Goal"
	   :use ((:instance close-x-y->same-standard-part
			    (x x)
			    (y b))
		 (:instance small-if-<-small
			    (x (- x+eps x))
			    (y (- b x)))
		 (:instance i-close-to-small-sum
			    (x x)
			    (eps (- b x)))
		 (:instance i-small-uminus
			    (x (- x+eps x)))
		 (:instance i-small-uminus
			    (x (- b x))))
	   :in-theory (enable-disable (i-close)
				      (close-x-y->same-standard-part
				       small-if-<-small
				       i-close-to-small-sum
				       i-close-small
				       i-close-small-2
				       i-small-uminus))))
  )

(defthm non-standard-between-standards-2
    (implies (and (realp a) (standardp a)
		  (realp x) (standardp x)
		  (< a x)
		  (realp x-eps)
		  (i-close x x-eps)
		  (< x-eps x))
	     (< a x-eps))
  :hints (("Goal"
	   :use ((:instance close-x-y->same-standard-part
			    (x a)
			    (y x))
		 (:instance small-if-<-small
			    (x (- x-eps x))
			    (y (- x a)))
		 (:instance i-close-to-small-sum
			    (x x)
			    (eps (- a x)))
		 (:instance i-small-uminus
			    (x (- x-eps x)))
		 (:instance i-small-uminus
			    (x (- x a))))
	   :in-theory (enable-disable (i-close)
				      (close-x-y->same-standard-part
				       small-if-<-small
				       i-close-to-small-sum
				       i-close-small
				       i-close-small-2
				       i-small-uminus))))
  )

(defthm inside-interval-x+eps
    (implies (and (inside-interval-p x interval)
		  (weak-interval-p interval)
		  (standardp x)
		  (standardp interval)
		  (realp eps)
		  (< 0 eps)
		  (i-small eps)
		  (not (equal (interval-right-endpoint interval) x)))
	     (inside-interval-p (+ x eps) interval))
  :hints (("Goal"
	   :use ((:instance non-standard-between-standards
			    (x x)
			    (x+eps (+ x eps))
			    (b (interval-right-endpoint interval))
			    )
		 (:instance standard-right-endpoint))
	   :in-theory (enable-disable (interval-definition-theory)
				      (standard-right-endpoint))
	   ))
  :rule-classes nil)

(defthm inside-interval-x-eps
    (implies (and (inside-interval-p x interval)
		  (weak-interval-p interval)
		  (standardp x)
		  (standardp interval)
		  (realp eps)
		  (< eps 0)
		  (i-small eps)
		  (not (equal (interval-left-endpoint interval) x)))
	     (inside-interval-p (+ x eps) interval))
  :hints (("Goal"
	   :use ((:instance non-standard-between-standards-2
			    (x x)
			    (x-eps (+ x eps))
			    (a (interval-left-endpoint interval))
			    )
		 (:instance standard-left-endpoint))
	   :in-theory (enable-disable (interval-definition-theory)
				      (standard-left-endpoint))
	   ))
  :rule-classes nil)

;; Now, if x+eps is in an interval, then x can't be the right endpoint.
;; Same goes for x-eps

(defthm inside-interval-not-right-endpoint
    (implies (and (weak-interval-p interval)
		  (realp x)
		  (realp eps)
		  (< 0 eps)
		  (inside-interval-p (+ x eps) interval))
	     (not (equal (interval-right-endpoint interval) x)))
  :hints (("Goal"
	   :in-theory (enable interval-definition-theory))))

(defthm inside-interval-not-left-endpoint
    (implies (and (weak-interval-p interval)
		  (realp x)
		  (realp eps)
		  (< eps 0)
		  (inside-interval-p (+ x eps) interval))
	     (not (equal (interval-left-endpoint interval) x)))
  :hints (("Goal"
	   :in-theory (enable interval-definition-theory))))

;; Now, if both x and x+eps are in a standard interval and x is standard,
;; then if follows that x+eps2 is also in the interval for any other
;; infinitesimal eps2.  This also follows for x-eps, of course.

(defthm inside-interval-x+eps2
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p x interval)
		  (standardp x)
		  (realp eps)
		  (< 0 eps)
		  (inside-interval-p (+ x eps) interval)
		  (realp eps2)
		  (< 0 eps2)
		  (i-small eps2))
	     (inside-interval-p (+ x eps2) interval))
  :hints (("Goal"
	   :use ((:instance inside-interval-x+eps (eps eps2))
		 (:instance inside-interval-not-right-endpoint))
	   :in-theory (disable inside-interval-not-right-endpoint))))

(defthm inside-interval-x-eps2
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p x interval)
		  (standardp x)
		  (realp eps)
		  (< eps 0)
		  (inside-interval-p (+ x eps) interval)
		  (realp eps2)
		  (< eps2 0)
		  (i-small eps2))
	     (inside-interval-p (+ x eps2) interval))
  :hints (("Goal"
	   :use ((:instance inside-interval-x-eps (eps eps2))
		 (:instance inside-interval-not-left-endpoint))
	   :in-theory (disable inside-interval-not-left-endpoint))))

(defthm inside-interval-x+-/-large-integer
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p x interval)
		  (standardp x)
		  (realp eps)
		  (< 0 eps)
		  (inside-interval-p (+ x eps) interval))
	     (inside-interval-p (+ x (/ (i-large-integer))) interval))
  :hints (("Goal"
	   :use ((:instance inside-interval-x+eps2 (eps2 (/ (i-large-integer)))))
	   :in-theory (disable inside-interval-x+eps2))))

(defthm inside-interval-x--/-large-integer
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p x interval)
		  (standardp x)
		  (realp eps)
		  (< eps 0)
		  (inside-interval-p (+ x eps) interval))
	     (inside-interval-p (- x (/ (i-large-integer))) interval))
  :hints (("Goal"
	   :use ((:instance inside-interval-x-eps2 (eps2 (- (/ (i-large-integer))))))
	   :in-theory (disable inside-interval-x-eps2))))


(defthm-std standard-rdfn-domain
    (standardp (rdfn-domain)))

(defthm differential-rdfn-x-large-integer-right-endpoint
    (implies (and (inside-interval-p x (rdfn-domain))
		  (standardp x)
		  (not (equal (interval-right-endpoint (rdfn-domain)) x)))
	     (and (realp (differential-rdfn x (/ (i-large-integer))))
		  (i-limited (differential-rdfn x (/ (i-large-integer))))))
  :hints (("Goal"
	   :use ((:instance differential-rdfn-limited
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps (/ (i-large-integer)))
			    (interval (rdfn-domain))))
	   :in-theory (disable differential-rdfn-limited))
	  ))

(defthm differential-rdfn-x-large-integer-left-endpoint
    (implies (and (inside-interval-p x (rdfn-domain))
		  (standardp x)
		  (not (equal (interval-left-endpoint (rdfn-domain)) x)))
	     (and (realp (differential-rdfn x (- (/ (i-large-integer)))))
		  (i-limited (differential-rdfn x (- (/ (i-large-integer)))))))
  :hints (("Goal"
	   :use ((:instance differential-rdfn-limited
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps (- (/ (i-large-integer))))
			    (interval (rdfn-domain))))
	   :in-theory (disable differential-rdfn-limited))))

;; One last useful theorem about intervals.  When an interval is non-trivial,
;; it is impossible to be both the left and right endpoints.

(defthm non-trivial-interval-not-both-endpoints
    (implies (inside-interval-p x (rdfn-domain))
	     (or (not (equal (interval-left-endpoint (rdfn-domain)) x))
		 (not (equal (interval-right-endpoint (rdfn-domain)) x))))
  :hints (("Goal"
	   :use ((:instance rdfn-domain-non-trivial))))
  :rule-classes nil)

(defthm non-trivial-interval-eps-or--eps
    (implies (and (inside-interval-p x (rdfn-domain))
		  (standardp x)
		  (realp eps)
		  (i-small eps))
	     (or (inside-interval-p (+ x eps) (rdfn-domain))
		 (inside-interval-p (- x eps) (rdfn-domain))))
  :hints (("Goal"
	   :use ((:instance non-trivial-interval-not-both-endpoints)
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps eps)
			    (interval (rdfn-domain)))
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps (- eps))
			    (interval (rdfn-domain)))
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps eps)
			    (interval (rdfn-domain))
			    )
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps (- eps))
			    (interval (rdfn-domain))
			    ))
	   ))
  :rule-classes nil)


;; Now, we can define the derivative of rdfn at x.  This is simply the
;; standard-part of an arbitrary infinitesimal differential at x.
;; Since the differential is arbitrary, we choose our favorite
;; epsilon.

(encapsulate
 ( ((derivative-rdfn *) => *) )

 (local
  (defun-std derivative-rdfn (x)
    (if (inside-interval-p x (rdfn-domain))
	(if (inside-interval-p (+ x (/ (i-large-integer))) (rdfn-domain))
	    (standard-part (differential-rdfn x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (rdfn-domain))
	      (standard-part (differential-rdfn x (- (/ (i-large-integer)))))
	    'error))
      'error)))

 (defthm derivative-rdfn-definition
   (implies (and (inside-interval-p x (rdfn-domain))
		 (standardp x))
	    (equal (derivative-rdfn x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (rdfn-domain))
		       (standard-part (differential-rdfn x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (rdfn-domain))
			 (standard-part (differential-rdfn x (- (/ (i-large-integer)))))
		       'error))))))

;; When x is in the domain, the derivative is well-defined

(defthmd derivative-rdfn-definition-clean
  (implies (and (inside-interval-p x (rdfn-domain))
		(standardp x))
	   (equal (derivative-rdfn x)
		  (if (inside-interval-p (+ x (/ (i-large-integer))) (rdfn-domain))
		      (standard-part (differential-rdfn x (/ (i-large-integer))))
		    (standard-part (differential-rdfn x (- (/ (i-large-integer))))))))
  :hints (("Goal"
	   :use ((:instance non-trivial-interval-not-both-endpoints)
		 (:instance differential-rdfn-limited
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-rdfn-limited
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 (:instance realp-differential-rdfn
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance realp-differential-rdfn
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps (- (/ (i-large-integer))))
			    (interval (rdfn-domain)))
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps (/ (i-large-integer)))
			    (interval (rdfn-domain)))
		 )
	   :in-theory (disable differential-rdfn-limited realp-differential-rdfn
			       differential-rdfn-x-large-integer-left-endpoint))))

(defthm-std derivative-well-defined
    (implies (inside-interval-p x (rdfn-domain))
	     (realp (derivative-rdfn x)))
    :hints (("Goal"
	   :use ((:instance derivative-rdfn-definition-clean)
		 (:instance non-trivial-interval-not-both-endpoints)
		 (:instance differential-rdfn-limited
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-rdfn-limited
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 (:instance realp-differential-rdfn
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance realp-differential-rdfn
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps (- (/ (i-large-integer))))
			    (interval (rdfn-domain)))
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps (/ (i-large-integer)))
			    (interval (rdfn-domain)))
		 )
	   :in-theory (disable differential-rdfn-limited realp-differential-rdfn
			       differential-rdfn-x-large-integer-left-endpoint))))

(in-theory (disable derivative-rdfn-definition))

;; We would like to rephrase the differentiability criteria in terms
;; of a small eps1 and eps2 instead of a y1, y2 close to x.

(defthm rdfn-differentiable-2a
   (implies (and (inside-interval-p x (rdfn-domain))
		 (standardp x)
		 (realp eps1) (i-small eps1) (not (= eps1 0))
		 (inside-interval-p (+ x eps1) (rdfn-domain))
		 (realp eps2) (i-small eps2) (not (= eps2 0))
		 (inside-interval-p (+ x eps2) (rdfn-domain)))
	    (i-close (differential-rdfn x eps1)
		     (differential-rdfn x eps2)))
   :hints (("Goal"
	    :use ((:instance rdfn-differentiable
			     (y1 (+ x eps1))
			     (y2 (+ x eps2))))
	    :in-theory (enable-disable (differential-rdfn-definition)
				       (rdfn-differentiable)))))

;; This is the ohter requirement of a differntiable function, namely
;; that the differntial is limited.

(defthm rdfn-differentiable-2b
   (implies (and (inside-interval-p x (rdfn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (rdfn-domain)))
	    (i-limited (differential-rdfn x eps)))
   :hints (("Goal"
	    :use ((:instance rdfn-differentiable
			     (y1 (+ x eps))
			     (y2 (+ x eps))))
	    :in-theory (disable rdfn-differentiable))))

;; This theorem is clearly another candidate for inclusion on nsa.lisp!

(local
 (defthm close-same-standard-part
   (implies (and (i-close x y)
		 (i-limited x)
		 (i-limited y))
	    (equal (standard-part x) (standard-part y)))
   :hints (("Goal" :in-theory (enable i-close i-small)))))

;; This rules converts instances of infinitesimal differntials into
;; the derivative.  The syntaxp is there to keep the rule from looping
;; on the definition of derivative!  This is probably a bad way of
;; going about the proof!

(defthm differential-rdfn-close
   (implies (and (inside-interval-p x (rdfn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (rdfn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-rdfn x eps))
		   (derivative-rdfn x)))
   :hints (("Goal"
	    :use ((:instance rdfn-differentiable-2a
			     (eps1 eps)
			     (eps2 (/ (i-large-integer))))
		  (:instance rdfn-differentiable-2a
			     (eps1 eps)
			     (eps2 (- (/ (i-large-integer)))))
		  (:instance rdfn-differentiable-2b)
		  (:instance rdfn-differentiable-2b
			     (eps (/ (i-large-integer))))
		  (:instance rdfn-differentiable-2b
			     (eps (- (/ (i-large-integer)))))
		  (:instance close-same-standard-part
			     (x (differential-rdfn x eps))
			     (y (differential-rdfn x (/ (i-large-integer)))))
		  (:instance close-same-standard-part
			     (x (differential-rdfn x eps))
			     (y (differential-rdfn x (- (/ (i-large-integer))))))
		  (:instance non-trivial-interval-eps-or--eps
			     (x x)
			     (eps (/ (i-large-integer)))))
	    :in-theory (enable-disable (derivative-rdfn-definition)
				       (rdfn-differentiable-2a
					rdfn-differentiable-2b
					close-same-standard-part)))))

;; This is a major lemma.  What it says if that if x is a number so
;; that a differential of rdfn at x with a given epsilon is positive,
;; but with -epsilon it's negative, then the derivative at x must be
;; zero.

(defthm derivative-==-0a
   (implies (and (inside-interval-p x (rdfn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (rdfn-domain))
		 (<= 0 (differential-rdfn x eps))
		 (inside-interval-p (- x eps) (rdfn-domain))
		 (<= (differential-rdfn x (- eps)) 0)
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (= 0 (derivative-rdfn x)))
   :rule-classes nil ; changed for v2-6
   :hints (("Goal"
	    :use ((:instance standard-part-<=
			     (x 0)
			     (y (differential-rdfn x eps)))
		  (:instance standard-part-<=
			     (x (differential-rdfn x (- eps)))
			     (y 0))
		  (:instance differential-rdfn-close)
		  (:instance differential-rdfn-close
			     (eps (- eps))))
	    :in-theory (disable derivative-rdfn-definition
				differential-rdfn-close
				standard-part-<=))))

;; Of course, the same applies if for a given epsilon the differntials
;; are negative and for -epsilon they're positive.  Hmmm, it looks
;; like the previous theorem is more general, so this is probably not
;; needed.

(defthm derivative-==-0b
   (implies (and (inside-interval-p x (rdfn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (rdfn-domain))
		 (<= (differential-rdfn x eps) 0)
		 (<= 0 (differential-rdfn x (- eps)))
		 (inside-interval-p (- x eps) (rdfn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (= 0 (derivative-rdfn x)))
   :rule-classes nil ; changed for v2-6
   :hints (("Goal"
	    :use ((:instance standard-part-<=
			     (x (differential-rdfn x eps))
			     (y 0))
		  (:instance standard-part-<=
			     (x 0)
			     (y (differential-rdfn x (- eps))))
		  (:instance differential-rdfn-close)
		  (:instance differential-rdfn-close
			     (eps (- eps))))
	    :in-theory (disable derivative-rdfn-definition
				differential-rdfn-close
				standard-part-<=))))

;; But it is enough to prove Rolle's theorem.  The derivative of the
;; critical point is equal to zero.  The critical point is either an
;; extreme value of rdfn interior to (a,b), or it's equal to the
;; midpoint of (a,b) if rdfn happens to be a constant function.  In
;; either case, the derivative is zero.

(defthm find-min-rdfn-x-inside-interval
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (< a b))
	     (inside-interval-p (find-min-rdfn-x a b) interval))
  :hints (("Goal"
	   :by (:functional-instance find-min-rcfn-x-inside-interval
				     (find-min-rcfn-x-n find-min-rdfn-x-n)
				     (find-min-rcfn-x find-min-rdfn-x)
				     (rcfn rdfn)
				     (rcfn-domain rdfn-domain)))))

(defthm find-max-rdfn-x-inside-interval
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (< a b))
	     (inside-interval-p (find-max-rdfn-x a b) interval))
  :hints (("Goal"
	   :by (:functional-instance find-max-rcfn-x-inside-interval
				     (find-max-rcfn-x-n find-max-rdfn-x-n)
				     (find-max-rcfn-x find-max-rdfn-x)
				     (rcfn rdfn)
				     (rcfn-domain rdfn-domain)))))

(defthm x-inside-interval-not-endpoint
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (realp x)
		  (< a x)
		  (< x b))
	     (and (not (equal (interval-left-endpoint interval) x))
		  (not (equal (interval-right-endpoint interval) x))))
  :hints (("Goal"
	   :in-theory (enable interval-definition-theory))))


(defthm x+-eps-inside-interval
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p a interval)
		  (standardp a)
		  (inside-interval-p b interval)
		  (standardp b)
		  (realp x)
		  (standardp x)
		  (< a x)
		  (< x b)
		  (realp eps)
		  (i-small eps))
	     (and (inside-interval-p (+ x eps) interval)
		  (inside-interval-p (- x eps) interval)
		  (inside-interval-p x interval)))
  :hints (("Goal"
	   :use ((:instance x-inside-interval-not-endpoint)
		 (:instance inside-interval-x+eps)
		 (:instance inside-interval-x+eps (eps (- eps)))
		 (:instance inside-interval-x-eps)
		 (:instance inside-interval-x-eps (eps (- eps)))
		 (:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c x)))
	   :in-theory (disable x-inside-interval-not-endpoint inside-interval-p-squeeze))))

(defthm x+-/i-large-integer-inside-interval
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p a interval)
		  (standardp a)
		  (inside-interval-p b interval)
		  (standardp b)
		  (realp x)
		  (standardp x)
		  (< a x)
		  (< x b))
	     (and (inside-interval-p (+ x (/ (i-large-integer))) interval)
		  (inside-interval-p (- x (/ (i-large-integer))) interval)
		  (inside-interval-p x interval)))
  :hints (("Goal"
	   :use ((:instance x+-eps-inside-interval
			    (eps (/ (i-large-integer))))))))

(defthm midpoint-inside-interval
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (< a b))
	     (inside-interval-p (+ (* 1/2 a) (* 1/2 b)) interval))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (+ (* 1/2 a) (* 1/2 b)))))
	   :in-theory (disable inside-interval-p-squeeze))))

(defthm midpoint-/i-large-integer-inside-interval
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p a interval)
		  (standardp a)
		  (inside-interval-p b interval)
		  (standardp b)
		  (< a b))
	     (and (inside-interval-p (+ (/ (i-large-integer)) (* 1/2 a) (* 1/2 b)) interval)
		  (inside-interval-p (+ (- (/ (i-large-integer))) (* 1/2 a) (* 1/2 b)) interval)
		  (inside-interval-p (+ (* 1/2 a) (* 1/2 b)) interval)))
  :hints (("Goal"
	   :use ((:instance midpoint-inside-interval)
		 (:instance x+-/i-large-integer-inside-interval
			    (x (/ (+ a b) 2))))
	   :in-theory (disable midpoint-inside-interval x+-/i-large-integer-inside-interval))))

(defthm find-min-rdfn-/i-large-integer-inside-interval
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p a interval)
		  (standardp a)
		  (inside-interval-p b interval)
		  (standardp b)
		  (not (equal (find-min-rdfn-x a b) a))
		  (not (equal (find-min-rdfn-x a b) b))
		  (< a b))
	     (and (inside-interval-p (+ (/ (i-large-integer)) (find-min-rdfn-x a b)) interval)
		  (inside-interval-p (+ (- (/ (i-large-integer))) (find-min-rdfn-x a b)) interval)
		  (inside-interval-p (find-min-rdfn-x a b) interval)))
  :hints (("Goal"
	   :use ((:instance find-min-rdfn-x-inside-interval)
		 (:instance FIND-MIN-RDFN-X->=-A)
		 (:instance FIND-MIN-RDFN-X-<=-B)
		 (:instance x+-/i-large-integer-inside-interval
			    (x (find-min-rdfn-x a b))))
	   :in-theory (disable find-min-rdfn-x-inside-interval x+-/i-large-integer-inside-interval
			       FIND-MIN-RDFN-X->=-A FIND-MIN-RDFN-X-<=-B))))


(defthm find-max-rdfn-/i-large-integer-inside-interval
    (implies (and (weak-interval-p interval)
		  (standardp interval)
		  (inside-interval-p a interval)
		  (standardp a)
		  (inside-interval-p b interval)
		  (standardp b)
		  (not (equal (find-max-rdfn-x a b) a))
		  (not (equal (find-max-rdfn-x a b) b))
		  (< a b))
	     (and (inside-interval-p (+ (/ (i-large-integer)) (find-max-rdfn-x a b)) interval)
		  (inside-interval-p (+ (- (/ (i-large-integer))) (find-max-rdfn-x a b)) interval)
		  (inside-interval-p (find-max-rdfn-x a b) interval)))
  :hints (("Goal"
	   :use ((:instance find-max-rdfn-x-inside-interval)
		 (:instance FIND-MAX-RDFN-X->=-A)
		 (:instance FIND-MAX-RDFN-X-<=-B)
		 (:instance x+-/i-large-integer-inside-interval
			    (x (find-max-rdfn-x a b))))
	   :in-theory (disable find-max-rdfn-x-inside-interval x+-/i-large-integer-inside-interval
			       FIND-MAX-RDFN-X->=-A FIND-MAX-RDFN-X-<=-B))))

(defthm rolles-theorem-lemma-5
    (implies (and (inside-interval-p a (rdfn-domain))
		  (inside-interval-p b (rdfn-domain))
		  (= (rdfn a) (rdfn b))
		  (< a b))
	     (< a (rolles-critical-point a b))))

(defthm rolles-theorem-lemma-6
    (implies (and (inside-interval-p a (rdfn-domain))
		  (inside-interval-p b (rdfn-domain))
		  (= (rdfn a) (rdfn b))
		  (< a b))
	     (< (rolles-critical-point a b) b)))

(defthm rolles-theorem-lemma-7
    (implies (and (inside-interval-p a (rdfn-domain))
		  (inside-interval-p b (rdfn-domain))
		  (= (rdfn a) (rdfn b))
		  (< a b))
	     (realp (rolles-critical-point a b))))

(defthm-std rolles-theorem-lemma-8
    (implies (and (inside-interval-p a (rdfn-domain))
		  (inside-interval-p b (rdfn-domain))
		  (= (rdfn a) (rdfn b))
		  (< a b))
	     (equal (derivative-rdfn (rolles-critical-point a b)) 0))
  :hints (("Subgoal 3"
	   :use ((:instance rolles-theorem-lemma-1
			    (eps (/ (i-large-integer))))
		 (:instance rolles-theorem-lemma-4
			    (eps (/ (i-large-integer)))))
	   :in-theory (enable-disable (derivative-rdfn-definition)
				      (rolles-theorem-lemma-1
				       rolles-theorem-lemma-4)))
	  ("Subgoal 2"
	   :use ((:instance rolles-theorem-lemma-2c
			    (eps (/ (i-large-integer))))
		 (:instance rolles-theorem-lemma-2d
			    (eps (/ (i-large-integer))))
		 (:instance rolles-theorem-lemma-2f
			    (eps (/ (i-large-integer))))
		 (:instance rolles-theorem-lemma-3b)
		 (:instance derivative-==-0a
			    (x (find-min-rdfn-x a b))
			    (eps (/ (i-large-integer)))))
	   :in-theory (disable rolles-theorem-lemma-2c
			       rolles-theorem-lemma-2d
			       rolles-theorem-lemma-2f
			       rolles-theorem-lemma-3b
			       ))
	  ("Subgoal 1"
	   :use ((:instance rolles-theorem-lemma-2a
			    (eps (/ (i-large-integer))))
		 (:instance rolles-theorem-lemma-2b
			    (eps (/ (i-large-integer))))
		 (:instance rolles-theorem-lemma-2e
			    (eps (/ (i-large-integer))))
		 (:instance rolles-theorem-lemma-3a)
		 (:instance derivative-==-0b
			    (x (find-max-rdfn-x a b))
			    (eps (/ (i-large-integer))))
		 )
	   :in-theory (disable rolles-theorem-lemma-2a
			       rolles-theorem-lemma-2b
			       rolles-theorem-lemma-2e
			       rolles-theorem-lemma-3a))))

(defthm rolles-theorem
    (implies (and (inside-interval-p a (rdfn-domain))
		  (inside-interval-p b (rdfn-domain))
		  (= (rdfn a) (rdfn b))
		  (< a b))
	     (and (realp (rolles-critical-point a b))
		  (< a (rolles-critical-point a b))
		  (< (rolles-critical-point a b) b)
		  (equal (derivative-rdfn (rolles-critical-point a b)) 0)))
  :hints (("Goal"
	   :in-theory (disable rolles-critical-point)))
  )

(defun-sk exists-critical-point (a b)
  (exists (x)
	  (and (realp x)
	       (< a x)
	       (< x b)
	       (equal (derivative-rdfn x) 0))))

(defthm rolles-theorem-sk
    (implies (and (inside-interval-p a (rdfn-domain))
		  (inside-interval-p b (rdfn-domain))
		  (= (rdfn a) (rdfn b))
		  (< a b))
	     (exists-critical-point a b))
  :hints (("Goal"
	   :use ((:instance exists-critical-point-suff
			    (x (rolles-critical-point a b)))
		 (:instance rolles-theorem))
	   :in-theory (disable exists-critical-point-suff rolles-theorem))))

;; OK now, we want to prove the mean-value theorem.  We can actually
;; use the usual (not based on nsa) proof of this fact.  The trick is
;; to use Rolle's theorem on a new function rdfn2 that's chosen so
;; that rdfn2 vanishes at both a and b.  The function is given by rdfn
;; minus the line that goes from (a,(rdfn a)) to (b,(rdfn b)).
;; Because of this choice, when the derivative of rdfn2 is zero -- and
;; the existence of such a point in (a,b) is given by Rolle's theorem
;; -- it folloes that the derivative of rdfn is the same as the slope
;; of the line from (a,(rdfn a)) to (b,(rdfn b)).  I.e., that point
;; satisfies the requirement of the mean value theorem.

;; First, we offer the definition of the function rdfn2.  Notice, the
;; function depends on the actual points a and b.  So, we use the
;; encapsulated range above.  The statement of Rolle's theorem was
;; more general, in that the range [a,b] was placed in the hypothesis,
;; instead of an encapsulate.  Unfortunately, we can't do that here,
;; because the function definition needs to know the values of a and b
;; (and we can't just pass them down, because we need to guarantee
;; that (rdfn2 x) is standard when x is standard, but since we use a
;; and b in the definition, that wouldn't be the case if a and b were
;; non-standard -- and if we explicitly check for that in the
;; definition, then the function becomes non-classical!  Yikes!  There
;; has to be an easier way.

(encapsulate
 ((rdfn-subdomain () t))

 (local
  (defun rdfn-subdomain ()
    (let ((left (interval-left-endpoint (rdfn-domain)))
	  (right (interval-right-endpoint (rdfn-domain))))
      (if (null left)
	  (if (null right)
	      (interval 0 1)
	      (interval (- right 2) (- right 1)))
	  (if (null right)
	      (interval (+ left 1) (+ left 2))
	      (interval (+ left (* 1/3 (- right left)))
			(+ left (* 2/3 (- right left)))))))))

 (defthm rdfn-subdomain-is-subdomain
     (subinterval-p (rdfn-subdomain) (rdfn-domain))
   :hints (("Goal"
	    :use ((:instance interval-p (interval (rdfn-domain))))
	    :in-theory (enable interval-definition-theory))
	   ))

 (defthm rdfn-subdomain-closed-bounded
     (and (interval-left-inclusive-p (rdfn-subdomain))
	  (interval-right-inclusive-p (rdfn-subdomain))))

 (defthm rdfn-subdomain-real-left
     (realp (interval-left-endpoint (rdfn-subdomain)))
   :rule-classes (:rewrite :type-prescription))

 (defthm rdfn-subdomain-real-right
     (realp (interval-right-endpoint (rdfn-subdomain)))
   :rule-classes (:rewrite :type-prescription))

 (defthm rdfn-subdomain-non-trivial
     (< (interval-left-endpoint (rdfn-subdomain))
	(interval-right-endpoint (rdfn-subdomain)))
   :hints (("Goal"
	    :use (:instance rdfn-domain-non-trivial)))
   )
 )

(defun rdfn2 (x)
  (let ((a (interval-left-endpoint (rdfn-subdomain)))
	(b (interval-right-endpoint (rdfn-subdomain))))
    (+ (rdfn x)
       (- (* (- (rdfn b) (rdfn a))
	     (- (realfix x) a)
	     (/ (- b a))))
       (- (rdfn a)))))
(in-theory (disable (rdfn2)))

;; rdfn2 always returns a real number.

(defthm subdomain-is-interval
    (interval-p (rdfn-subdomain))
  :hints (("Goal"
	   :use ((:instance subinterval-p
			    (subinterval (rdfn-subdomain))
			    (interval (rdfn-domain)))))))

(defthm subdomain-real
    (and (realp (interval-left-endpoint (rdfn-subdomain)))
	 (realp (interval-right-endpoint (rdfn-subdomain))))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-contains-left-endpoint (interval (rdfn-subdomain)))
		 (:instance inside-interval-p-contains-right-endpoint (interval (rdfn-subdomain))))
	   :in-theory (disable inside-interval-p-contains-left-endpoint
			       inside-interval-p-contains-right-endpoint)))
  :rule-classes (:rewrite :type-prescription :generalize))

(defthm rdfn2-real
    (realp (rdfn2 x))
  :rule-classes (:rewrite :type-prescription))

;; And a limited number when x is standard.

(defthm-std rdfn2-standard
  (implies (standardp x)
	   (standardp (rdfn2 x))))

(defthm rdfn2-limited
  (implies (standardp x)
	   (i-limited (rdfn2 x)))
  :hints (("Goal" :in-theory (enable-disable (standards-are-limited)
					     (rdfn2)))))

;; ACL2 is not really good at algebra, so we let it know how to
;; compute the value of (rdfn x) - (rdfn y), since that difference
;; will appear often, and the right simplification is important.

(encapsulate
 ()

 ;; Silly algebra!

 (local
  (defthm lemma-1
    (equal (* a (+ x (- y)) b)
	   (+ (* a x b)
	      (- (* a y b))))))

 ;; The important thing below is that the difference cancels out the
 ;; "- (rdfn a)" term, and that the terms involving the slope of the
 ;; line can be combined.

 (defthm rdfn2-diff
     (implies (and (realp x)
		   (realp y))
	      (equal (+ (rdfn2 x) (- (rdfn2 y)))
		     (+ (rdfn x)
			(- (rdfn y))
			(- (* (+ (rdfn (interval-right-endpoint (rdfn-subdomain)))
				 (- (rdfn (interval-left-endpoint (rdfn-subdomain)))))
			      (+ x (- y))
			      (/ (+ (interval-right-endpoint (rdfn-subdomain))
				    (- (interval-left-endpoint (rdfn-subdomain)))))))))))
)

;; Next, we want to show that rdfn2 really is a differentiable
;; function.  One way to do this (and probably the right way) is to
;; prove that the sum/product of two differentiable functions is
;; differentiable.  This would be similar to some of the theorems
;; about converging series we proved a long time ago.  But, for the
;; present time, it's simply easier to prove the differentiability of
;; rdfn2 directly.

(encapsulate
 ()

 ;; First, we show ACL2 some obvious algebraic simplifications.

 (local
  (defthm lemma-1
    (implies (not (equal (+ x (- y)) 0))
	     (equal (+ (- (* a b x (/ (+ x (- y)))))
		       (* a b y (/ (+ x (- y)))))
		    (- (* a b))))
    :hints (("Goal"
	     :use ((:instance (:theorem
			       (equal (* a b (+ (- x) y) z)
				      (+ (- (* a b x z))
					 (* a b y z))))
			      (z (/ (+ x (- y)))))
		   (:instance (:theorem
			       (implies (and (acl2-numberp z)
					     (not (equal z 0)))
					(equal (* a b (/ z) (- z))
					       (- (* a b)))))
			      (z (+ x (- y))))
		   ))
	    ("Subgoal 3"
	     :in-theory (disable distributivity)))
    ;:rule-classes (:built-in-clause :rewrite))
    ))

 (local
  (defthm lemma-1a
      (implies (and (realp x)
		    (realp y)
		    (realp a1)
		    (realp a2)
		    (realp b)
		    (not (equal x y)))
	       (equal (+ (* x a1 (/ (+ x (- y))) b)
			 (- (* x a2 (/ (+ x (- y))) b))
			 (- (* y a1 (/ (+ x (- y))) b))
			 (* y a2 (/ (+ x (- y))) b))
		      (+ (* a1 b)
			 (- (* a2 b)))))
    :hints (("Goal"
	     :use ((:instance lemma-1 (a (- a1)))
		   (:instance lemma-1 (a a2)))
	     :in-theory (disable lemma-1)))
    ))

 ;; This means that we can get a nice simplification for the
 ;; differentialof rdfn2.  Notice how it splits into two parts, the
 ;; differential of rdfn and the slope of the line from a to b.

 (local
  (defthm lemma-2
    (implies (and (not (equal (- x y1) 0))
		  (realp x)
		  (realp y)
		  (realp y1))
	     (equal (/ (+ (rdfn2 x) (- (rdfn2 y1))) (+ x (- y1)))
		    (+ (* (+ (rdfn x)
			     (- (rdfn y1)))
			  (/ (- x y1)))
		       (- (* (+ (rdfn (interval-right-endpoint (rdfn-subdomain)))
				(- (rdfn (interval-left-endpoint (rdfn-subdomain)))))
			     (/ (+ (interval-right-endpoint (rdfn-subdomain))
				   (- (interval-left-endpoint (rdfn-subdomain))))))))))
    :hints (("Goal"
	     :in-theory (disable rdfn2)))))

 ;; The second part of that is limited, because rdfn is a standard
 ;; function.

 (local
  (defthm-std lemma-3a
      (implies (standardp x)
	       (standardp (rdfn x)))))

 (local
  (defthm-std lemma-3b
      (standardp (rdfn (interval-left-endpoint (rdfn-subdomain))))))

 (local
  (defthm-std lemma-3c
      (standardp (rdfn (interval-right-endpoint (rdfn-subdomain))))))

 (local
  (defthm-std lemma-3d
      (standardp (+ (- (interval-left-endpoint (rdfn-subdomain)))
		    (interval-right-endpoint (rdfn-subdomain))))))

 (local
  (defthm lemma-3
      (i-limited (+ (* (rdfn (interval-left-endpoint (rdfn-subdomain)))
		       (/ (+ (- (interval-left-endpoint (rdfn-subdomain)))
			     (interval-right-endpoint (rdfn-subdomain)))))
		    (- (* (rdfn (interval-right-endpoint (rdfn-subdomain)))
			  (/ (+ (- (interval-left-endpoint (rdfn-subdomain)))
				(interval-right-endpoint (rdfn-subdomain))))))))
    :hints (("Goal" :in-theory (enable standards-are-limited)))))

 ;; This first part of the sum is limited, just because rdfn is
 ;; differentiable.

 (local
  (defthm lemma-4
    (implies (and (standardp x)
		  (inside-interval-p x (rdfn-domain))
		  (inside-interval-p y1 (rdfn-domain))
		  (i-close x y1) (not (= x y1)))
	     (i-limited (* (+ (rdfn2 x) (- (rdfn2 y1))) (/ (+ x (- y1))))))
    :hints (("Goal"
	     :use ((:instance i-limited-plus
			      (x (+ (* (rdfn (interval-left-endpoint (rdfn-subdomain)))
				       (/ (+ (- (interval-left-endpoint (rdfn-subdomain)))
					     (interval-right-endpoint (rdfn-subdomain)))))
				    (- (* (rdfn (interval-right-endpoint (rdfn-subdomain)))
					  (/ (+ (- (interval-left-endpoint (rdfn-subdomain)))
						(interval-right-endpoint (rdfn-subdomain))))))))
			      (y (+ (* (rdfn x) (/ (+ x (- y1))))
				    (- (* (rdfn y1) (/ (+ x (- y1))))))))
		   (:instance rdfn-differentiable (y2 y1))
		   (:instance lemma-2))
	     :in-theory (disable rdfn-differentiable lemma-2
				 )))))

 ;; This is a trivial simplification!

 (local
  (defthm lemma-5
    (equal (i-close (+ a b x) (+ a b y))
	   (i-close (fix x) (fix y)))
    :hints (("Goal" :in-theory (enable i-close)))))

 ;; We can now prove that rdfn2 is differentiable.

 (defthm rdfn2-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-domain))
		 (inside-interval-p y1 (rdfn-domain))
		 (inside-interval-p y2 (rdfn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (rdfn2 x) (rdfn2 y1)) (- x y1)))
		 (i-close (/ (- (rdfn2 x) (rdfn2 y1)) (- x y1))
			  (/ (- (rdfn2 x) (rdfn2 y2)) (- x y2)))))
   :hints (("Goal"
	    :use ((:instance lemma-4))
	    :in-theory (disable rdfn2 rdfn2-diff lemma-4))
	   ("Goal'''"
	    :use ((:instance rdfn-differentiable))
	    :in-theory (disable rdfn-differentiable))))
 )




;; To apply Rolle's theorem to rdfn2, we have to define the max-x-n
;; routine to find the maximum of rdfn2 on a given grid.

(defun find-max-rdfn2-x-n (a max-x i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (> (rdfn2 (+ a (* i eps))) (rdfn2 max-x))
	  (find-max-rdfn2-x-n a (+ a (* i eps)) (1+ i) n eps)
	(find-max-rdfn2-x-n a max-x (1+ i) n eps))
    max-x))

;; And we need to show that's limited (by functional instantiate).  We cannot instantiate
;; the result directly, because it uses free variables in the lambda expression, and
;; that is disallowed when the goal theorem is non-classical.  So we simply prove the
;; upper and lower bounds here, then prove that it's limited directly.

(defthm find-max-rdfn2-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-max-rdfn2-x-n a a
				    0 (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b)))))
  :hints (("Goal"
	   :by (:functional-instance find-max-rdfn-x-n-limited
				     (find-max-rdfn-x-n find-max-rdfn2-x-n)
				     (rdfn rdfn2))
	   :in-theory (disable find-max-rdfn-x-n-limited
; Added after v4-3 by Matt K.:
                               (tau-system)))
	  ("Subgoal 3"
	   :in-theory '(find-max-rdfn2-x-n rdfn2))
	  ("Subgoal 2"
	   :use ((:instance rdfn2-differentiable))
	   :in-theory (disable rdfn2-differentiable))))

;; And then, of course, we introduce the true maximum max-x.

(defun-std find-max-rdfn2-x (a b)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-max-rdfn2-x-n a
					 a
					 0
					 (i-large-integer)
					 (/ (- b a) (i-large-integer))))
      0)
  )


;; Foots!  Now we do it *again* for the minimum....sigh.  This is why
;; we need to use defchoose to pick the min/max.

(defun find-min-rdfn2-x-n (a min-x i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (< (rdfn2 (+ a (* i eps))) (rdfn2 min-x))
	  (find-min-rdfn2-x-n a (+ a (* i eps)) (1+ i) n eps)
	(find-min-rdfn2-x-n a min-x (1+ i) n eps))
    min-x))

;; The minimum is limited, yada, yada, yada....

(defthm find-min-rdfn2-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-min-rdfn2-x-n a a
				    0 (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b)))))
  :hints (("Goal"
	   :by (:functional-instance find-min-rdfn-x-n-limited
				     (find-min-rdfn-x-n find-min-rdfn2-x-n)
				     (rdfn rdfn2))
	   :in-theory '(find-min-rdfn2-x-n))))

;; And we use defun-std to get the "real" minimum.

(defun-std find-min-rdfn2-x (a b)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-min-rdfn2-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))))
    0))

;; Now, we define the critical point for rdfn2.

(defun rolles-critical-point-2 (a b)
  (if (equal (rdfn2 (find-min-rdfn2-x a b)) (rdfn2 (find-max-rdfn2-x a b)))
      (/ (+ a b) 2)
    (if (equal (rdfn2 (find-min-rdfn2-x a b)) (rdfn2 a))
	(find-max-rdfn2-x a b)
      (find-min-rdfn2-x a b))))

;; And we define "differentials" for rdfn2.

(encapsulate
 ( ((differential-rdfn2 * *) => *) )

 (local
  (defun differential-rdfn2 (x eps)
    (/ (- (rdfn2 (+ x eps)) (rdfn2 x)) eps)))

 (defthm differential-rdfn2-definition
   (implies (and (inside-interval-p x (rdfn-domain))
		 (inside-interval-p (+ x eps) (rdfn-domain)))
	    (equal (differential-rdfn2 x eps)
		   (/ (- (rdfn2 (+ x eps)) (rdfn2 x)) eps)))))

(defthm realp-differential-rdfn2
  (implies (and (inside-interval-p x (rdfn-domain))
		(inside-interval-p (+ x eps) (rdfn-domain))
		(realp eps))
	   (realp (differential-rdfn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-rdfn2)
				     (rdfn rdfn2))
	   :in-theory '(differential-rdfn2-definition)))
  )

(defthm differential-rdfn2-limited
    (implies (and (standardp x)
		  (inside-interval-p x (rdfn-domain))
		  (inside-interval-p (+ x eps) (rdfn-domain))
		  (i-small eps))
	     (i-limited (differential-rdfn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-rdfn2)
				     (rdfn rdfn2))
	   :in-theory '(differential-rdfn2-definition)))
  )

(in-theory (disable differential-rdfn2-definition))

;; And, of course, derivatives for rdfn2.

(defun-std derivative-rdfn2 (x)
  (if (inside-interval-p x (rdfn-domain))
      (if (inside-interval-p (+ x (/ (i-large-integer))) (rdfn-domain))
	  (standard-part (differential-rdfn2 x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (rdfn-domain))
	      (standard-part (differential-rdfn2 x (- (/ (i-large-integer)))))
	      'error))
      'error))

;; And now we can prove Rolle's theorem for rdfn2, by functional
;; instantiation.

(defthm rolles-theorem-2
  (implies (and (inside-interval-p a (rdfn-domain))
		(inside-interval-p b (rdfn-domain))
		(= (rdfn2 a) (rdfn2 b))
		(< a b))
	   (and (realp (rolles-critical-point-2 a b))
		(< a (rolles-critical-point-2 a b))
		(< (rolles-critical-point-2 a b) b)
		(equal (derivative-rdfn2 (rolles-critical-point-2 a b)) 0)))
  :hints (("Goal"
	   :by (:functional-instance rolles-theorem
				     (find-min-rdfn-x-n find-min-rdfn2-x-n)
				     (find-max-rdfn-x-n find-max-rdfn2-x-n)
				     (find-min-rdfn-x find-min-rdfn2-x)
				     (find-max-rdfn-x find-max-rdfn2-x)
				     (rdfn rdfn2)
				     (derivative-rdfn derivative-rdfn2)
				     (differential-rdfn differential-rdfn2)
				     (rolles-critical-point rolles-critical-point-2))
	   :in-theory (disable rolles-theorem))))

(in-theory (disable rolles-critical-point-2))
(in-theory (disable differential-rdfn2-definition))
(in-theory (disable derivative-rdfn2))

;; OK, now to apply Rolle's theorem to the specific range we have in
;; mind.  We need to show that (rdfn2 a) = (rdfn2 b).  Well, the first
;; is obviously zero.

(defthm rdfn2-a
  (equal (rdfn2 (interval-left-endpoint (rdfn-subdomain))) 0))

;; The second one is also zero, but that takes some algebra.....

(encapsulate
 ()

 ;; ....for example, we need a simple cancellation rule for a * x * 1/x

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x) (not (= x 0)))
	     (equal (* a x (/ x)) (fix a)))))

 ;; A trivial observation is that b-a isn't zero, since a<b.

 (local
  (defthm lemma-2
    (equal (equal (+ (- (interval-left-endpoint (rdfn-subdomain))) (interval-right-endpoint (rdfn-subdomain))) 0) nil)
    :hints (("Goal"
	     :use ((:instance rdfn-subdomain-non-trivial))
	     :in-theory (disable rdfn-subdomain-non-trivial)))))

 ;; So from the two theorems above, we get that a*(b-a)*1/(b-a) is
 ;; just equal to a.

 (local
  (defthm lemma-3
    (equal (* a (+ (- (interval-left-endpoint (rdfn-subdomain)))
		   (interval-right-endpoint (rdfn-subdomain)))
	      (/ (+ (- (interval-left-endpoint (rdfn-subdomain)))
		    (interval-right-endpoint (rdfn-subdomain)))))
	   (fix a))
    :hints (("Goal"
	     :use ((:instance lemma-1 (x (+ (- (interval-left-endpoint (rdfn-subdomain)))
					    (interval-right-endpoint (rdfn-subdomain))))))
	     :in-theory (disable lemma-1)))))

 ;; And so (rdfn2 b) is equal to zero!

 (defthm rdfn2-b
   (equal (rdfn2 (interval-right-endpoint (rdfn-subdomain))) 0))
 )

;; Now, let's specialize Rolle's theorem for the specific endpoints we
;; have in mind.  Notice how this does away with all the hypotheses,
;; since they were there just to limit the possibilities of a and b.

(encapsulate
 nil

 (local
  (defthm lemma-1
      (inside-interval-p (interval-left-endpoint (rdfn-subdomain))
			 (rdfn-domain))
    :hints (("Goal"
	     :use ((:instance inside-interval-p-contains-left-endpoint
			      (interval (rdfn-subdomain))))
	     :in-theory (disable inside-interval-p-contains-left-endpoint)))))

 (local
  (defthm lemma-2
      (inside-interval-p (interval-right-endpoint (rdfn-subdomain))
			 (rdfn-domain))
    :hints (("Goal"
	     :use ((:instance inside-interval-p-contains-right-endpoint
			      (interval (rdfn-subdomain))))
	     :in-theory (disable inside-interval-p-contains-right-endpoint)))))

 (defthm rolles-theorem-2-specialized
     (and (realp (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
					  (interval-right-endpoint (rdfn-subdomain))))
	  (< (interval-left-endpoint (rdfn-subdomain))
	     (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
				      (interval-right-endpoint (rdfn-subdomain))))
	  (< (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
				      (interval-right-endpoint (rdfn-subdomain)))
	     (interval-right-endpoint (rdfn-subdomain)))
	  (equal (derivative-rdfn2 (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							    (interval-right-endpoint (rdfn-subdomain))))
		 0))
   :hints (("Goal"
	    :use ((:instance rolles-theorem-2 (a (interval-left-endpoint (rdfn-subdomain)))
			     (b (interval-right-endpoint (rdfn-subdomain)))))
	    :in-theory (disable rolles-theorem-2))))

 )

;; So here's an obvious corollary.  Since the derivative of rdfn2 at
;; the critical point is zero, that means the differential of rdfn2 at
;; the critical point must be small.

(defthm-std standard-rolles-critical-point-2
    (standardp (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
					(interval-right-endpoint (rdfn-subdomain)))))

(local
 (defthm internal-point-inside-interval
     (implies (and (weak-interval-p interval)
		   (realp x)
		   (realp (interval-left-endpoint interval))
		   (realp (interval-right-endpoint interval))
		   (< (interval-left-endpoint interval) x)
		   (< x (interval-right-endpoint interval)))
	      (inside-interval-p x interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(defthm inside-interval-rolles-critical-point-2
  (inside-interval-p (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
					      (interval-right-endpoint (rdfn-subdomain)))
		     (rdfn-subdomain))
  :hints (("Goal"
	   :use ((:instance rolles-theorem-2-specialized)
		 (:instance inside-interval-p-squeeze
			    (a (interval-left-endpoint (rdfn-subdomain)))
			    (b (interval-right-endpoint (rdfn-subdomain)))
			    (c (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							(interval-right-endpoint (rdfn-subdomain))))
			    (interval (rdfn-subdomain)))
		 )
	   :in-theory (disable ROLLES-THEOREM-2-SPECIALIZED))))

(defthm interval-p-subdomain
    (interval-p (rdfn-subdomain)))

(defthm weak-interval-p-subdomain
    (weak-interval-p (rdfn-subdomain))
  :hints (("Goal"
	   :use ((:instance interval-p-is-weak-interval-p
			    (interval (rdfn-subdomain)))))))

(defthm-std standard-subdomain
    (standardp (rdfn-subdomain)))

(defthm inside-interval-rolles-critical-point-2+eps
    (implies (and (realp eps)
		  (i-small eps))
	     (inside-interval-p (+ (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							    (interval-right-endpoint (rdfn-subdomain)))
				   eps)
				(rdfn-subdomain)))
  :hints (("Goal"
	   :use ((:instance inside-interval-x+eps
			    (x (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							(interval-right-endpoint (rdfn-subdomain))))
			    (interval (rdfn-subdomain)))
		 (:instance inside-interval-x-eps
			    (x (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							(interval-right-endpoint (rdfn-subdomain))))
			    (interval (rdfn-subdomain)))
		 (:instance rolles-theorem-2-specialized)
		 )
	   :in-theory (disable rolles-theorem-2-specialized)
	   ))
)

(defthm inside-interval-rolles-critical-point-2+eps-2
    (implies (and (realp eps)
		  (i-small eps))
	     (inside-interval-p (+ eps
				   (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							    (interval-right-endpoint (rdfn-subdomain))))
				(rdfn-subdomain)))
    :hints (("Goal"
	     :use ((:instance inside-interval-rolles-critical-point-2+eps)))))

(defthm inside-interval-rolles-critical-point-+-/i-large-integer
    (inside-interval-p (+ (/ (i-large-integer))
			  (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
						   (interval-right-endpoint (rdfn-subdomain))))
		       (rdfn-subdomain))
  :hints (("Goal"
	   :use ((:instance inside-interval-rolles-critical-point-2+eps
			    (eps (/ (i-large-integer)))))
	   :in-theory (disable inside-interval-rolles-critical-point-2+eps))))

(defthm rolles-theorem-2-corollary
  (i-small (differential-rdfn2 (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							(interval-right-endpoint (rdfn-subdomain)))
			       (/ (i-large-integer))))
  :hints (("Goal"
	   :use ((:instance rolles-theorem-2-specialized))
	   :in-theory (enable-disable (i-small derivative-rdfn2)
				      (rolles-theorem-2
				       rolles-theorem-2-specialized)))))

;; And now we're almost ready for the mean value theorem!

(encapsulate
 ()

 ;; Well, actually, we need some algebra, so that ACL2 opens up the
 ;; addition in the middle of the following term.

 (local
  (defthm lemma-1
    (equal (* a (+ (- y) x) b)
	   (+ (* a x b)
	      (- (* a y b))))))

 ;; And here's more algebra, to cancel a z*1/z term.

 (local
  (defthm lemma-2
    (implies (and (acl2-numberp z)
		  (not (equal z 0)))
	     (equal (* a b z (/ z))
		    (* a b)))))

 ;; And here's an important lemma.  The differential of rdfn at any
 ;; point is the same as the differential of rdfn2 at that point,
 ;; plus the slope of the function from a to b.

 (defthm mvt-theorem-lemma
   (implies (and (inside-interval-p x (rdfn-subdomain))
		 (inside-interval-p (+ x eps) (rdfn-subdomain))
		 (realp eps)
		 (not (= eps 0)))
	    (equal (differential-rdfn x eps)
		   (+ (* (+ (- (rdfn (interval-left-endpoint (rdfn-subdomain))))
			    (rdfn (interval-right-endpoint (rdfn-subdomain))))
			 (/ (+ (- (interval-left-endpoint (rdfn-subdomain)))
			       (interval-right-endpoint (rdfn-subdomain)))))
		      (differential-rdfn2 x eps))))
   :hints (("Goal"
	    :in-theory (enable differential-rdfn-definition
			       differential-rdfn2-definition))))
 )

(in-theory (disable rdfn2))

;; Putting it all together, we get the mean value theorem!  We know
;; that the differential of rdfn is the sum of the differential of
;; rdfn2 and the slope of the line from a to b.  The differential of
;; rdfn2 at the critical point is small.  So, the derivative of rdfn
;; at the critical point must be equal to the slope of the line from a
;; to b!

(defthm expand-derivative-rolles-critical-point-2
    (equal (derivative-rdfn (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
						     (interval-right-endpoint (rdfn-subdomain))))
	   (STANDARD-PART
	    (DIFFERENTIAL-RDFN (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
						     (interval-right-endpoint (rdfn-subdomain)))
			       (/ (I-LARGE-INTEGER)))))
  :hints (("Goal"
	   :in-theory (enable derivative-rdfn-definition))))

(encapsulate
 nil

 (local
  (defthm lemma-1
      (REALP
       (ROLLES-CRITICAL-POINT-2 (INTERVAL-LEFT-ENDPOINT (RDFN-SUBDOMAIN))
				(INTERVAL-RIGHT-ENDPOINT (RDFN-SUBDOMAIN))))))
 (local
  (defthm lemma-2
      (realp (/ (i-large-integer)))))


 (local
  (defthm lemma-3
      (implies (and (standardp x)
		    (i-small eps))
	       (equal (standard-part (+ x eps))
		      (fix x)))
    ))

 (local
  (defthm-std lemma-4
      (STANDARDP (+ (* (RDFN (INTERVAL-RIGHT-ENDPOINT (RDFN-SUBDOMAIN)))
		       (/ (+ (- (INTERVAL-LEFT-ENDPOINT (RDFN-SUBDOMAIN)))
			     (INTERVAL-RIGHT-ENDPOINT (RDFN-SUBDOMAIN)))))
		    (* (- (RDFN (INTERVAL-LEFT-ENDPOINT (RDFN-SUBDOMAIN))))
		       (/ (+ (- (INTERVAL-LEFT-ENDPOINT (RDFN-SUBDOMAIN)))
			     (INTERVAL-RIGHT-ENDPOINT (RDFN-SUBDOMAIN)))))))))

 (defthm mvt-theorem
     (equal (derivative-rdfn (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
						      (interval-right-endpoint (rdfn-subdomain))))
	    (/ (- (rdfn (interval-right-endpoint (rdfn-subdomain)))
		  (rdfn (interval-left-endpoint (rdfn-subdomain))))
	       (- (interval-right-endpoint (rdfn-subdomain))
		  (interval-left-endpoint (rdfn-subdomain)))))
   :hints (("Goal"
	    :use ((:instance standard-part-of-plus
			     (x (differential-rdfn2 (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
									     (interval-right-endpoint (rdfn-subdomain)))
						    (/ (i-large-integer))))
			     (y (+ (- (* (rdfn (interval-left-endpoint (rdfn-subdomain)))
					 (/ (+ (- (interval-left-endpoint (rdfn-subdomain)))
					       (interval-right-endpoint (rdfn-subdomain))))))
				   (* (rdfn (interval-right-endpoint (rdfn-subdomain)))
				      (/ (+ (- (interval-left-endpoint (rdfn-subdomain)))
					    (interval-right-endpoint (rdfn-subdomain))))))))
		  (:instance mvt-theorem-lemma
			     (x (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							 (interval-right-endpoint (rdfn-subdomain))))
			     (eps (/ (i-large-integer))))
		  (:instance lemma-3
			     (eps (DIFFERENTIAL-RDFN2
				   (ROLLES-CRITICAL-POINT-2 (INTERVAL-LEFT-ENDPOINT (RDFN-SUBDOMAIN))
							    (INTERVAL-RIGHT-ENDPOINT (RDFN-SUBDOMAIN)))
				   (/ (I-LARGE-INTEGER))))
			     (x (+ (* (RDFN (INTERVAL-RIGHT-ENDPOINT (RDFN-SUBDOMAIN)))
				      (/ (+ (- (INTERVAL-LEFT-ENDPOINT (RDFN-SUBDOMAIN)))
					    (INTERVAL-RIGHT-ENDPOINT (RDFN-SUBDOMAIN)))))
				   (* (- (RDFN (INTERVAL-LEFT-ENDPOINT (RDFN-SUBDOMAIN))))
				      (/ (+ (- (INTERVAL-LEFT-ENDPOINT (RDFN-SUBDOMAIN)))
					    (INTERVAL-RIGHT-ENDPOINT (RDFN-SUBDOMAIN))))))))
		  )
	    :in-theory '(lemma-1 lemma-2 lemma-4 expand-derivative-rolles-critical-point-2
			 commutativity-of-* commutativity-of-+ distributivity
			 rolles-theorem-2-corollary
			 inside-interval-rolles-critical-point-2
			 inside-interval-rolles-critical-point-+-/i-large-integer
			 fix
			 ))))
 )

(defun-sk exists-mvt-point ()
  (exists (x)
	  (and (inside-interval-p x (rdfn-subdomain))
	       (not (equal x (interval-left-endpoint (rdfn-subdomain))))
	       (not (equal x (interval-right-endpoint (rdfn-subdomain))))
	       (equal (derivative-rdfn x)
		      (/ (- (rdfn (interval-right-endpoint (rdfn-subdomain)))
			    (rdfn (interval-left-endpoint (rdfn-subdomain))))
			 (- (interval-right-endpoint (rdfn-subdomain))
			    (interval-left-endpoint (rdfn-subdomain))))))))

(defthm mvt-theorem-sk
    (exists-mvt-point)
    :hints (("Goal"
	     :use ((:instance exists-mvt-point-suff
			      (x (rolles-critical-point-2 (interval-left-endpoint (rdfn-subdomain))
							  (interval-right-endpoint (rdfn-subdomain)))))
		   (:instance mvt-theorem)
		   (:instance rolles-theorem-2-specialized))
	     :in-theory (disable exists-mvt-point-suff
				 mvt-theorem
				 rolles-theorem-2-specialized))))
