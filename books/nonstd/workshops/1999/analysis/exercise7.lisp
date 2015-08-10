#|
 This book presents a proof of the _classical_ Rolle's theorem.  In
 particular, it does not insist that its arguments be standard (as it
 shouldn't).

 Compare this with derivatives.lisp.  The key step is the definition
 of derivative-rdfn, where we use defun-std instead of defun.  That
 way, when we prove Rolle's theorem, we can use defthm-std and
 dispense with the hypothesis that a and b are standard-numberp.  This
 works because rdfn, and rolles-critical-point are both standard
 functions, and the only non-standard function in the original
 statement of Rolles theorem was derivative-rdfn:

    (defthm rolles-theorem
      (implies (and (realp a) (standard-numberp a)
		    (realp b) (standard-numberp b)
		    (= (rdfn a) (rdfn b))
		    (< a b))
	       (equal (derivative-rdfn (rolles-critical-point a b)) 0)))

 The rest of the proof is exactly the same as in derivatives.lisp.

|#

(in-package "ACL2")

(include-book "continuity")
(include-book "exercise4")
(include-book "exercise5")

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
 ((rdfn (x) t))

 ;; Our witness continuous function is the identity function.

 (local (defun rdfn (x) x))

 ;; The function returns standard values for standard arguments.

 (defthm rdfn-standard
   (implies (standard-numberp x)
	    (standard-numberp (rdfn x)))
   :rule-classes (:rewrite :type-prescription))

 ;; For real arguments, the function returns real values.

 (defthm rdfn-real
   (implies (realp x)
	    (realp (rdfn x)))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y1 and y2 are two arbitrary reals
 ;; close to x, then (rdfn(x)-rdfn(y1))/(x-y1) is close to
 ;; (rdfn(x)-rdfn(y2))/(x-y2).  Also, (rdfn(x)-rdfn(y1))/(x-y1) is
 ;; limited.  What this means is that the standard-part of that is a
 ;; standard number, and we'll call that the derivative of rdfn at x.

 (defthm rdfn-differentiable
   (implies (and (standard-numberp x)
		 (realp x)
		 (realp y1)
		 (realp y2)
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
   (implies (and (standard-numberp x)
		 (realp x)
		 (i-close x y)
		 (realp y))
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
				       (rcfn rdfn)))
	   :in-theory (disable find-max-rcfn-x-n-limited))))

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
  (implies (and (realp a)
		(realp b)
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rdfn x) (rdfn (find-max-rdfn-x a b))))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-is-maximum
				       (find-max-rcfn-x-n find-max-rdfn-x-n)
				       (find-max-rcfn-x find-max-rdfn-x)
				       (rcfn rdfn)))
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
				       (rcfn rdfn)))
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
				       (rcfn rdfn)))
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
				       (rcfn rdfn)))
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
  (implies (and (realp a)
		(realp b)
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rdfn (find-min-rdfn-x a b)) (rdfn x)))
  :hints (("Goal"
	   :use ((:functional-instance find-min-rcfn-is-minimum
				       (find-min-rcfn-x-n find-min-rdfn-x-n)
				       (find-min-rcfn-x find-min-rdfn-x)
				       (rcfn rdfn)))
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
				       (rcfn rdfn)))
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
				       (rcfn rdfn)))
	   :in-theory (disable find-min-rcfn-x-<=-b))))

;; Now, here's an important theorem.  If the minimum is equal to the
;; maximum, then rdfn is constant throughout [a,b].  We prove this for
;; arbitrary continuous functions.

(defthm min=max->-constant-rcfn
  (implies (and (realp a)
		(realp b)
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
  (implies (and (realp a)
		(realp b)
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
				       (rcfn rdfn)))
	   :in-theory (disable min=max->-constant-rcfn))))

;; Now, let's define the differential of rdfn.  I probably should have
;; swapped x and (+ x eps), so that the denominator was positive.  Oh well....

(defun differential-rdfn (x eps)
  (/ (- (rdfn x) (rdfn (+ x eps))) (- eps)))

;; An obvious fact is that the differential is a real number.

(defthm realp-differential-rdfn
  (implies (and (realp x)
		(realp eps))
	   (realp (differential-rdfn x eps)))
  :hints (("Goal"
	   :expand ((differential-rdfn x eps)))))

(in-theory (disable find-min-rdfn-x find-max-rdfn-x))

;; OK now, if the minimum value of rdfn on [a,b] is equal to its
;; maximum value, then the differential of the midpoint of [a,b]
;; (actually of any point in (a,b)) must be zero.  This is because the
;; function is constant.

(defthm rolles-theorem-lemma-1
  (implies (and (realp a)
		(realp b)
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
  (implies (and (realp a)
		(realp b)
		(< a b)
		(realp eps)
		(< 0 eps)
		(< a (- (find-max-rdfn-x a b) eps))
		(< (+ (find-max-rdfn-x a b) eps) b))
	   (<= (differential-rdfn (find-max-rdfn-x a b) eps) 0)))

;; Similarly, for a negative eps, rdfn is rising from x+eps to x, so
;; the eps-differntial of x is non-negative.

(defthm rolles-theorem-lemma-2b
  (implies (and (realp a)
		(realp b)
		(< a b)
		(realp eps)
		(< 0 eps)
		(< a (- (find-max-rdfn-x a b) eps))
		(< (+ (find-max-rdfn-x a b) eps) b))
	   (<= 0 (differential-rdfn (find-max-rdfn-x a b) (- eps)))))

;; Of course, the same claims follow for an internal minimum, min-x.
;; For a positive epsilon, the differential is non-positive.

(defthm rolles-theorem-lemma-2c
  (implies (and (realp a)
		(realp b)
		(< a b)
		(realp eps)
		(< 0 eps)
		(< a (- (find-min-rdfn-x a b) eps))
		(< (+ (find-min-rdfn-x a b) eps) b))
	   (<= 0 (differential-rdfn (find-min-rdfn-x a b) eps))))

;; And for a negative epsilon it is non-negative.

(defthm rolles-theorem-lemma-2d
  (implies (and (realp a)
		(realp b)
		(< a b)
		(realp eps)
		(< 0 eps)
		(< a (- (find-min-rdfn-x a b) eps))
		(< (+ (find-min-rdfn-x a b) eps) b))
	   (<= (differential-rdfn (find-min-rdfn-x a b) (- eps)) 0)))

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
   (implies (and (realp a) (standard-numberp a)
		 (realp x) (standard-numberp x)
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
   (implies (and (realp b) (standard-numberp b)
		 (realp x) (standard-numberp x)
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
  (implies (and (standard-numberp a)
		(standard-numberp b))
	   (and (standard-numberp (find-min-rdfn-x a b))
		(standard-numberp (find-max-rdfn-x a b))))
  :hints (("Goal"
	   :in-theory (enable find-min-rdfn-x find-max-rdfn-x))))

;; So what this means is that if max-x is in (a,b), so are max-x+eps
;; and max-x-eps.

(defthm rolles-theorem-lemma-2e
  (implies (and (realp a) (standard-numberp a)
		(realp b) (standard-numberp b)
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
  (implies (and (realp a) (standard-numberp a)
		(realp b) (standard-numberp b)
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
  (implies (and (realp a)
		(realp b)
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
  (implies (and (realp a)
		(realp b)
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
  (implies (and (realp a) (standard-numberp a)
		(realp b) (standard-numberp b)
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

;; Now, we can define the derivative of rdfn at x.  This is simply the
;; standard-part of an arbitrary infinitesimal differential at x.
;; Since the differential is arbitrary, we choose our favorite
;; epsilon.

;; But first, we need to show that the derivative of a standard point is
;; limited, so that the defun-std is permissible.

;; This (or something like it) is another theorem that should be in
;; nsa.lisp.

(local
 (defthm small+limited-close
   (implies (and (i-limited x)
		 (i-small eps))
	    (i-close x (+ eps x)))
   :hints (("Goal" :in-theory (enable nsa-theory)))))

(defthm differential-rdfn-limited
  (implies (and (realp x)
		(standard-numberp x)
		(realp eps)
		(i-small eps))
	   (i-limited (differential-rdfn x eps)))
  :hints (("Goal"
	   :use ((:instance rdfn-differentiable (x x) (y1 (+ eps x)) (y2 (+ eps x))))
	   :in-theory (disable rdfn-differentiable)))
  )

(in-theory (disable differential-rdfn))

(defun-std derivative-rdfn (x)
  (if (realp x)
      (standard-part (differential-rdfn x (/ (i-large-integer))))
    0))

(in-theory (disable derivative-rdfn))

;; We would like to rephrase the differentiability criteria in terms
;; of a small eps1 and eps2 instead of a y1, y2 close to x.

(defthm rdfn-differentiable-2a
   (implies (and (realp x)    (standard-numberp x)
		 (realp eps1) (i-small eps1) (not (= eps1 0))
		 (realp eps2) (i-small eps2) (not (= eps2 0)))
	    (i-close (differential-rdfn x eps1)
		     (differential-rdfn x eps2)))
   :hints (("Goal"
	    :use ((:instance rdfn-differentiable
			     (y1 (+ x eps1))
			     (y2 (+ x eps2))))
	    :in-theory (enable-disable (differential-rdfn)
				       (rdfn-differentiable)))))

;; This is the ohter requirement of a differntiable function, namely
;; that the differntial is limited.

(defthm rdfn-differentiable-2b
   (implies (and (realp x)   (standard-numberp x)
		 (realp eps) (i-small eps) (not (= eps 0)))
	    (i-limited (differential-rdfn x eps)))
   :hints (("Goal"
	    :expand ((differential-rdfn x eps)))
	   ("Goal'"
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
   (implies (and (realp x)   (standard-numberp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-rdfn x eps))
		   (derivative-rdfn x)))
   :hints (("Goal"
	    :use ((:instance rdfn-differentiable-2a
			     (eps1 eps)
			     (eps2 (/ (i-large-integer))))
		  (:instance rdfn-differentiable-2b)
		  (:instance rdfn-differentiable-2b
			     (eps (/ (i-large-integer))))
		  (:instance close-same-standard-part
			     (x (differential-rdfn x eps))
			     (y (differential-rdfn x (/ (i-large-integer))))))
	    :in-theory (enable-disable (derivative-rdfn)
				       (rdfn-differentiable-2a
					rdfn-differentiable-2b
					close-same-standard-part)))))

;; This is a major lemma.  What it says if that if x is a number so
;; that a differential of rdfn at x with a given epsilon is positive,
;; but with -epsilon it's negative, then the derivative at x must be
;; zero.

(defthm derivative-==-0a
   (implies (and (realp x)   (standard-numberp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (<= 0 (differential-rdfn x eps))
		 (<= (differential-rdfn x (- eps)) 0)
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (= 0 (derivative-rdfn x)))
   :rule-classes nil ; added in v2-6 where "=" acts like "equal" just above.
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
	    :in-theory (disable derivative-rdfn
				differential-rdfn-close
				standard-part-<=))))

;; Of course, the same applies if for a given epsilon the differntials
;; are negative and for -epsilon they're positive.  Hmmm, it looks
;; like the previous theorem is more general, so this is probably not
;; needed.

(defthm derivative-==-0b
   (implies (and (realp x)   (standard-numberp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (<= (differential-rdfn x eps) 0)
		 (<= 0 (differential-rdfn x (- eps)))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (= 0 (derivative-rdfn x)))
   :rule-classes nil ; added in v2-6 where "=" acts like "equal" just above.
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
	    :in-theory (disable derivative-rdfn
				differential-rdfn-close
				standard-part-<=))))

;; But it is enough to prove Rolle's theorem.  The derivative of the
;; critical point is equal to zero.  The critical point is either an
;; extreme value of rdfn interior to (a,b), or it's equal to the
;; midpoint of (a,b) if rdfn happens to be a constant function.  In
;; either case, the derivative is zero.

(defthm-std rolles-theorem
  (implies (and (realp a)
		(realp b)
		(= (rdfn a) (rdfn b))
		(< a b))
	   (equal (derivative-rdfn (rolles-critical-point a b)) 0))
  :hints (("Subgoal 3"
	   :use ((:instance rolles-theorem-lemma-1
			    (eps (/ (i-large-integer))))
		 (:instance rolles-theorem-lemma-4
			    (eps (/ (i-large-integer)))))
	   :in-theory (enable-disable (derivative-rdfn)
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
	   :in-theory (disable ;derivative-rdfn
			       rolles-theorem-lemma-2c
			       rolles-theorem-lemma-2d
			       rolles-theorem-lemma-2f
			       rolles-theorem-lemma-3b))
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
			    (eps (/ (i-large-integer)))))
	   :in-theory (disable rolles-theorem-lemma-2a
			       rolles-theorem-lemma-2b
			       rolles-theorem-lemma-2e
			       rolles-theorem-lemma-3a))))

