(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "nsa")
(include-book "derivatives")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(encapsulate
 ((cr-fn1 (x) t)
  (cr-fn2 (x) t)
  (cr-fn2-domain () t)
  (cr-fn2-range () t))

 ;; Our witness continuous function is the identity function.

 (local (defun cr-fn1 (x) (realfix x)))
 (local (defun cr-fn2 (x) (realfix x)))
 (local (defun cr-fn2-domain () (interval 0 1)))
 (local (defun cr-fn2-range () (interval 0 1)))

 ;; The interval really is an interval

 (defthm intervalp-cr-fn2-domain
     (interval-p (cr-fn2-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm intervalp-cr-fn2-range
     (interval-p (cr-fn2-range))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is real

 (defthm cr-fn2-domain-real
     (implies (inside-interval-p x (cr-fn2-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 (defthm cr-fn2-range-real
     (implies (inside-interval-p x (cr-fn2-range))
	      (realp x))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm cr-fn2-domain-non-trivial
     (or (null (interval-left-endpoint (cr-fn2-domain)))
	 (null (interval-right-endpoint (cr-fn2-domain)))
	 (< (interval-left-endpoint (cr-fn2-domain))
	    (interval-right-endpoint (cr-fn2-domain))))
   :rule-classes nil)

 (defthm cr-fn2-range-non-trivial
     (or (null (interval-left-endpoint (cr-fn2-range)))
	 (null (interval-right-endpoint (cr-fn2-range)))
	 (< (interval-left-endpoint (cr-fn2-range))
	    (interval-right-endpoint (cr-fn2-range))))
   :rule-classes nil)

 ;; The functions return real values (even for improper arguments).

 (defthm cr-fn1-real
     (realp (cr-fn1 x))
   :rule-classes (:rewrite :type-prescription))

 (defthm cr-fn2-real
     (realp (cr-fn2 x))
   :rule-classes (:rewrite :type-prescription))

 ;; The range of fn2 is inside the domain of fn1

 (defthm cr-fn2-range-in-domain-of-fn2
     (implies (inside-interval-p x (cr-fn2-domain))
	      (inside-interval-p (cr-fn2 x) (cr-fn2-range))))

 ;; If x is a standard real and y1 and y2 are two arbitrary reals
 ;; close to x, then (rdfn(x)-rdfn(y1))/(x-y1) is close to
 ;; (rdfn(x)-rdfn(y2))/(x-y2).  Also, (rdfn(x)-rdfn(y1))/(x-y1) is
 ;; limited.  What this means is that the standard-part of that is a
 ;; standard number, and we'll call that the derivative of rdfn at x.

 (defthm cr-fn1-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (cr-fn2-range))
		 (inside-interval-p y1 (cr-fn2-range))
		 (inside-interval-p y2 (cr-fn2-range))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (cr-fn1 x) (cr-fn1 y1)) (- x y1)))
		 (i-close (/ (- (cr-fn1 x) (cr-fn1 y1)) (- x y1))
			  (/ (- (cr-fn1 x) (cr-fn1 y2)) (- x y2))))))

 (defthm cr-fn2-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (cr-fn2-domain))
		 (inside-interval-p y1 (cr-fn2-domain))
		 (inside-interval-p y2 (cr-fn2-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (cr-fn2 x) (cr-fn2 y1)) (- x y1)))
		 (i-close (/ (- (cr-fn2 x) (cr-fn2 y1)) (- x y1))
			  (/ (- (cr-fn2 x) (cr-fn2 y2)) (- x y2))))))


 )

;; It helps (for hint purposes) to separate the two parts of the
;; condition for differentiability

(defthm cr-fn1-differentiable-part1
    (implies (and (standardp x)
		  (inside-interval-p x (cr-fn2-range))
		  (inside-interval-p y1 (cr-fn2-range))
		  (i-close x y1) (not (= x y1)))
	     (i-limited (/ (- (cr-fn1 x) (cr-fn1 y1)) (- x y1))))
  :hints (("Goal"
	   :use ((:instance cr-fn1-differentiable (y2 y1)))
	   :in-theory nil)))

(defthm cr-fn1-differentiable-part2
    (implies (and (standardp x)
		  (inside-interval-p x (cr-fn2-range))
		  (inside-interval-p y1 (cr-fn2-range))
		  (inside-interval-p y2 (cr-fn2-range))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (cr-fn1 x) (cr-fn1 y1)) (- x y1))
		      (/ (- (cr-fn1 x) (cr-fn1 y2)) (- x y2))))
  :hints (("Goal"
	   :use ((:instance cr-fn1-differentiable))
	   :in-theory nil)))

(defthm cr-fn2-differentiable-part1
    (implies (and (standardp x)
		  (inside-interval-p x (cr-fn2-domain))
		  (inside-interval-p y1 (cr-fn2-domain))
		  (i-close x y1) (not (= x y1)))
	     (i-limited (/ (- (cr-fn2 x) (cr-fn2 y1)) (- x y1))))
  :hints (("Goal"
	   :use ((:instance cr-fn2-differentiable (y2 y1)))
	   :in-theory nil)))

(defthm cr-fn2-differentiable-part2
    (implies (and (standardp x)
		  (inside-interval-p x (cr-fn2-domain))
		  (inside-interval-p y1 (cr-fn2-domain))
		  (inside-interval-p y2 (cr-fn2-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (cr-fn2 x) (cr-fn2 y1)) (- x y1))
		      (/ (- (cr-fn2 x) (cr-fn2 y2)) (- x y2))))
  :hints (("Goal"
	   :use ((:instance cr-fn2-differentiable))
	   :in-theory nil)))

;; It follows by functional instantiation that both cr-fn1 and cr-fn2 are continuous

(defthm cr-fn1-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (cr-fn2-range))
		 (i-close x y)
		 (inside-interval-p y (cr-fn2-range)))
	    (i-close (cr-fn1 x) (cr-fn1 y)))

  :hints (("Goal"
	   :by (:functional-instance rdfn-continuous
				     (rdfn cr-fn1)
				     (rdfn-domain cr-fn2-range)))
	  ("Subgoal 3"
	   :use ((:instance cr-fn1-differentiable))
	   :in-theory (disable cr-fn1-differentiable))
	  ("Subgoal 2"
	   :use ((:instance cr-fn2-range-non-trivial)))
	  )
  )

(defthm cr-fn2-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (cr-fn2-domain))
		 (i-close x y)
		 (inside-interval-p y (cr-fn2-domain)))
	    (i-close (cr-fn2 x) (cr-fn2 y)))

  :hints (("Goal"
	   :by (:functional-instance rdfn-continuous
				     (rdfn cr-fn2)
				     (rdfn-domain cr-fn2-domain)))
	  ("Subgoal 3"
	   :use ((:instance cr-fn2-differentiable))
	   :in-theory (disable cr-fn2-differentiable))
	  ("Subgoal 2"
	   :use ((:instance cr-fn2-domain-non-trivial)))
	  )
  )

;; We define the differential and derivative functions for cr-fn1 and cr-fn2

(encapsulate

 ( ((differential-cr-fn1 * *) => *) )

 (local
  (defun differential-cr-fn1 (x eps)
    (/ (- (cr-fn1 (+ x eps)) (cr-fn1 x)) eps)))

 (defthm differential-cr-fn1-definition
   (implies (and (inside-interval-p x (cr-fn2-range))
                 (inside-interval-p (+ x eps) (cr-fn2-range)))
            (equal (differential-cr-fn1 x eps)
                   (/ (- (cr-fn1 (+ x eps)) (cr-fn1 x)) eps)))))

(defthm realp-differential-cr-fn1
  (implies (and (inside-interval-p x (cr-fn2-range))
		(inside-interval-p (+ x eps) (cr-fn2-range))
		(realp eps))
	   (realp (differential-cr-fn1 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-cr-fn1)
				     (rdfn cr-fn1)
				     (rdfn-domain cr-fn2-range)))))

(defthm differential-cr-fn1-limited
    (implies (and (standardp x)
		  (inside-interval-p x (cr-fn2-range))
		  (inside-interval-p (+ x eps) (cr-fn2-range))
		  (i-small eps))
	     (i-limited (differential-cr-fn1 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-cr-fn1)
				     (rdfn cr-fn1)
				     (rdfn-domain cr-fn2-range)))))


(in-theory (disable differential-cr-fn1-definition))

(encapsulate

 ( ((derivative-cr-fn1 *) => *) )

 (local
  (defun-std derivative-cr-fn1 (x)
    (if (inside-interval-p x (cr-fn2-range))
        (if (inside-interval-p (+ x (/ (i-large-integer))) (cr-fn2-range))
            (standard-part (differential-cr-fn1 x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (cr-fn2-range))
	      (standard-part (differential-cr-fn1 x (- (/ (i-large-integer)))))
            'error))
      'error)))

 (defthm derivative-cr-fn1-definition
   (implies (and (inside-interval-p x (cr-fn2-range))
                 (standardp x))
            (equal (derivative-cr-fn1 x)
                   (if (inside-interval-p (+ x (/ (i-large-integer))) (cr-fn2-range))
                       (standard-part (differential-cr-fn1 x (/ (i-large-integer))))
                     (if (inside-interval-p (- x (/ (i-large-integer))) (cr-fn2-range))
                         (standard-part (differential-cr-fn1 x (- (/ (i-large-integer)))))
                       'error)))))
 )

(defthm real-derivative-cr-fn1
    (implies (inside-interval-p x (cr-fn2-range))
	     (realp (derivative-cr-fn1 x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-cr-fn1)
				     (differential-rdfn differential-cr-fn1)
				     (rdfn cr-fn1)
				     (rdfn-domain cr-fn2-range)))))

(defthm differential-cr-fn1-close
   (implies (and (inside-interval-p x (cr-fn2-range))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (cr-fn2-range))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-cr-fn1 x eps))
		   (derivative-cr-fn1 x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-cr-fn1)
				     (differential-rdfn differential-cr-fn1)
				     (rdfn cr-fn1)
				     (rdfn-domain cr-fn2-range)))))

(in-theory (disable derivative-cr-fn1-definition))

(encapsulate

 ( ((differential-cr-fn2 * *) => *) )

 (local
  (defun differential-cr-fn2 (x eps)
    (/ (- (cr-fn2 (+ x eps)) (cr-fn2 x)) eps)))

 (defthm differential-cr-fn2-definition
   (implies (and (inside-interval-p x (cr-fn2-domain))
                 (inside-interval-p (+ x eps) (cr-fn2-domain)))
            (equal (differential-cr-fn2 x eps)
                   (/ (- (cr-fn2 (+ x eps)) (cr-fn2 x)) eps)))))

(defthm realp-differential-cr-fn2
  (implies (and (inside-interval-p x (cr-fn2-domain))
		(inside-interval-p (+ x eps) (cr-fn2-domain))
		(realp eps))
	   (realp (differential-cr-fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-cr-fn2)
				     (rdfn cr-fn2)
				     (rdfn-domain cr-fn2-domain)))))

(defthm differential-cr-fn2-limited
    (implies (and (standardp x)
		  (inside-interval-p x (cr-fn2-domain))
		  (inside-interval-p (+ x eps) (cr-fn2-domain))
		  (i-small eps))
	     (i-limited (differential-cr-fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-cr-fn2)
				     (rdfn cr-fn2)
				     (rdfn-domain cr-fn2-domain)))))


(in-theory (disable differential-cr-fn2-definition))

(encapsulate
 ( ((derivative-cr-fn2 *) => *) )

 (local
  (defun-std derivative-cr-fn2 (x)
    (if (inside-interval-p x (cr-fn2-domain))
        (if (inside-interval-p (+ x (/ (i-large-integer))) (cr-fn2-domain))
            (standard-part (differential-cr-fn2 x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (cr-fn2-domain))
	      (standard-part (differential-cr-fn2 x (- (/ (i-large-integer)))))
            'error))
      'error)))

 (defthm derivative-cr-fn2-definition
   (implies (and (inside-interval-p x (cr-fn2-domain))
                 (standardp x))
            (equal (derivative-cr-fn2 x)
                   (if (inside-interval-p (+ x (/ (i-large-integer))) (cr-fn2-domain))
                       (standard-part (differential-cr-fn2 x (/ (i-large-integer))))
                     (if (inside-interval-p (- x (/ (i-large-integer))) (cr-fn2-domain))
                         (standard-part (differential-cr-fn2 x (- (/ (i-large-integer)))))
                       'error)))))
 )

(defthm real-derivative-cr-fn2
    (implies (inside-interval-p x (cr-fn2-domain))
	     (realp (derivative-cr-fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-cr-fn2)
				     (differential-rdfn differential-cr-fn2)
				     (rdfn cr-fn2)
				     (rdfn-domain cr-fn2-domain)))))

(defthm differential-cr-fn2-close
   (implies (and (inside-interval-p x (cr-fn2-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (cr-fn2-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-cr-fn2 x eps))
		   (derivative-cr-fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-cr-fn2)
				     (differential-rdfn differential-cr-fn2)
				     (rdfn cr-fn2)
				     (rdfn-domain cr-fn2-domain)))))

(in-theory (disable derivative-cr-fn2-definition))

;; All functions are standard

(local
 (defthm-std standard-cr-fn1
     (implies (standardp x)
	      (standardp (cr-fn1 x)))))

(local
 (defthm-std standard-cr-fn2
     (implies (standardp x)
	      (standardp (cr-fn2 x)))))

;; The differentials of the functions are close to each other and the derivatives

(local
 (defthm close-if-same-standard-part
     (implies (and (acl2-numberp x)
		   (acl2-numberp y)
		   (i-limited x)
		   (i-limited y)
		   (equal (standard-part x) (standard-part y)))
	      (i-close x y))
   :hints (("Goal"
	    :use ((:instance i-close-transitive
			     (x x)
			     (y (standard-part x))
			     (z y)))
	    :in-theory (disable i-close-transitive)))))

(local
 (defthm close-differential-cr-fn1
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-range))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (cr-fn2-range))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (cr-fn2-range)))
	      (i-close (differential-cr-fn1 x eps1)
		       (differential-cr-fn1 x eps2)))
   :hints (("Goal"
	    :use ((:instance close-if-same-standard-part
			     (x (differential-cr-fn1 x eps1))
			     (y (differential-cr-fn1 x eps2)))
		  (:instance differential-cr-fn1-close
			     (eps eps1))
		  (:instance differential-cr-fn1-close
			     (eps eps2)))
	    :in-theory (disable close-if-same-standard-part differential-cr-fn1-close)))))

(local
 (defthm close-differential-cr-fn2
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (cr-fn2-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (cr-fn2-domain)))
	      (i-close (differential-cr-fn2 x eps1)
		       (differential-cr-fn2 x eps2)))
   :hints (("Goal"
	    :use ((:instance close-if-same-standard-part
			     (x (differential-cr-fn2 x eps1))
			     (y (differential-cr-fn2 x eps2)))
		  (:instance differential-cr-fn2-close
			     (eps eps1))
		  (:instance differential-cr-fn2-close
			     (eps eps2)))
	    :in-theory (disable close-if-same-standard-part differential-cr-fn2-close)))))

(local
 (defthm close-cr-fn1-eps1-eps2
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-range))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (cr-fn2-range))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (cr-fn2-range)))
	      (i-close (cr-fn1 (+ x eps1))
		       (cr-fn1 (+ x eps2))))
   :hints (("Goal"
	    :use ((:instance i-close-transitive
			     (x (cr-fn1 (+ x eps1)))
			     (y (cr-fn1 x))
			     (z (cr-fn1 (+ x eps2))))
		  (:instance i-close-symmetric
			     (x (cr-fn1 x))
			     (y (cr-fn1 (+ x eps1))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps1))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps2))
		  (:instance cr-fn1-continuous
			     (x x)
			     (y (+ x eps1)))
		  (:instance cr-fn1-continuous
			     (x x)
			     (y (+ x eps2))))
	    :in-theory '(inside-interval-is-real)))))


(local
 (defthm close-cr-fn2-eps1-eps2
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (cr-fn2-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (cr-fn2-domain)))
	      (i-close (cr-fn2 (+ x eps1))
		       (cr-fn2 (+ x eps2))))
   :hints (("Goal"
	    :use ((:instance i-close-transitive
			     (x (cr-fn2 (+ x eps1)))
			     (y (cr-fn2 x))
			     (z (cr-fn2 (+ x eps2))))
		  (:instance i-close-symmetric
			     (x (cr-fn2 x))
			     (y (cr-fn2 (+ x eps1))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps1))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps2))
		  (:instance cr-fn2-continuous
			     (x x)
			     (y (+ x eps1)))
		  (:instance cr-fn2-continuous
			     (x x)
			     (y (+ x eps2))))
	    :in-theory '(inside-interval-is-real)))))

(local
 (defthm limited-cr-fn1-eps
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-range))
		   (realp eps)
		   (i-small eps)
		   (inside-interval-p (+ x eps) (cr-fn2-range)))
	      (i-limited (cr-fn1 (+ x eps))))
   :hints (("Goal"
	    :use ((:instance i-close-limited
			     (x (cr-fn1 x))
			     (y (cr-fn1 (+ x eps))))
		  (:instance cr-fn1-continuous
			     (x x)
			     (y (+ x eps)))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps)))
	    :in-theory '(cr-fn1-real
			 standard-cr-fn1
			 standards-are-limited
			 inside-interval-is-real)))))

(local
 (defthm limited-cr-fn2-eps
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (realp eps)
		   (i-small eps)
		   (inside-interval-p (+ x eps) (cr-fn2-domain)))
	      (i-limited (cr-fn2 (+ x eps))))
   :hints (("Goal"
	    :use ((:instance i-close-limited
			     (x (cr-fn2 x))
			     (y (cr-fn2 (+ x eps))))
		  (:instance cr-fn2-continuous
			     (x x)
			     (y (+ x eps)))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps)))
	    :in-theory '(cr-fn2-real
			 standard-cr-fn2
			 standards-are-limited
			 inside-interval-is-real)))))

;; Now we define the composition and its derivative

(encapsulate
 ( ((cr-fn1-o-fn2 *) => *) )

 (local
  (defun cr-fn1-o-fn2 (x)
    (cr-fn1 (cr-fn2 x))))

 (defthm cr-fn1-o-fn2-definition
   (implies (inside-interval-p x (cr-fn2-domain))
            (equal (cr-fn1-o-fn2 x)
                   (cr-fn1 (cr-fn2 x)))))
 )

(encapsulate
 ( ((differential-cr-fn1-o-fn2 * *) => *) )

 (local
  (defun differential-cr-fn1-o-fn2 (x eps)
    (if (equal (cr-fn2 (+ x eps)) (cr-fn2 x))
        0
      (* (differential-cr-fn1 (cr-fn2 x) (- (cr-fn2 (+ x eps)) (cr-fn2 x)))
	 (differential-cr-fn2 x eps)))))

 (defthm differential-cr-fn1-o-fn2-definition
   (implies (and (inside-interval-p x (cr-fn2-domain))
                 (inside-interval-p (+ x eps) (cr-fn2-domain)))
            (equal (differential-cr-fn1-o-fn2 x eps)
                   (if (equal (cr-fn2 (+ x eps)) (cr-fn2 x))
                       0
                     (* (differential-cr-fn1 (cr-fn2 x) (- (cr-fn2 (+ x eps)) (cr-fn2 x)))
                        (differential-cr-fn2 x eps))))))
 )


(encapsulate
 ( ((derivative-cr-fn1-o-fn2 *) => *) )

 (local
  (defun derivative-cr-fn1-o-fn2 (x)
    (* (derivative-cr-fn1 (cr-fn2 x))
       (derivative-cr-fn2 x))))

 (defthm derivative-cr-fn1-o-fn2-definition
   (implies (inside-interval-p x (cr-fn2-domain))
            (equal (derivative-cr-fn1-o-fn2 x)
                   (* (derivative-cr-fn1 (cr-fn2 x))
                      (derivative-cr-fn2 x)))))
 )

;; First we show that the differential really is the differential of the
;; composition.

(encapsulate
 nil

 (local
  (defthm lemma-1
      (implies (and (not (equal (cr-fn2 (+ x eps)) (cr-fn2 x)))
                    (inside-interval-p x (cr-fn2-domain))
                    (inside-interval-p (+ x eps) (cr-fn2-domain)))
	       (equal (- (cr-fn1-o-fn2 (+ x eps)) (cr-fn1-o-fn2 x))
		      (* (differential-cr-fn1 (cr-fn2 x) (- (cr-fn2 (+ x eps)) (cr-fn2 x)))
			 (- (cr-fn2 (+ x eps)) (cr-fn2 x)))))
    :hints (("Goal"
	     :use ((:instance INVERSE-OF-*
			      (x (- (cr-fn2 (+ x eps)) (cr-fn2 x))))
                   (:instance cr-fn2-range-in-domain-of-fn2
                              (x (+ x eps)))
                   (:instance cr-fn2-range-in-domain-of-fn2
                              (x x))
		   (:theorem (equal (+ (CR-FN2 X)
				       (CR-FN2 (+ X EPS))
				       (- (CR-FN2 X)))
				    (CR-FN2 (+ X EPS))))
		   )
	     :in-theory '(differential-cr-fn1-definition
                          commutativity-of-*
			  associativity-of-*
			  inverse-of-+-as=0
			  /-CANCELLATION-ON-LEFT
			  fix
			  cr-fn2-real
			  cr-fn1-o-fn2-definition
					;commutativity-of-+
					;MINUS-CANCELLATION-ON-LEFT
			  )))))

 (local
  (defthm lemma-2
      (implies (and (inside-interval-p x (cr-fn2-domain))
                    (inside-interval-p (+ x eps) (cr-fn2-domain)))
               (equal (- (cr-fn1-o-fn2 (+ x eps)) (cr-fn1-o-fn2 x))
                      (* (differential-cr-fn1 (cr-fn2 x) (- (cr-fn2 (+ x eps)) (cr-fn2 x)))
                         (- (cr-fn2 (+ x eps)) (cr-fn2 x)))))
    :hints (("Goal"
	     :cases ((equal (cr-fn2 (+ x eps)) (cr-fn2 x)))
	     :use ((:instance lemma-1))
	     :in-theory (disable lemma-1 cr-fn1-o-fn2-definition))
	    ("Subgoal 1"
	     :in-theory '(differential-cr-fn1-definition
			  inverse-of-+
			  cr-fn1-o-fn2-definition)))))

 (defthm expand-differential-cr-fn1-o-fn2
   (implies (and (inside-interval-p x (cr-fn2-domain))
                 (inside-interval-p (+ x eps) (cr-fn2-domain)))
            (equal (differential-cr-fn1-o-fn2 x eps)
                   (/ (- (cr-fn1-o-fn2 (+ x eps)) (cr-fn1-o-fn2 x)) eps)))
   :hints (("Goal"
	    :in-theory '(lemma-2
			 differential-cr-fn1-o-fn2-definition
			 differential-cr-fn2-definition
			 inverse-of-+
			 associativity-of-*)
	    ))
   :rule-classes nil)
 )

;; When fn2(x) = fn2(x+eps), we have that fn2'(x) = 0, and fn1-o-fn2'(x) = 0.
;; So the theorem holds (somewhat vacuously).

;; We start with fn2'(x) = 0.

(defthm derivative-cr-fn2-must-be-zero
    (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (realp eps)
		   (not (equal eps 0))
		   (i-small eps)
		   (inside-interval-p (+ x eps) (cr-fn2-domain))
		   (equal (cr-fn2 (+ x eps)) (cr-fn2 x)))
	     (equal (derivative-cr-fn2 x) 0))
  :hints (("Goal"
	   :use ((:instance differential-cr-fn2-close))
	   :in-theory '(differential-cr-fn2-definition
			inverse-of-+)
	   )))

;; The definition shows that the differential of fn1-o-fn2(x) = 0

(defthm differential-cr-fn1-o-fn2-must-be-zero
    (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (realp eps)
		   (not (equal eps 0))
		   (i-small eps)
		   (inside-interval-p (+ x eps) (cr-fn2-domain))
		   (equal (cr-fn2 (+ x eps)) (cr-fn2 x)))
	     (equal (differential-cr-fn1-o-fn2 x eps) 0))
  :hints (("Goal"
	   :in-theory '(differential-cr-fn1-o-fn2-definition
			inverse-of-+)
	   )))

;; And of course, the derivative of fn1-o-fn2(x) is also 0

(defthm derivative-cr-fn1-o-fn2-must-be-zero
    (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (realp eps)
		   (not (equal eps 0))
		   (i-small eps)
		   (inside-interval-p (+ x eps) (cr-fn2-domain))
		   (equal (cr-fn2 (+ x eps)) (cr-fn2 x)))
	     (equal (derivative-cr-fn1-o-fn2 x) 0))
  :hints (("Goal"
	   :in-theory '(derivative-cr-fn2-must-be-zero
			derivative-cr-fn1-o-fn2-definition)
	   )))

;; So, let's get the easy case out of the way.  When
;; fn2(x) = fn2(x+eps), we have that fn1-o-fn2 is differentiable
;; (and its derivative is zero).

(encapsulate
 nil

 (local
  (defthm lemma-1
      (implies (and (acl2-numberp x)
		    (acl2-numberp y)
		    (not (= x y)))
	       (not (equal (+ (- x) y) 0)))))

 (local
  (defthm lemma-2
      (implies (i-close x y)
	       (i-small (+ (- x) y)))
    :hints (("Goal"
	     :use ((:instance i-small-uminus
			      (x (+ x (- y)))))
	     :in-theory '(i-close
			  distributivity-of-minus-over-+
			  functional-self-inversion-of-minus
			  fix)))))

 (local
  (defthm lemma-3
      (equal (+ (fix x) y) (+ x y))))

 (local
  (defthm lemma-4
      (equal (* (+ (- x1) y1)
		(/ (+ (- x) y)))
	     (* (+ x1 (- y1))
		(/ (+ x (- y)))))
    :hints (("Goal"
	     :use ((:instance (:theorem (equal (/ (- x) (- y)) (/ x y)))
			      (x (+ (- x1) y1))
			      (y (+ (- x) y))))))
    ))


 (local
  (defthm lemma-6
      (implies (inside-interval-p x (cr-fn2-domain))
	       (equal (differential-cr-fn1-o-fn2 x 0)
		      0))
    :hints (("goal"
             :use ((:instance differential-cr-fn1-o-fn2-definition
                              (x x)
                              (eps 0)))
	     :in-theory '(commutativity-of-+
			  unicity-of-0
			  fix
			  cr-fn2-real
                          (:forward-chaining inside-interval-is-real)
			  )))
    ))


 (local
  (defthm lemma-7
      (implies (and (acl2-numberp x)
		    (equal (standard-part x) 0))
	       (i-close 0 x))
    :hints (("Goal"
	     :in-theory '(i-close i-small fix standard-part-of-plus standard-part-of-uminus)))))

 (local
  (defthm lemma-8
      (implies (and (inside-interval-p x (cr-fn2-domain))
                    (inside-interval-p y2 (cr-fn2-domain)))
	       (realp (differential-cr-fn2 x (+ (- x) y2))))
    :hints (("Goal"
	     :in-theory (enable differential-cr-fn2-definition)))
    :rule-classes (:type-prescription :rewrite)))

 (local
  (defthm lemma-9a
      (implies (and (realp x)
		    (<= 0 x)
		    (equal (standard-part x) 0))
	       (not (i-large x)))
    :hints (("Goal"
	     :use ((:instance standard-part-<=
			      (x 1)
			      (y x))
		   (:instance standard-part-<=
			      (x 1)
			      (y (/ x)))
		   (:instance (:theorem (implies (and (realp x) (< x 1) (< 0 x)) (< 1 (/ x)))))
		   )
	     :in-theory '(i-small i-large
			  <-UNARY-/-POSITIVE-RIGHT
			  COMMUTATIVITY-OF-*
			  UNICITY-OF-1
			  fix
			  )))
    :rule-classes nil))

 (local
  (defthm lemma-9
      (implies (and (realp x)
		    (equal (standard-part x) 0))
	       (not (i-large x)))
    :hints (("Goal"
	     :use ((:instance lemma-9a)
		   (:instance lemma-9a (x (- x)))
		   (:instance i-large-uminus))
	     :in-theory '(standard-part-of-uminus fix)
	     ))))


 (local
  (defthm lemma-10a
      (equal (* a 0) 0)))

 (local
  (defthm lemma-10
      (implies (and (inside-interval-p x (cr-fn2-domain))
                    (inside-interval-p y2 (cr-fn2-domain))
		    (i-limited (DIFFERENTIAL-CR-FN1 (CR-FN2 X)
						    (+ (- (CR-FN2 X)) (CR-FN2 Y2))))
		    (EQUAL (STANDARD-PART (DIFFERENTIAL-CR-FN2 X (+ (- X) Y2)))
			   0))
	       (i-close 0 (DIFFERENTIAL-CR-FN1-O-FN2 X (+ (- X) Y2))))
    :hints (("Goal"
	     :use ((:instance STANDARD-PART-OF-TIMES
			      (x (DIFFERENTIAL-CR-FN1 (CR-FN2 X)
						      (+ (- (CR-FN2 X)) (CR-FN2 Y2))))
			      (y (DIFFERENTIAL-CR-FN2 X (+ (- X) Y2))))
                   (:instance DIFFERENTIAL-CR-FN1-O-FN2-definition
                              (x x)
                              (eps (- y2 x)))
                   )
	     :in-theory '(i-close-reflexive
			  realp-differential-cr-fn2
			  commutativity-of-+
			  commutativity-2-of-+
			  associativity-of-+
			  inverse-of-+
			  commutativity-of-*
			  minus-cancellation-on-left
			  fix
			  lemma-7
			  lemma-8
			  lemma-9
			  lemma-10a
                          (:forward-chaining inside-interval-is-real))))))

 (defthm cr-fn1-o-fn2-differentiable-for-trivial-case
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (inside-interval-p y1 (cr-fn2-domain))
		   (inside-interval-p y2 (cr-fn2-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2))
		   (equal (cr-fn2 y1) (cr-fn2 x)))
	      (and (i-limited (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y1)) (- x y1)))
		   (i-close (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y1)) (- x y1))
			    (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y2)) (- x y2)))))
   :hints (("Goal"
	    :use ((:instance expand-differential-cr-fn1-o-fn2
			     (x x)
			     (eps (- y1 x)))
		  (:instance expand-differential-cr-fn1-o-fn2
			     (x x)
			     (eps (- y2 x)))
		  (:instance differential-cr-fn1-o-fn2-must-be-zero
			     (x x)
			     (eps (- y1 x)))
		  (:instance derivative-cr-fn2-must-be-zero
			     (x x)
			     (eps (- y1 x)))
		  (:instance cr-fn2-continuous
			     (x x)
			     (y y2))
		  (:instance cr-fn1-continuous
			     (x (cr-fn2 x))
			     (y (cr-fn2 y2)))
		  (:instance differential-cr-fn1-limited
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y2) (cr-fn2 x))))
		  (:instance differential-cr-fn2-close
			     (x x)
			     (eps (- y2 x)))
		  (:instance limited-cr-fn1-eps
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y2) (cr-fn2 x))))
		  )
	    :in-theory '(inside-interval-is-real
			 commutativity-of-+
			 associativity-of-+
			 inverse-of-+
			 unicity-of-0
			 fix
			 minus-cancellation-on-left
			 lemma-1
			 lemma-2
			 lemma-4
			 lemma-6
			 lemma-10
			 (i-large)
			 standard-cr-fn2
			 cr-fn2-range-in-domain-of-fn2
			 cr-fn2-real
			 i-close-reflexive
			 )))
   )
 )

;; So from now on we can assume that fn2(x) != fn2(x+eps).  In these cases,
;; we should be able to use the properties of the differential and derivatives
;; of fn1 and fn2 to get the result.

;; The first key step is showing that the differential-fn1(fn2(x), fn2(x+eps)) is
;; limited.  That will allow us to show that the differential of fn1-o-fn2 is
;; limited, and it will also be the key to showing that it is close to the
;; differential with other epsilons.

(encapsulate
 nil

 (local
  (defthm lemma-0
    (implies (and (inside-interval-p x (cr-fn2-range))
                  (inside-interval-p (+ x eps) (cr-fn2-range)))
             (acl2-numberp (differential-cr-fn1 x eps)))
    :hints (("Goal"
	     :use ((:instance differential-cr-fn1-definition))))
    :rule-classes (:rewrite :type-prescription)))


 (local
  (defthm lemma-2
      (implies (i-close x y)
	       (i-small (+ (- x) y)))
    :hints (("Goal"
	     :use ((:instance i-small-uminus
			      (x (+ x (- y)))))
	     :in-theory '(i-close
			  distributivity-of-minus-over-+
			  functional-self-inversion-of-minus
			  fix)))))

 (defthm limited-differential-cr-fn1-after-fn2
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (inside-interval-p y1 (cr-fn2-domain))
		   (i-close x y1) (not (= x y1))
		   (not (equal (cr-fn2 y1) (cr-fn2 x))))
	      (i-limited (differential-cr-fn1 (cr-fn2 x)
					      (- (cr-fn2 y1) (cr-fn2 x)))))
   :hints (("Goal"
	    :use ((:instance cr-fn2-continuous
			     (x x)
			     (y y1))
		  (:instance differential-cr-fn1-limited
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y1) (cr-fn2 x))))
		  (:instance (:theorem (implies (and (realp x) (realp y)) (realp (+ x (- y)))))
			     (x (CR-FN2 X))
			     (y (CR-FN2 Y1)))
		  )
	    :in-theory '(standard-cr-fn2
			 cr-fn1-real
			 cr-fn2-real
			 realp-differential-cr-fn1
			 cr-fn2-range-in-domain-of-fn2
			 commutativity-of-+
			 associativity-of-+
			 minus-cancellation-on-left
			 fix
			 lemma-0
			 lemma-2))))
 )

(encapsulate
 nil

 (local
  (defthm lemma-2
      (implies (i-close x y)
	       (i-small (+ (- x) y)))
    :hints (("Goal"
	     :use ((:instance i-small-uminus
			      (x (+ x (- y)))))
	     :in-theory '(i-close
			  distributivity-of-minus-over-+
			  functional-self-inversion-of-minus
			  fix)))))

 (defthm cr-fn1-o-fn2-differentiable-part1-lemma
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (inside-interval-p y1 (cr-fn2-domain))
		   (i-close x y1) (not (= x y1)))
	      (i-limited (differential-cr-fn1-o-fn2 x (- y1 x))))
   :hints (("Goal"
	    :use ((:instance limited-differential-cr-fn1-after-fn2)
		  (:instance differential-cr-fn2-limited
			     (x x)
			     (eps (- y1 x)))
		  )
	    :in-theory '(differential-cr-fn1-o-fn2-definition
			 i-limited-times
			 (i-large)
			 commutativity-of-+
			 associativity-of-+
			 minus-cancellation-on-left
			 fix
			 inside-interval-is-real
			 lemma-2
			 )
	    )))
 )



(encapsulate
 nil

 (local
  (defthm lemma-3
      (equal (+ (fix x) y) (+ x y))))

 (local
  (defthm lemma-4
      (equal (* (+ (- x1) y1)
		(/ (+ (- x) y)))
	     (* (+ x1 (- y1))
		(/ (+ x (- y)))))
    :hints (("Goal"
	     :use ((:instance (:theorem (equal (/ (- x) (- y)) (/ x y)))
			      (x (+ (- x1) y1))
			      (y (+ (- x) y))))))
    ))

 (defthm cr-fn1-o-fn2-differentiable-part1
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (inside-interval-p y1 (cr-fn2-domain))
		   (i-close x y1) (not (= x y1)))
	      (i-limited (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y1)) (- x y1))))
   :hints (("Goal"
	    :use ((:instance expand-differential-cr-fn1-o-fn2
			     (x x)
			     (eps (- y1 x)))
		  (:instance cr-fn1-o-fn2-differentiable-part1-lemma)
		  (:instance cr-fn1-o-fn2-differentiable-for-trivial-case)
		  )
	    :in-theory '(lemma-4
			 commutativity-of-+
			 minus-cancellation-on-left
			 fix
			 inside-interval-is-real
			 )
	    )))
 )


(local
 (defthm i-close-limited-lemma
   (implies (and (i-close a b)
                 (standard-numberp a)
                 (i-limited a))
            (i-limited b))))

(local
 (defthm close-times
   (implies (and (i-close x1 x2)
		 (i-limited y))
	    (i-close (* x1 y) (* x2 y)))
   :hints (("Goal"
	    :use ((:instance small*limited->small
				      (x (- x1 x2))
				      (y y)))
	    :in-theory '(i-close
			 distributivity
			 commutativity-of-*
			 functional-commutativity-of-minus-*-right))
	    )))

(local
 (defthm close-times-2
   (implies (and (i-close x1 x2)
		 (i-close y1 y2)
		 (i-limited x1)
		 (i-limited y1))
	    (i-close (* x1 y1) (* x2 y2)))
   :hints (("Goal"
	    :use ((:instance close-times (x1 x1) (x2 x2) (y y1))
		  (:instance close-times (x1 y1) (x2 y2) (y x2))
		  (:instance i-close-transitive
			     (x (* x1 y1))
			     (y (* x2 y1))
			     (z (* x2 y2)))
		  (:instance i-close-limited
			     (x x1)
			     (y x2)))
	    :in-theory '(commutativity-of-*)
	    ))))


(encapsulate
 nil

 (local
  (defthm lemma-0
    (implies (and (inside-interval-p x (cr-fn2-range))
                  (inside-interval-p (+ x eps) (cr-fn2-range)))
             (acl2-numberp (differential-cr-fn1 x eps)))
    :hints (("Goal"
	     :use ((:instance differential-cr-fn1-definition))))
    :rule-classes (:rewrite :type-prescription)))


 (local
  (defthm lemma-2
      (implies (i-close x y)
	       (i-small (+ (- x) y)))
    :hints (("Goal"
	     :use ((:instance i-small-uminus
			      (x (+ x (- y)))))
	     :in-theory '(i-close
			  distributivity-of-minus-over-+
			  functional-self-inversion-of-minus
			  fix)))))

 (defthm close-differential-cr-fn1-after-fn2
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (inside-interval-p y1 (cr-fn2-domain))
		   (inside-interval-p y2 (cr-fn2-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y1))
		   (not (equal (cr-fn2 y1) (cr-fn2 x)))
		   (not (equal (cr-fn2 y2) (cr-fn2 x))))
	      (i-close (differential-cr-fn1 (cr-fn2 x)
					    (- (cr-fn2 y1) (cr-fn2 x)))
		       (differential-cr-fn1 (cr-fn2 x)
					    (- (cr-fn2 y2) (cr-fn2 x)))))
   :hints (("Goal"
	    :use ((:instance close-times-2
			     (x1 (differential-cr-fn1 (cr-fn2 x) (- (cr-fn2 y1) (cr-fn2 x))))
			     (x2 (differential-cr-fn1 (cr-fn2 x) (- (cr-fn2 y2) (cr-fn2 x))))
			     (y1 (differential-cr-fn2 x (- y1 x)))
			     (y2 (differential-cr-fn2 x (- y2 x))))
		  (:instance cr-fn2-continuous
			     (x x)
			     (y y1))
		  (:instance cr-fn2-continuous
			     (x x)
			     (y y2))
		  (:instance differential-cr-fn1-limited
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y1) (cr-fn2 x))))
		  (:instance differential-cr-fn1-limited
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y2) (cr-fn2 x))))
		  (:instance differential-cr-fn1-close
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y1) (cr-fn2 x))))
		  (:instance differential-cr-fn1-close
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y2) (cr-fn2 x))))
		  )
	    :in-theory '(standard-cr-fn2
			 cr-fn1-real
			 cr-fn2-real
			 realp-differential-cr-fn1
			 cr-fn2-range-in-domain-of-fn2
			 commutativity-of-+
			 associativity-of-+
			 minus-cancellation-on-left
			 i-close-symmetric
			 i-close-transitive
			 fix
			 close-if-same-standard-part
			 =
			 lemma-0
			 lemma-2))))
 )

(encapsulate
 nil

 (local
  (defthm lemma-2
      (implies (i-close x y)
	       (i-small (+ (- x) y)))
    :hints (("Goal"
	     :use ((:instance i-small-uminus
			      (x (+ x (- y)))))
	     :in-theory '(i-close
			  distributivity-of-minus-over-+
			  functional-self-inversion-of-minus
			  fix)))))

 (local
  (defthm lemma-3
      (implies (and (equal (+ (- x) y) 0)
		    (acl2-numberp x)
		    (acl2-numberp y))
	       (equal (equal x y) t))
    :hints (("Goal"
	     :use ((:instance LEFT-CANCELLATION-FOR-+
			      (x x)
			      (y (+ (- x) y))
			      (z 0)))
	     :in-theory (disable LEFT-CANCELLATION-FOR-+)
	     ))
    ))

 (local
  (defthm lemma-3b
      (implies (and (equal (+ (- x) y) 0)
		    (acl2-numberp x)
		    (acl2-numberp y))
	       (equal (cr-fn2 y) (cr-fn2 x)))
    :hints (("Goal"
	     :use ((:instance lemma-3))
	     :in-theory nil))))


 (defthm cr-fn1-o-fn2-differentiable-part2-lemma
       (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (inside-interval-p y1 (cr-fn2-domain))
		   (inside-interval-p y2 (cr-fn2-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y1))
		   (not (equal (cr-fn2 y1) (cr-fn2 x)))
		   (not (equal (cr-fn2 y2) (cr-fn2 x))))
	      (i-close (differential-cr-fn1-o-fn2 x (- y1 x))
		       (differential-cr-fn1-o-fn2 x (- y2 x))))
   :hints (("Goal"
	    :use ((:instance close-differential-cr-fn1-after-fn2)
		  (:instance differential-cr-fn2-limited
			     (x x)
			     (eps (- y1 x)))
		  (:instance differential-cr-fn2-limited
			     (x x)
			     (eps (- y2 x)))
		  (:instance close-times-2
			     (x1 (differential-cr-fn1 (cr-fn2 x) (- (cr-fn2 y1) (cr-fn2 x))))
			     (x2 (differential-cr-fn1 (cr-fn2 x) (- (cr-fn2 y2) (cr-fn2 x))))
			     (y1 (differential-cr-fn2 x (- y1 x)))
			     (y2 (differential-cr-fn2 x (- y2 x))))
		  (:instance cr-fn2-continuous
			     (x x)
			     (y y1))
		  (:instance cr-fn2-continuous
			     (x x)
			     (y y2))
		  (:instance differential-cr-fn2-close
			     (x x)
			     (eps (- y1 x)))
		  (:instance differential-cr-fn2-close
			     (x x)
			     (eps (- y2 x)))
		  (:instance differential-cr-fn1-limited
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y1) (cr-fn2 x))))
		  (:instance differential-cr-fn1-limited
			     (x (cr-fn2 x))
			     (eps (- (cr-fn2 y2) (cr-fn2 x))))
		  (:instance close-if-same-standard-part
			     (x (DIFFERENTIAL-CR-FN2 X (+ (- X) Y1)))
			     (y (DIFFERENTIAL-CR-FN2 X (+ (- X) Y2))))
		  )
	    :in-theory '(differential-cr-fn1-o-fn2-definition
			 i-limited-times
			 (i-large)
			 commutativity-of-+
			 associativity-of-+
			 minus-cancellation-on-left
			 fix
			 =
			 inside-interval-is-real
			 lemma-2
			 lemma-3b
			 i-close-reflexive
			 standard-cr-fn2
			 cr-fn2-range-in-domain-of-fn2
			 cr-fn1-real
			 cr-fn2-real
			 )
	    )))
 )

(encapsulate
 nil

 (local
  (defthm lemma-3
      (equal (+ (fix x) y) (+ x y))))

 (local
  (defthm lemma-4
      (equal (* (+ (- x1) y1)
		(/ (+ (- x) y)))
	     (* (+ x1 (- y1))
		(/ (+ x (- y)))))
    :hints (("Goal"
	     :use ((:instance (:theorem (equal (/ (- x) (- y)) (/ x y)))
			      (x (+ (- x1) y1))
			      (y (+ (- x) y))))))
    ))

 (defthm cr-fn1-o-fn2-differentiable-part2
     (implies (and (standardp x)
		   (inside-interval-p x (cr-fn2-domain))
		   (inside-interval-p y1 (cr-fn2-domain))
		   (inside-interval-p y2 (cr-fn2-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
	      (i-close (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y1)) (- x y1))
		       (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y2)) (- x y2))))
   :hints (("Goal"
	    :use ((:instance expand-differential-cr-fn1-o-fn2
			     (x x)
			     (eps (- y1 x)))
		  (:instance expand-differential-cr-fn1-o-fn2
			     (x x)
			     (eps (- y2 x)))
		  (:instance cr-fn1-o-fn2-differentiable-part2-lemma)
		  (:instance cr-fn1-o-fn2-differentiable-for-trivial-case)
		  (:instance cr-fn1-o-fn2-differentiable-for-trivial-case (y1 y2) (y2 y1))
		  )
	    :in-theory '(lemma-4
			 commutativity-of-+
			 minus-cancellation-on-left
			 fix
			 inside-interval-is-real
			 i-close-symmetric
			 )
	    )))
 )

(defthm cr-fn1-o-fn2-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (cr-fn2-domain))
		 (inside-interval-p y1 (cr-fn2-domain))
		 (inside-interval-p y2 (cr-fn2-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited  (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y1)) (- x y1)))
		 (i-close (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y1)) (- x y1))
			  (/ (- (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y2)) (- x y2)))))
  :hints (("Goal"
	   :use (cr-fn1-o-fn2-differentiable-part1
		 cr-fn1-o-fn2-differentiable-part2)
	   :in-theory nil
	   )))

(defthm cr-fn1-o-fn2-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (cr-fn2-domain))
		 (i-close x y)
		 (inside-interval-p y (cr-fn2-domain)))
	    (i-close (cr-fn1-o-fn2 x) (cr-fn1-o-fn2 y)))
  :hints (("Goal"
	   :use ((:functional-instance rdfn-continuous
                                       (rdfn (lambda (x) (realfix (cr-fn1-o-fn2 x))))
                                       (rdfn-domain cr-fn2-domain))))
	  ("Subgoal 3"
	   :use ((:instance cr-fn1-o-fn2-differentiable))
	   :in-theory (disable cr-fn1-o-fn2-differentiable))
	  ("Subgoal 2"
	   :use ((:instance cr-fn2-domain-non-trivial)))))

(defthm realp-differential-cr-fn1-o-fn2
  (implies (and (inside-interval-p x (cr-fn2-domain))
		(inside-interval-p (+ x eps) (cr-fn2-domain))
		(realp eps))
	   (realp (differential-cr-fn1-o-fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-cr-fn1-o-fn2)
                                     (rdfn (lambda (x) (realfix (cr-fn1-o-fn2 x))))
				     (rdfn-domain cr-fn2-domain))
	   :in-theory (enable differential-cr-fn1-definition
                              differential-cr-fn2-definition)
	   )
	  ("Goal'"
	   :use ((:instance expand-differential-cr-fn1-o-fn2)))
	  ))

(defthm differential-cr-fn1-o-fn2-limited
    (implies (and (standardp x)
		  (inside-interval-p x (cr-fn2-domain))
		  (inside-interval-p (+ x eps) (cr-fn2-domain))
		  (i-small eps))
	     (i-limited (differential-cr-fn1-o-fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-cr-fn1-o-fn2)
                                     (rdfn (lambda (x) (realfix (cr-fn1-o-fn2 x))))
				     (rdfn-domain cr-fn2-domain)))))

(in-theory (disable differential-cr-fn1-o-fn2-definition))

(defthm-std standard-cr-fn2-domain
  (standardp (cr-fn2-domain)))

(defthm non-trivial-interval-not-both-endpoints-cr-fn2-domain
    (implies (inside-interval-p x (cr-fn2-domain))
	     (or (not (equal (interval-left-endpoint (cr-fn2-domain)) x))
		 (not (equal (interval-right-endpoint (cr-fn2-domain)) x))))
  :hints (("Goal"
	   :use ((:instance cr-fn2-domain-non-trivial))))
  :rule-classes nil)

(defthm non-trivial-interval-eps-or--eps-cr-fn2-domain
    (implies (and (inside-interval-p x (cr-fn2-domain))
		  (standardp x)
		  (realp eps)
		  (i-small eps))
	     (or (inside-interval-p (+ x eps) (cr-fn2-domain))
		 (inside-interval-p (- x eps) (cr-fn2-domain))))
  :hints (("Goal"
	   :use ((:instance non-trivial-interval-not-both-endpoints-cr-fn2-domain)
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps eps)
			    (interval (cr-fn2-domain)))
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps (- eps))
			    (interval (cr-fn2-domain)))
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps eps)
			    (interval (cr-fn2-domain))
			    )
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps (- eps))
			    (interval (cr-fn2-domain))
			    ))
	   ))
  :rule-classes nil)

(local
 (defthm derivative-fn1-o-fn2-is-close-to-differential
   (implies (and (inside-interval-p x (cr-fn2-domain))
		 (standardp x)
		 (realp eps)
		 (not (equal 0 eps))
		 (i-small eps)
		 (inside-interval-p (+ eps x) (cr-fn2-domain)))
    (equal (* (derivative-cr-fn2 x)
	      (derivative-cr-fn1 (cr-fn2 x)))
	   (standard-part (differential-cr-fn1-o-fn2 x eps))))
   :hints (("Goal"
	    :use ((:instance differential-cr-fn1-o-fn2-definition)))
	   ("Subgoal 2"
	    :use ((:instance derivative-cr-fn2-must-be-zero))
	    :in-theory (disable derivative-cr-fn2-must-be-zero))
	  ("Subgoal 1"
	   :use ((:instance standard-part-of-times
			    (x (differential-cr-fn2 x eps))
			    (y (differential-cr-fn1 (cr-fn2 x)
                                                  (+ (- (cr-fn2 x))
                                                     (cr-fn2 (+ eps x))))))
		 (:instance differential-cr-fn1-limited
			    (x (cr-fn2 x))
			    (eps (+ (- (cr-fn2 x)) (cr-fn2 (+ eps x)))))
		 (:instance cr-fn2-continuous
			    (x x)
			    (y (+ eps x)))
		 (:instance i-close-to-small-sum)
		 (:instance differential-cr-fn2-close
			    (x x)
			    (eps eps))
		 (:instance differential-cr-fn1-close
			    (x (cr-fn2 x))
			    (eps (- (cr-fn2 (+ eps x))
				    (cr-fn2 x))))
		 )
	   :in-theory (e/d (i-close)
			   (standard-part-of-times
			    differential-cr-fn1-limited
			    cr-fn2-continuous
			    i-close-to-small-sum
			    differential-cr-fn1-close
			    differential-cr-fn2-close)))
	  )
   ))

(defthm real-derivative-cr-fn1-o-fn2
    (implies (inside-interval-p x (cr-fn2-domain))
	     (realp (derivative-cr-fn1-o-fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-cr-fn1-o-fn2)
				     (differential-rdfn differential-cr-fn1-o-fn2)
                                     (rdfn (lambda (x) (realfix (cr-fn1-o-fn2 x))))
				     (rdfn-domain cr-fn2-domain)))
	  ("Subgoal 3"
	   :use ((:instance derivative-fn1-o-fn2-is-close-to-differential
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 2"
	   :use ((:instance non-trivial-interval-eps-or--eps-cr-fn2-domain
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 1"
	   :use ((:instance derivative-fn1-o-fn2-is-close-to-differential
			    (eps (- (/ (i-large-integer)))))))
	  ))

(defthm differential-cr-fn1-o-fn2-close
   (implies (and (inside-interval-p x (cr-fn2-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (cr-fn2-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-cr-fn1-o-fn2 x eps))
		   (derivative-cr-fn1-o-fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-cr-fn1-o-fn2)
				     (differential-rdfn differential-cr-fn1-o-fn2)
                                     (rdfn (lambda (x) (realfix (cr-fn1-o-fn2 x))))
				     (rdfn-domain cr-fn2-domain)))))

(in-theory (disable derivative-cr-fn1-o-fn2-definition))

