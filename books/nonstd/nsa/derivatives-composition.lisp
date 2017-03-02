(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "nsa")
(include-book "derivatives")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(encapsulate
 ((dc-fn1 (x) t)
  (dc-fn2 (x) t)
  (dc-fnz (x) t)
  (dc-fn-domain () t))

 ;; Our witness continuous function is the identity function.

 (local (defun dc-fn1 (x) (realfix x)))
 (local (defun dc-fn2 (x) (realfix x)))
 (local (defun dc-fnz (x) (declare (ignore x)) 1))
 (local (defun dc-fn-domain () (interval 0 1)))

 ;; The interval really is an interval

 (defthm intervalp-dc-fn-domain
     (interval-p (dc-fn-domain))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is real

 (defthm dc-fn-domain-real
     (implies (inside-interval-p x (dc-fn-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm dc-fn-domain-non-trivial
     (or (null (interval-left-endpoint (dc-fn-domain)))
	 (null (interval-right-endpoint (dc-fn-domain)))
	 (< (interval-left-endpoint (dc-fn-domain))
	    (interval-right-endpoint (dc-fn-domain))))
   :rule-classes nil)

 ;; The functions return real values (even for improper arguments).

 (defthm dc-fn1-real
     (realp (dc-fn1 x))
   :rule-classes (:rewrite :type-prescription))

 (defthm dc-fn2-real
     (realp (dc-fn2 x))
   :rule-classes (:rewrite :type-prescription))

 (defthm dc-fnz-real
     (realp (dc-fnz x))
   :rule-classes (:rewrite :type-prescription))

 ;; The function fnz never returns zero.

 (defthm dc-fnz-non-zero
   (implies (inside-interval-p x (dc-fn-domain))
	    (not (equal (dc-fnz x) 0)))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y1 and y2 are two arbitrary reals
 ;; close to x, then (rdfn(x)-rdfn(y1))/(x-y1) is close to
 ;; (rdfn(x)-rdfn(y2))/(x-y2).  Also, (rdfn(x)-rdfn(y1))/(x-y1) is
 ;; limited.  What this means is that the standard-part of that is a
 ;; standard number, and we'll call that the derivative of rdfn at x.

 (defthm dc-fn1-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (inside-interval-p y2 (dc-fn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (dc-fn1 x) (dc-fn1 y1)) (- x y1)))
		 (i-close (/ (- (dc-fn1 x) (dc-fn1 y1)) (- x y1))
			  (/ (- (dc-fn1 x) (dc-fn1 y2)) (- x y2))))))

 (defthm dc-fn2-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (inside-interval-p y2 (dc-fn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (dc-fn2 x) (dc-fn2 y1)) (- x y1)))
		 (i-close (/ (- (dc-fn2 x) (dc-fn2 y1)) (- x y1))
			  (/ (- (dc-fn2 x) (dc-fn2 y2)) (- x y2))))))

 (defthm dc-fnz-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (inside-interval-p y2 (dc-fn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (dc-fnz x) (dc-fnz y1)) (- x y1)))
		 (i-close (/ (- (dc-fnz x) (dc-fnz y1)) (- x y1))
			  (/ (- (dc-fnz x) (dc-fnz y2)) (- x y2))))))

 )

;; It helps (for hint purposes) to separate the two parts of the
;; condition for differentiability

(defthm dc-fn1-differentiable-part1
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p y1 (dc-fn-domain))
		  (i-close x y1) (not (= x y1)))
	     (i-limited (/ (- (dc-fn1 x) (dc-fn1 y1)) (- x y1))))
  :hints (("Goal"
	   :use ((:instance dc-fn1-differentiable (y2 y1)))
	   :in-theory nil)))

(defthm dc-fn1-differentiable-part2
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p y1 (dc-fn-domain))
		  (inside-interval-p y2 (dc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (dc-fn1 x) (dc-fn1 y1)) (- x y1))
		      (/ (- (dc-fn1 x) (dc-fn1 y2)) (- x y2))))
  :hints (("Goal"
	   :use ((:instance dc-fn1-differentiable))
	   :in-theory nil)))

(defthm dc-fn2-differentiable-part1
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p y1 (dc-fn-domain))
		  (i-close x y1) (not (= x y1)))
	     (i-limited (/ (- (dc-fn2 x) (dc-fn2 y1)) (- x y1))))
  :hints (("Goal"
	   :use ((:instance dc-fn2-differentiable (y2 y1)))
	   :in-theory nil)))

(defthm dc-fn2-differentiable-part2
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p y1 (dc-fn-domain))
		  (inside-interval-p y2 (dc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (dc-fn2 x) (dc-fn2 y1)) (- x y1))
		      (/ (- (dc-fn2 x) (dc-fn2 y2)) (- x y2))))
  :hints (("Goal"
	   :use ((:instance dc-fn2-differentiable))
	   :in-theory nil)))

(defthm dc-fnz-differentiable-part1
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p y1 (dc-fn-domain))
		  (i-close x y1) (not (= x y1)))
	     (i-limited (/ (- (dc-fnz x) (dc-fnz y1)) (- x y1))))
  :hints (("Goal"
	   :use ((:instance dc-fnz-differentiable (y2 y1)))
	   :in-theory nil)))

(defthm dc-fnz-differentiable-part2
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p y1 (dc-fn-domain))
		  (inside-interval-p y2 (dc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (dc-fnz x) (dc-fnz y1)) (- x y1))
		      (/ (- (dc-fnz x) (dc-fnz y2)) (- x y2))))
  :hints (("Goal"
	   :use ((:instance dc-fnz-differentiable))
	   :in-theory nil)))

;; It follows by functional instantiation that both dc-fn1 and dc-fn2 are continuous

(defthm dc-fn1-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (i-close x y)
		 (inside-interval-p y (dc-fn-domain)))
	    (i-close (dc-fn1 x) (dc-fn1 y)))

  :hints (("Goal"
	   :by (:functional-instance rdfn-continuous
				     (rdfn dc-fn1)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 3"
	   :use ((:instance dc-fn1-differentiable))
	   :in-theory (disable dc-fn1-differentiable))
	  ("Subgoal 2"
	   :use ((:instance dc-fn-domain-non-trivial)))
	  )
  )

(defthm dc-fn2-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (i-close x y)
		 (inside-interval-p y (dc-fn-domain)))
	    (i-close (dc-fn2 x) (dc-fn2 y)))

  :hints (("Goal"
	   :by (:functional-instance rdfn-continuous
				     (rdfn dc-fn2)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 3"
	   :use ((:instance dc-fn2-differentiable))
	   :in-theory (disable dc-fn2-differentiable))
	  ("Subgoal 2"
	   :use ((:instance dc-fn-domain-non-trivial)))
	  )
  )

(defthm dc-fnz-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (i-close x y)
		 (inside-interval-p y (dc-fn-domain)))
	    (i-close (dc-fnz x) (dc-fnz y)))

  :hints (("Goal"
	   :by (:functional-instance rdfn-continuous
				     (rdfn dc-fnz)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 3"
	   :use ((:instance dc-fnz-differentiable))
	   :in-theory (disable dc-fnz-differentiable))
	  ("Subgoal 2"
	   :use ((:instance dc-fn-domain-non-trivial)))
	  )
  )

;; We define the differential and derivative functions for dc-fn1 and dc-fn2

(encapsulate
 ( ((differential-dc-fn1 * *) => *) )

 (local
  (defun differential-dc-fn1 (x eps)
    (/ (- (dc-fn1 (+ x eps)) (dc-fn1 x)) eps)))

 (defthm differential-dc-fn1-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p (+ x eps) (dc-fn-domain)))
	    (equal (differential-dc-fn1 x eps)
		   (/ (- (dc-fn1 (+ x eps)) (dc-fn1 x)) eps))))
 )


(defthm realp-differential-dc-fn1
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain))
		(realp eps))
	   (realp (differential-dc-fn1 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-dc-fn1)
				     (rdfn dc-fn1)
				     (rdfn-domain dc-fn-domain)))))

(defthm differential-dc-fn1-limited
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p (+ x eps) (dc-fn-domain))
		  (i-small eps))
	     (i-limited (differential-dc-fn1 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-dc-fn1)
				     (rdfn dc-fn1)
				     (rdfn-domain dc-fn-domain)))))


(in-theory (disable differential-dc-fn1-definition))

(encapsulate
 ( ((derivative-dc-fn1 *) => *) )

 (local
  (defun-std derivative-dc-fn1 (x)
    (if (inside-interval-p x (dc-fn-domain))
	(if (inside-interval-p (+ x (/ (i-large-integer))) (dc-fn-domain))
	    (standard-part (differential-dc-fn1 x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (dc-fn-domain))
	      (standard-part (differential-dc-fn1 x (- (/ (i-large-integer)))))
	    'error))
      'error)))

 (defthm derivative-dc-fn1-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x))
	    (equal (derivative-dc-fn1 x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (dc-fn-domain))
		       (standard-part (differential-dc-fn1 x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (dc-fn-domain))
			 (standard-part (differential-dc-fn1 x (- (/ (i-large-integer)))))
		       'error)))))
 )

(defthm real-derivative-dc-fn1
    (implies (inside-interval-p x (dc-fn-domain))
	     (realp (derivative-dc-fn1 x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-dc-fn1)
				     (differential-rdfn differential-dc-fn1)
				     (rdfn dc-fn1)
				     (rdfn-domain dc-fn-domain)))))

(defthm differential-dc-fn1-close
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dc-fn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-dc-fn1 x eps))
		   (derivative-dc-fn1 x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-dc-fn1)
				     (differential-rdfn differential-dc-fn1)
				     (rdfn dc-fn1)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable derivative-dc-fn1-definition))

(encapsulate
 ( ((differential-dc-fn2 * *) => *) )

 (local
  (defun differential-dc-fn2 (x eps)
    (/ (- (dc-fn2 (+ x eps)) (dc-fn2 x)) eps)))

 (defthm differential-dc-fn2-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p (+ x eps) (dc-fn-domain)))
	    (equal (differential-dc-fn2 x eps)
		   (/ (- (dc-fn2 (+ x eps)) (dc-fn2 x)) eps))))
 )

(defthm realp-differential-dc-fn2
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain))
		(realp eps))
	   (realp (differential-dc-fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-dc-fn2)
				     (rdfn dc-fn2)
				     (rdfn-domain dc-fn-domain)))))

(defthm differential-dc-fn2-limited
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p (+ x eps) (dc-fn-domain))
		  (i-small eps))
	     (i-limited (differential-dc-fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-dc-fn2)
				     (rdfn dc-fn2)
				     (rdfn-domain dc-fn-domain)))))


(in-theory (disable differential-dc-fn2-definition))



(encapsulate
 ( ((derivative-dc-fn2 *) => *) )

 (local
  (defun-std derivative-dc-fn2 (x)
    (if (inside-interval-p x (dc-fn-domain))
	(if (inside-interval-p (+ x (/ (i-large-integer))) (dc-fn-domain))
	    (standard-part (differential-dc-fn2 x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (dc-fn-domain))
	      (standard-part (differential-dc-fn2 x (- (/ (i-large-integer)))))
	    'error))
      'error)))

 (defthm derivative-dc-fn2-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x))
	    (equal (derivative-dc-fn2 x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (dc-fn-domain))
		       (standard-part (differential-dc-fn2 x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (dc-fn-domain))
			 (standard-part (differential-dc-fn2 x (- (/ (i-large-integer)))))
		       'error)))))
 )



(defthm real-derivative-dc-fn2
    (implies (inside-interval-p x (dc-fn-domain))
	     (realp (derivative-dc-fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-dc-fn2)
				     (differential-rdfn differential-dc-fn2)
				     (rdfn dc-fn2)
				     (rdfn-domain dc-fn-domain)))))

(defthm differential-dc-fn2-close
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dc-fn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-dc-fn2 x eps))
		   (derivative-dc-fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-dc-fn2)
				     (differential-rdfn differential-dc-fn2)
				     (rdfn dc-fn2)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable derivative-dc-fn2-definition))

(encapsulate
 ( ((differential-dc-fnz * *) => *) )

 (local
  (defun differential-dc-fnz (x eps)
    (/ (- (dc-fnz (+ x eps)) (dc-fnz x)) eps)))

 (defthm differential-dc-fnz-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p (+ x eps) (dc-fn-domain)))
	    (equal (differential-dc-fnz x eps)
		   (/ (- (dc-fnz (+ x eps)) (dc-fnz x)) eps))))
 )

(defthm realp-differential-dc-fnz
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain))
		(realp eps))
	   (realp (differential-dc-fnz x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-dc-fnz)
				     (rdfn dc-fnz)
				     (rdfn-domain dc-fn-domain)))
	  ("Goal'"
	   :use ((:instance differential-dc-fnz-definition))
	   :in-theory (disable differential-dc-fnz-definition))))

(defthm differential-dc-fnz-limited
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p (+ x eps) (dc-fn-domain))
		  (i-small eps))
	     (i-limited (differential-dc-fnz x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-dc-fnz)
				     (rdfn dc-fnz)
				     (rdfn-domain dc-fn-domain)))))


(in-theory (disable differential-dc-fnz-definition))

(encapsulate
 ( ((derivative-dc-fnz *) => *) )

 (local
  (defun-std derivative-dc-fnz (x)
    (if (inside-interval-p x (dc-fn-domain))
	(if (inside-interval-p (+ x (/ (i-large-integer))) (dc-fn-domain))
	    (standard-part (differential-dc-fnz x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (dc-fn-domain))
	      (standard-part (differential-dc-fnz x (- (/ (i-large-integer)))))
	    'error))
      'error)))

 (defthm derivative-dc-fnz-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x))
	    (equal (derivative-dc-fnz x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (dc-fn-domain))
		       (standard-part (differential-dc-fnz x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (dc-fn-domain))
			 (standard-part (differential-dc-fnz x (- (/ (i-large-integer)))))
		       'error)))))
 )

(defthm real-derivative-dc-fnz
    (implies (inside-interval-p x (dc-fn-domain))
	     (realp (derivative-dc-fnz x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-dc-fnz)
				     (differential-rdfn differential-dc-fnz)
				     (rdfn dc-fnz)
				     (rdfn-domain dc-fn-domain)))))

(defthm differential-dc-fnz-close
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dc-fn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-dc-fnz x eps))
		   (derivative-dc-fnz x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-dc-fnz)
				     (differential-rdfn differential-dc-fnz)
				     (rdfn dc-fnz)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable derivative-dc-fnz-definition))

;; All functions are standard

(local
 (defthm-std standard-dc-fn1
     (implies (standardp x)
	      (standardp (dc-fn1 x)))))

(local
 (defthm-std standard-dc-fn2
     (implies (standardp x)
	      (standardp (dc-fn2 x)))))

(local
 (defthm-std standard-dc-fnz
     (implies (standardp x)
	      (standardp (dc-fnz x)))))


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
 (defthm close-differential-dc-fn1
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (dc-fn-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (dc-fn-domain)))
	      (i-close (differential-dc-fn1 x eps1)
		       (differential-dc-fn1 x eps2)))
   :hints (("Goal"
	    :use ((:instance close-if-same-standard-part
			     (x (differential-dc-fn1 x eps1))
			     (y (differential-dc-fn1 x eps2)))
		  (:instance differential-dc-fn1-close
			     (eps eps1))
		  (:instance differential-dc-fn1-close
			     (eps eps2)))
	    :in-theory (disable close-if-same-standard-part differential-dc-fn1-close)))))

(local
 (defthm close-differential-dc-fn2
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (dc-fn-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (dc-fn-domain)))
	      (i-close (differential-dc-fn2 x eps1)
		       (differential-dc-fn2 x eps2)))
   :hints (("Goal"
	    :use ((:instance close-if-same-standard-part
			     (x (differential-dc-fn2 x eps1))
			     (y (differential-dc-fn2 x eps2)))
		  (:instance differential-dc-fn2-close
			     (eps eps1))
		  (:instance differential-dc-fn2-close
			     (eps eps2)))
	    :in-theory (disable close-if-same-standard-part differential-dc-fn2-close)))))

(local
 (defthm close-differential-dc-fnz
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (dc-fn-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (dc-fn-domain)))
	      (i-close (differential-dc-fnz x eps1)
		       (differential-dc-fnz x eps2)))
   :hints (("Goal"
	    :use ((:instance close-if-same-standard-part
			     (x (differential-dc-fnz x eps1))
			     (y (differential-dc-fnz x eps2)))
		  (:instance differential-dc-fnz-close
			     (eps eps1))
		  (:instance differential-dc-fnz-close
			     (eps eps2)))
	    :in-theory (disable close-if-same-standard-part differential-dc-fnz-close)))))

(local
 (defthm close-dc-fn1-eps1-eps2
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (dc-fn-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (dc-fn-domain)))
	      (i-close (dc-fn1 (+ x eps1))
		       (dc-fn1 (+ x eps2))))
   :hints (("Goal"
	    :use ((:instance i-close-transitive
			     (x (dc-fn1 (+ x eps1)))
			     (y (dc-fn1 x))
			     (z (dc-fn1 (+ x eps2))))
		  (:instance i-close-symmetric
			     (x (dc-fn1 x))
			     (y (dc-fn1 (+ x eps1))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps1))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps2))
		  (:instance dc-fn1-continuous
			     (x x)
			     (y (+ x eps1)))
		  (:instance dc-fn1-continuous
			     (x x)
			     (y (+ x eps2))))
	    :in-theory '(inside-interval-is-real)))))


(local
 (defthm close-dc-fn2-eps1-eps2
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (dc-fn-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (dc-fn-domain)))
	      (i-close (dc-fn2 (+ x eps1))
		       (dc-fn2 (+ x eps2))))
   :hints (("Goal"
	    :use ((:instance i-close-transitive
			     (x (dc-fn2 (+ x eps1)))
			     (y (dc-fn2 x))
			     (z (dc-fn2 (+ x eps2))))
		  (:instance i-close-symmetric
			     (x (dc-fn2 x))
			     (y (dc-fn2 (+ x eps1))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps1))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps2))
		  (:instance dc-fn2-continuous
			     (x x)
			     (y (+ x eps1)))
		  (:instance dc-fn2-continuous
			     (x x)
			     (y (+ x eps2))))
	    :in-theory '(inside-interval-is-real)))))

(local
 (defthm limited-dc-fn1-eps
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps)
		   (i-small eps)
		   (inside-interval-p (+ x eps) (dc-fn-domain)))
	      (i-limited (dc-fn1 (+ x eps))))
   :hints (("Goal"
	    :use ((:instance i-close-limited
			     (x (dc-fn1 x))
			     (y (dc-fn1 (+ x eps))))
		  (:instance dc-fn1-continuous
			     (x x)
			     (y (+ x eps)))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps)))
	    :in-theory '(dc-fn1-real
			 standard-dc-fn1
			 standards-are-limited
			 inside-interval-is-real)))))

(local
 (defthm limited-dc-fn2-eps
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps)
		   (i-small eps)
		   (inside-interval-p (+ x eps) (dc-fn-domain)))
	      (i-limited (dc-fn2 (+ x eps))))
   :hints (("Goal"
	    :use ((:instance i-close-limited
			     (x (dc-fn2 x))
			     (y (dc-fn2 (+ x eps))))
		  (:instance dc-fn2-continuous
			     (x x)
			     (y (+ x eps)))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps)))
	    :in-theory '(dc-fn2-real
			 standard-dc-fn2
			 standards-are-limited
			 inside-interval-is-real)))))

;; Now we can define the function fn1+fn2 and its derivatives

(encapsulate
 ( ;((dc-fn1+fn2 *) => *)
   ((differential-dc-fn1+fn2 * *) => *)
   ((derivative-dc-fn1+fn2 *) => *)
   )

 (defun dc-fn1+fn2 (x)
   (+ (dc-fn1 x) (dc-fn2 x)))

 (local
  (defun differential-dc-fn1+fn2 (x eps)
    (+ (differential-dc-fn1 x eps)
       (differential-dc-fn2 x eps))))

 (local
  (defun derivative-dc-fn1+fn2 (x)
    (+ (derivative-dc-fn1 x)
       (derivative-dc-fn2 x))))

 (defthm differential-dc-fn1+fn2-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p (+ x eps) (dc-fn-domain)))
	    (equal (differential-dc-fn1+fn2 x eps)
		   (+ (differential-dc-fn1 x eps)
		      (differential-dc-fn2 x eps)))))

 (defthm derivative-dc-fn1+fn2-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x))
	    (equal (derivative-dc-fn1+fn2 x)
		   (+ (derivative-dc-fn1 x)
		      (derivative-dc-fn2 x)))))
 )

;; Now we prove that these functions really are the differential and derivative of the sum

(local
 (defthm close-plus
   (implies (and (i-close x1 x2)
		 (i-close y1 y2))
	    (i-close (+ x1 y1) (+ x2 y2)))
   :hints (("Goal"
	    :use ((:instance i-small-plus
			     (x (+ x1 (- x2)))
			     (y (+ y1 (- y2)))))
	    :in-theory '(i-close
			 associativity-of-+
			 commutativity-of-+
			 commutativity-2-of-+
			 distributivity-of-minus-over-+
			 )))))

(defthm dc-fn1+fn2-differentiable-part1
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (i-close x y1) (not (= x y1)))
	    (i-limited  (/ (- (dc-fn1+fn2 x) (dc-fn1+fn2 y1)) (- x y1))))
  :hints (("Goal"
	   :use (dc-fn1-differentiable-part1
		 dc-fn2-differentiable-part1
		 (:instance i-limited-plus
			    (x (/ (- (dc-fn1 x) (dc-fn1 y1)) (- x y1)))
			    (y (/ (- (dc-fn2 x) (dc-fn2 y1)) (- x y1)))))
	   :in-theory '(dc-fn1+fn2 distributivity commutativity-of-* commutativity-of-+ commutativity-2-of-+
			associativity-of-+ distributivity-of-minus-over-+)
	   )))

(defthm dc-fn1+fn2-differentiable-part2
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (inside-interval-p y2 (dc-fn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (i-close (/ (- (dc-fn1+fn2 x) (dc-fn1+fn2 y1)) (- x y1))
		     (/ (- (dc-fn1+fn2 x) (dc-fn1+fn2 y2)) (- x y2))))
  :hints (("Goal"
	   :use (dc-fn1-differentiable-part2
		 dc-fn2-differentiable-part2
		 (:instance close-plus
			    (x1 (/ (- (dc-fn1 x) (dc-fn1 y1)) (- x y1)))
			    (x2 (/ (- (dc-fn1 x) (dc-fn1 y2)) (- x y2)))
			    (y1 (/ (- (dc-fn2 x) (dc-fn2 y1)) (- x y1)))
			    (y2 (/ (- (dc-fn2 x) (dc-fn2 y2)) (- x y2)))))
	   :in-theory '(dc-fn1+fn2 distributivity commutativity-of-* commutativity-of-+ commutativity-2-of-+
			associativity-of-+ distributivity-of-minus-over-+)
	   )))

(defthm dc-fn1+fn2-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (inside-interval-p y2 (dc-fn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited  (/ (- (dc-fn1+fn2 x) (dc-fn1+fn2 y1)) (- x y1)))
		 (i-close (/ (- (dc-fn1+fn2 x) (dc-fn1+fn2 y1)) (- x y1))
			  (/ (- (dc-fn1+fn2 x) (dc-fn1+fn2 y2)) (- x y2)))))
  :hints (("Goal"
	   :use (dc-fn1+fn2-differentiable-part1
		 dc-fn1+fn2-differentiable-part2)
	   :in-theory nil
	   )))

(defthm dc-fn1+fn2-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (i-close x y)
		 (inside-interval-p y (dc-fn-domain)))
	    (i-close (dc-fn1+fn2 x) (dc-fn1+fn2 y)))

  :hints (("Goal"
; Added after v4-3 by Matt K.:
           :in-theory (disable (tau-system))
	   :by (:functional-instance rdfn-continuous
				     (rdfn dc-fn1+fn2)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 4"
	   :use ((:instance dc-fn1+fn2-differentiable))
	   :in-theory (disable dc-fn1+fn2-differentiable))
	  ("Subgoal 2"
	   :use ((:instance dc-fn-domain-non-trivial)))))

(defthm realp-differential-dc-fn1+fn2
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain))
		(realp eps))
	   (realp (differential-dc-fn1+fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-dc-fn1+fn2)
				     (rdfn dc-fn1+fn2)
				     (rdfn-domain dc-fn-domain))
	   :in-theory (enable differential-dc-fn1-definition
			      differential-dc-fn2-definition)
	   )))

(defthm differential-dc-fn1+fn2-limited
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p (+ x eps) (dc-fn-domain))
		  (i-small eps))
	     (i-limited (differential-dc-fn1+fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-dc-fn1+fn2)
				     (rdfn dc-fn1+fn2)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable differential-dc-fn1+fn2-definition))

(defthm-std standard-dc-fn-domain
  (standardp (dc-fn-domain)))

(defthm non-trivial-interval-not-both-endpoints-dc-fn-domain
    (implies (inside-interval-p x (dc-fn-domain))
	     (or (not (equal (interval-left-endpoint (dc-fn-domain)) x))
		 (not (equal (interval-right-endpoint (dc-fn-domain)) x))))
  :hints (("Goal"
	   :use ((:instance dc-fn-domain-non-trivial))))
  :rule-classes nil)

(defthm non-trivial-interval-eps-or--eps-dc-fn-domain
    (implies (and (inside-interval-p x (dc-fn-domain))
		  (standardp x)
		  (realp eps)
		  (i-small eps))
	     (or (inside-interval-p (+ x eps) (dc-fn-domain))
		 (inside-interval-p (- x eps) (dc-fn-domain))))
  :hints (("Goal"
	   :use ((:instance non-trivial-interval-not-both-endpoints-dc-fn-domain)
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps eps)
			    (interval (dc-fn-domain)))
		 (:instance inside-interval-x+eps
			    (x x)
			    (eps (- eps))
			    (interval (dc-fn-domain)))
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps eps)
			    (interval (dc-fn-domain))
			    )
		 (:instance inside-interval-x-eps
			    (x x)
			    (eps (- eps))
			    (interval (dc-fn-domain))
			    ))
	   ))
  :rule-classes nil)

(local
 (defthm derivative-fn1-o-fn2-is-close-to-differential
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps)
		 (not (equal 0 eps))
		 (i-small eps)
		 (inside-interval-p (+ eps x) (dc-fn-domain)))
    (equal (+ (derivative-dc-fn1 x)
	      (derivative-dc-fn2 x))
	   (standard-part (differential-dc-fn1+fn2 x eps))))
   :hints (("Goal"
	    :use ((:instance differential-dc-fn1-close)
		  (:instance differential-dc-fn2-close))
	    :in-theory (e/d (differential-dc-fn1+fn2-definition)
			    (differential-dc-fn1-close
			     differential-dc-fn2-close))))))

(defthm real-derivative-dc-fn1+fn2
    (implies (inside-interval-p x (dc-fn-domain))
	     (realp (derivative-dc-fn1+fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-dc-fn1+fn2)
				     (differential-rdfn differential-dc-fn1+fn2)
				     (rdfn dc-fn1+fn2)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 3"
	   :use ((:instance derivative-fn1-o-fn2-is-close-to-differential
			    (x x)
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 2"
	   :use ((:instance non-trivial-interval-eps-or--eps-dc-fn-domain
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 1"
	   :use ((:instance derivative-fn1-o-fn2-is-close-to-differential
			    (x x)
			    (eps (- (/ (i-large-integer)))))))
	  ))

(defthm differential-dc-fn1+fn2-close
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dc-fn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-dc-fn1+fn2 x eps))
		   (derivative-dc-fn1+fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-dc-fn1+fn2)
				     (differential-rdfn differential-dc-fn1+fn2)
				     (rdfn dc-fn1+fn2)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable derivative-dc-fn1+fn2-definition))

;; On to unary minus!  As before, we begin with defining the function and its derivative

(encapsulate
 ( ;((dc-munis-fn1 *) => *)
   ((differential-dc-minus-fn1 * *) => *)
   ((derivative-dc-minus-fn1 *) => *)
   )

 (defun dc-minus-fn1 (x)
   (- (dc-fn1 x)))

 (local
  (defun differential-dc-minus-fn1 (x eps)
    (- (differential-dc-fn1 x eps))))

 (local
  (defun derivative-dc-minus-fn1 (x)
    (- (derivative-dc-fn1 x))))

 (defthm differential-dc-minus-fn1-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p (+ x eps) (dc-fn-domain)))
	    (equal (differential-dc-minus-fn1 x eps)
		   (- (differential-dc-fn1 x eps)))))

 (defthm derivative-dc-minus-fn1-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x))
	    (equal (derivative-dc-minus-fn1 x)
		   (- (derivative-dc-fn1 x)))))
 )

;; Now we prove that these functions really are the differential and derivative of the sum

(encapsulate
 nil

 (local
  (defthm lemma-1
      (equal (- (* (+ x1 (- y1))
		   (/ (+ x (- y)))))
	     (* (+ (- x1) y1)
		(/ (+ x (- y)))))))

 (defthm dc-minus-fn1-differentiable-part1
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (inside-interval-p y1 (dc-fn-domain))
		   (i-close x y1) (not (= x y1)))
	      (i-limited  (/ (- (dc-minus-fn1 x) (dc-minus-fn1 y1)) (- x y1))))
   :hints (("Goal"
	    :use ((:instance dc-fn1-differentiable-part1)
		  (:instance i-large-uminus
			     (x (/ (- (dc-fn1 x) (dc-fn1 y1)) (- x y1)))))
	    :in-theory '(dc-minus-fn1
			 functional-self-inversion-of-minus
			 fix
			 dc-fn1-real
			 lemma-1)
	    )))

 (defthm dc-minus-fn1-differentiable-part2
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (inside-interval-p y1 (dc-fn-domain))
		   (inside-interval-p y2 (dc-fn-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
	      (i-close (/ (- (dc-minus-fn1 x) (dc-minus-fn1 y1)) (- x y1))
		       (/ (- (dc-minus-fn1 x) (dc-minus-fn1 y2)) (- x y2))))
   :hints (("Goal"
	    :use (dc-fn1-differentiable-part2
		  (:instance close-uminus
			     (x (/ (- (dc-fn1 x) (dc-fn1 y1)) (- x y1)))
			     (y (/ (- (dc-fn1 x) (dc-fn1 y2)) (- x y2)))))
	    :in-theory '(dc-minus-fn1
			 functional-self-inversion-of-minus
			 fix
			 dc-fn1-real
			 lemma-1)
	    )))
 )

(defthm dc-minus-fn1-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (inside-interval-p y2 (dc-fn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited  (/ (- (dc-minus-fn1 x) (dc-minus-fn1 y1)) (- x y1)))
		 (i-close (/ (- (dc-minus-fn1 x) (dc-minus-fn1 y1)) (- x y1))
			  (/ (- (dc-minus-fn1 x) (dc-minus-fn1 y2)) (- x y2)))))
  :hints (("Goal"
	   :use (dc-minus-fn1-differentiable-part1
		 dc-minus-fn1-differentiable-part2)
	   :in-theory nil
	   )))

(defthm dc-minus-fn1-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (i-close x y)
		 (inside-interval-p y (dc-fn-domain)))
	    (i-close (dc-minus-fn1 x) (dc-minus-fn1 y)))

  :hints (("Goal"
; Added after v4-3 by Matt K.:
           :in-theory (disable (tau-system))
	   :by (:functional-instance rdfn-continuous
				     (rdfn dc-minus-fn1)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 4"
	   :use ((:instance dc-minus-fn1-differentiable))
	   :in-theory (disable dc-minus-fn1-differentiable))
	  ("Subgoal 2"
	   :use ((:instance dc-fn-domain-non-trivial)))))

(defthm realp-differential-dc-minus-fn1
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain))
		(realp eps))
	   (realp (differential-dc-minus-fn1 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-dc-minus-fn1)
				     (rdfn dc-minus-fn1)
				     (rdfn-domain dc-fn-domain))
	   :in-theory (enable differential-dc-fn1-definition
			      differential-dc-fn2-definition)
	   )))

(defthm differential-dc-minus-fn1-limited
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p (+ x eps) (dc-fn-domain))
		  (i-small eps))
	     (i-limited (differential-dc-minus-fn1 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-dc-minus-fn1)
				     (rdfn dc-minus-fn1)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable differential-dc-minus-fn1-definition))

(local
 (defthm derivative-dc-minus-fn1-is-close-to-differential
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps)
		 (not (equal 0 eps))
		 (i-small eps)
		 (inside-interval-p (+ eps x) (dc-fn-domain)))
    (equal (derivative-dc-fn1 x)
	   (standard-part (differential-dc-fn1 x eps))))
   :hints (("Goal"
	    :use ((:instance differential-dc-fn1-close))
	    :in-theory (disable differential-dc-fn1-close)))))

(defthm real-derivative-dc-minus-fn1
    (implies (inside-interval-p x (dc-fn-domain))
	     (realp (derivative-dc-minus-fn1 x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-dc-minus-fn1)
				     (differential-rdfn differential-dc-minus-fn1)
				     (rdfn dc-minus-fn1)
				     (rdfn-domain dc-fn-domain))
	   :in-theory (enable differential-dc-minus-fn1-definition))
	  ("Subgoal 3"
	   :use ((:instance derivative-dc-minus-fn1-is-close-to-differential
			    (x x)
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 2"
	   :use ((:instance non-trivial-interval-eps-or--eps-dc-fn-domain
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 1"
	   :use ((:instance derivative-dc-minus-fn1-is-close-to-differential
			    (x x)
			    (eps (- (/ (i-large-integer)))))))
	  ))

(defthm differential-dc-minus-fn1-close
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dc-fn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-dc-minus-fn1 x eps))
		   (derivative-dc-minus-fn1 x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-dc-minus-fn1)
				     (differential-rdfn differential-dc-minus-fn1)
				     (rdfn dc-minus-fn1)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable derivative-dc-minus-fn1-definition))

;; Now we can define the function fn1*fn2 and its derivatives

(encapsulate
 ( ;((dc-fn1*fn2 *) => *)
   ((differential-dc-fn1*fn2 * *) => *)
   ((derivative-dc-fn1*fn2 *) => *)
   )

  (defun dc-fn1*fn2 (x)
    (* (dc-fn1 x) (dc-fn2 x)))

  (local
   (defun differential-dc-fn1*fn2 (x eps)
     (+ (* (dc-fn1 (+ x eps))
	   (differential-dc-fn2 x eps))
	(* (dc-fn2 x)
	   (differential-dc-fn1 x eps)))))

  (local
   (defun derivative-dc-fn1*fn2 (x)
     (+ (* (dc-fn1 x)
	   (derivative-dc-fn2 x))
	(* (dc-fn2 x)
	   (derivative-dc-fn1 x)))))

  (defthm differential-dc-fn1*fn2-definition
    (implies (and (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p (+ x eps) (dc-fn-domain)))
	     (equal (differential-dc-fn1*fn2 x eps)
		    (+ (* (dc-fn1 (+ x eps))
			  (differential-dc-fn2 x eps))
		       (* (dc-fn2 x)
			  (differential-dc-fn1 x eps))))))

  (defthm derivative-dc-fn1*fn2-definition
    (implies (inside-interval-p x (dc-fn-domain))
	     (equal (derivative-dc-fn1*fn2 x)
		    (+ (* (dc-fn1 x)
			  (derivative-dc-fn2 x))
		       (* (dc-fn2 x)
			  (derivative-dc-fn1 x))))))
  )

;; now we prove that these functions really are the differential and derivative of the sum

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

(defthm expand-differential-dc-fn1*fn2
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain)))
	   (equal (differential-dc-fn1*fn2 x eps)
		  (/ (- (dc-fn1*fn2 (+ x eps)) (dc-fn1*fn2 x)) eps)))
  :hints (("Goal"
	   :in-theory (enable differential-dc-fn1-definition
			      differential-dc-fn2-definition)))
  :rule-classes nil)

(local
 (defthm numberp-differential-dc-fn1*fn2
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p (+ x eps) (dc-fn-domain)))
	    (acl2-numberp (differential-dc-fn1*fn2 x eps)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm limited-differential-dc-fn1*fn2
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps)
		   (not (equal eps 0))
		   (i-small eps)
		   (inside-interval-p (+ x eps) (dc-fn-domain)))
	      (i-limited (differential-dc-fn1*fn2 x eps)))
   :hints (("Goal"
	    :use ((:instance i-limited-plus
			     (x (* (dc-fn1 (+ x eps))
				   (differential-dc-fn2 x eps)))
			     (y (* (dc-fn2 x)
				   (differential-dc-fn1 x eps))))
		  (:instance i-limited-times
			     (x (dc-fn1 (+ x eps)))
			     (y  (differential-dc-fn2 x eps)))
		  (:instance i-limited-times
			     (x (dc-fn2 x))
			     (y (differential-dc-fn1 x eps)))
		  (:instance i-close-limited-lemma
			     (a (dc-fn1 x))
			     (b (dc-fn1 (+ x eps))))
		  (:instance dc-fn1-continuous
			     (x x)
			     (y (+ x eps))))
	    :in-theory '(dc-fn1-real
			 dc-fn2-real
			 i-close-to-small-sum
			 differential-dc-fn1-limited
			 differential-dc-fn2-limited
			 numberp-differential-dc-fn1*fn2
			 standard-dc-fn1
			 standard-dc-fn2
			 standards-are-limited
			 inside-interval-is-real
			 differential-dc-fn1*fn2-definition)))))

(local
 (defthm close-differential-dc-fn1*fn2
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (dc-fn-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (dc-fn-domain)))
	      (i-close (differential-dc-fn1*fn2 x eps1)
		       (differential-dc-fn1*fn2 x eps2)))
   :hints (("Goal"
	    :use ((:instance dc-fn1-continuous
			     (x x)
			     (y (+ x eps1)))
		  (:instance dc-fn1-continuous
			     (x x)
			     (y (+ x eps2)))
		  (:instance i-close-symmetric
			     (x (dc-fn1 x))
			     (y (dc-fn1 (+ x eps1))))
		  (:instance dc-fn2-continuous
			     (x x)
			     (y (+ x eps1)))
		  (:instance dc-fn2-continuous
			     (x x)
			     (y (+ x eps2)))
		  (:instance i-close-symmetric
			     (x (dc-fn2 x))
			     (y (dc-fn2 (+ x eps1))))
		  (:instance i-close-transitive
			     (x (dc-fn1 (+ x eps1)))
			     (y (dc-fn1 x))
			     (z (dc-fn1 (+ x eps2))))
		  (:instance i-close-transitive
			     (x (dc-fn2 (+ x eps1)))
			     (y (dc-fn2 x))
			     (z (dc-fn2 (+ x eps2))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps1))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps2))
		  (:instance close-times-2
			     (x1 (DC-FN1 (+ X EPS1)))
			     (x2 (DC-FN1 (+ X EPS2)))
			     (y1 (DIFFERENTIAL-DC-FN2 X EPS1))
			     (y2 (DIFFERENTIAL-DC-FN2 X EPS2)))
		  (:instance close-times-2
			     (x1 (DC-FN2 x))
			     (x2 (DC-FN2 x))
			     (y1 (DIFFERENTIAL-DC-FN1 X EPS1))
			     (y2 (DIFFERENTIAL-DC-FN1 X EPS2)))
		  (:instance close-differential-dc-fn1)
		  (:instance close-differential-dc-fn2)
		  )
	    :in-theory '(inside-interval-is-real
			 differential-dc-fn1*fn2-definition
			 differential-dc-fn1-limited
			 differential-dc-fn2-limited
			 limited-dc-fn1-eps
			 i-close-reflexive
			 i-close-symmetric
			 dc-fn1-real
			 dc-fn2-real
			 close-plus
			 standard-dc-fn2
			 standards-are-limited)))))

(encapsulate
 nil

 (local
  (defthm lemma-0
      (equal (+ (fix x) y) (+ x y))))

 (local
  (defthm lemma-1
      (equal (* (+ (- x1) y1)
		(/ (+ (- x) y)))
	     (* (+ x1 (- y1))
		(/ (+ x (- y)))))
    :hints (("Goal"
	     :use ((:instance (:theorem (equal (/ (- x) (- y)) (/ x y)))
			      (x (+ (- x1) y1))
			      (y (+ (- x) y))))))
    ))

 (defthm dc-fn1*fn2-differentiable-part1
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (inside-interval-p y1 (dc-fn-domain))
		   (i-close x y1) (not (= x y1)))
	      (i-limited  (/ (- (dc-fn1*fn2 x) (dc-fn1*fn2 y1)) (- x y1))))
   :hints (("Goal"
	    :use ((:instance expand-differential-dc-fn1*fn2
			     (x x)
			     (eps (- y1 x)))
		  (:instance limited-differential-dc-fn1*fn2
			     (eps (- y1 x)))
		  (:instance i-small-uminus
			     (x (- y1 x)))
		  (:instance i-large-uminus
			     (x (* (+ (DC-FN1*FN2 X) (- (DC-FN1*FN2 Y1)))
				   (/ (+ X (- Y1))))))
		  )
	    :in-theory '(differential-dc-fn1*fn2-definition
			 inside-interval-is-real
			 inverse-of-+-as=0
			 fix
			 i-close
			 DISTRIBUTIVITY-OF-MINUS-OVER-+
			 COMMUTATIVITY-OF-+
			 DEFAULT-+-1
			 FUNCTIONAL-SELF-INVERSION-OF-MINUS
			 unicity-of-0
			 MINUS-CANCELLATION-ON-LEFT
			 lemma-1)
	    )))

 (defthm dc-fn1*fn2-differentiable-part2
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (inside-interval-p y1 (dc-fn-domain))
		   (inside-interval-p y2 (dc-fn-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
	      (i-close (/ (- (dc-fn1*fn2 x) (dc-fn1*fn2 y1)) (- x y1))
		       (/ (- (dc-fn1*fn2 x) (dc-fn1*fn2 y2)) (- x y2))))
   :hints (("Goal"
	    :use ((:instance expand-differential-dc-fn1*fn2
			     (x x)
			     (eps (- y1 x)))
		  (:instance expand-differential-dc-fn1*fn2
			     (x x)
			     (eps (- y2 x)))
		  (:instance close-differential-dc-fn1*fn2
			     (eps1 (- y1 x))
			     (eps2 (- y2 x)))
		  (:instance i-small-uminus
			     (x (- y1 x)))
		  (:instance i-small-uminus
			     (x (- y2 x)))
		  )
	    :in-theory '(differential-dc-fn1*fn2-definition
			 inside-interval-is-real
			 inverse-of-+-as=0
			 fix
			 i-close
			 DISTRIBUTIVITY-OF-MINUS-OVER-+
			 COMMUTATIVITY-OF-+
			 DEFAULT-+-1
			 FUNCTIONAL-SELF-INVERSION-OF-MINUS
			 unicity-of-0
			 MINUS-CANCELLATION-ON-LEFT
			 lemma-1
			 )
	    )))
 )

(defthm dc-fn1*fn2-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (inside-interval-p y2 (dc-fn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited  (/ (- (dc-fn1*fn2 x) (dc-fn1*fn2 y1)) (- x y1)))
		 (i-close (/ (- (dc-fn1*fn2 x) (dc-fn1*fn2 y1)) (- x y1))
			  (/ (- (dc-fn1*fn2 x) (dc-fn1*fn2 y2)) (- x y2)))))
  :hints (("Goal"
	   :use (dc-fn1*fn2-differentiable-part1
		 dc-fn1*fn2-differentiable-part2)
	   :in-theory nil
	   )))

(defthm dc-fn1*fn2-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (i-close x y)
		 (inside-interval-p y (dc-fn-domain)))
	    (i-close (dc-fn1*fn2 x) (dc-fn1*fn2 y)))

  :hints (("Goal"
; Added after v4-3 by Matt K.:
           :in-theory (disable (tau-system))
	   :by (:functional-instance rdfn-continuous
				     (rdfn dc-fn1*fn2)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 4"
	   :use ((:instance dc-fn1*fn2-differentiable))
	   :in-theory (disable dc-fn1*fn2-differentiable))
	  ("Subgoal 2"
	   :use ((:instance dc-fn-domain-non-trivial)))))

(defthm realp-differential-dc-fn1*fn2
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain))
		(realp eps))
	   (realp (differential-dc-fn1*fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-dc-fn1*fn2)
				     (rdfn dc-fn1*fn2)
				     (rdfn-domain dc-fn-domain))
	   :in-theory (enable differential-dc-fn1-definition
			      differential-dc-fn2-definition)
	   )))

(defthm differential-dc-fn1*fn2-limited
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p (+ x eps) (dc-fn-domain))
		  (i-small eps))
	     (i-limited (differential-dc-fn1*fn2 x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-dc-fn1*fn2)
				     (rdfn dc-fn1*fn2)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable differential-dc-fn1*fn2-definition))

(local
 (defthm derivative-fn1-*-fn2-is-close-to-differential
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps)
		 (not (equal 0 eps))
		 (i-small eps)
		 (inside-interval-p (+ eps x) (dc-fn-domain)))
    (equal (derivative-dc-fn1*fn2 x)
	   (standard-part (differential-dc-fn1*fn2 x eps))))
   :hints (("Goal"
	    :use ((:instance differential-dc-fn1-close)
		  (:instance differential-dc-fn2-close)
		  (:instance standard-part-of-times
			     (x (dc-fn2 x))
			     (y (differential-dc-fn1 x eps)))
		  (:instance standard-part-of-times
			     (x (differential-dc-fn2 x eps))
			     (y (dc-fn1 (+ eps x))))
		  (:instance limited-dc-fn1-eps)
		  (:instance standard-dc-fn2)
		  (:instance dc-fn1-continuous
			     (x x)
			     (y (+ eps x)))
		  (:instance close-x-y->same-standard-part
			     (x (dc-fn1 x))
			     (y (dc-fn1 (+ eps x))))
		  (:instance i-close-to-small-sum)
		  )
	    :in-theory (e/d (differential-dc-fn1*fn2-definition)
			    (differential-dc-fn1-close
			     differential-dc-fn2-close
			     standard-part-of-times
			     limited-dc-fn1-eps
			     standard-dc-fn2
			     dc-fn1-continuous
			     close-x-y->same-standard-part
			     i-close-to-small-sum))))))

(defthm real-derivative-dc-fn1*fn2
    (implies (inside-interval-p x (dc-fn-domain))
	     (realp (derivative-dc-fn1*fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-dc-fn1*fn2)
				     (differential-rdfn differential-dc-fn1*fn2)
				     (rdfn dc-fn1*fn2)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 3"
	   :use ((:instance derivative-fn1-*-fn2-is-close-to-differential
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 2"
	   :use ((:instance non-trivial-interval-eps-or--eps-dc-fn-domain
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 1"
	   :use ((:instance derivative-fn1-*-fn2-is-close-to-differential
			    (eps (- (/ (i-large-integer)))))))
	  ))

(defthm differential-dc-fn1*fn2-close
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dc-fn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-dc-fn1*fn2 x eps))
		   (derivative-dc-fn1*fn2 x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-dc-fn1*fn2)
				     (differential-rdfn differential-dc-fn1*fn2)
				     (rdfn dc-fn1*fn2)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable derivative-dc-fn1*fn2-definition))

;; On to unary division!  As before, we begin with defining the function and its derivative

(encapsulate
 ( ;((dc-/-fnz *) => *)
   ((differential-dc-/-fnz * *) => *)
   ((derivative-dc-/-fnz *) => *)
   )

 (defun dc-/-fnz (x)
   (/ (dc-fnz x)))

 (local
  (defun differential-dc-/-fnz (x eps)
    (- (/ (differential-dc-fnz x eps)
	  (* (dc-fnz (+ x eps))
	     (dc-fnz x))))
    ))

 (local
  (defun derivative-dc-/-fnz (x)
    (- (/ (derivative-dc-fnz x)
	  (* (dc-fnz x)
	     (dc-fnz x))))
    ))

 (defthm differential-dc-/-fnz-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p (+ x eps) (dc-fn-domain)))
	    (equal (differential-dc-/-fnz x eps)
		   (- (/ (differential-dc-fnz x eps)
			 (* (dc-fnz (+ x eps))
			    (dc-fnz x)))))))

 (defthm derivative-dc-/-fnz-definition
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x))
	    (equal (derivative-dc-/-fnz x)
		   (- (/ (derivative-dc-fnz x)
			 (* (dc-fnz x)
			    (dc-fnz x)))))))
 )

;; Now we prove that these functions really are the differential and derivative of the sum

(defthm expand-differential-dc-/-fnz
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain)))
	   (equal (differential-dc-/-fnz x eps)
		  (/ (- (dc-/-fnz (+ x eps)) (dc-/-fnz x)) eps)))
  :hints (("Goal"
	   :in-theory (enable differential-dc-fnz-definition)))
  :rule-classes nil)


(local
 (defthm numberp-differential-dc-/-fnz
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p (+ x eps) (dc-fn-domain)))
	    (acl2-numberp (differential-dc-/-fnz x eps)))))

(local
 (defthm prod-of-non-small-is-non-small
     (implies (and (i-limited x)
		   (i-limited y)
		   (not (i-small x))
		   (not (i-small y)))
	      (not (i-small (* x y))))
   :hints (("Goal"
	    :use ((:instance standard-part-of-times))
	    :in-theory '(i-small)))))


(local
 (defthm limited-differential-dc-/-fnz
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps)
		   (not (equal eps 0))
		   (i-small eps)
		   (inside-interval-p (+ x eps) (dc-fn-domain)))
	      (i-limited (differential-dc-/-fnz x eps)))
   :hints (("Goal"
	    :use ((:instance i-limited-udivide
			     (x (* (dc-fnz (+ x eps))
				   (dc-fnz x))))
		  (:instance i-limited-times
			     (x (dc-fnz (+ x eps)))
			     (y (dc-fnz x)))
		  (:instance i-limited-times
			     (x (DIFFERENTIAL-DC-FNZ X EPS))
			     (y (/ (* (DC-FNZ (+ X EPS)) (DC-FNZ X)))))
		  (:instance i-close-limited
			     (x x)
			     (y (+ x eps)))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps))
		  (:instance dc-fnz-continuous
			     (x x)
			     (y (+ x eps)))
		  (:instance standard-dc-fnz
			     (x x))
		  (:instance i-close-limited
			     (x (dc-fnz x))
			     (y (dc-fnz (+ x eps))))
		  (:instance differential-dc-fnz-limited)
		  (:instance standard-small-is-zero
			     (x (DC-FNZ X)))
		  (:instance i-close-small-2
			     (x (dc-fnz x))
			     (y (DC-FNZ (+ X eps))))
		  (:instance prod-of-non-small-is-non-small
			     (x (dc-fnz x))
			     (y (DC-FNZ (+ X eps))))
		  )
	    :in-theory '(dc-fnz-real
			 differential-dc-/-fnz-definition
			 standards-are-limited
			 inside-interval-is-real
			 numberp-differential-dc-/-fnz
			 i-large-uminus
			 commutativity-of-*)
	    ))))


(encapsulate
 nil

 (local
  (defthm lemma-0
      (implies (and (acl2-numberp x)
		    (acl2-numberp y)
		    (NOT (EQUAL (+ (- X) Y) 0))
		    (EQUAL (STANDARD-PART (+ (- X) Y)) 0))
	       (not (EQUAL (STANDARD-PART (/ (+ (- X) Y)))
			   0)))
    :hints (("Goal" :use ((:instance I-SMALL-UDIVIDE (x (+ (- X) Y)))
			  (:instance small-are-limited-forward
				     (x (/ (+ (- X) Y)))))
		    :in-theory '(i-small i-large)))))

 (local
  (defthm lemma-1		     ; i-close-multiplicative-inverses
      (implies (and (i-limited x)
		    (not (i-small x))
		    (i-close x y))
	       (equal (standard-part (/ (- y x) (* x y))) 0))
    :hints (("Goal"
	     :use ((:instance i-close-small-2
			      (x x)
			      (y y))
		   (:instance prod-of-non-small-is-non-small
			      (x x)
			      (y y))
		   (:instance i-close-limited
			      (x x)
			      (y y))
		   (:instance i-limited-times
			      (x x)
			      (y y))
		   (:instance i-limited-udivide
			      (x (* x y)))
		   (:instance standard-part-of-udivide
			      (x (* x y)))
		   (:instance standard-part-of-times
			      (x (+ Y (- X)))
			      (y (/ (* x y))))
		   (:instance I-SMALL-UMINUS
			      (x (- y x)))
		   (:instance i-small-udivide
			      (x (+ (- X) Y)))
		   (:instance i-small-udivide
			      (x (/ (+ (- X) Y))))
		   )
	     :in-theory '(i-close
			  i-small
			  i-large
			  fix
			  DISTRIBUTIVITY-OF-MINUS-OVER-+
			  COMMUTATIVITY-OF-+
			  DEFAULT-+-1
			  FUNCTIONAL-SELF-INVERSION-OF-MINUS
			  unicity-of-0
			  MINUS-CANCELLATION-ON-LEFT
			  FUNCTIONAL-SELF-INVERSION-OF-/
			  lemma-0))
	    )))

 (local
  (defthm lemma-2
      (implies (and (acl2-numberp x)
		    (not (equal x 0))
		    (acl2-numberp y)
		    (not (equal y 0)))
	       (equal (* (+ Y (- X)) (/ (* X Y)))
		      (+ (/ X) (- (/ Y)))))))

  (defthm i-close-multiplicative-inverses
      (implies (and (i-limited x)
		    (not (i-small x))
		    (i-close x y))
	       (i-close (/ y) (/ x)))
    :hints (("Goal"
	     :use ((:instance lemma-1)
		   (:instance lemma-2)
		   (:instance STANDARD-PART-OF-UMINUS
			      (x (+ (/ Y) (- (/ X))))))
	     :in-theory '(i-close i-small
			  fix
			  distributivity-of-minus-over-+
			  FUNCTIONAL-SELF-INVERSION-OF-MINUS
			  commutativity-of-+
			  UNICITY-OF-0))))
 )

(encapsulate
 nil

 (local
  (defthm lemma-1
      (implies (and (acl2-numberp x)
		    (not (= x 0))
		    )
	       (equal (i-large (/ x))
		      (i-small x)))
    :hints (("Goal"
	     :in-theory '(i-large
			  fix
			  FUNCTIONAL-SELF-INVERSION-OF-/)))))

 (defthm close-differential-dc-/-fnz
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (realp eps1)
		   (not (equal eps1 0))
		   (i-small eps1)
		   (inside-interval-p (+ x eps1) (dc-fn-domain))
		   (realp eps2)
		   (not (equal eps2 0))
		   (i-small eps2)
		   (inside-interval-p (+ x eps2) (dc-fn-domain)))
	      (i-close (differential-dc-/-fnz x eps1)
		       (differential-dc-/-fnz x eps2)))
   :hints (("Goal"
	    :use ((:instance dc-fnz-continuous
			     (x x)
			     (y (+ x eps1)))
		  (:instance dc-fnz-continuous
			     (x x)
			     (y (+ x eps2)))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps1))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps eps2))
		  (:instance close-times-2
			     (x1 (DIFFERENTIAL-DC-FNZ X EPS1))
			     (x2 (DIFFERENTIAL-DC-FNZ X EPS2))
			     (y1 (/ (* (DC-FNZ (+ X EPS1)) (DC-FNZ X))))
			     (y2 (/ (* (DC-FNZ (+ X EPS2)) (DC-FNZ X)))))
		  (:instance i-close-multiplicative-inverses
			     (x (* (DC-FNZ (+ X EPS1)) (DC-FNZ X)))
			     (y (* (DC-FNZ (+ X EPS2)) (DC-FNZ X))))
		  (:instance i-limited-times
			     (x (DC-FNZ (+ X EPS1)))
			     (Y (DC-FNZ X)))
		  (:instance dc-fnz-continuous
			     (x x)
			     (y (+ x eps1)))
		  (:instance standard-dc-fnz
			     (x x))
		  (:instance i-close-limited
			     (x (dc-fnz x))
			     (y (dc-fnz (+ x eps1))))
		  (:instance dc-fnz-continuous
			     (x x)
			     (y (+ x eps2)))
		  (:instance i-close-limited
			     (x (dc-fnz x))
			     (y (dc-fnz (+ x eps2))))
		  (:instance close-times
			     (x1 (DC-FNZ (+ X EPS1)))
			     (x2 (DC-FNZ (+ X EPS2)))
			     (y (DC-FNZ X)))
		  (:instance i-close-transitive
			     (x (DC-FNZ (+ X EPS1)))
			     (y (DC-FNZ X))
			     (z (DC-FNZ (+ X EPS2))))
		  (:instance prod-of-non-small-is-non-small
			     (x (DC-FNZ (+ X EPS1)))
			     (y (DC-FNZ X)))
		  (:instance I-CLOSE-SMALL
			     (x (DC-FNZ (+ X EPS1)))
			     (y (DC-FNZ X)))
		  (:instance STANDARD-SMALL-IS-ZERO
			     (x (DC-FNZ X)))
		  (:instance lemma-1
			     (x (* (DC-FNZ (+ X EPS1)) (DC-FNZ X))))
		  )
	    :in-theory '(differential-dc-/-fnz-definition
			 dc-fnz-real
			 dc-fnz-non-zero
			 i-close-multiplicative-inverses
			 inside-interval-is-real
			 close-uminus
			 close-differential-dc-fnz
			 i-close-symmetric
			 standards-are-limited
			 differential-dc-fnz-limited
			 realp-differential-dc-fnz)))
	    )
 )


(encapsulate
 nil

 (local
  (defthm lemma-0
      (equal (+ (fix x) y) (+ x y))))

 (local
  (defthm lemma-1
      (equal (* (+ (- x1) y1)
		(/ (+ (- x) y)))
	     (* (+ x1 (- y1))
		(/ (+ x (- y)))))
    :hints (("Goal"
	     :use ((:instance (:theorem (equal (/ (- x) (- y)) (/ x y)))
			      (x (+ (- x1) y1))
			      (y (+ (- x) y))))))
    ))

 (defthm dc-/-fnz-differentiable-part1
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (inside-interval-p y1 (dc-fn-domain))
		   (i-close x y1) (not (= x y1)))
	      (i-limited  (/ (- (dc-/-fnz x) (dc-/-fnz y1)) (- x y1))))
   :hints (("Goal"
	    :use ((:instance expand-differential-dc-/-fnz
			     (x x)
			     (eps (- y1 x)))
		  (:instance limited-differential-dc-/-fnz
			     (x x)
			     (eps (- y1 x)))
		  (:instance I-SMALL-UMINUS
			     (x (+ X (- Y1))))
		  )
	    :in-theory '(commutativity-of-+
			 associativity-of-+
			 commutativity-2-of-+
			 MINUS-CANCELLATION-ON-LEFT
			 inside-interval-is-real
			 fix
			 =
			 i-close
			 distributivity-of-minus-over-+
			 FUNCTIONAL-SELF-INVERSION-OF-MINUS
			 lemma-1)
	    )))

 (defthm dc-/-fnz-differentiable-part2
     (implies (and (standardp x)
		   (inside-interval-p x (dc-fn-domain))
		   (inside-interval-p y1 (dc-fn-domain))
		   (inside-interval-p y2 (dc-fn-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
	      (i-close (/ (- (dc-/-fnz x) (dc-/-fnz y1)) (- x y1))
		       (/ (- (dc-/-fnz x) (dc-/-fnz y2)) (- x y2))))
   :hints (("Goal"
	    :use ((:instance expand-differential-dc-/-fnz
			     (x x)
			     (eps (- y1 x)))
		  (:instance expand-differential-dc-/-fnz
			     (x x)
			     (eps (- y2 x)))
		  (:instance close-differential-dc-/-fnz
			     (x x)
			     (eps1 (- y1 x))
			     (eps2 (- y2 x)))
		  (:instance I-SMALL-UMINUS
			     (x (+ X (- Y1))))
		  (:instance I-SMALL-UMINUS
			     (x (+ X (- Y2))))
		  )
	    :in-theory '(commutativity-of-+
			 associativity-of-+
			 commutativity-2-of-+
			 MINUS-CANCELLATION-ON-LEFT
			 inside-interval-is-real
			 fix
			 =
			 i-close
			 distributivity-of-minus-over-+
			 FUNCTIONAL-SELF-INVERSION-OF-MINUS
			 lemma-1)
	    )))
 )

(defthm dc-/-fnz-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (inside-interval-p y1 (dc-fn-domain))
		 (inside-interval-p y2 (dc-fn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited  (/ (- (dc-/-fnz x) (dc-/-fnz y1)) (- x y1)))
		 (i-close (/ (- (dc-/-fnz x) (dc-/-fnz y1)) (- x y1))
			  (/ (- (dc-/-fnz x) (dc-/-fnz y2)) (- x y2)))))
  :hints (("Goal"
	   :use (dc-/-fnz-differentiable-part1
		 dc-/-fnz-differentiable-part2)
	   :in-theory nil
	   )))

(defthm dc-/-fnz-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (dc-fn-domain))
		 (i-close x y)
		 (inside-interval-p y (dc-fn-domain)))
	    (i-close (dc-/-fnz x) (dc-/-fnz y)))

  :hints (("Goal"
; Added after v4-3 by Matt K.:
           :in-theory (disable (tau-system))
	   :by (:functional-instance rdfn-continuous
				     (rdfn dc-/-fnz)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 4"
	   :use ((:instance dc-/-fnz-differentiable))
	   :in-theory (disable dc-/-fnz-differentiable))
	  ("Subgoal 2"
	   :use ((:instance dc-fn-domain-non-trivial)))))

(local
 (defthm-std standard-/-dc-fnz
   (implies (standardp x)
	    (standardp (/ (dc-fnz x))))))

(local
 (defthm large-not-large-/
   (implies (i-large x)
	    (i-limited (/ x)))
   :hints (("Goal"
	    :in-theory (enable i-close  i-large)))))

(local
 (defthm close-to-/-standard-are-limited
   (implies (and (standardp (/ x))
		 (i-close (fix x) y))
	    (i-limited y))
   :hints (("Goal"
	    :use ((:instance i-close-limited))
	    :in-theory (disable i-close-limited)))
   ))

(local
 (defthm derivative-/-fnz-is-close-to-differential
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps)
		 (not (equal 0 eps))
		 (i-small eps)
		 (inside-interval-p (+ eps x) (dc-fn-domain)))
    (equal (derivative-dc-/-fnz x)
	   (standard-part (differential-dc-/-fnz x eps))))
   :hints (("Goal"
	    :use ((:instance differential-dc-fnz-close)
		  (:instance standard-part-of-times
			     (x (/ (dc-fnz x)))
			     (y (* (differential-dc-fnz x eps)
				   (/ (dc-fnz (+ eps x))))))
		  (:instance standard-part-of-times
			     (x (differential-dc-fnz x eps))
			     (y (/ (dc-fnz (+ eps x)))))
		  (:instance standard-/-dc-fnz)
		  (:instance dc-fnz-continuous
			     (x x)
			     (y (+ eps x)))
		  (:instance i-close-to-small-sum)
		  (:instance standard-small-is-zero
			     (x (dc-fnz x)))
		  (:instance i-close-small
			     (x (dc-fnz (+ eps x)))
			     (y (dc-fnz x)))
		  (:instance close-x-y->same-standard-part
			     (x (dc-fnz x))
			     (y (dc-fnz (+ eps x))))
		  (:instance i-limited-udivide
			     (x (dc-fnz (+ eps x))))
		  )
	    :in-theory (e/d (differential-dc-/-fnz-definition)
			    (differential-dc-fnz-close
			     standard-part-of-times
			     standard-/-dc-fnz
			     standardp-udivide
			     dc-fnz-continuous
			     i-close-to-small-sum
			     i-close-small
			     close-x-y->same-standard-part
			     i-limited-udivide
			     LARGE-IF->-LARGE
			     SMALL-IF-<-SMALL
			     ))))))

(defthm realp-differential-dc-/-fnz
  (implies (and (inside-interval-p x (dc-fn-domain))
		(inside-interval-p (+ x eps) (dc-fn-domain))
		(realp eps))
	   (realp (differential-dc-/-fnz x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-dc-/-fnz)
				     (rdfn dc-/-fnz)
				     (rdfn-domain dc-fn-domain))
	   :in-theory (enable differential-dc-fnz-definition)
	   )))


(defthm differential-dc-/-fnz-limited
    (implies (and (standardp x)
		  (inside-interval-p x (dc-fn-domain))
		  (inside-interval-p (+ x eps) (dc-fn-domain))
		  (i-small eps))
	     (i-limited (differential-dc-/-fnz x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-dc-/-fnz)
				     (rdfn dc-/-fnz)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable differential-dc-/-fnz-definition))

(defthm real-derivative-dc-/-fnz
    (implies (inside-interval-p x (dc-fn-domain))
	     (realp (derivative-dc-/-fnz x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-dc-/-fnz)
				     (differential-rdfn differential-dc-/-fnz)
				     (rdfn dc-/-fnz)
				     (rdfn-domain dc-fn-domain)))
	  ("Subgoal 3"
	   :use ((:instance derivative-/-fnz-is-close-to-differential
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 2"
	   :use ((:instance non-trivial-interval-eps-or--eps-dc-fn-domain
			    (eps (/ (i-large-integer))))))
	  ("Subgoal 1"
	   :use ((:instance derivative-/-fnz-is-close-to-differential
			    (eps (- (/ (i-large-integer)))))))
	  ))

(defthm differential-dc-/-fnz-close
   (implies (and (inside-interval-p x (dc-fn-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dc-fn-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-dc-/-fnz x eps))
		   (derivative-dc-/-fnz x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-dc-/-fnz)
				     (differential-rdfn differential-dc-/-fnz)
				     (rdfn dc-/-fnz)
				     (rdfn-domain dc-fn-domain)))))

(in-theory (disable derivative-dc-/-fnz-definition))

