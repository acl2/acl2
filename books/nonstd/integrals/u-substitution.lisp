; Integration by Substitution
;
; Copyright (C) 2021 University of Wyoming
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Author: Jagadish Bapanapally (jagadishb285@gmail.com)
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(local (include-book "nonstd/nsa/nsa" :dir :system))
(include-book "nonstd/integrals/ftc-2" :dir :system)
(include-book "nonstd/nsa/chain-rule" :dir :system)
(include-book "nonstd/nsa/continuity-product" :dir :system)

(encapsulate
 (
  ((fi *) => *)
  ((fi-domain) => *)
  ((f-prime *) => *)
  ((fi-prime *) => *)
  (fi-range () t)
  (consta () t)
  )

 (local (defun fi (x) (declare (ignore x)) 0))
 (local (defun fi-domain () (interval 0 1)))
 (local (defun f-prime (x) (declare (ignore x)) 0))
 (local (defun fi-prime (x) (declare (ignore x)) 0))
 (local (defun fi-range () (interval 0 1)))
 (local (defun consta() 1))

 (defthmd consta-def
   (and (inside-interval-p (consta) (fi-range))
	(standardp (consta))
	)
   )

 (defthm f-prime-real
   (realp (f-prime x))
   :rule-classes (:rewrite :type-prescription))

 (defthm f-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (i-close x x1)
		 (inside-interval-p x1 (fi-range)))
	    (i-close (f-prime x)
		     (f-prime x1))))

 (defthm fi-real
   (realp (fi x))
   :rule-classes (:rewrite :type-prescription))

 (defthm fi-prime-real
   (realp (fi-prime x))
   :rule-classes (:rewrite :type-prescription))

 (local (defthm i-close-0-lemma
	  (implies (and (standardp x)
			(inside-interval-p x '(0 . 1))
			(inside-interval-p x1 '(0 . 1))
			(i-close x x1)
			(not (equal x x1)))
		   (equal (* 0 (/ (+ x (- x1)))) 0))
	  ))

 (defthm fi-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p x1 (fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (fi x) (fi x1)) (- x x1))
		     (fi-prime x)))
   :hints (("goal"
	    :use (
		  (:instance i-close-0-lemma (x x) (x1 x1))
		  )
	    ))
   )

 (defthm fi-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (fi-domain)))
	    (i-close (fi-prime x)
		     (fi-prime x1))))

 (defthm intervalp-fi-range
   (interval-p (fi-range))
   :rule-classes (:type-prescription :rewrite))

 (defthm fi-range-non-trivial
   (or (null (interval-left-endpoint (fi-range)))
       (null (interval-right-endpoint (fi-range)))
       (< (interval-left-endpoint (fi-range))
	  (interval-right-endpoint (fi-range))))
   :rule-classes nil)

 (defthm intervalp-fi-domain
   (interval-p (fi-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm fi-domain-non-trivial
   (or (null (interval-left-endpoint (fi-domain)))
       (null (interval-right-endpoint (fi-domain)))
       (< (interval-left-endpoint (fi-domain))
	  (interval-right-endpoint (fi-domain))))
   :rule-classes nil)

 (defthm fi-range-in-domain-of-f
   (implies (inside-interval-p x (fi-domain))
	    (inside-interval-p (fi x) (fi-range))))

 )

(defthm fi-range-real
  (implies (inside-interval-p x (fi-range))
	   (realp x))
  :rule-classes (:forward-chaining))

(defthm fi-domain-real
  (implies (inside-interval-p x (fi-domain))
	   (realp x))
  :rule-classes (:forward-chaining))


(defthm-std fi-der-std
  (implies (standardp x)
           (standardp (fi-prime x))
           )
  )

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp a)
		  (i-close a b))
	     (acl2-numberp b))
    :hints (
	    ("goal"
	     :in-theory (enable nsa-theory)
	     ))
    ))

 (local
  (defthm fi-differentiable-lemma1
    (implies (and (standardp x)
		  (inside-interval-p x (fi-domain))
		  (inside-interval-p y1 (fi-domain))
		  (i-close x y1) (not (= x y1)))
	     (and (i-limited (/ (- (fi x) (fi y1)) (- x y1)))))
    :hints (("goal"
	     :use ((:instance fi-der-std)
		   (:instance standards-are-limited-forward (x (fi-prime x)))
		   (:instance fi-prime-is-derivative (x x) (x1 y1))
		   (:instance i-close-symmetric (x (/ (- (fi x) (fi y1)) (- x y1))) (y (fi-prime x)))
		   (:instance i-close-limited (x (fi-prime x)) (y (/ (- (fi x) (fi y1)) (- x y1))))
		   (:instance fi-real)
		   (:instance fi-real (x y1))
		   (:instance fi-domain-real)
		   (:instance fi-domain-real (x y1))
		   (:instance lemma-1 (a (/ (- (fi x) (fi y1)) (- x y1))) (b (fi-prime x))))
	     ))
    ))

 (local
  (defthm fi-differentiable-lemma2
    (implies (and (standardp x)
		  (inside-interval-p x (fi-domain))
		  (inside-interval-p y1 (fi-domain))
		  (inside-interval-p y2 (fi-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (fi x) (fi y1)) (- x y1))
		      (/ (- (fi x) (fi y2)) (- x y2))))
    :hints (("goal"
	     :use ((:instance fi-prime-is-derivative (x x) (x1 y1))
		   (:instance fi-prime-is-derivative (x x) (x1 y2))
		   (:instance i-close-reflexive (x (fi-prime x))))
	     ))
    ))

 (defthm fi-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p y1 (fi-domain))
		 (inside-interval-p y2 (fi-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (fi x) (fi y1)) (- x y1)))
		 (i-close (/ (- (fi x) (fi y1)) (- x y1))
			  (/ (- (fi x) (fi y2)) (- x y2)))))
   :hints(("goal"
	   :use ((:instance fi-differentiable-lemma1)
		 (:instance fi-differentiable-lemma2))
	   ))
   )
 )

(local
 (defthmd i-large-lemma
   (i-small (/(i-large-integer)))
   :hints(("goal"
	   :use (:instance i-large-udivide
			   (x (i-large-integer))
			   )
	   :in-theory (enable nsa-theory)
	   ))
   )
 )

(local
 (defthmd i-small-plus-lemma
   (implies (i-close x y)
	    (i-small (- x y)))
   :hints(("goal"
	   :in-theory (enable nsa-theory)
	   ))
   )
 )

(local
 (defthmd i-close-plus-lemma
   (implies (i-small (- x y))
	    (i-close (- x y) 0))
   :hints(("goal"
	   :in-theory (enable nsa-theory)
	   ))
   )
 )

(local
 (defthmd i-close-plus-lemma-1
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-close (- x y) 0))
	    (i-close x y)
	    )
   :hints(("goal"
	   :in-theory (enable nsa-theory)
	   ))
   )
 )

(local
 (defthmd i-close-plus-lemma-2
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-small (- x y))
		 )
	    (i-close x y))

   :hints (("goal"
	    :use (
		  (:instance i-close-plus-lemma(x x) )
		  (:instance i-close-plus-lemma-1(x x))
		  )
	    )))
 )

(local
 (defthmd i-small-limited-lemma
   (implies (and (acl2-numberp x) (i-small x))
	    (i-limited x))
   )
 )

(local
 (defthmd close-stdpart-lemma1
   (implies (and (i-close x y)
		 (i-limited x))
	    (equal (standard-part x) (standard-part y)))
   )
 )

(local
 (defthmd close-stdpart-lemma2-1
   (implies (and  (standardp x)
		  (acl2-numberp x)
		  )
	    (equal (standard-part x) x)
	    )
   )
 )

(local
 (defthmd close-stdpart-lemma2
   (implies (and (i-close x y)
		 (standardp x)
		 (acl2-numberp x)
		 (acl2-numberp y))
	    (equal (standard-part y) x))
   :hints (("goal"
	    :use ((:instance close-stdpart-lemma1 (x x) (y y))
		  (:instance close-stdpart-lemma2-1 (x x))
		  )))
   )
 )

(local
 (defthmd i-close-lemma1
   (implies (and (i-close x y)
		 (equal x z))
	    (i-close y z)
	    )
   )
 )

(local
 (defthmd i-close-lemma2
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (acl2-numberp x)
		 (acl2-numberp y)
		 (i-close a b)
		 (i-close x y)
		 (i-limited a)
		 (i-limited y)
		 )
	    (i-small (+ (* a (- x y)) (* y (- a b))))
	    )
   :hints (("goal"
	    :use ((:instance i-small-plus-lemma
			     (x x)
			     (y y))
		  (:instance i-small-plus-lemma
			     (x a)
			     (y b))
		  (:instance small*limited->small
			     (x (- x y))
			     (y a))
		  (:instance small*limited->small
			     (x (- a b))
			     (y y))
		  (:instance i-small-plus
			     (x (* a (- x y)))
			     (y (* y (- a b))))
		  )
	    ))
   )
 )

(local
 (defthmd i-close-lemma3
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (acl2-numberp x)
		 (acl2-numberp y)
		 (i-close a b)
		 (i-close x y)
		 (i-limited a)
		 (i-limited y)
		 )
	    (i-close  (* a x) (* b y))
	    )
   :hints (("goal"
	    :use ((:instance i-close-lemma2)
		  (:instance i-close-plus-lemma-2
			     (x (* a x))
			     (y (* b y)))
		  )
	    ))
   )
 )

(local
 (defthm-std standard-f-prime
   (implies (standardp x)
	    (standardp (f-prime x)))))

(local
 (defthm-std standard-fi-prime
   (implies (standardp x)
	    (standardp (fi-prime x)))))


(encapsulate
 (
  ((f-o-fi *) => *)
  ((differential-cr-f * *) => *)
  ((differential-cr-fi * *) => *)
  ((f *) => *)
  ((map-f-prime-1 *) => *)
  ((riemann-f-prime-1 *) => *)
  ((strict-int-f-prime-1 * *) => *)
  ((int-f-prime-1 * *) => *)
  )

 (local
  (defun map-f-prime-1 (p)
    (if (consp p)
	(cons (f-prime (car p))
	      (map-f-prime-1 (cdr p)))
      nil))
  )

 (local
  (defun riemann-f-prime-1 (p)
    (dotprod (deltas p)
	     (map-f-prime-1 (cdr p))))
  )

 (local
  (defthm limited-riemann-f-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (fi-range))
		  (inside-interval-p b (fi-range))
		  (< a b))
	     (i-limited (riemann-f-prime-1 (make-small-partition a b))))
    :hints (("goal"
	     :use (
		   (:functional-instance limited-riemann-rcfn-small-partition
					 (rcfn-domain fi-range)
					 (riemann-rcfn riemann-f-prime-1)
					 (map-rcfn map-f-prime-1)
					 (rcfn f-prime)
					 )
		   )
	     :in-theory (enable interval-definition-theory)
	     )
	    ("subgoal 1"
	     :use ((:instance fi-range-non-trivial))
	     )
	    )
    )
  )

 (local (in-theory (disable riemann-f-prime-1)))
 (local (defun-std strict-int-f-prime-1 (a b)
	  (if (and (realp a)
		   (realp b)
		   (inside-interval-p a (fi-range))
		   (inside-interval-p b (fi-range))
		   (< a b))
	      (standard-part (riemann-f-prime-1 (make-small-partition a b)))
	    0)))

 (local
  (defun int-f-prime-1 (a b)
    (if (<= a b)
	(strict-int-f-prime-1 a b)
      (- (strict-int-f-prime-1 b a))))
  )

 (local
  (defthm ftc-1-fprime
    (implies (and (inside-interval-p a (fi-range))
		  (inside-interval-p b (fi-range))
		  (inside-interval-p c (fi-range))
		  (standardp b)
		  (i-close b c)
		  (not (equal b c)))
	     (i-close (/ (- (int-f-prime-1 a b) (int-f-prime-1 a c))
			 (- b c))
		      (f-prime b)))
    :hints (("goal"
	     :use ((:functional-instance ftc-1
					 (int-rcfn int-f-prime-1)
					 (strict-int-rcfn strict-int-f-prime-1)
					 (map-rcfn map-f-prime-1)
					 (riemann-rcfn riemann-f-prime-1)
					 (rcfn f-prime)
					 (rcfn-domain fi-range)
					 )
		   )
	     ))
    )
  )

 (local
  (defthm realp-strict-int-f-prime
    (implies (and (realp a)
		  (realp b))
	     (realp (strict-int-f-prime-1 a b)))
    :hints (("goal"
	     :by (:functional-instance realp-strict-int-rcfn
				       (strict-int-rcfn strict-int-f-prime-1)
				       (rcfn-domain fi-range)
				       (rcfn f-prime)
				       (riemann-rcfn riemann-f-prime-1)
				       (map-rcfn map-f-prime-1))))))

 (local
  (defthm-std realp-strict-int-f-prime-stronger
    (realp (strict-int-f-prime-1 a b))
    :hints (("goal"
	     :cases ((not (realp a))
		     (not (realp b))))
	    ("subgoal 3"
	     :use ((:instance realp-strict-int-f-prime)))
	    )))

 (local
  (defthm realp-int-f-prime
    (realp (int-f-prime-1 a b))
    )
  )

 (local
  (defun f(x)
    (int-f-prime-1 (consta) x)
    )
  )

 (local
  (encapsulate
   nil

   (local
    (defthm int-f-prime-1-lemma-1
      (implies
       (standardp x)
       (standardp (int-f-prime-1 (consta) x))
       )
      :hints (("goal"
	       :use (
		     (:instance fi-range-real (x x))
		     (:instance consta-def)
		     )
	       ))
      )
    )

   (local
    (in-theory '(int-f-prime-1-lemma-1)))
   (defun-std  f (x)
     (int-f-prime-1 (consta) x)
     )
   )
  )

 (defthm f-real
   (realp (f x))
   :hints (("goal"
	    :use (
		  (:definition f)
		  (:instance realp-int-f-prime
			     (a (consta))
			     (b x))
		  )
	    :in-theory (disable int-f-prime-1)
	    ))
   )

 (defthm f-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (inside-interval-p x1 (fi-range))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (f x) (f x1)) (- x x1))
		     (f-prime x)))
   :hints (("goal"
	    :use ((:instance ftc-1-fprime
			     (b x)
			     (a (consta))
			     (c x1)
			     )
		  (:instance consta-def)
		  )
	    ))
   )

 (defthm f-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (inside-interval-p y1 (fi-range))
		 (inside-interval-p y2 (fi-range))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (f x) (f y1)) (- x y1)))
		 (i-close (/ (- (f x) (f y1)) (- x y1))
			  (/ (- (f x) (f y2)) (- x y2)))))
   :hints (("goal"
	    :use ((:instance f-prime-is-derivative
			     (x x)
			     (x1 y1)
			     )
		  (:instance f-prime-is-derivative
			     (x x)
			     (x1 y2)
			     )
		  (:instance standard-f-prime)
		  (:instance standards-are-limited-forward
			     (x (f-prime x))
			     )
		  )
	    ))
   )

 (local
  (defun f-o-fi (x)
    (f (fi x))))

 (local
  (defun differential-cr-f (x eps)
    (/ (- (f (+ x eps)) (f x)) eps)))
 (local
  (defun differential-cr-fi (x eps)
    (/ (- (fi (+ x eps)) (fi x)) eps)))

 (defthm f-o-fi-equal
   (implies (inside-interval-p x (fi-domain))
	    (equal (f-o-fi x) (f (fi x))))
   )

 (defthm f-o-fi-real
   (realp (f-o-fi x))
   :rule-classes (:rewrite :type-prescription))

 (defthm differential-cr-f-definition
   (implies (and (inside-interval-p x (fi-range))
		 (inside-interval-p (+ x eps) (fi-range)))
	    (equal (differential-cr-f x eps)
		   (/ (- (f (+ x eps)) (f x)) eps))))

 (defthm differential-cr-fi-definition
   (implies (and (inside-interval-p x (fi-domain))
		 (inside-interval-p (+ x eps) (fi-domain)))
	    (equal (differential-cr-fi x eps)
		   (/ (- (fi (+ x eps)) (fi x)) eps))))
 )

(local
 (defthm-std standard-fi-range
   (standardp (fi-range))))

(local
 (defthm-std standard-fi-range-left-endpoint
   (standardp (interval-left-endpoint (fi-range)))))

(local
 (defthm-std standard-fi-range-right-endpoint
   (standardp (interval-right-endpoint (fi-range)))))

(local
 (defthm standard-part-eps
   (implies (i-small eps)
	    (equal (standard-part eps) 0))
   :hints (("goal"
	    :in-theory (enable i-small)))
   ))

(local
 (defthmd x-in-interval-implies-x+-eps-in-interval-1
   (implies (and (realp x)
		 (standardp x)
		 (realp x1)
		 (standardp x1)
		 (< x1 x)
		 (realp eps)
		 (i-small eps))
	    (< x1
	       (+ x eps)))
   :hints (("goal"
	    :use ((:instance standard-part-<-2
			     (x x1)
			     (y (+ x eps))))))))

(local
 (defthmd x-in-interval-implies-x+-eps-in-interval-2
   (implies (and (realp x)
		 (standardp x)
		 (realp x2)
		 (standardp x2)
		 (< x x2)
		 (realp eps)
		 (i-small eps))
	    (< (+ x eps)
	       x2))
   :hints (("goal"
	    :use ((:instance standard-part-<-2
			     (x (+ x eps))
			     (y x2)))))))

(local
 (defthm x-in-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-left-endpoint interval)))
		 (not (realp (interval-right-endpoint interval))))
	    (inside-interval-p x interval))
   :hints (("goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-left-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-left-endpoint interval)))
		 (inside-interval-p y interval)
		 (< x y))
	    (inside-interval-p x interval))
   :hints (("goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-right-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-right-endpoint interval)))
		 (inside-interval-p y interval)
		 (> x y))
	    (inside-interval-p x interval))
   :hints (("goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm nil-not-in-interval
   (implies (and (not x)
		 (interval-p interval))
	    (not (inside-interval-p x interval)))
   :hints (("goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-interval-implies-x+-eps-in-interval
   (implies (and (inside-interval-p x (fi-range))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (fi-range))
		(inside-interval-p (- x eps) (fi-range))))
   :hints (("goal"
	    :use (
		  (:instance fi-range-non-trivial)
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
		  	     (x x)
		  	     (eps eps)
		  	     (x1 (interval-left-endpoint (fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
		  	     (x x)
		  	     (eps (- eps))
		  	     (x1 (interval-left-endpoint (fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
		  	     (x x)
		  	     (eps eps)
		  	     (x2 (interval-right-endpoint (fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
		  	     (x x)
		  	     (eps (- eps))
		  	     (x2 (interval-right-endpoint (fi-range))))
		  )
	    )
	   ("subgoal 9"
	    :in-theory (enable interval-definition-theory))
	   ("subgoal 7"
	    :in-theory (enable interval-definition-theory))
	   ("subgoal 6"
	    :in-theory (enable interval-definition-theory))
	   ("subgoal 3"
	    :in-theory (enable interval-definition-theory))
	   ("subgoal 1"
	    :in-theory (enable interval-definition-theory))
	   )
   :rule-classes nil
   ))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm f-prime-definition
   (implies (and (inside-interval-p x (fi-range))
		 (standardp x))
	    (equal (f-prime x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (fi-range))
		       (standard-part (differential-cr-f x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (fi-range))
			 (standard-part (differential-cr-f x (- (/ (i-large-integer)))))
		       'error))))

   :hints (("goal"
	    :use (
		  (:instance standard-f-prime)
		  (:instance x-in-interval-implies-x+-eps-in-interval
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-large-lemma)
		  (:instance f-prime-is-derivative (x x)
			     (x1 (+ x (/ (i-large-integer))))
			     )
		  (:instance i-close-plus-lemma-2
			     (y x)
			     (x  (+ (/ (i-large-integer)) x))
			     )
		  (:instance close-stdpart-lemma2
			     (x (f-prime x))
			     (y (differential-cr-f x (/ (i-large-integer))))
			     )
		  (:instance f-prime-is-derivative (x x)
			     (x1 (+ x (-(/ (i-large-integer)))))
			     )
		  (:instance i-close-plus-lemma-2
			     (x x)
			     (y (+ (- (/ (i-large-integer))) x))
			     )
		  (:instance close-stdpart-lemma2
			     (x (f-prime x))
			     (y (differential-cr-f x (- (/ (i-large-integer)))))
			     )
		  )
	    ))
   )
 )

(local
 (defthm-std standard-fi-domain
   (standardp (fi-domain))))

(local
 (defthm-std standard-fi-domain-left-endpoint
   (standardp (interval-left-endpoint (fi-domain)))))

(local
 (defthm-std standard-fi-domain-right-endpoint
   (standardp (interval-right-endpoint (fi-domain)))))

(local
 (defthm x-in-interval-implies-x+-eps-in-interval-fi-domain
   (implies (and (inside-interval-p x (fi-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (fi-domain))
		(inside-interval-p (- x eps) (fi-domain))))
   :hints (("goal"
	    :use (
		  (:instance fi-domain-non-trivial)
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps eps)
			     (x1 (interval-left-endpoint (fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps (- eps))
			     (x1 (interval-left-endpoint (fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps eps)
			     (x2 (interval-right-endpoint (fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps (- eps))
			     (x2 (interval-right-endpoint (fi-domain))))
		  )
	    )
	   ("subgoal 9"
	    :in-theory (enable interval-definition-theory))
	   ("subgoal 7"
	    :in-theory (enable interval-definition-theory))
	   ("subgoal 6"
	    :in-theory (enable interval-definition-theory))
	   ("subgoal 3"
	    :in-theory (enable interval-definition-theory))
	   ("subgoal 1"
	    :in-theory (enable interval-definition-theory))
	   )
   ))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fi-prime-definition
   (implies (and (inside-interval-p x (fi-domain))
		 (standardp x))
	    (equal (fi-prime x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (fi-domain))
		       (standard-part (differential-cr-fi x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (fi-domain))
			 (standard-part (differential-cr-fi x (- (/ (i-large-integer)))))
		       'error))))

   :hints (("goal"
	    :use (
		  (:instance standard-fi-prime)
		  (:instance x-in-interval-implies-x+-eps-in-interval-fi-domain
		  	     (x x)
		  	     (eps (/ (i-large-integer))))
		  (:instance fi-prime-is-derivative (x x)
		  	     (x1 (+ x (/ (i-large-integer))))
		  	     )
		  (:instance fi-prime-is-derivative (x x)
		  	     (x1 (- x (/ (i-large-integer))))
		  	     )
		  (:instance i-close-plus-lemma-2
		  	     (x x)
		  	     (y (+ (- (/ (i-large-integer))) x))
		  	     )
		  (:instance i-close-plus-lemma-2
		  	     (y x)
		  	     (x  (+ (/ (i-large-integer)) x))
		  	     )
		  (:instance close-stdpart-lemma2
		  	     (x (fi-prime x))
		  	     (y (differential-cr-fi x (/ (i-large-integer))))
		  	     )
		  (:instance close-stdpart-lemma2
		  	     (x (fi-prime x))
		  	     (y (differential-cr-fi x (- (/ (i-large-integer)))))
		  	     )
		  )
	    ))
   )
 )

(local
 (defthm realp-differential-cr-f
   (implies (and (inside-interval-p x (fi-range))
		 (inside-interval-p (+ x eps) (fi-range))
		 (realp eps))
	    (realp (differential-cr-f x eps)))
   :hints (("goal"
	    :use (:functional-instance realp-differential-rdfn
				       (differential-rdfn differential-cr-f)
				       (rdfn f)
				       (rdfn-domain fi-range)))
	   ("subgoal 3"
	    :use (:instance f-differentiable)
	    )

	   ("subgoal 2"
	    :use (:instance fi-range-non-trivial)
	    )

	   ("subgoal 7"
	    :use (:instance fi-differentiable
			    (x x)
			    (y1 y1)
			    (y2 y2))
	    )
	   )
   )
 )

(local
 (defthm differential-cr-f-limited
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (inside-interval-p (+ x eps) (fi-range))
		 (i-small eps))
	    (i-limited (differential-cr-f x eps)))
   :hints (("goal"
	    :use ((:functional-instance differential-cr-fn1-limited
					(differential-cr-fn1 differential-cr-f)
					(cr-fn1 f)
					(cr-fn2-range fi-range)
					(cr-fn2 fi)
					(cr-fn2-domain fi-domain))

		  ))
	   ("subgoal 2"
	    :use (:instance  f-real)
	    )
	   ("subgoal 3"
	    :use (:instance fi-domain-non-trivial)
	    )
	   ("subgoal 4"
	    :use (:instance fi-range-non-trivial)
	    )
	   ("subgoal 6"
	    :use (:instance f-differentiable
			    (x x)
			    (y1 y1)
			    (y2 y2))
	    )
	   ("subgoal 7"
	    :use (:instance fi-differentiable
			    (x x)
			    (y1 y1)
			    (y2 y2))
	    )
	   ))
 )

(local (in-theory (disable differential-cr-f-definition)))
(local (in-theory (disable f-prime-definition)))

(local
 (defthm realp-differential-cr-fi
   (implies (and (inside-interval-p x (fi-domain))
		 (inside-interval-p (+ x eps) (fi-domain))
		 (realp eps))
	    (realp (differential-cr-fi x eps)))
   :hints (("goal"
	    :by (:functional-instance realp-differential-rdfn
				      (differential-rdfn differential-cr-fi)
				      (rdfn fi)
				      (rdfn-domain fi-domain)))


	   ("subgoal 3"
	    :use (:instance fi-differentiable)
	    )

	   ("subgoal 2"
	    :use (:instance fi-domain-non-trivial)
	    )

	   ("subgoal 7"
	    :use (:instance fi-differentiable
			    (x x)
			    (y1 y1)
			    (y2 y2))
	    )
	   ))
 )

(local
 (defthm differential-cr-fi-limited
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p (+ x eps) (fi-domain))
		 (i-small eps))
	    (i-limited (differential-cr-fi x eps)))
   :hints (("goal"
	    :by (:functional-instance differential-rdfn-limited
				      (differential-rdfn differential-cr-fi)
				      (rdfn fi)
				      (rdfn-domain fi-domain)))))
 )

(local (in-theory (disable differential-cr-fi-definition)))
(local (in-theory (disable fi-prime-definition)))

(encapsulate
 (((differential-cr-f-o-fi * *) => *))
 (local
  (defun differential-cr-f-o-fi (x eps)
    (if (equal (fi (+ x eps)) (fi x))
	0
      (* (differential-cr-f (fi x) (- (fi (+ x eps)) (fi x)))
	 (differential-cr-fi x eps))))
  )

 (defthm differential-cr-f-o-fi-definition
   (implies (and (inside-interval-p x (fi-domain))
		 (inside-interval-p (+ x eps) (fi-domain)))
	    (equal (differential-cr-f-o-fi x eps)
		   (if (equal (fi (+ x eps)) (fi x))
		       0
		     (* (differential-cr-f (fi x) (- (fi (+ x eps)) (fi x)))
			(differential-cr-fi x eps))))))
 )


(encapsulate
 (((derivative-cr-f-o-fi *) => *))

 (local
  (defun derivative-cr-f-o-fi (x)
    (* (f-prime (fi x))
       (fi-prime x)))
  )

 (defthm derivative-cr-f-o-fi-definition
   (implies (inside-interval-p x (fi-domain))
	    (equal (derivative-cr-f-o-fi x)
		   (* (f-prime (fi x))
		      (fi-prime x)))))
 )

(local
 (defthm differential-cr-f-o-fi-close
   (implies (and (inside-interval-p x (fi-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (fi-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-cr-f-o-fi x eps))
		   (derivative-cr-f-o-fi x)))
   :hints (("goal"
	    :use (:functional-instance differential-cr-fn1-o-fn2-close
				       (derivative-cr-fn1-o-fn2 derivative-cr-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-f-o-fi)
				       (cr-fn1-o-fn2 f-o-fi)
				       (cr-fn2-domain fi-domain)
				       (cr-fn2-range fi-range)
				       (cr-fn1 f)
				       (cr-fn2 fi)
				       (derivative-cr-fn2 fi-prime)
				       (derivative-cr-fn1 f-prime)
				       (differential-cr-fn1 differential-cr-f)
				       (differential-cr-fn2 differential-cr-fi)))

	   ("subgoal 4"
	    :use (:instance fi-prime-definition)
	    )
	   ("subgoal 3"
	    :use (:instance differential-cr-fi-definition)
	    )

	   ("subgoal 2"
	    :use (:instance f-prime-definition)
	    )
	   ))
 )

(local
 (defthm differential-cr-f-o-fi-close-1
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p x1 (fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (equal (standard-part (differential-cr-f-o-fi x (- x1 x)))
		   (derivative-cr-f-o-fi x))
	    )
   :hints(("goal"
	   :use ((:instance differential-cr-f-o-fi-close
			    (x x)
			    (eps (- x1 x))
			    )
		 (:instance i-small-plus-lemma
			    (x x1)
			    (y x))
		 )
	   ))
   )
 )

(local
 (defthm expand-differential-cr-f-o-fi
   (implies (and (inside-interval-p x (fi-domain))
		 (inside-interval-p (+ x eps) (fi-domain)))
	    (equal (differential-cr-f-o-fi x eps)
		   (/ (- (f-o-fi (+ x eps)) (f-o-fi x)) eps)))
   :hints (("goal"
	    :use (:functional-instance expand-differential-cr-fn1-o-fn2
				       (derivative-cr-fn1-o-fn2 derivative-cr-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-f-o-fi)
				       (cr-fn1-o-fn2 f-o-fi)
				       (cr-fn2-domain fi-domain)
				       (cr-fn2-range fi-range)
				       (cr-fn1 f)
				       (cr-fn2 fi)
				       (derivative-cr-fn2 fi-prime)
				       (derivative-cr-fn1 f-prime)
				       (differential-cr-fn1 differential-cr-f)
				       (differential-cr-fn2 differential-cr-fi)))
	   )
   )
 )

(encapsulate
 nil

 (local
  (encapsulate
   nil
   (local (include-book "arithmetic/equalities" :dir :system))

   (defthm lemma-1-1
     (implies (and (acl2-numberp a)
		   (acl2-numberp b))
	      (equal (* -1 (- a b))
		     (- b a)
		     ))

     )

   (defthm lemma-1-2
     (implies (and (acl2-numberp a)
		   (acl2-numberp b)
		   (acl2-numberp c)
		   (acl2-numberp d))
	      (equal (/ (* -1 (- a b)) (* -1 (- c d)))
		     (/ (- b a) (- d c)))
	      )
     :hints (("goal"
	      :use ((:instance lemma-1-1)
		    (:instance lemma-1-1 (a c) (b d)))
	      :in-theory nil
	      ))
     )

   (defthm lemma-1-3
     (implies (and (acl2-numberp a)
		   (acl2-numberp b)
		   (acl2-numberp c)
		   (acl2-numberp d))
	      (equal (* (/ a b) (/ c d))
		     (/ (* a c) (* b d))))
     )

   (defthm lemma-1
     (implies (and
	       (acl2-numberp a)
	       (acl2-numberp b)
	       (acl2-numberp c)
	       (acl2-numberp d))
	      (equal (/ (- a b) (- c d))
		     (/ (- b a) (- d c))
		     )
	      )
     :hints (("goal"
	      :use ((:instance lemma-1-3
			       (a -1) (b -1) (c (- a b)) (d (- c d)))
		    (:instance lemma-1-2))

	      ))
     )
   )
  )

 (local
  (defthm lemma
    (implies (and
	      (inside-interval-p x (fi-domain))
	      (inside-interval-p x1 (fi-domain)))
	     (equal (+ x1 x (- x1)) x)
	     )
    ))

 (defthmd expand-differential-cr-f-o-fi-1
   (implies (and (inside-interval-p x (fi-domain))
		 (inside-interval-p x1 (fi-domain)))
	    (equal (differential-cr-f-o-fi x1 (- x x1))
		   (/ (- (f-o-fi x) (f-o-fi x1)) (- x x1))))
   :hints (("goal"
	    :use ((:instance expand-differential-cr-f-o-fi
			     (x x1)
			     (eps (- x x1))
			     )
		  (:instance fi-domain-real)
		  (:instance lemma)
		  )
	    :in-theory '(expand-differential-cr-f-o-fi)
	    ))
   )

 (defthmd expand-differential-cr-f-o-fi-2
   (implies (and (inside-interval-p x (fi-domain))
		 (inside-interval-p x1 (fi-domain)))
	    (equal (differential-cr-f-o-fi x (- x1 x))
		   (/ (- (f-o-fi x) (f-o-fi x1)) (- x x1))))
   :hints (("goal"
	    :use ((:instance expand-differential-cr-f-o-fi-1
			     (x x1)
			     (x1 x)
			     )
		  (:instance fi-domain-real(x x))
		  (:instance fi-domain-real(x x1))
		  (:instance lemma-1
			     (a (f-o-fi x))
			     (b (f-o-fi x1))
			     (c x)
			     (d x1)
			     )
		  (:instance f-o-fi-real(x x))
		  (:instance f-o-fi-real(x x1))
		  )
	    :in-theory '(expand-differential-cr-f-o-fi-1)
	    )
	   ))
 )

(local
 (defthm differential-cr-f-o-fi-limited
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p (+ x eps) (fi-domain))
		 (i-small eps))
	    (i-limited (differential-cr-f-o-fi x eps)))

   :hints (("goal"
	    :use (:functional-instance differential-cr-fn1-o-fn2-limited
				       (derivative-cr-fn1-o-fn2 derivative-cr-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-f-o-fi)
				       (cr-fn1-o-fn2 f-o-fi)
				       (cr-fn2-domain fi-domain)
				       (cr-fn2-range fi-range)
				       (cr-fn1 f)
				       (cr-fn2 fi)
				       (derivative-cr-fn2 fi-prime)
				       (derivative-cr-fn1 f-prime)
				       (differential-cr-fn1 differential-cr-f)
				       (differential-cr-fn2 differential-cr-fi)))
	   )
   )
 )

(encapsulate
 nil
 (local
  (defthm lemma
    (implies (and
	      (inside-interval-p x (fi-domain))
	      (inside-interval-p x1 (fi-domain)))
	     (equal (+ x x1 (- x)) x1)
	     )
    ))

 (defthmd derivative-cr-f-o-fi-limited-1
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p x1 (fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (i-limited (differential-cr-f-o-fi x (- x1 x))))
   :hints (("goal"
	    :use ((:instance differential-cr-f-o-fi-limited
			     (x x)
			     (eps (- x1 x))
			     )
		  (:instance lemma)
		  (:instance i-close-symmetric
			     (x x)
			     (y x1))
		  (:instance i-small-plus-lemma
			     (x x1)
			     (y x))
		  )
	    :in-theory '(differential-cr-f-o-fi-limited)
	    ))
   )
 )

(local
 (defthm derivative-cr-f-o-fi-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p x1 (fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (f-o-fi x) (f-o-fi x1)) (- x x1))
		     (derivative-cr-f-o-fi x))
	    )

   :hints (("goal"
	    :use(
		 (:instance expand-differential-cr-f-o-fi-2
			    (x x)
			    (x1 x1))
		 (:instance  derivative-cr-f-o-fi-limited-1
			     (x x)
			     (x1 x1))
		 (:instance standard-part-close
			    (x (differential-cr-f-o-fi x (- x1 x)))
			    )
		 (:instance differential-cr-f-o-fi-close-1
			    (x x)
			    (x1 x1))
		 (:instance i-close-lemma1
			    (x (standard-part (differential-cr-f-o-fi x (- x1 x))))
			    (y (differential-cr-f-o-fi x (- x1 x)))
			    (z (derivative-cr-f-o-fi x))
			    )
		 )
	    ))
   )
 )

(local
 (defthm real-derivative-cr-f-o-fi
   (implies (inside-interval-p x (fi-domain))
	    (realp (derivative-cr-f-o-fi x)))
   :hints (("goal"
	    :use (:functional-instance real-derivative-cr-fn1-o-fn2
				       (derivative-cr-fn1-o-fn2 derivative-cr-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-f-o-fi)
				       (cr-fn1-o-fn2 f-o-fi)
				       (cr-fn2-domain fi-domain)
				       (cr-fn2-range fi-range)
				       (cr-fn1 f)
				       (cr-fn2 fi)
				       (derivative-cr-fn2 fi-prime)
				       (derivative-cr-fn1 f-prime)
				       (differential-cr-fn1 differential-cr-f)
				       (differential-cr-fn2 differential-cr-fi)))
	   )
   )
 )

(defun f-o-fi-prime (x)
  (if (inside-interval-p x (fi-domain))
      (derivative-cr-f-o-fi x)
    0)
  )

(local
 (defthm f-o-fi-prime-real
   (realp (f-o-fi-prime x))
   :hints (("goal"
	    :use (:instance real-derivative-cr-f-o-fi)
	    ))
   )
 )

(local
 (defthm f-o-fi-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p x1 (fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (f-o-fi x) (f-o-fi x1)) (- x x1))
		     (f-o-fi-prime x)))
   :hints (("goal"
	    :use (
		  (:instance  derivative-cr-f-o-fi-is-derivative)
		  )
	    :in-theory '(f-o-fi-prime derivative-cr-f-o-fi-is-derivative)
	    ))
   )
 )

(local
 (defthm-std fi-standard-1
   (implies (standardp x)
	    (standardp (fi x))
	    )
   )
 )

(local
 (defthm fi-standard
   (implies (standard-numberp x)
	    (standard-numberp (fi x))
	    )
   :hints (("goal"
	    :use (:instance fi-standard-1)
	    ))
   )
 )

(local
 (defthm-std fi-prime-standard-1
   (implies (standardp x)
	    (standardp (fi-prime x))
	    )
   )
 )

(local
 (defthm fi-prime-standard
   (implies (standard-numberp x)
	    (standard-numberp (fi-prime x))
	    )
   :hints (("goal"
	    :use (:instance fi-prime-standard-1)
	    ))
   )
 )

(local
 (defthm-std f-prime-f-standard-1
   (implies (standardp x)
	    (standardp (f-prime (fi x)))
	    )
   )
 )

(local
 (defthm f-prime-f-standard
   (implies (standard-numberp x)
	    (standard-numberp (f-prime (fi x)))
	    )
   :hints (("goal"
	    :use (:instance f-prime-f-standard-1)
	    ))
   )
 )

(local
 (defthm f-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (i-close x y)
		 (inside-interval-p y (fi-range))
		 )
	    (i-close (f x) (f y))
	    )
   :hints (("goal"
	    :use ((:functional-instance rdfn-continuous
					(rdfn f)
					(rdfn-domain fi-range))
		  )
	    ))
   )
 )


(local
 (defthm fi-prime-real-1
   (implies (realp x)
	    (realp (fi-prime x)))
   )
 )

(local
 (defthm f-prime-fi-real-1
   (implies (realp x)
	    (realp (f-prime (fi x))))
   )
 )

(local
 (defthm fi-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (i-close x y)
		 (inside-interval-p y (fi-domain))
		 )
	    (i-close (fi x) (fi y))
	    )
   :hints (("goal"
	    :use ((:functional-instance rdfn-continuous
					(rdfn fi)
					(rdfn-domain fi-domain))
		  )
	    ))
   )
 )

(local
 (defthm f-prime-fi-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (fi-domain))
		 )
	    (i-close (f-prime (fi x))
		     (f-prime (fi x1))))
   :hints (("goal"
	    :use ((:instance f-prime-continuous)
		  (:instance fi-range-in-domain-of-f (x x))
		  (:instance fi-range-in-domain-of-f (x x1))
		  )
	    ))
   ))

(local
 (defthm f-o-fi-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (fi-domain))
		 )
	    (i-close (f-o-fi-prime x)
		     (f-o-fi-prime x1)))
   :hints (("goal"
	    :in-theory (enable standards-are-limited)
	    )
	   )
   )
 )

(local (in-theory (disable f-o-fi-prime)))

(defun map-f-o-fi-prime (p)
  (if (consp p)
      (cons (f-o-fi-prime (car p))
	    (map-f-o-fi-prime (cdr p)))
    nil))

(defun riemann-f-o-fi-prime (p)
  (dotprod (deltas p)
	   (map-f-o-fi-prime (cdr p))))

(local
 (defthm realp-riemann-f-o-fi-prime
   (implies (partitionp p)
	    (realp (riemann-f-o-fi-prime p)))
   :hints (("goal"
	    :use (:instance  f-o-fi-prime-real)
	    ))
   )
 )

(encapsulate
 nil

 (local
  (defthmd limited-riemann-f-o-fi-prime-small-partition-lemma
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (fi-domain))
		  (inside-interval-p b (fi-domain))
		  (< a b))
	     (i-limited (riemann-f-o-fi-prime (make-small-partition a b))))
    :hints (("goal"
	     :by (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain fi-domain)
				       (rcfn f-o-fi-prime)
				       (map-rcfn map-f-o-fi-prime)
				       (riemann-rcfn riemann-f-o-fi-prime)))
	    ("subgoal 2"
	     :use ((:instance fi-domain-non-trivial)))))
  )

 (defthmd limited-riemann-f-o-fi-prime-small-partition
   (implies (and (realp a) (standardp a)
		 (realp b) (standardp b)
		 (inside-interval-p a (fi-domain))
		 (inside-interval-p b (fi-domain))
		 (< a b))
	    (standardp (standard-part(riemann-f-o-fi-prime (make-small-partition a b)))))
   :hints (("goal"
	    :use ((:instance limited-riemann-f-o-fi-prime-small-partition-lemma)
		  (:instance standardp-standard-part (x (riemann-f-o-fi-prime (make-small-partition a b)))))
	    ))
   )

 (local (in-theory nil))
 (local (in-theory (enable limited-riemann-f-o-fi-prime-small-partition)))

 (defun-std strict-int-f-o-fi-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (fi-domain))
	    (inside-interval-p b (fi-domain))
	    (< a b))
       (standard-part (riemann-f-o-fi-prime (make-small-partition a b)))
     0))
 )

(defun int-f-o-fi-prime (a b)
  (if (<= a b)
      (strict-int-f-o-fi-prime a b)
    (- (strict-int-f-o-fi-prime b a))))

(local  (in-theory (disable f-o-fi-equal)))

(local
 (defthmd ftc-2-usub
   (implies (and (inside-interval-p a (fi-domain))
		 (inside-interval-p b (fi-domain)))
	    (equal (int-f-o-fi-prime a b)
		   (- (f-o-fi b)
		      (f-o-fi a))))
   :hints (("goal"
	    :use ((:functional-instance ftc-2
					(rcdfn-domain fi-domain)
					(int-rcdfn-prime int-f-o-fi-prime)
					(riemann-rcdfn-prime riemann-f-o-fi-prime)
					(map-rcdfn-prime map-f-o-fi-prime)
					(rcdfn f-o-fi)
					(rcdfn-prime f-o-fi-prime)
					(strict-int-rcdfn-prime strict-int-f-o-fi-prime))))


	   ("subgoal 7"
	    :use ((:instance f-o-fi-prime-is-derivative)))
	   ("subgoal 8"
	    :use ((:instance f-o-fi-real)))
	   ("subgoal 6"
	    :use ((:instance  fi-domain-non-trivial)))
	   )
   )
 )

(local
 (defthmd ftc2-usub-equal
   (implies (and (inside-interval-p a (fi-domain))
		 (inside-interval-p b (fi-domain)))
	    (equal (int-f-o-fi-prime a b)
		   (- (f (fi b))
		      (f (fi a)))))
   :hints (("goal"
	    :use ((:instance ftc-2-usub)
		  (:instance f-o-fi-equal(x a))
		  (:instance f-o-fi-equal(x b))
		  )

	    ))
   )
 )

(defun map-f-prime (p)
  (if (consp p)
      (cons (f-prime (car p))
	    (map-f-prime (cdr p)))
    nil))

(defun riemann-f-prime (p)
  (dotprod (deltas p)
	   (map-f-prime (cdr p))))

(local
 (defthm realp-riemann-f-prime
   (implies (partitionp p)
	    (realp (riemann-f-prime p))))
 )

(encapsulate
 nil

 (local
  (defthmd limited-riemann-f-prime-small-partition-lemma
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (fi-range))
		  (inside-interval-p b (fi-range))
		  (< a b))
	     (i-limited (riemann-f-prime (make-small-partition a b))))
    :hints (("goal"
	     :by (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain fi-range)
				       (rcfn f-prime)
				       (map-rcfn map-f-prime)
				       (riemann-rcfn riemann-f-prime))
	     :in-theory (disable f-prime-definition)
	     )
	    ("subgoal 2"
	     :use ((:instance fi-range-non-trivial)))
	    )))

 (defthmd limited-riemann-f-prime-small-partition
   (implies (and (realp a) (standardp a)
		 (realp b) (standardp b)
		 (inside-interval-p a (fi-range))
		 (inside-interval-p b (fi-range))
		 (< a b))
	    (standardp (standard-part(riemann-f-prime (make-small-partition a b)))))
   :hints (("goal"
	    :use ((:instance limited-riemann-f-prime-small-partition-lemma)
		  (:instance standardp-standard-part (x (riemann-f-prime (make-small-partition a b)))))
	    ))
   )

 (local (in-theory nil))
 (local (in-theory (enable limited-riemann-f-prime-small-partition)))

 (defun-std strict-int-f-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (fi-range))
	    (inside-interval-p b (fi-range))
	    (< a b))
       (standard-part (riemann-f-prime (make-small-partition a b)))
     0))
 )

(defun int-f-prime (a b)
  (if (<= a b)
      (strict-int-f-prime a b)
    (- (strict-int-f-prime b a))))


(local
 (defthmd ftc-2-usub-1
   (implies (and (inside-interval-p a (fi-range))
		 (inside-interval-p b (fi-range)))
	    (equal (int-f-prime a b)
		   (- (f b)
		      (f a))))
   :hints (("goal"
	    :use (:functional-instance ftc-2
				       (rcdfn-domain fi-range)
				       (int-rcdfn-prime int-f-prime)
				       (riemann-rcdfn-prime riemann-f-prime)
				       (map-rcdfn-prime map-f-prime)
				       (rcdfn f)
				       (rcdfn-prime f-prime)
				       (strict-int-rcdfn-prime strict-int-f-prime))

	    :in-theory (disable f-prime-definition)
	    )
	   ("subgoal 7"
	    :use ((:instance f-prime-is-derivative)))
	   ("subgoal 8"
	    :use ((:instance f-real)))
	   ("subgoal 6"
	    :use ((:instance  fi-range-non-trivial)))
	   )
   )
 )

(local
 (defthmd ftc2-usub-1-equal
   (implies (and (inside-interval-p a (fi-domain))
		 (inside-interval-p b (fi-domain)))
	    (equal (int-f-prime (fi a) (fi b))
		   (- (f (fi b))
		      (f (fi a)))))
   :hints (("goal"
	    :use (
		  (:instance ftc-2-usub-1 (a (fi a))
			     (b (fi b))
			     )
		  )
	    ))
   )
 )

(defthm usubstitution-f-o-fi
  (implies (and (inside-interval-p a (fi-domain))
		(inside-interval-p b (fi-domain)))
	   (equal (int-f-prime (fi a) (fi b))
		  (int-f-o-fi-prime a b)))
  :hints (("goal"
	   :use (
		 (:instance ftc2-usub-1-equal)
		 (:instance ftc2-usub-equal)
		 )
	   :in-theory (disable int-f-o-fi-prime int-f-prime)
	   ))
  )
