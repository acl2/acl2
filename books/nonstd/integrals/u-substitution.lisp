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
  ((usub-fi * *) => *)
  ((usub-fi-domain) => *)
  ((usub-f-prime * *) => *)
  ((usub-fi-prime * *) => *)
  (usub-fi-range () t)
  (consta () t)
  )

 (local (defun usub-fi (contexti x) (declare (ignore contexti x)) 0))
 (local (defun usub-fi-domain () (interval 0 1)))
 (local (defun usub-f-prime (contextf x) (declare (ignore contextf x)) 0))
 (local (defun usub-fi-prime (contexti x) (declare (ignore contexti x)) 0))
 (local (defun usub-fi-range () (interval 0 1)))
 (local (defun consta () 1))

 (defthmd consta-def
   (and (inside-interval-p (consta) (usub-fi-range))
	(standardp (consta))
	)
   )

 (defthm usub-f-prime-real
   (realp (usub-f-prime contextf x))
   :rule-classes (:rewrite :type-prescription))

 (defthm usub-f-prime-continuous
     (implies (and (standardp x)1
                   (standardp contextf)
		   (inside-interval-p x (usub-fi-range))
		   (i-close x x1)
		   (inside-interval-p x1 (usub-fi-range)))
	      (i-close (usub-f-prime contextf x)
		       (usub-f-prime contextf x1))))

 (defthm usub-fi-real
   (realp (usub-fi contexti x))
   :rule-classes (:rewrite :type-prescription))

 (defthm usub-fi-prime-real
   (realp (usub-fi-prime contexti x))
   :rule-classes (:rewrite :type-prescription))

 (local (defthm i-close-0-lemma
	  (implies (and (standardp x)
			(inside-interval-p x '(0 . 1))
			(inside-interval-p x1 '(0 . 1))
			(i-close x x1)
			(not (equal x x1)))
		   (equal (* 0 (/ (+ x (- x1)))) 0))
	  ))

 (defthm usub-fi-prime-is-derivative
     (implies (and (standardp x)
                   (standardp contexti)
		   (inside-interval-p x (usub-fi-domain))
		   (inside-interval-p x1 (usub-fi-domain))
		   (i-close x x1) (not (= x x1)))
	      (i-close (/ (- (usub-fi contexti x) (usub-fi contexti x1))
                          (- x x1))
		       (usub-fi-prime contexti x)))
   :hints (("goal"
	    :use (
		  (:instance i-close-0-lemma (x x) (x1 x1))
		  )
	    ))
   )

 (defthm usub-fi-prime-continuous
     (implies (and (standardp x)
                   (standardp contexti)
		   (inside-interval-p x (usub-fi-domain))
		   (i-close x x1)
		   (inside-interval-p x1 (usub-fi-domain)))
	      (i-close (usub-fi-prime contexti x)
		       (usub-fi-prime contexti x1))))

 (defthm intervalp-usub-fi-range
   (interval-p (usub-fi-range))
   :rule-classes (:type-prescription :rewrite))

 (defthm usub-fi-range-non-trivial
   (or (null (interval-left-endpoint (usub-fi-range)))
       (null (interval-right-endpoint (usub-fi-range)))
       (< (interval-left-endpoint (usub-fi-range))
	  (interval-right-endpoint (usub-fi-range))))
   :rule-classes nil)

 (defthm intervalp-usub-fi-domain
   (interval-p (usub-fi-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm usub-fi-domain-non-trivial
   (or (null (interval-left-endpoint (usub-fi-domain)))
       (null (interval-right-endpoint (usub-fi-domain)))
       (< (interval-left-endpoint (usub-fi-domain))
	  (interval-right-endpoint (usub-fi-domain))))
   :rule-classes nil)

 (defthm usub-fi-range-in-domain-of-f
   (implies (inside-interval-p x (usub-fi-domain))
	    (inside-interval-p (usub-fi contexti x) (usub-fi-range))))

 )

(defthm usub-fi-range-real
  (implies (inside-interval-p x (usub-fi-range))
	   (realp x))
  :rule-classes (:forward-chaining))

(defthm usub-fi-domain-real
  (implies (inside-interval-p x (usub-fi-domain))
	   (realp x))
  :rule-classes (:forward-chaining))


(defthm-std usub-fi-der-std
    (implies (and (standardp x)
                  (standardp contexti))
             (standardp (usub-fi-prime contexti x))))

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
  (defthm usub-fi-differentiable-lemma1
      (implies (and (standardp x)
                    (standardp contexti)
		    (inside-interval-p x (usub-fi-domain))
		    (inside-interval-p y1 (usub-fi-domain))
		    (i-close x y1) (not (= x y1)))
	       (and (i-limited (/ (- (usub-fi contexti x)
                                     (usub-fi contexti y1))
                                  (- x y1)))))
    :hints (("goal"
	     :use ((:instance usub-fi-der-std)
		   (:instance standards-are-limited-forward (x (usub-fi-prime contexti x)))
		   (:instance usub-fi-prime-is-derivative (x x) (x1 y1))
		   (:instance i-close-symmetric (x (/ (- (usub-fi contexti x)
                                                         (usub-fi contexti y1))
                                                      (- x y1)))
                              (y (usub-fi-prime contexti x)))
		   (:instance i-close-limited (x (usub-fi-prime contexti x))
                              (y (/ (- (usub-fi contexti x) (usub-fi contexti y1)) (- x y1))))
		   (:instance usub-fi-real)
		   (:instance usub-fi-real (x y1))
		   (:instance usub-fi-domain-real)
		   (:instance usub-fi-domain-real (x y1))
		   (:instance lemma-1 (a (/ (- (usub-fi contexti x)
                                               (usub-fi contexti y1))
                                            (- x y1)))
                              (b (usub-fi-prime contexti x))))
	     ))
    ))

 (local
  (defthm usub-fi-differentiable-lemma2
      (implies (and (standardp x)
                    (standardp contexti)
		    (inside-interval-p x (usub-fi-domain))
		    (inside-interval-p y1 (usub-fi-domain))
		    (inside-interval-p y2 (usub-fi-domain))
		    (i-close x y1) (not (= x y1))
		    (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (usub-fi contexti x) (usub-fi contexti y1)) (- x y1))
		      (/ (- (usub-fi contexti x) (usub-fi contexti y2)) (- x y2))))
    :hints (("goal"
	     :use ((:instance usub-fi-prime-is-derivative (x x) (x1 y1))
		   (:instance usub-fi-prime-is-derivative (x x) (x1 y2))
		   (:instance i-close-reflexive (x (usub-fi-prime contexti x))))
	     ))
    ))

 (defthm usub-fi-differentiable
     (implies (and (standardp x)
                   (standardp contexti)
		   (inside-interval-p x (usub-fi-domain))
		   (inside-interval-p y1 (usub-fi-domain))
		   (inside-interval-p y2 (usub-fi-domain))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
	      (and (i-limited (/ (- (usub-fi contexti x)
                                    (usub-fi contexti y1))
                                 (- x y1)))
		   (i-close (/ (- (usub-fi contexti x)
                                  (usub-fi contexti y1))
                               (- x y1))
			    (/ (- (usub-fi contexti x)
                                  (usub-fi contexti y2))
                               (- x y2)))))
   :hints(("goal"
	   :use ((:instance usub-fi-differentiable-lemma1)
		 (:instance usub-fi-differentiable-lemma2))
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
 (defthm-std standard-usub-f-prime
     (implies (and (standardp x)
                   (standardp contextf))
	      (standardp (usub-f-prime contextf x)))))

(local
 (defthm-std standard-usub-fi-prime
     (implies (and (standardp x)
                   (standardp contexti))
	      (standardp (usub-fi-prime contexti x)))))


(encapsulate
 (
  ((usub-f-o-fi * *) => *)
  ((differential-cr-usub-f * * *) => *)
  ((differential-cr-usub-fi * * *) => *)
  ((usub-f * *) => *)
  ((map-usub-f-prime-1 * *) => *)
  ((riemann-usub-f-prime-1 * *) => *)
  ((strict-int-usub-f-prime-1 * * *) => *)
  ((int-usub-f-prime-1 * * *) => *)
  ((usub-car-context *) => *)
  ((usub-cdr-context *) => *)
  )

    (local
     (defun usub-car-context (context) (car context)))

    (local
     (defun usub-cdr-context (context) (cdr context)))

 (local
  (defun map-usub-f-prime-1 (contextf p)
    (if (consp p)
	(cons (usub-f-prime contextf (car p))
	      (map-usub-f-prime-1 contextf (cdr p)))
      nil))
  )

 (local
  (defun riemann-usub-f-prime-1 (contextf p)
    (dotprod (deltas p)
	     (map-usub-f-prime-1 contextf (cdr p))))
  )

 (local
  (defthm limited-riemann-usub-f-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
                  (standardp contextf)
		  (inside-interval-p a (usub-fi-range))
		  (inside-interval-p b (usub-fi-range))
		  (< a b))
	     (i-limited (riemann-usub-f-prime-1 contextf (make-small-partition a b))))
    :hints (("goal"
	     :use ((:instance
		    (:functional-instance limited-riemann-rcfn-small-partition
					  (rcfn-domain usub-fi-range)
					  (riemann-rcfn riemann-usub-f-prime-1)
					  (map-rcfn map-usub-f-prime-1)
					  (rcfn usub-f-prime)
					  )
                    (context contextf))
		   )
	     :in-theory (enable interval-definition-theory)
	     )
	    ("subgoal 1"
	     :use ((:instance usub-fi-range-non-trivial))
	     )
	    )
    )
  )

 (local (in-theory (disable riemann-usub-f-prime-1)))
 (local (defun-std strict-int-usub-f-prime-1 (contextf a b)
	  (if (and (realp a)
		   (realp b)
		   (inside-interval-p a (usub-fi-range))
		   (inside-interval-p b (usub-fi-range))
		   (< a b))
	      (standard-part (riemann-usub-f-prime-1 contextf (make-small-partition a b)))
	    0)))

 (local
  (defun int-usub-f-prime-1 (contextf a b)
    (if (<= a b)
	(strict-int-usub-f-prime-1 contextf a b)
      (- (strict-int-usub-f-prime-1 contextf b a))))
  )

 (local
  (defthm ftc-1-fprime
    (implies (and (inside-interval-p a (usub-fi-range))
		  (inside-interval-p b (usub-fi-range))
		  (inside-interval-p c (usub-fi-range))
		  (standardp b)
                  (standardp contextf)
		  (i-close b c)
		  (not (equal b c)))
	     (i-close (/ (- (int-usub-f-prime-1 contextf a b)
                            (int-usub-f-prime-1 contextf a c))
			 (- b c))
		      (usub-f-prime contextf b)))
    :hints (("goal"
	     :use ((:instance
                    (:functional-instance ftc-1
					  (int-rcfn int-usub-f-prime-1)
					  (strict-int-rcfn strict-int-usub-f-prime-1)
					  (map-rcfn map-usub-f-prime-1)
					  (riemann-rcfn riemann-usub-f-prime-1)
					  (rcfn usub-f-prime)
					  (rcfn-domain usub-fi-range)
					  )
                    (context contextf))
		   )
	     ))
    )
  )

 (local
  (defthm realp-strict-int-usub-f-prime
    (implies (and (realp a)
		  (realp b))
	     (realp (strict-int-usub-f-prime-1 contextf a b)))
    :hints (("goal"
	     :by (:functional-instance realp-strict-int-rcfn
				       (strict-int-rcfn strict-int-usub-f-prime-1)
				       (rcfn-domain usub-fi-range)
				       (rcfn usub-f-prime)
				       (riemann-rcfn riemann-usub-f-prime-1)
				       (map-rcfn map-usub-f-prime-1))))))

 (local
  (defthm-std realp-strict-int-usub-f-prime-stronger
    (realp (strict-int-usub-f-prime-1 contextf a b))
    :hints (("goal"
	     :cases ((not (realp a))
		     (not (realp b))))
	    ("subgoal 3"
	     :use ((:instance realp-strict-int-usub-f-prime)))
	    )))

 (local
  (defthm realp-int-usub-f-prime
    (realp (int-usub-f-prime-1 contextf a b))
    )
  )

 (local
  (defun usub-f (contextf x)
    (int-usub-f-prime-1 contextf (consta) x)
    )
  )

 (local
  (encapsulate
   nil

   (local
    (defthm int-usub-f-prime-1-lemma-1
      (implies
       (and (standardp x)
            (standardp contextf))
       (standardp (int-usub-f-prime-1 contextf (consta) x))
       )
      :hints (("goal"
	       :use (
		     (:instance usub-fi-range-real (x x))
		     (:instance consta-def)
		     )
	       ))
      )
    )

   (local
    (in-theory '(int-usub-f-prime-1-lemma-1)))
   (defun-std  f (contextf x)
     (int-usub-f-prime-1 contextf (consta) x)
     )
   )
  )

 (defthm usub-f-real
   (realp (usub-f contextf x))
   :hints (("goal"
	    :use (
		  (:definition usub-f)
		  (:instance realp-int-usub-f-prime
			     (a (consta))
			     (b x))
		  )
	    :in-theory (disable int-usub-f-prime-1)
	    ))
   )

 (defthm usub-f-prime-is-derivative
     (implies (and (standardp x)
                   (standardp contextf)
		   (inside-interval-p x (usub-fi-range))
		   (inside-interval-p x1 (usub-fi-range))
		   (i-close x x1) (not (= x x1)))
	      (i-close (/ (- (usub-f contextf x)
                             (usub-f contextf x1))
                          (- x x1))
		       (usub-f-prime contextf x)))
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

 (defthm usub-f-differentiable
     (implies (and (standardp x)
                   (standardp contextf)
		   (inside-interval-p x (usub-fi-range))
		   (inside-interval-p y1 (usub-fi-range))
		   (inside-interval-p y2 (usub-fi-range))
		   (i-close x y1) (not (= x y1))
		   (i-close x y2) (not (= x y2)))
	      (and (i-limited (/ (- (usub-f contextf x)
                                    (usub-f contextf y1))
                                 (- x y1)))
		   (i-close (/ (- (usub-f contextf x) (usub-f contextf y1))
                               (- x y1))
			    (/ (- (usub-f contextf x) (usub-f contextf y2))
                               (- x y2)))))
   :hints (("goal"
	    :use ((:instance usub-f-prime-is-derivative
			     (x x)
			     (x1 y1)
			     )
		  (:instance usub-f-prime-is-derivative
			     (x x)
			     (x1 y2)
			     )
		  (:instance standard-usub-f-prime)
		  (:instance standards-are-limited-forward
			     (x (usub-f-prime contextf x))
			     )
		  )
	    ))
   )

 (local
  (defun usub-f-o-fi (context x)
    (usub-f (usub-car-context context) (usub-fi (usub-cdr-context context) x))))

 (local
  (defun differential-cr-usub-f (contextf x eps)
    (/ (- (usub-f contextf (+ x eps)) (usub-f contextf x)) eps)))
 (local
  (defun differential-cr-usub-fi (contexti x eps)
    (/ (- (usub-fi contexti (+ x eps)) (usub-fi contexti x)) eps)))

 (defthm usub-f-o-fi-equal
   (implies (inside-interval-p x (usub-fi-domain))
	    (equal (usub-f-o-fi context x)
                   (usub-f (usub-car-context context) (usub-fi (usub-cdr-context context) x))))
   )

 (defthm usub-f-o-fi-real
   (realp (usub-f-o-fi context x))
   :rule-classes (:rewrite :type-prescription))

 (defthm differential-cr-usub-f-definition
   (implies (and (inside-interval-p x (usub-fi-range))
		 (inside-interval-p (+ x eps) (usub-fi-range)))
	    (equal (differential-cr-usub-f contextf x eps)
		   (/ (- (usub-f contextf (+ x eps))
                         (usub-f contextf x))
                      eps))))

 (defthm differential-cr-usub-fi-definition
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (inside-interval-p (+ x eps) (usub-fi-domain)))
	    (equal (differential-cr-usub-fi contexti x eps)
		   (/ (- (usub-fi contexti (+ x eps))
                         (usub-fi contexti x))
                      eps))))
 )

(local
 (defthm-std standard-fi-range
   (standardp (usub-fi-range))))

(local
 (defthm-std standard-usub-fi-range-left-endpoint
   (standardp (interval-left-endpoint (usub-fi-range)))))

(local
 (defthm-std standard-usub-fi-range-right-endpoint
   (standardp (interval-right-endpoint (usub-fi-range)))))

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
   (implies (and (inside-interval-p x (usub-fi-range))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (usub-fi-range))
		(inside-interval-p (- x eps) (usub-fi-range))))
   :hints (("goal"
	    :use (
		  (:instance usub-fi-range-non-trivial)
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
		  	     (x x)
		  	     (eps eps)
		  	     (x1 (interval-left-endpoint (usub-fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
		  	     (x x)
		  	     (eps (- eps))
		  	     (x1 (interval-left-endpoint (usub-fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
		  	     (x x)
		  	     (eps eps)
		  	     (x2 (interval-right-endpoint (usub-fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
		  	     (x x)
		  	     (eps (- eps))
		  	     (x2 (interval-right-endpoint (usub-fi-range))))
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

 (defthm usub-f-prime-definition
   (implies (and (inside-interval-p x (usub-fi-range))
		 (standardp x)
                 (standardp contextf))
	    (equal (usub-f-prime contextf x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (usub-fi-range))
		       (standard-part (differential-cr-usub-f contextf x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (usub-fi-range))
			 (standard-part (differential-cr-usub-f contextf x (- (/ (i-large-integer)))))
		       'error))))

   :hints (("goal"
	    :use (
		  (:instance standard-usub-f-prime)
		  (:instance x-in-interval-implies-x+-eps-in-interval
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-large-lemma)
		  (:instance usub-f-prime-is-derivative (x x)
			     (x1 (+ x (/ (i-large-integer))))
			     )
		  (:instance i-close-plus-lemma-2
			     (y x)
			     (x  (+ (/ (i-large-integer)) x))
			     )
		  (:instance close-stdpart-lemma2
			     (x (usub-f-prime contextf x))
			     (y (differential-cr-usub-f contextf x (/ (i-large-integer))))
			     )
		  (:instance usub-f-prime-is-derivative (x x)
			     (x1 (+ x (-(/ (i-large-integer)))))
			     )
		  (:instance i-close-plus-lemma-2
			     (x x)
			     (y (+ (- (/ (i-large-integer))) x))
			     )
		  (:instance close-stdpart-lemma2
			     (x (usub-f-prime contextf x))
			     (y (differential-cr-usub-f contextf x (- (/ (i-large-integer)))))
			     )
		  )
	    ))
   )
 )

(local
 (defthm-std standard-usub-fi-domain
   (standardp (usub-fi-domain))))

(local
 (defthm-std standard-usub-fi-domain-left-endpoint
   (standardp (interval-left-endpoint (usub-fi-domain)))))

(local
 (defthm-std standard-usub-fi-domain-right-endpoint
   (standardp (interval-right-endpoint (usub-fi-domain)))))

(local
 (defthm x-in-interval-implies-x+-eps-in-interval-usub-fi-domain
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (usub-fi-domain))
		(inside-interval-p (- x eps) (usub-fi-domain))))
   :hints (("goal"
	    :use (
		  (:instance usub-fi-domain-non-trivial)
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps eps)
			     (x1 (interval-left-endpoint (usub-fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps (- eps))
			     (x1 (interval-left-endpoint (usub-fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps eps)
			     (x2 (interval-right-endpoint (usub-fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps (- eps))
			     (x2 (interval-right-endpoint (usub-fi-domain))))
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
 (defthm usub-fi-prime-definition
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (standardp x)
                 (standardp contexti))
	    (equal (usub-fi-prime contexti x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (usub-fi-domain))
		       (standard-part (differential-cr-usub-fi contexti x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (usub-fi-domain))
			 (standard-part (differential-cr-usub-fi contexti x (- (/ (i-large-integer)))))
		       'error))))

   :hints (("goal"
	    :use (
		  (:instance standard-usub-fi-prime)
		  (:instance x-in-interval-implies-x+-eps-in-interval-usub-fi-domain
		  	     (x x)
		  	     (eps (/ (i-large-integer))))
		  (:instance usub-fi-prime-is-derivative (x x)
		  	     (x1 (+ x (/ (i-large-integer))))
		  	     )
		  (:instance usub-fi-prime-is-derivative (x x)
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
		  	     (x (usub-fi-prime contexti x))
		  	     (y (differential-cr-usub-fi contexti x (/ (i-large-integer))))
		  	     )
		  (:instance close-stdpart-lemma2
		  	     (x (usub-fi-prime contexti x))
		  	     (y (differential-cr-usub-fi contexti x (- (/ (i-large-integer)))))
		  	     )
		  )
	    ))
   )
 )

(local
 (defthm realp-differential-cr-usub-f
   (implies (and (inside-interval-p x (usub-fi-range))
		 (inside-interval-p (+ x eps) (usub-fi-range))
		 (realp eps))
	    (realp (differential-cr-usub-f contextf x eps)))
   :hints (("goal"
	    :use ((:instance
                   (:functional-instance realp-differential-rdfn
				         (differential-rdfn differential-cr-usub-f)
				         (rdfn usub-f)
				         (rdfn-domain usub-fi-range))
                   (context contextf))))
	   ("subgoal 3"
	    :use (:instance usub-f-differentiable
                            (contextf context)))
	   ("subgoal 2"
	    :use (:instance usub-fi-range-non-trivial))
           )
   )
 )

(local
 (defthm differential-cr-usub-f-limited
     (implies (and (standardp x)
                   (standardp contextf)
		   (inside-interval-p x (usub-fi-range))
		   (inside-interval-p (+ x eps) (usub-fi-range))
		   (i-small eps))
	    (i-limited (differential-cr-usub-f contextf x eps)))
   :hints (("goal"
	    :use ((:instance
                   (:functional-instance differential-cr-fn1-limited
					 (differential-cr-fn1 differential-cr-usub-f)
					 (cr-fn1 usub-f)
					 (cr-fn2-range usub-fi-range)
					 (cr-fn2 usub-fi)
					 (cr-fn2-domain usub-fi-domain)
                                         (cr-car-context usub-car-context)
                                         (cr-cdr-context usub-cdr-context)
                                         )
                   (context contextf))))
	   ("subgoal 2"
	    :use (:instance  usub-f-real))
	   ("subgoal 3"
	    :use (:instance usub-fi-domain-non-trivial))
	   ("subgoal 4"
	    :use (:instance usub-fi-range-non-trivial))
	   ("subgoal 6"
	    :use ((:instance usub-f-differentiable
                             (contextf context)
			     (x x)
			     (y1 y1)
			     (y2 y2))))
	   ("subgoal 7"
	    :use (:instance usub-fi-differentiable
                            (contexti context)
			    (x x)
			    (y1 y1)
			    (y2 y2)))
	   ))
 )

(local (in-theory (disable differential-cr-usub-f-definition)))
(local (in-theory (disable usub-f-prime-definition)))

(local
 (defthm realp-differential-cr-usub-fi
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (inside-interval-p (+ x eps) (usub-fi-domain))
		 (realp eps))
	    (realp (differential-cr-usub-fi contexti x eps)))
   :hints (("goal"
	    :by (:instance
                 (:functional-instance realp-differential-rdfn
				       (differential-rdfn differential-cr-usub-fi)
				       (rdfn usub-fi)
				       (rdfn-domain usub-fi-domain))
                 (context contexti)))
	   ("subgoal 3"
	    :use (:instance usub-fi-differentiable
                            (contexti context))
	    )

	   ("subgoal 2"
	    :use (:instance usub-fi-domain-non-trivial)
	    )
	   ))
 )

(local
 (defthm differential-cr-usub-fi-limited
     (implies (and (standardp x)
                   (standardp contexti)
		   (inside-interval-p x (usub-fi-domain))
		   (inside-interval-p (+ x eps) (usub-fi-domain))
		   (i-small eps))
	      (i-limited (differential-cr-usub-fi contexti x eps)))
   :hints (("goal"
	    :by (:instance
                 (:functional-instance differential-rdfn-limited
				       (differential-rdfn differential-cr-usub-fi)
				       (rdfn usub-fi)
				       (rdfn-domain usub-fi-domain))
                 (context contexti)
                 ))))
 )

(local (in-theory (disable differential-cr-usub-fi-definition)))
(local (in-theory (disable usub-fi-prime-definition)))

(encapsulate
 (((differential-cr-usub-f-o-fi * * *) => *))
 (local
  (defun differential-cr-usub-f-o-fi (context x eps)
    (if (equal (usub-fi (usub-cdr-context context) (+ x eps)) (usub-fi (usub-cdr-context context) x))
	0
        (* (differential-cr-usub-f (usub-car-context context)
                              (usub-fi (usub-cdr-context context) x)
                              (- (usub-fi (usub-cdr-context context) (+ x eps))
                                 (usub-fi (usub-cdr-context context) x)))
	 (differential-cr-usub-fi (usub-cdr-context context) x eps))))
  )

 (defthm differential-cr-usub-f-o-fi-definition
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (inside-interval-p (+ x eps) (usub-fi-domain)))
	    (equal (differential-cr-usub-f-o-fi context x eps)
		   (if (equal (usub-fi (usub-cdr-context context) (+ x eps))
                              (usub-fi (usub-cdr-context context) x))
		       0
		       (* (differential-cr-usub-f (usub-car-context context)
                                             (usub-fi (usub-cdr-context context) x)
                                             (- (usub-fi (usub-cdr-context context)
                                                         (+ x eps))
                                                (usub-fi (usub-cdr-context context) x)))
			(differential-cr-usub-fi (usub-cdr-context context) x eps))))))
 )


(encapsulate
 (((derivative-cr-usub-f-o-fi * *) => *))

 (local
  (defun derivative-cr-usub-f-o-fi (context x)
    (* (usub-f-prime (usub-car-context context) (usub-fi (usub-cdr-context context) x))
       (usub-fi-prime (usub-cdr-context context) x)))
  )

 (defthm derivative-cr-usub-f-o-fi-definition
   (implies (inside-interval-p x (usub-fi-domain))
	    (equal (derivative-cr-usub-f-o-fi context x)
		   (* (usub-f-prime (usub-car-context context) (usub-fi (usub-cdr-context context) x))
		      (usub-fi-prime (usub-cdr-context context) x)))))
 )

(local
 (defthm differential-cr-usub-f-o-fi-close
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (standardp x)
                 (standardp context)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (usub-fi-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-cr-usub-f-o-fi context x eps))
		   (derivative-cr-usub-f-o-fi context x)))
   :hints (("goal"
	    :use (:functional-instance differential-cr-fn1-o-fn2-close
				       (derivative-cr-fn1-o-fn2 derivative-cr-usub-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-usub-f-o-fi)
				       (cr-fn1-o-fn2 usub-f-o-fi)
				       (cr-fn2-domain usub-fi-domain)
				       (cr-fn2-range usub-fi-range)
				       (cr-fn1 usub-f)
				       (cr-fn2 usub-fi)
                                       (cr-car-context usub-car-context)
                                       (cr-cdr-context usub-cdr-context)
				       (derivative-cr-fn2 usub-fi-prime)
				       (derivative-cr-fn1 usub-f-prime)
				       (differential-cr-fn1 differential-cr-usub-f)
				       (differential-cr-fn2 differential-cr-usub-fi)))

	   ("subgoal 5"
	    :use (:instance usub-fi-prime-definition
                            (contexti context))
	    )
	   ("subgoal 4"
	    :use (:instance differential-cr-usub-fi-definition
                            (contexti context))
	    )

	   ("subgoal 2"
	    :use (:instance usub-f-prime-definition
                            (contextf context))
	    )
	   ))
 )

(local
 (defthm differential-cr-usub-f-o-fi-close-1
     (implies (and (standardp x)
                   (standardp context)
		   (inside-interval-p x (usub-fi-domain))
		   (inside-interval-p x1 (usub-fi-domain))
		   (i-close x x1) (not (= x x1)))
	      (equal (standard-part (differential-cr-usub-f-o-fi context x (- x1 x)))
		     (derivative-cr-usub-f-o-fi context x))
	    )
   :hints(("goal"
	   :use ((:instance differential-cr-usub-f-o-fi-close
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
 (defthm expand-differential-cr-usub-f-o-fi
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (inside-interval-p (+ x eps) (usub-fi-domain)))
	    (equal (differential-cr-usub-f-o-fi context x eps)
		   (/ (- (usub-f-o-fi context (+ x eps)) (usub-f-o-fi context x)) eps)))
   :hints (("goal"
	    :use (:functional-instance expand-differential-cr-fn1-o-fn2
				       (derivative-cr-fn1-o-fn2 derivative-cr-usub-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-usub-f-o-fi)
				       (cr-fn1-o-fn2 usub-f-o-fi)
				       (cr-fn2-domain usub-fi-domain)
				       (cr-fn2-range usub-fi-range)
				       (cr-fn1 usub-f)
				       (cr-fn2 usub-fi)
                                       (cr-car-context usub-car-context)
                                       (cr-cdr-context usub-cdr-context)
				       (derivative-cr-fn2 usub-fi-prime)
				       (derivative-cr-fn1 usub-f-prime)
				       (differential-cr-fn1 differential-cr-usub-f)
				       (differential-cr-fn2 differential-cr-usub-fi)))
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
	      (inside-interval-p x (usub-fi-domain))
	      (inside-interval-p x1 (usub-fi-domain)))
	     (equal (+ x1 x (- x1)) x)
	     )
    ))

 (defthmd expand-differential-cr-usub-f-o-fi-1
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (inside-interval-p x1 (usub-fi-domain)))
	    (equal (differential-cr-usub-f-o-fi context x1 (- x x1))
		   (/ (- (usub-f-o-fi context x)
                         (usub-f-o-fi context x1))
                      (- x x1))))
   :hints (("goal"
	    :use ((:instance expand-differential-cr-usub-f-o-fi
			     (x x1)
			     (eps (- x x1))
			     )
		  (:instance usub-fi-domain-real)
		  (:instance lemma)
		  )
	    :in-theory '(expand-differential-cr-usub-f-o-fi)
	    ))
   )

 (defthmd expand-differential-cr-usub-f-o-fi-2
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (inside-interval-p x1 (usub-fi-domain)))
	    (equal (differential-cr-usub-f-o-fi context x (- x1 x))
		   (/ (- (usub-f-o-fi context x)
                         (usub-f-o-fi context x1))
                      (- x x1))))
   :hints (("goal"
	    :use ((:instance expand-differential-cr-usub-f-o-fi-1
			     (x x1)
			     (x1 x)
			     )
		  (:instance usub-fi-domain-real(x x))
		  (:instance usub-fi-domain-real(x x1))
		  (:instance lemma-1
			     (a (usub-f-o-fi context x))
			     (b (usub-f-o-fi context x1))
			     (c x)
			     (d x1)
			     )
		  (:instance usub-f-o-fi-real(x x))
		  (:instance usub-f-o-fi-real(x x1))
		  )
	    :in-theory '(expand-differential-cr-usub-f-o-fi-1)
	    )
	   ))
 )

(local
 (defthm expand-differential-cr-usub-f-o-fi
   (implies (and (inside-interval-p x (usub-fi-domain))
		 (inside-interval-p (+ x eps) (usub-fi-domain)))
	    (equal (differential-cr-usub-f-o-fi context x eps)
		   (/ (- (usub-f-o-fi context (+ x eps))
                         (usub-f-o-fi context x))
                      eps)))
   :hints (("goal"
	    :use (:functional-instance expand-differential-cr-fn1-o-fn2
				       (derivative-cr-fn1-o-fn2 derivative-cr-usub-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-usub-f-o-fi)
				       (cr-fn1-o-fn2 usub-f-o-fi)
				       (cr-fn2-domain usub-fi-domain)
				       (cr-fn2-range usub-fi-range)
				       (cr-fn1 usub-f)
				       (cr-fn2 usub-fi)
                                       (cr-car-context usub-car-context)
                                       (cr-cdr-context usub-cdr-context)
				       (derivative-cr-fn2 usub-fi-prime)
				       (derivative-cr-fn1 usub-f-prime)
				       (differential-cr-fn1 differential-cr-usub-f)
				       (differential-cr-fn2 differential-cr-usub-fi)))
	   )
   )
 )

(local
 (defthm differential-cr-usub-f-o-fi-limited
     (implies (and (standardp x)
                   (standardp context)
		   (inside-interval-p x (usub-fi-domain))
		   (inside-interval-p (+ x eps) (usub-fi-domain))
		   (i-small eps))
	      (i-limited (differential-cr-usub-f-o-fi context x eps)))

   :hints (("goal"
	    :use (:functional-instance differential-cr-fn1-o-fn2-limited
				       (derivative-cr-fn1-o-fn2 derivative-cr-usub-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-usub-f-o-fi)
				       (cr-fn1-o-fn2 usub-f-o-fi)
				       (cr-fn2-domain usub-fi-domain)
				       (cr-fn2-range usub-fi-range)
				       (cr-fn1 usub-f)
				       (cr-fn2 usub-fi)
                                       (cr-car-context usub-car-context)
                                       (cr-cdr-context usub-cdr-context)
				       (derivative-cr-fn2 usub-fi-prime)
				       (derivative-cr-fn1 usub-f-prime)
				       (differential-cr-fn1 differential-cr-usub-f)
				       (differential-cr-fn2 differential-cr-usub-fi)))
	   )
   )
 )

(encapsulate
 nil
 (local
  (defthm lemma
    (implies (and
	      (inside-interval-p x (usub-fi-domain))
	      (inside-interval-p x1 (usub-fi-domain)))
	     (equal (+ x x1 (- x)) x1)
	     )
    ))

 (defthmd derivative-cr-usub-f-o-fi-limited-1
     (implies (and (standardp x)
                   (standardp context)
		   (inside-interval-p x (usub-fi-domain))
		   (inside-interval-p x1 (usub-fi-domain))
		   (i-close x x1) (not (= x x1)))
	      (i-limited (differential-cr-usub-f-o-fi context x (- x1 x))))
   :hints (("goal"
	    :use ((:instance differential-cr-usub-f-o-fi-limited
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
	    :in-theory '(differential-cr-usub-f-o-fi-limited)
	    ))
   )
 )

(local
 (defthm derivative-cr-usub-f-o-fi-is-derivative
     (implies (and (standardp x)
                   (standardp context)
		   (inside-interval-p x (usub-fi-domain))
		   (inside-interval-p x1 (usub-fi-domain))
		   (i-close x x1) (not (= x x1)))
	      (i-close (/ (- (usub-f-o-fi context x)
                             (usub-f-o-fi context x1))
                          (- x x1))
		       (derivative-cr-usub-f-o-fi context x))
	      )

   :hints (("goal"
	    :use(
		 (:instance expand-differential-cr-usub-f-o-fi-2
			    (x x)
			    (x1 x1))
		 (:instance  derivative-cr-usub-f-o-fi-limited-1
			     (x x)
			     (x1 x1))
		 (:instance standard-part-close
			    (x (differential-cr-usub-f-o-fi context x (- x1 x)))
			    )
		 (:instance differential-cr-usub-f-o-fi-close-1
			    (x x)
			    (x1 x1))
		 (:instance i-close-lemma1
			    (x (standard-part
                                (differential-cr-usub-f-o-fi context x (- x1 x))))
			    (y (differential-cr-usub-f-o-fi context x (- x1 x)))
			    (z (derivative-cr-usub-f-o-fi context x))
			    )
		 )
	    ))
   )
 )

(local
 (defthm real-derivative-cr-usub-f-o-fi
   (implies (inside-interval-p x (usub-fi-domain))
	    (realp (derivative-cr-usub-f-o-fi context x)))
   :hints (("goal"
	    :use (:functional-instance real-derivative-cr-fn1-o-fn2
				       (derivative-cr-fn1-o-fn2 derivative-cr-usub-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-usub-f-o-fi)
				       (cr-fn1-o-fn2 usub-f-o-fi)
				       (cr-fn2-domain usub-fi-domain)
				       (cr-fn2-range usub-fi-range)
				       (cr-fn1 usub-f)
				       (cr-fn2 usub-fi)
                                       (cr-car-context usub-car-context)
                                       (cr-cdr-context usub-cdr-context)
				       (derivative-cr-fn2 usub-fi-prime)
				       (derivative-cr-fn1 usub-f-prime)
				       (differential-cr-fn1 differential-cr-usub-f)
				       (differential-cr-fn2 differential-cr-usub-fi)))
	   )
   )
 )

(defun usub-f-o-fi-prime (context x)
  (if (inside-interval-p x (usub-fi-domain))
      (derivative-cr-usub-f-o-fi context x)
    0)
  )

(local
 (defthm usub-f-o-fi-prime-real
   (realp (usub-f-o-fi-prime context x))
   :hints (("goal"
	    :use (:instance real-derivative-cr-usub-f-o-fi)
	    ))
   )
 )

(local
 (defthm usub-f-o-fi-prime-is-derivative
     (implies (and (standardp x)
                   (standardp context)
		   (inside-interval-p x (usub-fi-domain))
		   (inside-interval-p x1 (usub-fi-domain))
		   (i-close x x1) (not (= x x1)))
	      (i-close (/ (- (usub-f-o-fi context x)
                             (usub-f-o-fi context x1))
                          (- x x1))
		       (usub-f-o-fi-prime context x)))
   :hints (("goal"
	    :use (
		  (:instance  derivative-cr-usub-f-o-fi-is-derivative)
		  )
	    :in-theory '(usub-f-o-fi-prime derivative-cr-usub-f-o-fi-is-derivative)
	    ))
   )
 )

(local
 (defthm-std usub-fi-standard
     (implies (and (standardp x)
                   (standardp contexti))
	      (standardp (usub-fi contexti x))
	      )
   )
 )

(local
 (defthm-std usub-fi-prime-standard
     (implies (and (standardp x)
                   (standardp contexti))
	      (standardp (usub-fi-prime contexti x))
	    )
   )
 )

(local
 (defthm-std usub-f-prime-f-standard
     (implies (and (standardp x)
                   (standardp context))
	      (standardp (usub-f-prime (car context)
                                       (usub-fi (cadr context) x)))
	    )
   )
 )

(local
 (defthm usub-f-continuous
     (implies (and (standardp x)
                   (standardp contextf)
		   (inside-interval-p x (usub-fi-range))
		   (i-close x y)
		   (inside-interval-p y (usub-fi-range))
		   )
	      (i-close (usub-f contextf x)
                       (usub-f contextf y)))
   :hints (("goal"
	    :use ((:instance
                   (:functional-instance rdfn-continuous
					 (rdfn usub-f)
					 (rdfn-domain usub-fi-range))
                   (context contextf))
		  )
	    ))
   )
 )


(local
 (defthm usub-fi-prime-real-1
   (implies (realp x)
	    (realp (usub-fi-prime contexti x)))
   )
 )

(local
 (defthm usub-f-prime-usub-fi-real-1
   (implies (realp x)
	    (realp (usub-f-prime contextf (usub-fi contexti x))))
   )
 )

(local
 (defthm usub-fi-continuous
     (implies (and (standardp x)
                   (standardp contexti)
		   (inside-interval-p x (usub-fi-domain))
		   (i-close x y)
		   (inside-interval-p y (usub-fi-domain))
		   )
	      (i-close (usub-fi contexti x) (usub-fi contexti y))
	    )
   :hints (("goal"
	    :use ((:instance
                   (:functional-instance rdfn-continuous
					 (rdfn usub-fi)
					 (rdfn-domain usub-fi-domain))
                   (context contexti))
		  )
	    ))
   )
 )

(local
 (defthm usub-f-prime-usub-fi-continuous
     (implies (and (standardp x)
                   (standardp contextf)
                   (standardp contexti)
		   (inside-interval-p x (usub-fi-domain))
		   (i-close x x1)
		   (inside-interval-p x1 (usub-fi-domain))
		   )
	    (i-close (usub-f-prime contextf (usub-fi contexti x))
		     (usub-f-prime contextf (usub-fi contexti x1))))
   :hints (("goal"
	    :use ((:instance usub-f-prime-continuous)
		  (:instance usub-fi-range-in-domain-of-f (x x))
		  (:instance usub-fi-range-in-domain-of-f (x x1))
		  )
	    ))
   ))

(local
 (defthm-std standard-usub-car-context
     (implies (standardp context)
              (standardp (usub-car-context context)))))

(local
 (defthm-std standard-usub-cdr-context
     (implies (standardp context)
              (standardp (usub-cdr-context context)))))

(local
 (defthm usub-f-o-fi-prime-continuous
     (implies (and (standardp x)
                   (standardp context)
		   (inside-interval-p x (usub-fi-domain))
		   (i-close x x1)
		   (inside-interval-p x1 (usub-fi-domain))
		 )
	    (i-close (usub-f-o-fi-prime context x)
		     (usub-f-o-fi-prime context x1)))
   :hints (("goal"
            :use ((:instance usub-f-prime-usub-fi-continuous
                             (contextf usub-car-context)
                             (contexti usub-cdr-context)))
	    :in-theory (e/d (standards-are-limited)
                            (usub-f-prime-usub-fi-continuous))
	    )
	   )
   )
 )

(local (in-theory (disable usub-f-o-fi-prime)))

(defun map-usub-f-o-fi-prime (context p)
  (if (consp p)
      (cons (usub-f-o-fi-prime context (car p))
	    (map-usub-f-o-fi-prime context (cdr p)))
    nil))

(defun riemann-usub-f-o-fi-prime (context p)
  (dotprod (deltas p)
	   (map-usub-f-o-fi-prime context (cdr p))))

(local
 (defthm realp-riemann-usub-f-o-fi-prime
   (implies (partitionp p)
	    (realp (riemann-usub-f-o-fi-prime context p)))
   :hints (("goal"
	    :use (:instance  usub-f-o-fi-prime-real)
	    ))
   )
 )

(encapsulate
 nil

 (local
  (defthmd limited-riemann-usub-f-o-fi-prime-small-partition-lemma
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
                  (standardp context)
		  (inside-interval-p a (usub-fi-domain))
		  (inside-interval-p b (usub-fi-domain))
		  (< a b))
	     (i-limited (riemann-usub-f-o-fi-prime context (make-small-partition a b))))
    :hints (("goal"
	     :by (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain usub-fi-domain)
				       (rcfn usub-f-o-fi-prime)
				       (map-rcfn map-usub-f-o-fi-prime)
				       (riemann-rcfn riemann-usub-f-o-fi-prime)))
	    ("subgoal 2"
	     :use ((:instance usub-fi-domain-non-trivial)))))
  )

 (defthmd limited-riemann-usub-f-o-fi-prime-small-partition
   (implies (and (realp a) (standardp a)
		 (realp b) (standardp b)
                 (standardp context)
		 (inside-interval-p a (usub-fi-domain))
		 (inside-interval-p b (usub-fi-domain))
		 (< a b))
	    (standardp (standard-part (riemann-usub-f-o-fi-prime
                                       context (make-small-partition a b)))))
   :hints (("goal"
	    :use ((:instance limited-riemann-usub-f-o-fi-prime-small-partition-lemma)
		  (:instance standardp-standard-part
                             (x (riemann-usub-f-o-fi-prime context
                                                           (make-small-partition a b)))))
	    ))
   )

 (local (in-theory nil))
 (local (in-theory (enable limited-riemann-usub-f-o-fi-prime-small-partition)))

 (defun-std strict-int-usub-f-o-fi-prime (context a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (usub-fi-domain))
	    (inside-interval-p b (usub-fi-domain))
	    (< a b))
       (standard-part (riemann-usub-f-o-fi-prime context (make-small-partition a b)))
     0))
 )

(defun int-usub-f-o-fi-prime (context a b)
  (if (<= a b)
      (strict-int-usub-f-o-fi-prime context a b)
    (- (strict-int-usub-f-o-fi-prime context b a))))

(local  (in-theory (disable usub-f-o-fi-equal)))

(local
 (defthmd ftc-2-usub
   (implies (and (inside-interval-p a (usub-fi-domain))
		 (inside-interval-p b (usub-fi-domain)))
	    (equal (int-usub-f-o-fi-prime context a b)
		   (- (usub-f-o-fi context b)
		      (usub-f-o-fi context a))))
   :hints (("goal"
	    :use ((:functional-instance ftc-2
					(rcdfn-domain usub-fi-domain)
					(int-rcdfn-prime int-usub-f-o-fi-prime)
					(riemann-rcdfn-prime riemann-usub-f-o-fi-prime)
					(map-rcdfn-prime map-usub-f-o-fi-prime)
					(rcdfn usub-f-o-fi)
					(rcdfn-prime usub-f-o-fi-prime)
					(strict-int-rcdfn-prime strict-int-usub-f-o-fi-prime))))


	   ("subgoal 7"
	    :use ((:instance usub-f-o-fi-prime-is-derivative)))
	   ("subgoal 8"
	    :use ((:instance usub-f-o-fi-real)))
	   ("subgoal 6"
	    :use ((:instance  usub-fi-domain-non-trivial)))
	   )
   )
 )

(local
 (defthmd ftc2-usub-equal
   (implies (and (inside-interval-p a (usub-fi-domain))
		 (inside-interval-p b (usub-fi-domain)))
	    (equal (int-usub-f-o-fi-prime context a b)
		   (- (usub-f (usub-car-context context) (usub-fi (usub-cdr-context context) b))
		      (usub-f (usub-car-context context) (usub-fi (usub-cdr-context context) a)))))
   :hints (("goal"
	    :use ((:instance ftc-2-usub)
		  (:instance usub-f-o-fi-equal(x a))
		  (:instance usub-f-o-fi-equal(x b))
		  )

	    ))
   )
 )

(defun map-usub-f-prime (contextf p)
  (if (consp p)
      (cons (usub-f-prime contextf (car p))
	    (map-usub-f-prime contextf (cdr p)))
    nil))

(defun riemann-usub-f-prime (contextf p)
  (dotprod (deltas p)
	   (map-usub-f-prime contextf (cdr p))))

(local
 (defthm realp-riemann-usub-f-prime
   (implies (partitionp p)
	    (realp (riemann-usub-f-prime contextf p))))
 )

(encapsulate
 nil

 (local
  (defthmd limited-riemann-usub-f-prime-small-partition-lemma
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
                  (standardp contextf)
		  (inside-interval-p a (usub-fi-range))
		  (inside-interval-p b (usub-fi-range))
		  (< a b))
	     (i-limited (riemann-usub-f-prime contextf
                                              (make-small-partition a b))))
    :hints (("goal"
	     :by (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain usub-fi-range)
				       (rcfn usub-f-prime)
				       (map-rcfn map-usub-f-prime)
				       (riemann-rcfn riemann-usub-f-prime))
	     :in-theory (disable usub-f-prime-definition)
	     )
	    ("subgoal 2"
	     :use ((:instance usub-fi-range-non-trivial)))
	    )))

 (defthmd limited-riemann-usub-f-prime-small-partition
   (implies (and (realp a) (standardp a)
		 (realp b) (standardp b)
                 (standardp contextf)
		 (inside-interval-p a (usub-fi-range))
		 (inside-interval-p b (usub-fi-range))
		 (< a b))
	    (standardp (standard-part (riemann-usub-f-prime contextf (make-small-partition a b)))))
   :hints (("goal"
	    :use ((:instance limited-riemann-usub-f-prime-small-partition-lemma)
		  (:instance standardp-standard-part
                             (x (riemann-usub-f-prime contextf (make-small-partition a b)))))
	    ))
   )

 (local (in-theory nil))
 (local (in-theory (enable limited-riemann-usub-f-prime-small-partition)))

 (defun-std strict-int-usub-f-prime (contextf a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (usub-fi-range))
	    (inside-interval-p b (usub-fi-range))
	    (< a b))
       (standard-part (riemann-usub-f-prime contextf (make-small-partition a b)))
     0))
 )

(defun int-usub-f-prime (contextf a b)
  (if (<= a b)
      (strict-int-usub-f-prime contextf a b)
    (- (strict-int-usub-f-prime contextf b a))))


(local
 (defthmd ftc-2-usub-1
   (implies (and (inside-interval-p a (usub-fi-range))
		 (inside-interval-p b (usub-fi-range)))
	    (equal (int-usub-f-prime contextf a b)
		   (- (usub-f contextf b)
		      (usub-f contextf a))))
   :hints (("goal"
	    :use ((:instance
                   (:functional-instance ftc-2
				         (rcdfn-domain usub-fi-range)
				         (int-rcdfn-prime int-usub-f-prime)
				         (riemann-rcdfn-prime riemann-usub-f-prime)
				         (map-rcdfn-prime map-usub-f-prime)
				         (rcdfn usub-f)
				         (rcdfn-prime usub-f-prime)
				         (strict-int-rcdfn-prime
                                          strict-int-usub-f-prime))
                   (context contextf)))
	    :in-theory (disable usub-f-prime-definition)
	    )
	   ("subgoal 7"
	    :use ((:instance usub-f-prime-is-derivative
                             (contextf context))))
	   ("subgoal 8"
	    :use ((:instance usub-f-real
                             (contextf context))))
	   ("subgoal 6"
	    :use ((:instance  usub-fi-range-non-trivial)))
	   )
   )
 )

(local
 (defthmd ftc2-usub-1-equal
   (implies (and (inside-interval-p a (usub-fi-domain))
		 (inside-interval-p b (usub-fi-domain)))
	    (equal (int-usub-f-prime contextf
                                     (usub-fi contexti a)
                                     (usub-fi contexti b))
		   (- (usub-f contextf (usub-fi contexti b))
		      (usub-f contextf (usub-fi contexti a)))))
   :hints (("goal"
	    :use (
		  (:instance ftc-2-usub-1
                             (a (usub-fi contexti a))
			     (b (usub-fi contexti b))
			     )
		  )
	    ))
   )
 )

(defthm usubstitution-usub-f-o-fi
  (implies (and (inside-interval-p a (usub-fi-domain))
		(inside-interval-p b (usub-fi-domain)))
	   (equal (int-usub-f-prime (usub-car-context context)
                                    (usub-fi (usub-cdr-context context) a)
                                    (usub-fi (usub-cdr-context context) b))
		  (int-usub-f-o-fi-prime context a b)))
  :hints (("goal"
	   :use (
		 (:instance ftc2-usub-1-equal
                            (contextf (usub-car-context context))
                            (contexti (usub-cdr-context context)))
		 (:instance ftc2-usub-equal)
		 )
	   :in-theory (disable int-usub-f-o-fi-prime int-usub-f-prime)
	   ))
  )
