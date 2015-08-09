#|

This book shows that the sum and product of two differentiable
functions is differentiable.  (See exercise6.lisp for the analogous
result about continuous functions.)

|#

(in-package "ACL2")

(include-book "derivatives")

;; First, we define a generic differentiable function, f1.  This is
;; just a rewrite of the definition in derivatives.lisp for rdfn.

(encapsulate
 ((f1 (x) t))

 ;; Our witness continuous function is the identity function.

 (local (defun f1 (x) x))

 ;; The function returns standard values for standard arguments.

 (defthm f1-standard
   (implies (standard-numberp x)
	    (standard-numberp (f1 x)))
   :rule-classes (:rewrite :type-prescription))

 ;; For real arguments, the function returns real values.

 (defthm f1-real
   (implies (realp x)
	    (realp (f1 x)))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y1 and y2 are two arbitrary reals
 ;; close to x, then (f1(x)-f1(y1))/(x-y1) is close to
 ;; (f1(x)-f1(y2))/(x-y2).  Also, (f1(x)-f1(y1))/(x-y1) is
 ;; limited.  What this means is that the standard-part of that is a
 ;; standard number, and we'll call that the derivative of f1 at x.

 (defthm f1-differentiable
   (implies (and (standard-numberp x)
		 (realp x)
		 (realp y1)
		 (realp y2)
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (f1 x) (f1 y1)) (- x y1)))
		 (i-close (/ (- (f1 x) (f1 y1)) (- x y1))
			  (/ (- (f1 x) (f1 y2)) (- x y2))))))

 )

;; Now, we do the same for another generic differentiable function,
;; f2.

(encapsulate
 ((f2 (x) t))

 ;; Our witness continuous function is the identity function.

 (local (defun f2 (x) x))

 ;; The function returns standard values for standard arguments.

 (defthm f2-standard
   (implies (standard-numberp x)
	    (standard-numberp (f2 x)))
   :rule-classes (:rewrite :type-prescription))

 ;; For real arguments, the function returns real values.

 (defthm f2-real
   (implies (realp x)
	    (realp (f2 x)))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y1 and y2 are two arbitrary reals
 ;; close to x, then (f2(x)-f2(y1))/(x-y1) is close to
 ;; (f2(x)-f2(y2))/(x-y2).  Also, (f2(x)-f2(y1))/(x-y1) is
 ;; limited.  What this means is that the standard-part of that is a
 ;; standard number, and we'll call that the derivative of f2 at x.

 (defthm f2-differentiable
   (implies (and (standard-numberp x)
		 (realp x)
		 (realp y1)
		 (realp y2)
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (f2 x) (f2 y1)) (- x y1)))
		 (i-close (/ (- (f2 x) (f2 y1)) (- x y1))
			  (/ (- (f2 x) (f2 y2)) (- x y2))))))

 )

;; Now, we define the sum of f1 and f2.

(defun f1+f2 (x)
  (+ (f1 x) (f2 x)))

;; To show that f1+f2 is differentiable we concentrate on showing that
;; it satisfies the constraint rdfn-differentiable, since the others
;; are trivial.  First, we have to show that under suitable
;; hypothesis, the slope of the secant chord is limited.  This follows
;; from the fact that the slope of the chord at f1+f2 is the sum of
;; the separate slopes at f1 and f2.

(defthm f1+f2-differentiable-part1
  (implies (and (standard-numberp x)
		(realp x)
		(realp y1)
		(i-close x y1) (not (= x y1)))
	   (i-limited (/ (- (f1+f2 x) (f1+f2 y1)) (- x y1))))
  :hints (("Goal"
	   :use ((:instance i-limited-plus
			    (x (/ (- (f1 x) (f1 y1)) (- x y1)))
			    (y (/ (- (f2 x) (f2 y1)) (- x y1))))
		 (:instance f1-differentiable (y2 y1))
		 (:instance f2-differentiable (y2 y1)))
	   :in-theory (disable i-limited-plus f1-differentiable f2-differentiable))))

;; Next we need to show that if two chords at x are "close", so is their slope.

(encapsulate
 ()

 (local
  (defthm lemma-1
    (equal (i-close (+ a x) (+ a y))
	   (i-close (fix x) (fix y)))
    :hints (("Goal" :in-theory (enable i-close)))))

 (local
  (defthm lemma-2
    (equal (i-close (+ x a) (+ y a))
	   (i-close (fix x) (fix y)))
    :hints (("Goal" :in-theory (enable i-close)))))

 (defthm congruence-of-close-over-+
   (implies (and (i-close x1 x2)
		 (i-close y1 y2))
	    (i-close (+ x1 y1) (+ x2 y2)))
   :hints (("Goal" :use ((:instance i-close-transitive
				    (x (+ x1 y1))
				    (y (+ x1 y2))
				    (z (+ x2 y2))))
	    :in-theory (enable-disable (i-close) (i-close-transitive)))))
 )

(defthm f1+f2-differentiable-part2
  (implies (and (standard-numberp x)
		(realp x)
		(realp y1)
		(realp y2)
		(i-close x y1) (not (= x y1))
		(i-close x y2) (not (= x y2)))
	   (i-close (/ (- (f1+f2 x) (f1+f2 y1)) (- x y1))
		    (/ (- (f1+f2 x) (f1+f2 y2)) (- x y2))))
  :hints (("Goal"
	   :use ((:instance congruence-of-close-over-+
			    (x1 (+ (* (F1 X) (/ (+ X (- Y1))))
				   (- (* (F1 Y1) (/ (+ X (- Y1)))))))
			    (x2 (+ (* (F1 X) (/ (+ X (- Y2))))
				   (- (* (F1 Y2) (/ (+ X (- Y2)))))))
			    (y1 (+ (* (F2 X) (/ (+ X (- Y1))))
				   (- (* (F2 Y1) (/ (+ X (- Y1)))))))
			    (y2 (+ (* (F2 X) (/ (+ X (- Y2))))
				   (- (* (F2 Y2) (/ (+ X (- Y2))))))))
		 (:instance f1-differentiable)
		 (:instance f2-differentiable))
	   :in-theory (disable f1-differentiable f2-differentiable))))

;; Now, to show that indeed we have the f1+f2 is differentiable, we
;; force ACL2 to functionally instantiate rdfn with f1+f2.  The
;; specific theorem we use doesn't matter as much as the :hint.

(encapsulate
 ()

 (local
  (defthm f1+f2-continuous
    (implies (and (standard-numberp x)
		  (realp x)
		  (i-close x y)
		  (realp y))
	     (i-close (f1+f2 x) (f1+f2 y)))
    :hints (("Goal"
	     :by (:functional-instance rdfn-continuous
				       (rdfn f1+f2)))
	    ("Subgoal 3"
	     :use ((:instance f1+f2-differentiable-part1)
		   (:instance f1+f2-differentiable-part2))
	     :in-theory (disable f1+f2-differentiable-part1
				 f1+f2-differentiable-part2
				 f1+f2)))))
 )

;; Now, we do the same for f1*f2.  First, we define this function:

(defun f1*f2 (x)
  (* (f1 x) (f2 x)))

;; Again, we concentrate on showing that it satisfies the constraint
;; rdfn-differentiable, since the others are trivial.  First, we have
;; to show that under suitable hypothesis, the slope of the secant
;; chord is limited.  This follows from the fact that the slope of the
;; chord at f1*f2 is f1*slope(f2) + slope(f1)*f2.  Both slopes are
;; limited, and so are the f1, f2, since f1&f2 are standard functions
;; and we're taking their values at either a standard point or a point
;; close to a standard point.

(defthm f2-continuous
   (implies (and (standard-numberp x)
		 (realp x)
		 (i-close x y)
		 (realp y))
	    (i-close (f2 x) (f2 y)))
   :hints (("Goal"
	    :by (:functional-instance rdfn-continuous
				      (rdfn f2)))
; Changed by Matt K. after v4-3 for tau-system to include these under "Goal'"
; instead of under "Subgoal 3", then again after 6.0 for (most likely)
; tau-system changing "Goal'" to "Subgoal 2".
           ("Subgoal 2"
	    :use (:instance f2-differentiable)
	    :in-theory (disable f2-differentiable))))


(local
 (defthm f2-y1-limited
   (implies (and (realp x)
		 (standard-numberp x)
		 (realp y1)
		 (i-close x y1))
	    (i-limited (f2 y1)))
   :hints (("Goal"
	    :use ((:instance i-close-limited
			     (x (f2 x))
			     (y (f2 y1)))
		  (:instance f2-differentiable (y2 y1)))
	    :in-theory (enable-disable (standards-are-limited)
				       (i-close-limited f2-differentiable
                                                        ;; The following are
                                                        ;; also needed for v2-6.
                                                        I-CLOSE-SYMMETRIC
                                                        I-CLOSE-LARGE-2
                                                        ))))))

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (standard-numberp x)
		  (realp y1)
		  (i-close x y1))
	     (i-limited (/ (* (f2 y1) (- (f1 x) (f1 y1))) (- x y1))))
    :hints (("Goal"
	     :use ((:instance f2-y1-limited)
		   (:instance i-limited-times
			      (x (f2 y1))
			      (y (/ (- (f1 x) (f1 y1)) (- x y1))))
		   (:instance f1-differentiable (y2 y1)))
	     :in-theory (disable f2-y1-limited i-limited-times f1-differentiable)))))

 (local
  (defthm lemma-2
    (implies (and (realp x)
		  (standard-numberp x)
		  (realp y1)
		  (i-close x y1))
	     (i-limited (/ (* (f1 x) (- (f2 x) (f2 y1))) (- x y1))))
    :hints (("Goal"
	     :use ((:instance standards-are-limited
			      (x (f1 x)))
		   (:instance i-limited-times
			      (x (f1 x))
			      (y (/ (- (f2 x) (f2 y1)) (- x y1))))
		   (:instance f2-differentiable (y2 y1)))
	     :in-theory (disable i-limited-times f2-differentiable)))))



 (defthm f1*f2-differentiable-part1
   (implies (and (realp x)
		 (standard-numberp x)
		 (realp y1)
		 (i-close x y1) (not (= x y1)))
	    (i-limited (/ (- (f1*f2 x) (f1*f2 y1)) (- x y1))))
   :hints (("Goal"
	    :use ((:instance i-limited-plus
			     (x (/ (* (f1 x) (- (f2 x) (f2 y1))) (- x y1)))
			     (y (/ (* (f2 y1) (- (f1 x) (f1 y1))) (- x y1))))
		  (:instance lemma-1)
		  (:instance lemma-2))
	    :in-theory (disable i-limited-plus lemma-1 lemma-2))))
 )

;; Next we need to show that if two chords at x are "close", so is their slope.

(defthm f2-uniformly-continuous
   (implies (and (standard-numberp x)
		 (realp x)
		 (i-close x y1)
		 (realp y1)
		 (i-close x y2)
		 (realp y2))
	    (i-close (f2 y1) (f2 y2)))
   :hints (("Goal"
	    :use ((:instance i-close-transitive
			     (x (f2 y1))
			     (y (f2 x))
			     (z (f2 y2))))
	    :in-theory (disable i-close-transitive))))

(defthm congruence-of-close-over-*
  (implies (and (i-close x1 x2)
		(i-close y1 y2)
		(i-limited x1)
		(i-limited y1))
	   (i-close (* x1 y1) (* x2 y2)))
  :hints (("Goal"
	   :use ((:instance i-small-plus
			    (x (* x1 (- y1 y2)))
			    (y (* y2 (- x1 x2))))
		 (:instance small*limited->small
			    (x (- y1 y2))
			    (y x1))
		 (:instance small*limited->small
			    (x (- x1 x2))
			    (y y2)))
	   :in-theory (enable-disable (i-close) (i-small-plus small*limited->small)))))

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (standard-numberp x)
		  (realp x)
		  (i-close x y1)
		  (not (= x y1))
		  (realp y1)
		  (i-close x y2)
		  (not (= x y2))
		  (realp y2))
	     (i-close (/ (* (f2 y1) (- (f1 x) (f1 y1))) (- x y1))
		      (/ (* (f2 y2) (- (f1 x) (f1 y2))) (- x y2))))
    :hints (("Goal"
	     :use ((:instance congruence-of-close-over-*
			      (x1 (f2 y1))
			      (x2 (f2 y2))
			      (y1 (/ (- (f1 x) (f1 y1)) (- x y1)))
			      (y2 (/ (- (f1 x) (f1 y2)) (- x y2))))
		   (:instance f2-uniformly-continuous)
		   (:instance f1-differentiable)
		   (:instance f2-y1-limited))
	     :in-theory (disable congruence-of-close-over-* f2-uniformly-continuous
				 f1-differentiable f2-y1-limited)))))

 (local
  (defthm lemma-2
    (implies (and (standard-numberp x)
		  (realp x)
		  (i-close x y1)
		  (not (= x y1))
		  (realp y1)
		  (i-close x y2)
		  (not (= x y2))
		  (realp y2))
	     (i-close (/ (* (f1 x) (- (f2 x) (f2 y1))) (- x y1))
		      (/ (* (f1 x) (- (f2 x) (f2 y2))) (- x y2))))
    :hints (("Goal"
	     :use ((:instance congruence-of-close-over-*
			      (x1 (f1 x))
			      (x2 (f1 x))
			      (y1 (/ (- (f2 x) (f2 y1)) (- x y1)))
			      (y2 (/ (- (f2 x) (f2 y2)) (- x y2))))
		   (:instance f2-differentiable)
		   (:instance standards-are-limited
			      (x (f1 x))))
	     :in-theory (disable congruence-of-close-over-* f2-differentiable)))))

 (defthm f1*f2-differentiable-part2
   (implies (and (standard-numberp x)
		 (realp x)
		 (realp y1)
		 (realp y2)
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (i-close (/ (- (f1*f2 x) (f1*f2 y1)) (- x y1))
		     (/ (- (f1*f2 x) (f1*f2 y2)) (- x y2))))
   :hints (("Goal"
	    :use ((:instance congruence-of-close-over-+
			     (x1 (/ (* (f1 x) (- (f2 x) (f2 y1))) (- x y1)))
			     (x2 (/ (* (f1 x) (- (f2 x) (f2 y2))) (- x y2)))
			     (y1 (/ (* (f2 y1) (- (f1 x) (f1 y1))) (- x y1)))
			     (y2 (/ (* (f2 y2) (- (f1 x) (f1 y2))) (- x y2))))
		  (:instance lemma-1)
		  (:instance lemma-2))
	    :in-theory (disable congruence-of-close-over-+ lemma-1 lemma-2))))
 )

;; Now, to show that indeed we have the f1*f2 is differentiable, we
;; force ACL2 to functionally instantiate rdfn with f1*f2.  The
;; specific theorem we use doesn't matter as much as the :hint.

(encapsulate
 ()

 (local
  (defthm f1*f2-continuous
    (implies (and (standard-numberp x)
		  (realp x)
		  (i-close x y)
		  (realp y))
	     (i-close (f1*f2 x) (f1*f2 y)))
    :hints (("Goal"
	     :by (:functional-instance rdfn-continuous
				       (rdfn f1*f2)))
	    ("Subgoal 3"
	     :use ((:instance f1*f2-differentiable-part1)
		   (:instance f1*f2-differentiable-part2))
	     :in-theory (disable f1*f2-differentiable-part1
				 f1*f2-differentiable-part2
				 f1*f2)))))
 )

