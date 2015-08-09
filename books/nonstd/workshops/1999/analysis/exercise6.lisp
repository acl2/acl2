#|

This book shows that the sum and product of two continuous functions
is continuous.  (See exercise8.lisp for the analogous result about
differentiable functions.)

|#

(in-package "ACL2")

(include-book "nonstd/nsa/nsa" :dir :system)
(include-book "arithmetic/top" :dir :system)
(include-book "arithmetic/realp" :dir :system)

;; First, we define a generic continuous function, f1.  This is just a
;; rewrite of the definition in continuity.lisp for rcfn.

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

 ;; If x is a standard real and y is a real close to x, then f1(x)
 ;; is close to f1(y).

 (defthm f1-continuous
   (implies (and (standard-numberp x)
		 (realp x)
		 (i-close x y)
		 (realp y))
	    (i-close (f1 x) (f1 y))))
 )

;; We need a separate definition for the second continuous function.
;; This is the way we can reason about two continuous functions
;; simultaneously.  It would be nice to have some support for this
;; sort of syntactic encapsulate building in Acl2.

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

 ;; If x is a standard real and y is a real close to x, then f2(x)
 ;; is close to f2(y).

 (defthm f2-continuous
   (implies (and (standard-numberp x)
		 (realp x)
		 (i-close x y)
		 (realp y))
	    (i-close (f2 x) (f2 y))))
 )

;; Now, we define the sum of f1 and f2.

(defun f1+f2 (x)
  (+ (f1 x) (f2 x)))

;; To show that f1+f2 is continuous, we concentrate on the continuity
;; condition since the other two constraints are obviously true.  The
;; continuity result follows from the fact that x1+y1 is close to
;; x2+y2 when x1 is close to x2 and y1 is close to y2.  But this lemma
;; isn't quite obvious, so we get there in two steps:

(defthm close-plus
  (implies (and (i-close x1 x2)
		(i-limited y))
	   (i-close (+ x1 y) (+ x2 y)))
  :hints (("Goal" :in-theory (enable i-close))))

(defthm close-plus-2
  (implies (and (i-close x1 x2)
		(i-close y1 y2)
		(i-limited x1)
		(i-limited y1))
	   (i-close (+ x1 y1) (+ x2 y2)))
  :hints (("Goal"
	   :use ((:instance close-plus (x1 x1) (x2 x2) (y y1))
		 (:instance close-plus (x1 y1) (x2 y2) (y x2))
		 (:instance i-close-transitive
			    (x (+ x1 y1))
			    (y (+ x2 y1))
			    (z (+ x2 y2)))
		 (:instance i-close-limited
			    (x x1)
			    (y x2)))
	   :in-theory (disable close-plus i-close-transitive i-close-limited))))

;; Now we can show that f1+f2 is continuous:

(defthm f1+f2-continuous
  (implies (and (standard-numberp x)
		(realp x)
		(i-close x y)
		(realp y))
	   (i-close (f1+f2 x) (f1+f2 y)))
  :hints (("Goal" :in-theory (enable standards-are-limited))))

;; But are we really done?  To show that we are, we force ACL2 to
;; functionally instantiate rcfn with f1+f2 (Note, the actual theorem
;; we prove doesn't matter):

(encapsulate
 nil
 (local (include-book "continuity"))

 (local
  (defthm f1+f2-uniformly-continuous
    (implies (and (i-limited x)
		  (realp x)
		  (i-close x y)
		  (realp y))
	     (i-close (f1+f2 x) (f1+f2 y)))
    :hints (("Goal"
	     :by (:functional-instance rcfn-uniformly-continuous
				       (rcfn f1+f2)))
	    ("Subgoal 3"
	     :in-theory (disable f1+f2))))))

;; We can also show that the product of f1 and f2 is continuous.  The
;; reasoning follows the one above very closely.

;; First, we define the function f1*f2.

(defun f1*f2 (x)
  (* (f1 x) (f2 x)))

;; The key lemma is that when x1 is close to x2 and y1 is close to y2,
;; x1*y1 is close to x2*y2.  As before, we get this in two steps:

(defthm close-times
  (implies (and (i-close x1 x2)
		(i-limited y))
	   (i-close (* x1 y) (* x2 y)))
  :hints (("Goal" :in-theory (enable i-close))
	  ("Goal''" :use ((:instance small*limited->small
				     (x (- x1 x2))
				     (y y)))
	   :in-theory (disable small*limited->small))))

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
	   :in-theory (disable close-times i-close-transitive i-close-limited))))

;; And from that, the continuity of f1*f2 trivially follows:

(defthm f1*f2-continuous
  (implies (and (standard-numberp x)
		(realp x)
		(i-close x y)
		(realp y))
	   (i-close (f1*f2 x) (f1*f2 y)))
  :hints (("Goal" :in-theory (enable standards-are-limited))))

;; As before, we show that f1*f2 really is continuous, by instantiating
;; rcfn with f1*f2 in a proof:

(encapsulate
 nil
 (local (include-book "continuity"))

 (local
  (defthm f1*f2-uniformly-continuous
    (implies (and (i-limited x)
		  (realp x)
		  (i-close x y)
		  (realp y))
	     (i-close (f1*f2 x) (f1*f2 y)))
    :hints (("Goal"
	     :by (:functional-instance rcfn-uniformly-continuous
				       (rcfn f1*f2)))
	    ("Subgoal 3"
	     :in-theory (disable f1*f2))))))

