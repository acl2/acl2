(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(include-book "nsa")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

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

(defun f1*f2 (x)
  (* (f1 x) (f2 x)))

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

(defthm f1*f2-continuous
  (implies (and (standard-numberp x)
		(realp x)
		(i-close x y)
		(realp y))
	   (i-close (f1*f2 x) (f1*f2 y)))
  :hints (("Goal" :in-theory (enable standards-are-limited)))
  )
