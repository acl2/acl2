;;; Contributed by Ruben A. Gamboa

(in-package "ACL2")

;;; The absolute-value function has many useful properties, but ACL2
;;; doesn't know about them.  Instead, it likes to explode abs(x) into
;;; the two cases x<0 and x>=0, and that often leads to unnecessary
;;; case explosions.  In this book, we prove the more useful lemmas
;;; about abs.

(include-book "top")

;;; We start with |x*y| = |x| * |y|.  This is actually a dangerous
;;; lemma, sometimes, so we often disable it.

(defthm abs-*
  (implies (and (real/rationalp x) (real/rationalp y))
	   (equal (abs (* x y))
		  (* (abs x) (abs y)))))

;;; An obvious lemma that ACL2 doesn't know is that |-x| = |x|.

(defthm abs-uminus
  (equal (abs (- x))
	 (abs (fix x))))

;;; And |x| is always real, so long as x is real (which is should be
;;; from the guards).

(defthm realp-abs
  (implies (real/rationalp x)
	   (real/rationalp (abs x))))

;;; Similarly, abs is always numeric.

(defthm numberp-abs
  (implies (acl2-numberp x)
	   (acl2-numberp (abs x))))

;;; |x| = x when x is a non-negative real.

(defthm abs-x->-0
  (implies (and (real/rationalp x)
		(<= 0 x))
	   (equal (abs x) x)))

;;; If x is real and non-zero, then |x| is positive.

(defthm abs-x-=-0-iff-x=0
  (implies (and (real/rationalp x)
		(not (= 0 x)))
	   (< 0 (abs x))))

;;; And no matter what, |x|>=0.

(defthm not-abs-x-<-0
  (not (< (abs x) 0))
  :rule-classes (:rewrite :type-prescription))

;;; When you see a term |x| in an expression and you want to replace
;;; it with a new variable x1, keep in mind that x1>=0.

(defthm abs-x-generalize-weak
  (implies (real/rationalp x)
	   (and (<= 0 (abs x))
		(real/rationalp (abs x))))
  :rule-classes (:generalize :rewrite))

;;; Moreover, if you know x is non-zero, when you generalize |x| with
;;; x1, you can assume that x1>0.

(defthm abs-x-generalize-strong
  (implies (and (real/rationalp x)
		(not (equal x 0)))
	   (< 0 (abs x)))
  :rule-classes (:generalize :rewrite))

;;; |x+y| <= |x| + |y|.

(defthm abs-triangle
  (<= (abs (+ x y)) (+ (abs x) (abs y))))

(in-theory (disable abs))
