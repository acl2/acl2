#|

We use the intermediate value theorem to show the existence of some x
so that x*x=2.  From the results in exercise1, we know that this x must
be a real irrational number.

|#

(in-package "ACL2")

(include-book "continuity")

;; First, we define the function f(x) = x*x:

(defun square (x)
  (* x x))

;; The main part of the proof is to show that x*x is continuous.
;; According to the constraints for rcfn, we need to prove the
;; following three theorems:

;; rcfn-standard:

(defthm square-standard
  (implies (standard-numberp x)
	   (standard-numberp (square x)))
  :rule-classes (:rewrite :type-prescription))

;; rcfn-real:

(defthm square-real
  (implies (realp x)
	   (realp (square x)))
  :rule-classes (:rewrite :type-prescription))

;; rcfn-continuous

(encapsulate
 ()

 ;; We need to show that x*x is close to y*y when x is close to y.
 ;; It's actually easier to think in terms of small instead of close.
 ;; Specifically, if x-y is small, then x*x - y*y is also small, since
 ;; it's equal to (x+y)*(x-y), the product of a small and a limited
 ;; number (note that x+y is limited, since x is standard and y is
 ;; close to x).

 (local (in-theory (enable i-close)))

 (local
  (defthm lemma-1
    (implies (and (i-limited x)
		  (realp x)
		  (i-small (+ x (- y)))
		  (realp y))
	     (i-limited (+ x y)))
    :hints (("Goal"
	     :use ((:instance i-close-large-2)
		   (:instance i-limited-plus))
	     :in-theory (disable i-limited-plus i-close-large)))))

 (local
  (defthm lemma-2
    (implies (and (standard-numberp x)
		  (realp x)
		  (i-close x y)
		  (realp y))
	     (i-small (* (+ x y) (+ x (- y)))))
    :hints (("Goal"
	     :in-theory (disable distributivity)))))

 (defthm square-continuous
   (implies (and (standard-numberp x)
		 (realp x)
		 (i-close x y)
		 (realp y))
	    (i-close (square x) (square y)))
   :hints (("Goal"
	    :use ((:instance lemma-2))
	    :in-theory (disable lemma-2)))))

;; Now, we have to find the root.  Again we wish for a more automatic
;; way of doing this.

(in-theory (disable square))

(defun find-zero-n-square (a z i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (realp a)
	   (integerp i)
	   (integerp n)
	   (< i n)
	   (realp eps)
	   (< 0 eps)
	   (< (square (+ a eps)) z))
      (find-zero-n-square (+ a eps) z (1+ i) n eps)
    (realfix a)))

;; We prove that this function returns a limited number for limited
;; arguments.

(defthm limited-find-zero-square-body
  (implies (and (i-limited a)
		(i-limited b)
		(realp b)
		(realp z))
	   (i-limited (find-zero-n-square a
					  z
					  0
					  (i-large-integer)
					  (+ (- (* (/ (i-large-integer)) a))
					     (* (/ (i-large-integer)) b)))))
  :hints (("Goal"
	   :by (:functional-instance
		 limited-find-zero-body
		 (rcfn square)
		 (find-zero-n find-zero-n-square))
	   :in-theory (disable limited-find-zero-body))))

;; We define the root we want in the range [a,b)

(defun-std find-zero-square (a b z)
  (if (and (realp a)
	   (realp b)
	   (realp z)
	   (< a b))
      (standard-part
       (find-zero-n-square a
			   z
			   0
			   (i-large-integer)
			   (/ (- b a) (i-large-integer))))
    0))

;; And now, we  can invoke the intermediate-value theorem  to find the
;; number x so that x*x=2.

(defthm existence-of-sqrt-2
  (equal (square (find-zero-square 0 2 2)) 2)
  :hints (("Goal"
	   :use ((:instance
		  (:functional-instance intermediate-value-theorem
					(rcfn square)
					(find-zero find-zero-square)
					(find-zero-n find-zero-n-square))
		  (a 0)
		  (b 2)
		  (z 2)))
	   :in-theory (disable intermediate-value-theorem))))

