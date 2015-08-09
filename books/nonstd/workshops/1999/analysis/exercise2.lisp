#|

This book uses the "increasing" version of the intermediate value
theorem to prove a "decreasing" version (i.e., when f(a) > f(b)).
The basic idea is to consider the "increasing" version for the
function g(x)=-f(x).

|#

(in-package "ACL2")

(include-book "continuity")

;; First, we find the root.  It would be nice if we could define this
;; using something akin to a :functional-instance (:lambda-instance,
;; anyone?)

(defun find-zero-n-2 (a z i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (realp a)
	   (integerp i)
	   (integerp n)
	   (< i n)
	   (realp eps)
	   (< 0 eps)
	   (< z (rcfn (+ a eps))))
      (find-zero-n-2 (+ a eps) z (1+ i) n eps)
    (realfix a)))

;; The key lemma -- if -x is close to -y, then x is close to y.

(defthm close-uminus
  (implies (and (acl2-numberp x)
		(acl2-numberp y))
	   (equal (i-close (- x) (- y))
		  (i-close x y)))
  :hints (("Goal"
	   :use ((:instance i-small-uminus (x (+ x (- y)))))
	   :in-theory (enable i-close i-small-uminus))))

;; We prove that this function returns a limited number for limited
;; arguments.

(defthm limited-find-zero-2-body
  (implies (and (i-limited a)
		(i-limited b)
		(realp b)
		(realp z))
	   (i-limited (find-zero-n-2 a
				     z
				     0
				     (i-large-integer)
				     (+ (- (* (/ (i-large-integer)) a))
					(* (/ (i-large-integer)) b)))))
   :hints (("Goal"
	    :use ((:instance
		   (:functional-instance
		    limited-find-zero-body
		    (rcfn (lambda (x) (- (rcfn x))))
		    (find-zero-n (lambda (a z i n
					    eps)
				   (find-zero-n-2
				    a (- z) i n eps))))
		   (z (- z))))
	    :in-theory (disable limited-find-zero-body))))

;; We define the root we want in the range [a,b)

(defun-std find-zero-2 (a b z)
  (if (and (realp a)
	   (realp b)
	   (realp z)
	   (< a b))
      (standard-part
       (find-zero-n-2 a
		      z
		      0
		      (i-large-integer)
		      (/ (- b a) (i-large-integer))))
    0))

;; And here is the second version of the intermediate value theorem.

(local
 (defthm standardp-minus-z
   (implies (and (realp z)
                 (standardp z))
            (standardp (- z)))
   :rule-classes (:type-prescription :forward-chaining)))

(local
 (defthmd definition-of-find-zero-2-lemma
   (implies (and (standardp a)
                 (standardp b)
                 (standardp z))
            (equal (find-zero-2 a b z)
                   (if (and (realp a)
                            (realp b)
                            (realp z)
                            (< a b))
                       (standard-part
                        (find-zero-n-2 a
                                       z
                                       0
                                       (i-large-integer)
                                       (/ (- b a) (i-large-integer))))
                     0)))))

(local
 (defthmd definition-of-find-zero-2-uminus-z
   (implies (and (standardp a)
                 (standardp b)
                 (standardp z))
            (equal (find-zero-2 a b (- z))
                   (if (and (realp a)
                            (realp b)
                            (realp (- z))
                            (< a b))
                       (standard-part
                        (find-zero-n-2 a
                                       (- z)
                                       0
                                       (i-large-integer)
                                       (/ (- b a) (i-large-integer))))
                     0)))
   :hints (("Goal"
            :use ((:instance definition-of-find-zero-2-lemma
                             (z (- z))))))
   ))

(defthm intermediate-value-theorem-2
  (implies (and (realp a)
		(realp b)
		(realp z)
		(< a b)
		(< z (rcfn a))
		(< (rcfn b) z))
	   (and (realp (find-zero-2 a b z))
		(< a (find-zero-2 a b z))
		(< (find-zero-2 a b z) b)
		(equal (rcfn (find-zero-2 a b z))
		       z)))
  :hints (("Goal"
	   :use ((:instance
		  (:functional-instance
		   intermediate-value-theorem
		   (rcfn (lambda (x) (- (rcfn x))))
		   (find-zero (lambda (a b z)
				(find-zero-2 a b
					     (if (realp z) (- z) z))))
		   (find-zero-n (lambda (a z i n
					   eps)
				  (find-zero-n-2
				   a (- z) i n eps))))
		  (z (if (realp z) (- z) z))
		  ))
	   :in-theory
	   (disable intermediate-value-theorem))
           ))
