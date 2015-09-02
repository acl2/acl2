#|

This is the flip-side of exercise4.lisp; it finds the minimum point of
a continuous function in a closed interval.  The idea is simply to
consider the function g(x) = -f(x) and find the maximum of g.

|#

(in-package "ACL2")

(include-book "exercise4")

;; A continuous function also achieves its minimum.  To show that, we
;; start with the follogin function, which is similar to the "max-x-n"
;; function defined in exercise4.lisp.  Sadly ACL2 does not do this
;; sort of thing by itself.

(defun find-min-rcfn-x-n (a min-x i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (< (rcfn (+ a (* i eps))) (rcfn min-x))
	  (find-min-rcfn-x-n a (+ a (* i eps)) (1+ i) n eps)
	(find-min-rcfn-x-n a min-x (1+ i) n eps))
    min-x))

;; The key lemma -- if -x is close to -y, then x is close to y.  This
;; is also proved in exercise2.lisp, where it serves the same purpose.

(defthm close-uminus
  (implies (and (acl2-numberp x)
		(acl2-numberp y))
	   (equal (i-close (- x) (- y))
		  (i-close x y)))
  :hints (("Goal"
	   :use ((:instance i-small-uminus (x (+ x (- y)))))
	   :in-theory (enable i-close i-small-uminus))))

;; We have to prove that this function is limited.  Luckily, we can
;; just reuse the theorem about max-n being limited.

(defthm find-min-rcfn-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-min-rcfn-x-n a a
				    0 (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b)))))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x-n-limited
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       ))
	   :in-theory (disable find-max-rcfn-x-n-limited))))

;; That justifies the definition of min-x.

(defun-std find-min-rcfn-x (a b)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-min-rcfn-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))))
    0))

;; Now, to see that this function really returns a minimum, we just
;; have to instantiate the appropriate theorem about maximums.

(defthm find-min-rcfn-is-minimum
  (implies (and (realp a)
		(realp b)
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rcfn (find-min-rcfn-x a b)) (rcfn x)))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-is-maximum
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       (find-max-rcfn-x find-min-rcfn-x)))
	   :in-theory (disable find-max-rcfn-is-maximum))))

;; Similarly, we want to show that a <= min-x -- just instantiate the
;; theorem about maximum!

(defthm find-min-rcfn-x->=-a
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= a (find-min-rcfn-x a b)))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x->=-a
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       (find-max-rcfn-x find-min-rcfn-x)))
	   :in-theory (disable find-max-rcfn-x->=-a))))

;; And finally,, we want to show that min-x <= b -- again, just
;; instantiate the theorem about maximum!

(defthm find-min-rcfn-x-<=-b
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= (find-min-rcfn-x a b) b))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x-<=-b
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       (find-max-rcfn-x find-min-rcfn-x)))
	   :in-theory (disable find-max-rcfn-x-<=-b))))
