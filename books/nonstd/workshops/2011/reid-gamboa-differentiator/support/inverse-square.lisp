(in-package "ACL2")

#|
 (defpkg "U" (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*))
 (certify-book "inverse-square" 1)
|#


(include-book "nonstd/nsa/inverse-square" :dir :system)
(include-book "differentiator")

(defun sqr (x)
  (* x x))

(local
 (defthm sqr-square
     (implies (realp x)
	      (equal (sqr x)
		     (square x)))))

(defun sqr-prime (x)
  (* 2 x))

(defun sqr-domain-p (x)
  (and (realp x)
       (< 0 x)))

(defun sqr-inverse (x)
  (square-inverse x))

(defun sqr-inverse-prime (x)
  (/ (* 2 (sqr-inverse x))))

(defun sqr-inverse-domain-p (x)
  (and (realp x)
       (< 0 x)))

(local
 (defthm sqr-square-domain
     (implies (and (realp x) (< 0 x))
	      (inside-interval-p x (interval 0 nil)))
   :hints (("Goal"
	    :in-theory (enable inside-interval-p)))))

(local
 (defthm sqr-inverse-zero
     (implies (and (sqr-inverse-domain-p x)
		   (equal (sqr-inverse x) 0))
	      (equal x 0))
   :hints (("Goal" :use ((:instance square-inverse-exists
			  (y x))
			 (:instance (:theorem (implies (equal x 0) (equal (square x) 0)))
				    (x (square-inverse x))))
		   :in-theory (disable square-inverse-exists
				       square-inverse-unique
				       square-inverse->sqrt)
			 ))
   :rule-classes nil))

(defthm sqr-inverse-in-range
    (implies (sqr-inverse-domain-p x)
	     (sqr-domain-p (sqr-inverse x))))

(defthm sqr-domain-is-number
    (implies (sqr-domain-p x)
	     (acl2-numberp x)))

(defthm sqr-inverse-relation
    (implies (sqr-inverse-domain-p x)
	     (equal (sqr (sqr-inverse x))
		    x)))

(defthm sqr-d/dx-f-relation
    (implies (sqr-inverse-domain-p x)
	     (equal (sqr-inverse-prime x)
		    (/ (sqr-prime (sqr-inverse x))))))

(defthm sqr-prime-not-zero
     (implies (sqr-domain-p x)
	      (not (equal (sqr-prime x) 0))))

(local
 (defthm inside-interval-non-negative
     (implies (inside-interval-p x (interval 0 nil))
	      (<= 0 x))
   :hints (("Goal"
	    :in-theory (enable inside-interval-p)))))


(local
 (defthm square-lemma-4
     (IMPLIES (AND (realp x1)
		   (realp x2)
		   (<= 0 x1)
		   (< x1 x2))
	      (< (* X1 X1) (* X2 X2)))
   :hints (("Goal"
	    :cases ((< 0 x1))))))

(local
 (defthm square-lemma-6
     (IMPLIES (AND (inside-interval-p x1 (interval 0 nil))
		   (inside-interval-p x2 (interval 0 nil))
		   (equal (* X1 X1) (* X2 X2)))
	      (equal x1 x2))
   :hints (("Goal"
	    :use ((:instance square-lemma-4
			     (x1 x1)
			     (x2 x2))
		  (:instance square-lemma-4
			     (x1 x2)
			     (x2 x1)))
	    :in-theory (disable square-lemma-4)))
   :rule-classes (:built-in-clause)))

(local
 (defthm square-lemma-7
     (IMPLIES (INSIDE-INTERVAL-P X (INTERVAL 0 NIL))
         (INSIDE-INTERVAL-P (* X X)
                            (INTERVAL 0 NIL)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:built-in-clause)))

(local
 (defthm trivial-subinterval
     (SUBINTERVAL-P (INTERVAL 0 1)
		    (INTERVAL 0 NIL))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:built-in-clause)))


(defthm sqr-preserves-not-close
    (implies (and (sqr-domain-p x)
		  (sqr-domain-p y)
		  (i-limited x)
		  (not (i-close x y)))
	     (not (i-close (sqr x) (sqr y))))
  :hints (("Goal"
	   :use ((:instance
		  (:functional-instance icfn-preserves-not-close
					(icfn square)
					(icfn-inv-interval square-interval)
					(icfn-domain (lambda () (interval 0 nil)))
					(icfn-range (lambda () (interval 0 nil))))
		  (a x)
		  (b y)))
	   ))
  )

(encapsulate
 nil

 (local (defderivative sqr-deriv-local (sqr x)))

 (local
  (defthm close-2x
      (implies (and (acl2-numberp x)
		    (acl2-numberp y)
		    (i-close x y))
	       (i-close (* 2 x) (* 2 y)))
    :hints (("Goal"
	     :use ((:instance limited*small->small (x 2) (y (- x y))))
	     :in-theory (enable-disable (i-close) (limited*small->small))))
    ))

 (local
  (defthm twice-x
      (implies (realp x)
	       (equal (+ x x) (* 2 x)))))

 (derivative-hyps sqr
		  :close-hints (("Goal" :use ((:instance sqr-deriv-local)) :in-theory (disable sqr sqr-deriv-local))))
 )

(def-elem-derivative sqr sqr (sqr-domain-p x) (sqr-prime x))

(def-elem-inverse sqr-inverse sqr-inverse (sqr-domain-p x) (sqr-inverse-domain-p x) sqr)

(defderivative sqr-inverse-deriv-local (sqr-inverse x))

(in-theory (disable sqr square-inverse->sqrt))

(local
 (defthm-std sqr-inverse-standard-local
     (IMPLIES (AND (STANDARDP X) (REALP X) (< 0 X))
         (STANDARDP (SQUARE-INVERSE X)))))

(derivative-hyps sqr-inverse
		 :continuous-hints (("Goal"
				     :use ((:instance sqr-inverse-deriv-local-dirty-inverse-continuous))
				     ))
		 :prime-continuous-hints (("Goal"
					   :use ((:instance sqr-inverse-deriv-local-dirty-inverse-prime-continuous))
					   ))
		 :close-hints (("Goal" :use ((:instance sqr-inverse-deriv-local))
					:in-theory (disable sqr sqr-inverse-deriv-local))))
