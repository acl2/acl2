(in-package "ACL2")

#|
 (defpkg "U" (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*))
 (certify-book "inverse-composition" 1)
|#

(include-book "nonstd/nsa/nsa" :dir :system)
(include-book "nonstd/nsa/inverse-monotone" :dir :system)
(include-book "arithmetic/top" :dir :system)
(include-book "composition-helpers")

(encapsulate
 (( inv-f (x) t)
  ( inv-f-prime (x) t)
  ( inv-f-domain-p (x) t)

  ( inv-f-inverse (y) t)
  ( inv-f-inverse-prime (y) t)
  ( inv-f-inverse-domain-p (x) t)
  )

 (local (defun inv-f (x) x))
 (local (defun inv-f-inverse (x) x))
 (local (defun inv-f-prime (x) (declare (ignore x)) 1))
 (local (defun inv-f-inverse-prime (x) (declare (ignore x)) 1))
 (local (defun inv-f-domain-p (x) (acl2-numberp x)))
 (local (defun inv-f-inverse-domain-p (x) (acl2-numberp x)))

#|
 (defthm inv-f-in-range
     (implies (inv-f-domain-p x)
	      (inv-f-inverse-domain-p (inv-f x))))
|#

 (defthm inv-f-inverse-in-range
     (implies (inv-f-inverse-domain-p x)
	      (inv-f-domain-p (inv-f-inverse x))))

 (defthm inv-f-domain-is-number
     (implies (inv-f-domain-p x)
	      (acl2-numberp x)))

#|
 (defthm inv-f-relation
     (implies (inv-f-domain-p x)
	      (equal (inv-f-inverse (inv-f x))
		     x)))
|#

 (defthm inv-f-inverse-relation
     (implies (inv-f-inverse-domain-p x)
	      (equal (inv-f (inv-f-inverse x))
		     x)))

 (defthm inv-f-d/dx-f-relation
     (implies (inv-f-inverse-domain-p x)
	      (equal (inv-f-inverse-prime x)
		     (/ (inv-f-prime (inv-f-inverse x))))))

 (derivative-hyps inv-f)

 (defthm inv-f-prime-not-zero
     (implies (inv-f-domain-p x)
	      (not (equal (inv-f-prime x) 0))))

 (defthm inv-f-preserves-not-close
     (implies (and (inv-f-domain-p x)
		   (inv-f-domain-p y)
		   (i-limited x)
		   (not (i-close x y)))
	      (not (i-close (inv-f x) (inv-f y)))))
 )

(local
 (defthm-std inv-f-inverse-standard-local
     (implies (standardp x)
	      (standardp (inv-f-inverse x)))))

(local
 (defthm-std inv-f-prime-standard-local
     (implies (standardp x)
	      (standardp (inv-f-prime x)))))

(local
 (defthm inv-f-inverse-continuous-local
     (implies (and (inv-f-inverse-domain-p x1)
		   (inv-f-inverse-domain-p x2)
		   (standardp x1)
		   (i-close x1 x2))
	      (i-close (inv-f-inverse x1)
		       (inv-f-inverse x2)))
   :hints (("Goal"
	    :use ((:instance inv-f-preserves-not-close
			     (x (inv-f-inverse x1))
			     (y (inv-f-inverse x2)))
		  (:instance inv-f-inverse-standard-local
			     (x x1))
		  (:instance inv-f-inverse-in-range
			     (x x1))
		  (:instance inv-f-inverse-in-range
			     (x x2))
		  (:instance inv-f-domain-is-number
			     (x (inv-f-inverse x1)))
		  )
	    :in-theory (disable inv-f-preserves-not-close
				inv-f-inverse-standard-local
				inv-f-inverse-in-range
				inv-f-domain-is-number
				)))))

(local
 (defthm inv-f-inverse-prime-not-small
     (implies (and (inv-f-domain-p x)
		   (standardp x))
	      (not (i-small (inv-f-prime x))))
   :hints (("Goal"
	    :use ((:instance inv-f-prime-not-zero)
		  (:instance standard-small-is-zero (x (inv-f-prime x)))
		  )
	    :in-theory (disable inv-f-prime-not-zero)
	    ))
   ))

(local
 (encapsulate
 nil
 (local
  (defthm close-/-lemma-1
    (implies (and (not (i-small x))
		  (i-close x y))
	     (equal (/ (standard-part x)) (/ (standard-part y))))
    :hints (("Goal" :in-theory (enable nsa-theory)))))

 (local
  (defthm close-/-lemma-2
    (implies (and (not (i-small x))
		  (i-close x y)
		  (i-limited x))
	     (equal (standard-part (/ x)) (standard-part (/ y))))
    :hints (("Goal"
	     :use ((:instance close-/-lemma-1)
		   (:instance standard-part-of-udivide
			      (x y)))))))

 (defthm close-/
   (implies (and (not (i-small x))
		 (i-close x y)
		 (i-limited x))
	    (i-close (/ x) (/ y)))
   :hints (("Goal"
	    :use (:instance close-/-lemma-2)
	    :in-theory (enable i-close i-small))))))

(local
 (defthm inv-f-inverse-prime-continuous-local
     (implies (and (inv-f-inverse-domain-p x)
		   (standardp x)
		   (inv-f-inverse-domain-p y)
		   (i-close x y))
	      (i-close (inv-f-inverse-prime x)
		       (inv-f-inverse-prime y)))
   :hints (("Goal"
	    :use ((:instance close-/
			     (x (inv-f-prime (inv-f-inverse x)))
			     (y (inv-f-prime (inv-f-inverse y))))
		  (:instance standards-are-limited
			     (x (inv-f-prime (inv-f-inverse x))))

		  )
	    :in-theory (disable close-/
				standards-are-limited
				))
	   )
   )
 )

(local
 (defthm convert-inverse-differentials-local
     (implies (and (inv-f-inverse-domain-p y1)
		   (inv-f-inverse-domain-p y2)
		   )
	      (equal (/ (- (inv-f-inverse y1) (inv-f-inverse y2))
			(- y1 y2))
		     (/ (- (inv-f-inverse y1) (inv-f-inverse y2))
			(- (inv-f (inv-f-inverse y1))
			   (inv-f (inv-f-inverse y2))))))
   :hints (("Goal"
	    :use ((:instance inv-f-inverse-relation (x y1))
		  (:instance inv-f-inverse-relation (x y2)))
	    :in-theory nil))
   :rule-classes nil))

(local
 (defthm inv-f-inverse-1-to-1
     (implies (and (inv-f-inverse-domain-p x)
		   (inv-f-inverse-domain-p y)
		   (equal (inv-f-inverse x)
			  (inv-f-inverse y)))
	      (equal x y))
   :hints (("Goal"
	    :use ((:instance inv-f-inverse-relation (x x))
		  (:instance inv-f-inverse-relation (x y)))
	    :in-theory (disable inv-f-inverse-relation)))
   :rule-classes nil))

(local
 (defthm inv-f-prime-not-large
     (implies (and (standardp x)
		   (inv-f-inverse-domain-p x))
	      (not (I-LARGE (INV-F-PRIME (INV-F-INVERSE X)))))
   :hints (("Goal"
	    :use ((:instance standards-are-limited
			     (x (inv-f-prime (inv-f-inverse x))))
		  )
	    :in-theory (disable standards-are-limited
				))
	   )   ))

(local
 (defthm inv-f-inverse-close-local
     (implies (and (inv-f-inverse-domain-p x)
		   (standardp x)
		   (inv-f-inverse-domain-p y)
		   (i-close x y)
		   (not (equal x y)))
	      (i-close (/ (- (inv-f-inverse x) (inv-f-inverse y))
			  (- x y))
		       (inv-f-inverse-prime x)))
   :hints (("Goal"
	    :use ((:instance convert-inverse-differentials-local (y1 x) (y2 y))
		  (:instance close-/
			     (x (inv-f-prime (inv-f-inverse x)))
			     (y (/ (- (inv-f (inv-f-inverse x))
				      (inv-f (inv-f-inverse y)))
				   (- (inv-f-inverse x) (inv-f-inverse y)))))
		  (:instance inv-f-close
			     (x (inv-f-inverse x))
			     (y (inv-f-inverse y)))
		  (:instance inv-f-inverse-1-to-1)
		  )
	    :in-theory (disable inv-f-inverse-relation
				close-/
				inv-f-close
				DISTRIBUTIVITY
				)
	    ))
   :rule-classes nil
   )
 )


(derivative-hyps
 inv-f-inverse
 :close-hints (("Goal" :use ((:instance inv-f-inverse-close-local))))
 )


; Basic steps here:
;  define functions to wrap the raw expresiions
;  show that the functions do indeed wrap the expressions
;  apply functional instantiation to those functions
;  unwrap the results, getting the theorems we need

; fnX, fnX-derivative, fnX-domain are expressions
(defun inv-d/dx-apply-fn
  (fn
   fn-derivative fn-domain fn-symbol
   inv-fn-domain inv-fn-symbol)

  (let* ((instantiation-fns `((inv-f (lambda (x) ,fn))
			      (inv-f-domain-p (lambda (x) ,fn-domain))
			      (inv-f-prime (lambda (x) ,fn-derivative))
			      (inv-f-inverse (lambda (x) (,inv-fn-symbol x)))
			      (inv-f-inverse-domain-p (lambda (x) ,inv-fn-domain))
			      (inv-f-inverse-prime
			       (lambda (x)
				 (/ ((lambda (x)
				       ,fn-derivative)
				     (,inv-fn-symbol x))))))))


  `( (encapsulate
        nil

        (local
         (in-theory '(,@(deriv-symbols (first fn))
		      ,@(inverse-symbols (first fn))
		      )))

	,@(use-deriv-unary fn-symbol 'inv-f-inverse
		   `(,inv-fn-symbol x)
		   `(/ ((lambda (x) ,fn-derivative) (,inv-fn-symbol x)))
		   inv-fn-domain
		   instantiation-fns)

        )
       (/ ((lambda (x) ,fn-derivative) (,inv-fn-symbol x))) ; compound derivative
       ,inv-fn-domain                   ; compound domain

       )

    ))


;(inv-d/dx-apply-fn '(sqr x) '(sqr-prime x) '(sqr-domain-p x) 'sqr '(sqr-inverse-domain-p x) 'sqr-inverse)
