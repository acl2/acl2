(in-package "ACL2")

#|
 (defpkg "U" (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*))
 (certify-book "inverse-monotone" 1)
|#

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "continuity")
(include-book "intervals")
(include-book "inverses")
(include-book "data-structures/utilities" :dir :system)

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(encapsulate
 ((icfn (x) t)
  (icfn-domain () t)
  (icfn-range () t)
  (icfn-inv-interval (y) t))

 (local (defun icfn (x) (realfix x)))
 (local (defun icfn-domain () (interval nil nil)))
 (local (defun icfn-range () (interval nil nil)))
 (local (defun icfn-inv-interval (y) (interval y y)))

 ; The intervals are really intervals

 (defthm domain-is-an-interval
     (interval-p (icfn-domain))
   :rule-classes (:rewrite :type-prescription))

 (defthm range-is-an-interval
     (interval-p (icfn-range))
   :rule-classes (:rewrite :type-prescription)
   )

 ;; The intervals are non-trivial

 (defthm icfn-domain-non-trivial
     (or (null (interval-left-endpoint (icfn-domain)))
	 (null (interval-right-endpoint (icfn-domain)))
	 (< (interval-left-endpoint (icfn-domain))
	    (interval-right-endpoint (icfn-domain))))
   :rule-classes nil)

 (defthm icfn-range-non-trivial
     (or (null (interval-left-endpoint (icfn-range)))
	 (null (interval-right-endpoint (icfn-range)))
	 (< (interval-left-endpoint (icfn-range))
	    (interval-right-endpoint (icfn-range))))
   :rule-classes nil)

 ; The function value is in the range when the input is in the domain

 (defthm icfn-in-range
     (implies (inside-interval-p x (icfn-domain))
	      (inside-interval-p (icfn x) (icfn-range))))

 ; Regardless of the input, the function is real

 (defthm icfn-real
     (realp (icfn x))
   :rule-classes (:rewrite :type-prescription))

 ; We restrict ourselves to increasing functions

 (defthm icfn-is-1-to-1
     (implies (and (inside-interval-p x1 (icfn-domain))
		   (inside-interval-p x2 (icfn-domain))
		   (equal (icfn x1) (icfn x2)))
	      (equal x1 x2))
   :rule-classes nil)

 ; The function inv-interval takes y and return a pair of x1 <= x2 such that icfn(x1) <= y <= icfn(x2)
 ; or icfn(y1) >= y >= icfn(x2).  That is, they find a bounded, closed interval that contains the
 ; inverse of y

 (defthm icfn-inv-interval-correctness
     (implies (inside-interval-p y (icfn-range))
	      (let* ((estimate (icfn-inv-interval y))
		     (x1 (interval-left-endpoint estimate))
		     (x2 (interval-right-endpoint estimate)))
		(and (interval-p estimate)
		     (subinterval-p estimate (icfn-domain))
		     (interval-left-inclusive-p estimate)
		     (interval-right-inclusive-p estimate)
		     (or (and (<= (icfn x1) y)
			      (<= y (icfn x2)))
			 (and (>= (icfn x1) y)
			      (>= y (icfn x2)))))))
   :rule-classes nil)

 ; The function is continuous over its range

 (defthm icfn-continuous
     (implies (and (standardp x1)
		   (inside-interval-p x1 (icfn-domain))
		   (i-close x1 x2)
		   (inside-interval-p x2 (icfn-domain)))
	      (i-close (icfn x1) (icfn x2))))
 )

(local
 (defun find-zero-increasing-n (a z i n eps)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (realp a)
	    (integerp i)
	    (integerp n)
	    (< i n)
	    (realp eps)
	    (< 0 eps)
	    (< (icfn (+ a eps)) z))
       (find-zero-increasing-n (+ a eps) z (1+ i) n eps)
       (realfix a))))

(local
 (defthm limited-find-zero-increasing-body
     (implies (and (i-limited a)
		   (i-limited b)
		   (realp b)
		   (realp z)
		   )
	      (i-limited (find-zero-increasing-n a
						 z
						 0
						 (i-large-integer)
						 (+ (- (* (/ (i-large-integer)) a))
						    (* (/ (i-large-integer)) b)))))
   :hints (("Goal"
	    :use ((:functional-instance limited-find-zero-body
					(rcfn icfn)
					(rcfn-domain icfn-domain)
					(find-zero-n find-zero-increasing-n)))
	    :in-theory (disable limited-find-zero-body))
	   ("Subgoal 2"
	    :use ((:instance icfn-domain-non-trivial)))
	   ("Subgoal 1"
	    :use ((:instance icfn-range-non-trivial)))
	   )))

(local
 (defun-std find-zero-increasing (a b z)
   (if (and (realp a)
	    (realp b)
	    (realp z)
	    (< a b))
       (standard-part
	(find-zero-increasing-n a
				z
				0
				(i-large-integer)
				(/ (- b a) (i-large-integer))))
       0)))

(local
 (defun find-zero-decreasing-n (a z i n eps)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (realp a)
	    (integerp i)
	    (integerp n)
	    (< i n)
	    (realp eps)
	    (< 0 eps)
	    (< z (icfn (+ a eps))))
       (find-zero-decreasing-n (+ a eps) z (1+ i) n eps)
       (realfix a))))


(local
 (defthm limited-find-zero-decreasing-body
     (implies (and (i-limited a)
		   (i-limited b)
		   (realp b)
		   (realp z)
		   )
	      (i-limited (find-zero-decreasing-n a
						 z
						 0
						 (i-large-integer)
						 (+ (- (* (/ (i-large-integer)) a))
						    (* (/ (i-large-integer)) b)))))
   :hints (("Goal"
	    :use ((:functional-instance limited-find-zero-2-body
					(rcfn icfn)
					(rcfn-domain icfn-domain)
					(find-zero-n-2 find-zero-decreasing-n)))
	    :in-theory (disable limited-find-zero-2-body)))))

(local
 (defun-std find-zero-decreasing (a b z)
   (if (and (realp a)
	    (realp b)
	    (realp z)
	    (< a b))
       (standard-part
	(find-zero-decreasing-n a
				z
				0
				(i-large-integer)
				(/ (- b a) (i-large-integer))))
       0)))



(local
 (defun inverse-witness (y)
   (if (equal (icfn (interval-left-endpoint (icfn-inv-interval y)))
	      y)
       (interval-left-endpoint (icfn-inv-interval y))
       (if (equal (icfn (interval-right-endpoint (icfn-inv-interval y)))
		  y)
	   (interval-right-endpoint (icfn-inv-interval y))
	   (if (<= (icfn (interval-left-endpoint (icfn-inv-interval y)))
		   (icfn (interval-right-endpoint (icfn-inv-interval y))))
	       (find-zero-increasing (interval-left-endpoint (icfn-inv-interval y))
				     (interval-right-endpoint (icfn-inv-interval y)) y)
	       (find-zero-decreasing (interval-left-endpoint (icfn-inv-interval y))
				     (interval-right-endpoint (icfn-inv-interval y)) y))))))

(local
 (defthm inverse-witness-is-inverse
     (implies (inside-interval-p y (icfn-range))
	      (and (inside-interval-p (inverse-witness y) (icfn-domain))
		   (equal (icfn (inverse-witness y)) y)))
   :hints (("Goal"
	    :use ((:instance
		   (:functional-instance intermediate-value-theorem
					 (rcfn icfn)
					 (rcfn-domain icfn-domain)
					 (find-zero find-zero-increasing)
                                         (find-zero-n find-zero-increasing-n)
                                         )
		   (a (interval-left-endpoint (icfn-inv-interval y)))
		   (b (interval-right-endpoint (icfn-inv-interval y)))
		   (z y))
		  (:instance
		   (:functional-instance intermediate-value-theorem-2
					 (rcfn icfn)
					 (rcfn-domain icfn-domain)
					 (find-zero-2 find-zero-decreasing)
                                         (find-zero-n-2 find-zero-decreasing-n))
		   (a (interval-left-endpoint (icfn-inv-interval y)))
		   (b (interval-right-endpoint (icfn-inv-interval y)))
		   (z y))
		  (:instance icfn-inv-interval-correctness (y y))
		  (:instance inside-interval-p-squeeze
			     (a (interval-left-endpoint (icfn-inv-interval y)))
			     (b (interval-right-endpoint (icfn-inv-interval y)))
			     (c (find-zero-decreasing (interval-left-endpoint (icfn-inv-interval y))
						      (interval-right-endpoint (icfn-inv-interval y))
						      y))
			     (interval (icfn-domain)))
		  (:instance inside-interval-p-squeeze
			     (a (interval-left-endpoint (icfn-inv-interval y)))
			     (b (interval-right-endpoint (icfn-inv-interval y)))
			     (c (find-zero-increasing (interval-left-endpoint (icfn-inv-interval y))
						      (interval-right-endpoint (icfn-inv-interval y))
						      y))
			     (interval (icfn-domain)))
		  )
	    :in-theory (disable intermediate-value-theorem intermediate-value-theorem-2 ;icfn-inv-interval-correctness
				inside-interval-p-squeeze)
	    )
	   )))



(local
 (defun-sk icfn-is-onto-predicate (y)
   (exists (x)
	   (and (inside-interval-p x (icfn-domain))
		(equal (icfn x) y)))))


(local
 (defthm icfn-is-onto
     (implies (inside-interval-p y (icfn-range))
	      (icfn-is-onto-predicate y))
   :hints (("Goal"
	    :use ((:instance icfn-is-onto-predicate-suff (x (inverse-witness y)) (y y))
		  (:instance inverse-witness-is-inverse))
	    :in-theory (disable inverse-witness-is-inverse)))))

(defchoose icfn-inverse (x) (y)
  (if (inside-interval-p y (icfn-range))
      (and (inside-interval-p x (icfn-domain))
	   (equal (icfn x) y))
      (realp x)))

(defthm icfn-inverse-exists
    (implies (inside-interval-p y (icfn-range))
	     (and (inside-interval-p (icfn-inverse y) (icfn-domain))
		  (equal (icfn (icfn-inverse y)) y)))
  :hints (("Goal"
	   :by (:instance
		(:functional-instance ifn-inverse-exists
				      (ifn icfn)
				      (ifn-is-onto-predicate icfn-is-onto-predicate)
				      (ifn-is-onto-predicate-witness icfn-is-onto-predicate-witness)
				      (ifn-inverse icfn-inverse)
				      (ifn-domain-p (lambda (x) (inside-interval-p x (icfn-domain))))
				      (ifn-range-p  (lambda (y) (inside-interval-p y (icfn-range)))))))
	  ("Subgoal 5"
	   :use ((:instance icfn-is-1-to-1)))
	  ("Subgoal 1"
	   :cases ((inside-interval-p y (icfn-range))))
	  ("Subgoal 1.2"
	   :use ((:instance icfn-inverse
			    (x 0)
			    (y y))))
	  ("Subgoal 1.1"
	   :use ((:instance inverse-witness-is-inverse)
		 (:instance icfn-inverse
			    (x (inverse-witness y))))
	   :in-theory (disable inverse-witness-is-inverse ))))


(defthm icfn-inverse-is-real
    (realp (icfn-inverse y))
  :hints (("Goal"
	   :by (:instance
		(:functional-instance ifn-inverse-is-real
				      (ifn icfn)
				      (ifn-is-onto-predicate icfn-is-onto-predicate)
				      (ifn-is-onto-predicate-witness icfn-is-onto-predicate-witness)
				      (ifn-inverse icfn-inverse)
				      (ifn-domain-p (lambda (x) (inside-interval-p x (icfn-domain))))
				      (ifn-range-p  (lambda (y) (inside-interval-p y (icfn-range))))))))
    :rule-classes (:rewrite :type-prescription))


(defthm icfn-inverse-unique
    (implies (and (inside-interval-p y (icfn-range))
		  (inside-interval-p x (icfn-domain))
		  (equal (icfn x) y))
	     (equal (icfn-inverse y) x))
  :hints (("Goal"
	   :by (:instance
		(:functional-instance ifn-inverse-unique
				      (ifn icfn)
				      (ifn-is-onto-predicate icfn-is-onto-predicate)
				      (ifn-is-onto-predicate-witness icfn-is-onto-predicate-witness)
				      (ifn-inverse icfn-inverse)
				      (ifn-domain-p (lambda (x) (inside-interval-p x (icfn-domain))))
				      (ifn-range-p  (lambda (y) (inside-interval-p y (icfn-range)))))))))

(defthm icfn-inverse-inverse-exists
    (implies (inside-interval-p x (icfn-domain))
	     (equal (icfn-inverse (icfn x)) x))
  :hints (("Goal"
	   :by (:instance
		(:functional-instance ifn-inverse-inverse-exists
				      (ifn icfn)
				      (ifn-is-onto-predicate icfn-is-onto-predicate)
				      (ifn-is-onto-predicate-witness icfn-is-onto-predicate-witness)
				      (ifn-inverse icfn-inverse)
				      (ifn-domain-p (lambda (x) (inside-interval-p x (icfn-domain))))
				      (ifn-range-p  (lambda (y) (inside-interval-p y (icfn-range)))))))))


(defthm icfn-inverse-is-1-to-1
    (implies (and (inside-interval-p y1 (icfn-range))
		  (inside-interval-p y2 (icfn-range))
		  (equal (icfn-inverse y1)
			 (icfn-inverse y2)))
	     (equal y1 y2))
  :hints (("Goal"
	   :by (:instance
		(:functional-instance ifn-inverse-is-1-to-1
				      (ifn icfn)
				      (ifn-is-onto-predicate icfn-is-onto-predicate)
				      (ifn-is-onto-predicate-witness icfn-is-onto-predicate-witness)
				      (ifn-inverse icfn-inverse)
				      (ifn-domain-p (lambda (x) (inside-interval-p x (icfn-domain))))
				      (ifn-range-p  (lambda (y) (inside-interval-p y (icfn-range))))))))
  :rule-classes nil)

;; Now we prove some useful properties of icfn itself.....

;; To start with, icfn reall is a monotone function.  If it isn't, we can find points A, B, C with idfn(B) bigger (or smaller)
;; than both idfn(A) and idfn(C).  But then we use the IVT to find a point in (A,B) with the same value as idfn(C) -- or a point
;; in (B,C) with the same value as idfn(A).  Either way, that violates the 1-1ness of idfn.

(defun-sk icfn-exists-intermediate-point (a b z)
  (exists (x)
	  (and (realp x)
	       (< a x)
	       (< x b)
	       (equal (icfn x) z))))

(defthm icfn-intermediate-value-theorem-sk
    (implies (and (inside-interval-p a (icfn-domain))
		  (inside-interval-p b (icfn-domain))
		  (realp z)
		  (< a b)
		  (or (and (< (icfn a) z) (< z (icfn b)))
		      (and (< z (icfn a)) (< (icfn b) z))))
	      (icfn-exists-intermediate-point a b z))
  :hints (("Goal"
; Hint modified just before v3-5 release by Matt K. for fallout from
; "subversive" soundness fix.
	   :use ((:functional-instance intermediate-value-theorem-sk
				       (rcfn icfn)
				       (rcfn-domain icfn-domain)
				       (exists-intermediate-point icfn-exists-intermediate-point)
				       (exists-intermediate-point-witness icfn-exists-intermediate-point-witness))
                 (:instance icfn-exists-intermediate-point-suff)
                 (:instance icfn-exists-intermediate-point)
                 (:instance icfn-exists-intermediate-point)
                 )))
  )

(encapsulate
 nil

 (local
  (defthm lemma-1a
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (inside-interval-p c (icfn-domain))
		    (< a b)
		    (< b c)
		    (< (icfn a) (icfn b))
		    (<= (icfn a) (icfn c)))
	       (< (icfn b) (icfn c)))
    :hints (("Goal"
	     :use ((:instance icfn-intermediate-value-theorem-sk
			      (a a)
			      (b b)
			      (z (icfn c)))
		   (:instance icfn-is-1-to-1
			      (x1 c)
			      (x2 (icfn-exists-intermediate-point-witness a b (icfn c))))
		   (:instance icfn-is-1-to-1
			      (x1 a)
			      (x2 c))
		   (:instance icfn-is-1-to-1
			      (x1 b)
			      (x2 c))
		   (:instance inside-interval-p-squeeze
			      (a a)
			      (b b)
			      (c (icfn-exists-intermediate-point-witness a b (icfn c)))
			      (interval (icfn-domain)))
		   )
	     :in-theory (disable icfn-intermediate-value-theorem-sk
				 inside-interval-p-squeeze
				 ))
	    )
    ))

 (local
  (defthm lemma-1b
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (inside-interval-p c (icfn-domain))
		    (< a b)
		    (< b c)
		    (< (icfn a) (icfn b))
		    (<= (icfn c) (icfn a)))
	       (< (icfn b) (icfn c)))
    :hints (("Goal"
	     :use ((:instance icfn-intermediate-value-theorem-sk
			      (a b)
			      (b c)
			      (z (icfn a)))
		   (:instance icfn-is-1-to-1
			      (x1 a)
			      (x2 (icfn-exists-intermediate-point-witness b c (icfn a))))
		   (:instance icfn-is-1-to-1
			      (x1 a)
			      (x2 c))
		   (:instance icfn-is-1-to-1
			      (x1 b)
			      (x2 c))
		   (:instance inside-interval-p-squeeze
			      (a b)
			      (b c)
			      (c (icfn-exists-intermediate-point-witness b c (icfn a)))
			      (interval (icfn-domain)))
		   )
	     :in-theory (disable icfn-intermediate-value-theorem-sk
				 inside-interval-p-squeeze
				 ))
	    )
    ))

 (local
  (defthm lemma-1
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (inside-interval-p c (icfn-domain))
		    (< a b)
		    (< b c)
		    (< (icfn a) (icfn b)))
	       (< (icfn b) (icfn c)))
    :hints (("Goal"
	     :use ((:instance lemma-1a)
		   (:instance lemma-1b))
	     :in-theory (disable lemma-1a lemma-1b))
	    )
    ))

 (local
  (defthm lemma-2a
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (inside-interval-p c (icfn-domain))
		    (< a b)
		    (< b c)
		    (> (icfn a) (icfn b))
		    (>= (icfn a) (icfn c)))
	       (> (icfn b) (icfn c)))
    :hints (("Goal"
	     :use ((:instance icfn-intermediate-value-theorem-sk
			      (a a)
			      (b b)
			      (z (icfn c)))
		   (:instance icfn-is-1-to-1
			      (x1 c)
			      (x2 (icfn-exists-intermediate-point-witness a b (icfn c))))
		   (:instance icfn-is-1-to-1
			      (x1 a)
			      (x2 c))
		   (:instance icfn-is-1-to-1
			      (x1 b)
			      (x2 c))
		   (:instance inside-interval-p-squeeze
			      (a a)
			      (b b)
			      (c (icfn-exists-intermediate-point-witness a b (icfn c)))
			      (interval (icfn-domain)))
		   )
	     :in-theory (disable icfn-intermediate-value-theorem-sk
				 inside-interval-p-squeeze
				 ))
	    )
    ))

 (local
  (defthm lemma-2b
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (inside-interval-p c (icfn-domain))
		    (< a b)
		    (< b c)
		    (> (icfn a) (icfn b))
		    (>= (icfn c) (icfn a)))
	       (> (icfn b) (icfn c)))
    :hints (("Goal"
	     :use ((:instance icfn-intermediate-value-theorem-sk
			      (a b)
			      (b c)
			      (z (icfn a)))
		   (:instance icfn-is-1-to-1
			      (x1 a)
			      (x2 (icfn-exists-intermediate-point-witness b c (icfn a))))
		   (:instance icfn-is-1-to-1
			      (x1 a)
			      (x2 c))
		   (:instance icfn-is-1-to-1
			      (x1 b)
			      (x2 c))
		   (:instance inside-interval-p-squeeze
			      (a b)
			      (b c)
			      (c (icfn-exists-intermediate-point-witness b c (icfn a)))
			      (interval (icfn-domain)))
		   )
	     :in-theory (disable icfn-intermediate-value-theorem-sk
				 inside-interval-p-squeeze
				 ))
	    )
    ))

 (local
  (defthm lemma-2
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (inside-interval-p c (icfn-domain))
		    (< a b)
		    (< b c)
		    (> (icfn a) (icfn b)))
	       (> (icfn b) (icfn c)))
    :hints (("Goal"
	     :use ((:instance lemma-2a)
		   (:instance lemma-2b))
	     :in-theory (disable lemma-2a lemma-2b))
	    )
    ))

 (defthm icfn-is-monotonic
    (implies (and (inside-interval-p a (icfn-domain))
		  (inside-interval-p b (icfn-domain))
		  (inside-interval-p c (icfn-domain))
		  (< a b)
		  (< b c))
	     (or (and (< (icfn a) (icfn b))
		      (< (icfn b) (icfn c)))
		 (and (> (icfn a) (icfn b))
		      (> (icfn b) (icfn c)))))
   :hints (("Goal"
	    :use ((:instance lemma-1)
		  (:instance lemma-2)
		  (:instance icfn-is-1-to-1
			     (x1 a)
			     (x2 b)))
	    :in-theory (disable lemma-1 lemma-2)))
  :rule-classes nil)
 )

;; Here's another useful property of idfn.  If a and b are not i-close,
;; then neither are idfn(a) and idfn(b).  The reason is simple.  If they're
;; not i-close, then there must be standard points c1 and c2 between a and b.
;; Then, by monotonicity, we have idfn(a) < idfn(c1) < idfn(c2) < idfn(b)
;; (or decreasing....).  The important point is that idfn(c2) - idfn(c1) is
;; not i-small, since idfn(c1) and idfn(c2) are standard and not equal to
;; each other.  Thus, idfn(b)-idfn(a) > idfn(c2)-idfn(c1) can't be i-small,
;; either, so idfn(a) is not i-close to idfn(b).

(local
 (defun innerpoint (a b)
   (if (i-limited a)
       (if (i-limited b)
	   (/ (+ a b) 2)
	   (+ a 1))
       (if (i-limited b)
	   (- b 1)
	   (/ (+ a b) 2)))))

(local
 (defthm innerpoint-almost-commutes
     (implies (iff (i-limited a)
		   (i-limited b))
	      (equal (innerpoint a b)
		     (innerpoint b a)))))

(local
 (defthm innerpoint-between-a-b
     (implies (and (realp a)
		   (realp b)
		   (< a b))
	      (and (< a (innerpoint a b))
		   (< (innerpoint a b) b)))
   :hints (("Subgoal 3"
	    :use ((:instance large->-non-large
			     (x b)
			     (y (1+ a)))))
	   ("Subgoal 2"
	    :use ((:instance large->-non-large
			     (x a)
			     (y (1- b)))))
	   )))

(local
 (defthm limited-not-close-to-large
     (implies (and (i-limited x)
		   (i-large y))
	      (not (i-close x y)))
   ))

(local
 (defthm innerpoint-not-close-to-a
     (implies (and (realp a)
		   (realp b)
		   (not (i-close a b)))
	      (not (i-close a (innerpoint a b))))
   :hints (("Goal"
	    :cases ((< a b))
	    :use ((:instance limited-not-close-to-large
			     (x (- b 1))
			     (y a))
		  (:instance i-small-uminus
			     (x (+ 1 a (- b))))
		  )
	    :in-theory (enable-disable (i-close) (limited-not-close-to-large i-small-uminus))))))

(local
 (defthm innerpoint-not-close-to-b
     (implies (and (realp a)
		   (realp b)
		   (not (i-close a b)))
	      (not (i-close b (innerpoint a b))))
   :hints (("Goal"
	    :use ((:instance innerpoint-not-close-to-a (a b) (b a))
		  (:instance limited-not-close-to-large
			     (x (+ a 1))
			     (y b))
		  (:instance limited-not-close-to-large
			     (x (- b 1))
			     (y a))
		  (:instance i-small-uminus
			     (x (+ 1 a (- b))))
		  )
	    :in-theory (enable-disable (i-close) (innerpoint-not-close-to-a limited-not-close-to-large i-small-uminus))))))


(local
 (defthm realp-innerpoint
     (implies (and (realp a)
		   (realp b))
	      (realp (innerpoint a b)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm innerpoint-a-a
     (equal (innerpoint a a)
	    (fix a))))

(local
 (defthm innerpoint-limited
     (implies (or (i-limited a)
		  (i-limited b))
	      (i-limited (innerpoint a b)))))

(local (in-theory (disable innerpoint)))

(local
 (defthm innerpoint-inside-interval
     (implies (and (inside-interval-p a interval)
		   (inside-interval-p b interval)
		   (<= a b))
	      (inside-interval-p (innerpoint a b) interval))
   :hints (("Goal"
	    :use ((:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c (innerpoint a b)))
		  (:instance innerpoint-between-a-b))
	    :in-theory (disable inside-interval-p-squeeze innerpoint-between-a-b))
	   )))

(local
 (defthm same-standard-part-then-close
     (implies (and (realp a)
		   (realp b)
		   (equal (standard-part a)
			  (standard-part b))
		   (i-limited a)
		   (i-limited b)
		   )
	      (i-close a b))
   :hints (("Goal"
	    :use ((:instance standard-part-close
			     (x a))
		  (:instance standard-part-close
			     (x b))
		  (:instance i-close-transitive
			     (x a)
			     (y (standard-part a))
			     (z b)))
	    :in-theory (disable standard-part-close i-close-transitive)))
   ))

(local
 (defthm close-standards-are-equal
     (implies (and (realp a)
		   (realp b)
		   (standardp a)
		   (standardp b)
		   (i-close a b))
	      (equal (equal a b) t))
   :hints (("Goal"
	    :use ((:instance standard-small-is-zero
			     (x (- a b))))
	    :in-theory (enable i-close)))))

(local
 (defthm not-close-not-same-standard-part
     (implies (and (realp a)
		   (realp b)
		   (not (i-close a b))
		   (i-limited a)
		   (i-limited b))
	      (not (i-close (standard-part a)
			    (standard-part b))))
   :hints (("Goal"
	    :use ((:instance same-standard-part-then-close)
		  (:instance close-standards-are-equal (a (standard-part a)) (b (standard-part b))))
	    :in-theory (disable same-standard-part-then-close close-standards-are-equal)))
   ))

(local
 (defthm standard-part-innerpoint-greater-than-a
     (implies (and (realp a)
		   (realp x) (i-limited x)
		   (< a x)
		   (not (i-close a x))
		   )
	      (< a (standard-part x)))
   :hints (("Goal"
	    :cases ((i-limited a)))
	   ("Subgoal 2"
	    :use ((:instance large->-non-large
			     (x a)
			     (y (standard-part x))))
	    :in-theory (disable large->-non-large))
	   ("Subgoal 1"
	    :use ((:instance standard-part-squeeze
			     (x (standard-part x))
			     (y a)
			     (z x)))
	    ))))

(local
 (defthm standard-part-innerpoint-less-than-b
     (implies (and (realp b)
		   (realp x) (i-limited x)
		   (< x b)
		   (not (i-close b x))
		   )
	      (< (standard-part x) b))
   :hints (("Goal"
	    :cases ((i-limited b)))
	   ("Subgoal 2"
	    :use ((:instance large->-non-large
			     (x b)
			     (y (standard-part x))))
	    :in-theory (disable large->-non-large))
	   ("Subgoal 1"
	    :use ((:instance standard-part-squeeze
			     (x x)
			     (y b)
			     (z (standard-part x))))))))

(defthm-std standard-icfn-domain
    (standardp (icfn-domain)))

(local
 (defthm standard-part-innerpoint-inside-interval
     (implies (and (inside-interval-p a (icfn-domain))
		   (inside-interval-p b (icfn-domain))
		   (or (i-limited a) (i-limited b))
		   (not (i-close a b))
		   (< a b))
	      (inside-interval-p (standard-part (innerpoint a b))
				 (icfn-domain)))
   :hints (("Goal"
	    :use ((:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c (standard-part (innerpoint a b)))
			     (interval (icfn-domain)))
		  (:instance standard-part-innerpoint-greater-than-a
			     (a a)
			     (x (innerpoint a b)))
		  (:instance standard-part-innerpoint-less-than-b
			     (b b)
			     (x (innerpoint a b))))
	    :in-theory (disable inside-interval-p-squeeze
				standard-part-innerpoint-greater-than-a
				standard-part-innerpoint-less-than-b)))))



(local
 (defthm limited-not-close-standard-part
     (implies (and (realp x)
		   (realp y)
		   (i-limited x)
		   (not (i-close x y)))
	      (not (i-close (standard-part x) y)))
   :hints (("Goal"
	    :cases ((i-limited y))))))

(local
 (defthm standard-part-innerpoint-innerpoint-b-inside-interval
     (implies (and (inside-interval-p a (icfn-domain))
		   (inside-interval-p b (icfn-domain))
		   (or (i-limited a) (i-limited b))
		   (not (i-close a b))
		   (< a b))
	      (inside-interval-p (standard-part (innerpoint (standard-part (innerpoint a b)) b))
				 (icfn-domain)))
   :hints (("Goal"
	    :use ((:instance standard-part-innerpoint-inside-interval
			     (a a)
			     (b b))
		  (:instance standard-part-innerpoint-inside-interval
			     (a (standard-part (innerpoint a b)))
			     (b b))
		  (:instance innerpoint-not-close-to-b)
		  (:instance limited-not-close-standard-part
			     (x (innerpoint a b))
			     (y b)))
	    :in-theory (disable standard-part-innerpoint-inside-interval
				limited-not-close-standard-part innerpoint-not-close-to-b)))))

(local
 (defthm standard-part-innerpoint-less-than-innerpoint-innerpoint
     (implies (and (inside-interval-p a (icfn-domain))
		   (inside-interval-p b (icfn-domain))
		   (or (i-limited a) (i-limited b))
		   (not (i-close a b))
		   (< a b))
	      (< (STANDARD-PART (INNERPOINT A B))
		 (STANDARD-PART (INNERPOINT (STANDARD-PART (INNERPOINT A B))
					    B))))
   :hints (("Goal"
	    :use ((:instance standard-part-innerpoint-greater-than-a
			     (a (standard-part (innerpoint a b)))
			     (x (INNERPOINT (STANDARD-PART (INNERPOINT A B))
					    B)))
		  (:instance innerpoint-not-close-to-a
			     (a (standard-part (innerpoint a b)))
			     (b b))
		  (:instance innerpoint-not-close-to-b
			     (a (innerpoint a b))
			     (b b))
		  (:instance innerpoint-not-close-to-b
			     (a a)
			     (b b))
		  (:instance standard-part-innerpoint-less-than-b
			     (x (innerpoint (standard-part (innerpoint a b)) b))
			     (b b))
		  (:instance standard-part-innerpoint-less-than-b
			     (x (innerpoint a b))
			     (b b))
		  (:instance standard-part-innerpoint-less-than-b
			     (x a)
			     (b b))
		  (:instance limited-not-close-standard-part
			     (x (innerpoint a b))
			     (y b))
		  )
	    :in-theory (disable standard-part-innerpoint-greater-than-a
				innerpoint-not-close-to-a
				innerpoint-not-close-to-b
				standard-part-innerpoint-less-than-b
				INNERPOINT-ALMOST-COMMUTES
				limited-not-close-standard-part)))))

(local
 (defthm standard-part-innerpoint-standard-part-less-than-b
     (implies (and (inside-interval-p a (icfn-domain))
		   (inside-interval-p b (icfn-domain))
		   (or (i-limited a) (i-limited b))
		   (not (i-close a b))
		   (< a b))
	      (< (STANDARD-PART (INNERPOINT (STANDARD-PART (INNERPOINT A B))
					    B))
		 B))
   :hints (("Goal"
	    :use ((:instance standard-part-innerpoint-less-than-b
			     (x (INNERPOINT (STANDARD-PART (INNERPOINT A B)) B))
			     (b b))
		  (:instance innerpoint-between-a-b
			     (a (STANDARD-PART (INNERPOINT A B)))
			     (b b))
		  (:instance innerpoint-between-a-b
			     (a a)
			     (b b))
		  (:instance standard-part-innerpoint-less-than-b
			     (x (innerpoint a b))
			     (b b))
		  (:instance innerpoint-not-close-to-b
			     (a (STANDARD-PART (INNERPOINT A B)))
			     (b b))
		  (:instance innerpoint-not-close-to-b
			     (a a)
			     (b b))
		  (:instance limited-not-close-standard-part
			     (x (innerpoint a b))
			     (y b))
		  )
	    :in-theory (disable standard-part-innerpoint-less-than-b
				INNERPOINT-ALMOST-COMMUTES
				innerpoint-between-a-b
				innerpoint-not-close-to-b
				limited-not-close-standard-part
				)))))

(defthm-std standard-icfn
    (implies (standardp x)
	     (standardp (icfn x))))

(encapsulate
 nil

 (local
  (defthm lemma-1
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (or (i-limited a) (i-limited b))
		    (not (i-close a b))
		    (< a b)
		    (<= (icfn a) (icfn b)))
	       (and (< (icfn a)
		       (icfn (standard-part (innerpoint a b))))
		    (< (icfn (standard-part (innerpoint a b)))
		       (icfn (standard-part (innerpoint (standard-part (innerpoint a b)) b))))
		    (< (icfn (standard-part (innerpoint (standard-part (innerpoint a b)) b)))
		       (icfn b))))
    :hints (("Goal"
	     :use ((:instance icfn-is-monotonic
			      (a a)
			      (b (standard-part (innerpoint a b)))
			      (c (standard-part (innerpoint (standard-part (innerpoint a b)) b))))
		   (:instance icfn-is-monotonic
			      (a (standard-part (innerpoint a b)))
			      (b (standard-part (innerpoint (standard-part (innerpoint a b)) b)))
			      (c b))
		   (:instance inside-interval-p-squeeze
			      (a a)
			      (b b)
			      (c (standard-part (innerpoint a b)))
			      (interval (icfn-domain)))
		   )
					;:in-theory (disable icfn-is-monotonic)
	     ))))

 (local
  (defthm lemma-2
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (or (i-limited a) (i-limited b))
		    (not (i-close a b))
		    (< a b)
		    (> (icfn a) (icfn b)))
	       (and (> (icfn a)
		       (icfn (standard-part (innerpoint a b))))
		    (> (icfn (standard-part (innerpoint a b)))
		       (icfn (standard-part (innerpoint (standard-part (innerpoint a b)) b))))
		    (> (icfn (standard-part (innerpoint (standard-part (innerpoint a b)) b)))
		       (icfn b))))
    :hints (("Goal"
	     :use ((:instance icfn-is-monotonic
			      (a a)
			      (b (standard-part (innerpoint a b)))
			      (c (standard-part (innerpoint (standard-part (innerpoint a b)) b))))
		   (:instance icfn-is-monotonic
			      (a (standard-part (innerpoint a b)))
			      (b (standard-part (innerpoint (standard-part (innerpoint a b)) b)))
			      (c b))
		   (:instance inside-interval-p-squeeze
			      (a a)
			      (b b)
			      (c (standard-part (innerpoint a b)))
			      (interval (icfn-domain)))
		   )
					;:in-theory (disable icfn-is-monotonic)
	     ))))

 (local
  (defthm lemma-3
      (implies (and (realp a)
		    (realp x1) (standardp x1)
		    (realp x2) (standardp x2)
		    (realp b)
		    (< a x1)
		    (< x1 x2)
		    (< x2 b))
	       (not (i-close a b)))
    :hints (("Goal"
	     :use ((:instance close-standards-are-equal (a x1) (b x2))
		   (:instance small-if-<-small
			      (x (- a b))
			      (y (- x1 x2))))
	     :in-theory (enable-disable (i-close) (close-standards-are-equal small-if-<-small)))
	    )))

 (local
  (defthm lemma-4
      (implies (and (realp a)
		    (realp x1) (standardp x1)
		    (realp x2) (standardp x2)
		    (realp b)
		    (> a x1)
		    (> x1 x2)
		    (> x2 b))
	       (not (i-close a b)))
    :hints (("Goal"
	     :use ((:instance close-standards-are-equal (a x1) (b x2))
		   (:instance small-if-<-small
			      (x (- a b))
			      (y (- x1 x2))))
	     :in-theory (enable-disable (i-close) (close-standards-are-equal small-if-<-small)))
	    )))

 (local
  (defthm lemma-5
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (or (i-limited a) (i-limited b))
		    (not (i-close a b))
		    (< a b)
		    (<= (icfn a) (icfn b)))
	       (not (i-close (icfn a) (icfn b))))
    :hints (("Goal"
	     :use ((:instance lemma-1)
		   (:instance lemma-3
			      (a (icfn a))
			      (x1 (icfn (standard-part (innerpoint a b))))
			      (x2 (icfn (standard-part (innerpoint (standard-part (innerpoint a b)) b))))
			      (b (icfn b))))
	     :in-theory (disable lemma-1 lemma-3)))))

 (local
  (defthm lemma-6
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (or (i-limited a) (i-limited b))
		    (not (i-close a b))
		    (< a b)
		    (> (icfn a) (icfn b)))
	       (not (i-close (icfn a) (icfn b))))
    :hints (("Goal"
	     :use ((:instance lemma-2)
		   (:instance lemma-4
			      (a (icfn a))
			      (x1 (icfn (standard-part (innerpoint a b))))
			      (x2 (icfn (standard-part (innerpoint (standard-part (innerpoint a b)) b))))
			      (b (icfn b))))
	     :in-theory (disable lemma-2 lemma-4)))))

 (local
  (defthm lemma-7
      (implies (and (inside-interval-p a (icfn-domain))
		    (inside-interval-p b (icfn-domain))
		    (or (i-limited a) (i-limited b))
		    (not (i-close a b))
		    (< a b))
	       (not (i-close (icfn a) (icfn b))))
    :hints (("Goal"
	     :use ((:instance lemma-5)
		   (:instance lemma-6))
	     :in-theory nil))))

 (defthm icfn-preserves-not-close
     (implies (and (inside-interval-p a (icfn-domain))
		   (inside-interval-p b (icfn-domain))
		   (i-limited a)
		   (not (i-close a b)))
	      (not (i-close (icfn a) (icfn b))))
   :hints (("Goal"
	    :use ((:instance lemma-7)
		  (:instance lemma-7 (a b) (b a)))
	    :in-theory (disable lemma-7)))
   :rule-classes nil)
 )

(defmacro definv (f &key f-inverse domain range inverse-interval
		  f-continuous-hints interval-correctness-hints f-1-to-1-hints f-real-hints
		  f-in-range-hints range-interval-hints domain-interval-hints
		  domain-non-trivial-hints range-non-trivial-hints inverse-hints
		  )
  (let* ((f-inverse        	   	     (if (null f-inverse) (u::pack-intern f f '-inverse) f-inverse))
	 (f-inverse-exists 	   	     (u::pack-intern f-inverse f-inverse '-exists))
	 (f-inverse-is-real                  (u::pack-intern f-inverse f-inverse '-is-real))
	 (f-inverse-unique 	   	     (u::pack-intern f-inverse f-inverse '-unique))
	 (f-inverse-inverse-exists 	     (u::pack-intern f-inverse f-inverse '-inverse-exists))
	 (f-inverse-is-1-to-1      	     (u::pack-intern f-inverse f-inverse '-is-1-to-1))
	 ;(f-is-monotonic        	     (u::pack-intern f-inverse f '-is-monotonic))
	 (f-obligation-continuity  	     (u::pack-intern f f '-obligation-continuity))
	 (f-obligation-interval-correctness  (u::pack-intern f f '-obligation-interval-correctness))
	 (f-obligation-1-to-1                (u::pack-intern f f '-obligation-1-to-1))
	 (f-obligation-real                  (u::pack-intern f f '-obligation-real))
	 (f-obligation-in-range              (u::pack-intern f f '-obligation-in-range))
	 (f-obligation-range-interval        (u::pack-intern f f '-obligation-range-interval))
	 (f-obligation-domain-interval       (u::pack-intern f f '-obligation-domain-interval))
	 (f-obligation-domain-non-trivial    (u::pack-intern f f '-obligation-domain-non-trivial))
	 (f-obligation-range-non-trivial     (u::pack-intern f f '-obligation-range-non-trivial))
	 (f-obligation-inverse               (u::pack-intern f f '-obligation-inverse))
	 (domain                   	     (if (null domain) (interval nil nil) domain))
	 (range                    	     (if (null range)  (interval nil nil) range))
	 (inverse-interval         	     (if (null inverse-interval)  '(lambda (y) (interval y y)) inverse-interval))
	 (inverse-hints                      (if (null inverse-hints) `(("Goal" :use ((:instance ,f-inverse)))) inverse-hints))
	 )
    `(encapsulate
       nil

       (local
	(defthm ,f-obligation-continuity
	    (implies (and (standardp x1)
			  (inside-interval-p x1 ,domain)
			  (i-close x1 x2)
			  (inside-interval-p x2 ,domain))
		     (i-close (,f x1)
			      (,f x2)))
	  :hints ,f-continuous-hints
	  :rule-classes (:built-in-clause)))

       (local
	(defthm ,f-obligation-interval-correctness
	    (implies (inside-interval-p y ,range)
		     (let ((estimate (,inverse-interval y)))
		       (let ((x1 (interval-left-endpoint estimate)))
			 (let ((x2 (interval-right-endpoint estimate)))
			   (and (interval-p estimate)
				(subinterval-p estimate ,domain)
				(interval-left-inclusive-p estimate)
				(interval-right-inclusive-p estimate)
				(or (and (<= (,f x1) y)
					 (<= y (,f x2)))
				    (and (<= y (,f x1))
					 (<= (,f x2) y))))))))
	  :hints ,interval-correctness-hints
	  :rule-classes (:built-in-clause)))

       (local
	(defthm ,f-obligation-1-to-1
	    (IMPLIES (AND (INSIDE-INTERVAL-P X1 ,domain)
			  (INSIDE-INTERVAL-P X2 ,domain)
			  (EQUAL (,f X1) (,f X2)))
		     (EQUAL X1 X2))
	  :hints ,f-1-to-1-hints
	  :rule-classes (:built-in-clause)))

       (local
	(defthm ,f-obligation-real
	    (realp (,f x))
	  :hints ,f-real-hints
	  :rule-classes (:built-in-clause)))

       (local
	(defthm ,f-obligation-in-range
	    (implies (inside-interval-p x ,domain)
		     (inside-interval-p (,f x) ,range))
	  :hints ,f-in-range-hints
	  :rule-classes (:built-in-clause)))

       (local
	(defthm ,f-obligation-range-interval
	    (interval-p ,range)
	  :hints ,range-interval-hints
	  :rule-classes (:built-in-clause)))

       (local
	(defthm ,f-obligation-domain-interval
	    (interval-p ,domain)
	  :hints ,domain-interval-hints
	  :rule-classes (:built-in-clause)))

       (local
	(defthm ,f-obligation-domain-non-trivial
	    (or (null (interval-left-endpoint ,domain))
		(null (interval-right-endpoint ,domain))
		(< (interval-left-endpoint ,domain)
		   (interval-right-endpoint ,domain)))
	  :hints ,domain-non-trivial-hints
	  :rule-classes (:built-in-clause)))

       (local
	(defthm ,f-obligation-range-non-trivial
	    (or (null (interval-left-endpoint ,range))
		(null (interval-right-endpoint ,range))
		(< (interval-left-endpoint ,range)
		   (interval-right-endpoint ,range)))
	  :hints ,range-non-trivial-hints
	  :rule-classes (:built-in-clause)))

       (defchoose ,f-inverse (x) (y)
		  (if (inside-interval-p y ,range)
		      (and (inside-interval-p x ,domain)
			   (equal (,f x) y))
		      (realp x)))

       (local
	(defthm ,f-obligation-inverse
	    (implies (if (inside-interval-p y ,range)
			 (and (inside-interval-p x ,domain)
			      (equal (,f x) y))
			 (realp x))
		     (let ((x (,f-inverse y)))
		       (if (inside-interval-p y ,range)
			   (and (inside-interval-p x ,domain)
				(equal (,f x) y))
			   (realp x))))
	  :hints ,inverse-hints
	  :rule-classes (:built-in-clause)))

       (defthm ,f-inverse-exists
	   (implies (inside-interval-p y ,range)
		    (and (inside-interval-p (,f-inverse y) ,domain)
			 (equal (,f (,f-inverse y)) y)))
	 :hints (("Goal"
		  :do-not '(preprocess)
		  :use ((:functional-instance icfn-inverse-exists
					      (icfn ,f)
					      (icfn-domain (lambda () ,domain))
					      (icfn-range (lambda () ,range))
					      (icfn-inv-interval ,inverse-interval)
					      (icfn-inverse ,f-inverse))))
		 ("Subgoal 15"
		  :use ((:instance ,f-obligation-inverse (y (,f x)))))
		 ("Subgoal 13"
		  :use ((:instance ,f-obligation-inverse (y (,f x)))))
		 ("Subgoal 12"
		  :use ((:instance ,f-obligation-inverse (y (,f x)))))
		 ("Subgoal 11"
		  :use ((:instance ,f-obligation-inverse (y (,f x)))))
		 ("Subgoal 2"
		  :use ((:instance ,f-obligation-domain-non-trivial)))
		 ("Subgoal 1"
		  :use ((:instance ,f-obligation-range-non-trivial)))
		 ))

       (defthm ,f-inverse-is-real
	   (realp (,f-inverse y))
	 :hints (("goal"
		  :use ((:functional-instance icfn-inverse-is-real
					      (icfn ,f)
					      (icfn-domain (lambda () ,domain))
					      (icfn-range (lambda () ,range))
					      (icfn-inv-interval ,inverse-interval)
					      (icfn-inverse ,f-inverse)))))
	 :rule-classes (:rewrite :type-prescription))

       (defthm ,f-inverse-unique
	   (implies (and (inside-interval-p y ,range)
			 (inside-interval-p x ,domain)
			 (equal (,f x) y))
		    (equal (,f-inverse y) x))
	 :hints (("goal"
		  :use ((:functional-instance icfn-inverse-unique
					      (icfn ,f)
					      (icfn-domain (lambda () ,domain))
					      (icfn-range (lambda () ,range))
					      (icfn-inv-interval ,inverse-interval)
					      (icfn-inverse ,f-inverse))))))

       (defthm ,f-inverse-inverse-exists
	   (implies (inside-interval-p x ,domain)
		    (equal (,f-inverse (,f x)) x))
	 :hints (("goal"
		  :use ((:functional-instance icfn-inverse-inverse-exists
					      (icfn ,f)
					      (icfn-domain (lambda () ,domain))
					      (icfn-range (lambda () ,range))
					      (icfn-inv-interval ,inverse-interval)
					      (icfn-inverse ,f-inverse))))))

       (defthm ,f-inverse-is-1-to-1
	   (implies (and (inside-interval-p y1 ,range)
			 (inside-interval-p y2 ,range)
			 (equal (,f-inverse y1)
				(,f-inverse y2)))
		    (equal y1 y2))
	 :hints (("goal"
		  :use ((:functional-instance icfn-inverse-is-1-to-1
					      (icfn ,f)
					      (icfn-domain (lambda () ,domain))
					      (icfn-range (lambda () ,range))
					      (icfn-inv-interval ,inverse-interval)
					      (icfn-inverse ,f-inverse)))))
	 :rule-classes nil)

       #|
       ; This is a property of f, not of f-inverse, so we should not include it in this macro

       (defthm ,f-is-monotonic
	   (implies (and (inside-interval-p a ,domain)
			 (inside-interval-p b ,domain)
			 (inside-interval-p c ,domain)
			 (< a b)
			 (< b c))
		    (or (and (<= (,f a) (,f b))
			     (<= (,f b) (,f c)))
			(and (>= (,f a) (,f b))
			     (>= (,f b) (,f c)))))
	 :hints (("goal"
		  :use ((:functional-instance icfn-is-monotonic
					      (icfn ,f)
					      (icfn-domain (lambda () ,domain))))))
	 :rule-classes nil)
       |#
       )
    ))


#| Example:

(defun idfunction (x) (realfix x))

(defun idfunction-interval (y)
  (interval (- y 1) (+ y 1)))

(definv idfunction
    :domain (interval nil nil)
    :range (interval nil nil)
    :inverse-interval idfunction-interval)

|#
