(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "inverse-monotone")
(include-book "derivatives")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(encapsulate
 ((idfn (x) t)
  (idfn-domain () t)
  (idfn-range () t)
  (idfn-inv-interval (y) t))

 (local (defun idfn (x) (realfix x)))
 (local (defun idfn-domain () (interval nil nil)))
 (local (defun idfn-range () (interval nil nil)))
 (local (defun idfn-inv-interval (y) (interval y y)))

 ; The intervals are really intervals

 (defthm idfn-domain-is-an-interval
     (interval-p (idfn-domain))
   :rule-classes (:rewrite :type-prescription))

 (defthm idfn-range-is-an-interval
     (interval-p (idfn-range))
   :rule-classes (:rewrite :type-prescription))

 ;; The intervals are non-trivial

 (defthm idfn-domain-non-trivial
     (or (null (interval-left-endpoint (idfn-domain)))
	 (null (interval-right-endpoint (idfn-domain)))
	 (< (interval-left-endpoint (idfn-domain))
	    (interval-right-endpoint (idfn-domain))))
   :rule-classes nil)

 (defthm idfn-range-non-trivial
     (or (null (interval-left-endpoint (idfn-range)))
	 (null (interval-right-endpoint (idfn-range)))
	 (< (interval-left-endpoint (idfn-range))
	    (interval-right-endpoint (idfn-range))))
   :rule-classes nil)

 ; The function value is in the range when the input is in the domain

 (defthm idfn-in-range
     (implies (inside-interval-p x (idfn-domain))
	      (inside-interval-p (idfn x) (idfn-range))))

 ; Regardless of the input, the function is real

 (defthm idfn-real
     (realp (idfn x))
   :rule-classes (:rewrite :type-prescription))

 ; We restrict ourselves to increasing functions

 (defthm idfn-is-1-to-1
     (implies (and (inside-interval-p x1 (idfn-domain))
		   (inside-interval-p x2 (idfn-domain))
		   (equal (idfn x1) (idfn x2)))
	      (equal x1 x2))
   :rule-classes nil)

 ; The function inv-interval takes y and return a pair of x1 <= x2 such that idfn(x1) <= y <= idfn(x2)
 ; or idfn(y1) >= y >= idfn(x2).  That is, they find a bounded, closed interval that contains the
 ; inverse of y

 (defthm idfn-inv-interval-correctness
     (implies (inside-interval-p y (idfn-range))
	      (let* ((estimate (idfn-inv-interval y))
		     (x1 (interval-left-endpoint estimate))
		     (x2 (interval-right-endpoint estimate)))
		(and (interval-p estimate)
		     (subinterval-p estimate (idfn-domain))
		     (interval-left-inclusive-p estimate)
		     (interval-right-inclusive-p estimate)
		     (or (and (<= (idfn x1) y)
			      (<= y (idfn x2)))
			 (and (>= (idfn x1) y)
			      (>= y (idfn x2)))))))
   :rule-classes nil)

 ; The function is differentiable on its range

 (defthm idfn-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (idfn-domain))
		 (inside-interval-p y1 (idfn-domain))
		 (inside-interval-p y2 (idfn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (idfn x) (idfn y1)) (- x y1)))
		 (i-close (/ (- (idfn x) (idfn y1)) (- x y1))
			  (/ (- (idfn x) (idfn y2)) (- x y2))))))

  ; But the derivative is never zero over the range

 (defthm idfn-differential-not-small
   (implies (and (standardp x)
		 (inside-interval-p x (idfn-domain))
		 (inside-interval-p y1 (idfn-domain))
		 (i-close x y1) (not (= x y1)))
	    (not (i-small (/ (- (idfn x) (idfn y1)) (- x y1))))))
 )

; The function is continuous over its range

(defthm idfn-continuous
    (implies (and (standardp x1)
		  (inside-interval-p x1 (idfn-domain))
		  (i-close x1 x2)
		  (inside-interval-p x2 (idfn-domain)))
	     (i-close (idfn x1) (idfn x2)))
  :hints (("Goal"
	   :use ((:instance (:functional-instance rdfn-continuous
						  (rdfn-domain idfn-domain)
						  (rdfn idfn)
						  )
			    (x x1)
			    (y x2)))
	   )
	  ("Subgoal 3"
	   :use ((:instance idfn-differentiable))
	   :in-theory (disable idfn-differentiable))
	  ("Subgoal 2"
	   :use ((:instance idfn-domain-non-trivial)))
	  ))

; Now let's define the inverse

;; This macro doesn't handle the new obligation on intervals properly.  We need
;; to add a hint for it, and we also need to add the theorem explicitly.

(definv idfn
    :domain (idfn-domain)
    :range (idfn-range)
    :inverse-interval idfn-inv-interval
    :interval-correctness-hints (("Goal" :use idfn-inv-interval-correctness))
    :f-1-to-1-hints (("Goal" :use idfn-is-1-to-1))
    :domain-non-trivial-hints (("Goal" :use idfn-domain-non-trivial))
    :range-non-trivial-hints (("Goal" :use idfn-range-non-trivial))
    )

; The function is monotonic

(defthm idfn-is-monotonic
    (implies (and (inside-interval-p a (idfn-domain))
		  (inside-interval-p b (idfn-domain))
		  (inside-interval-p c (idfn-domain))
		  (< a b)
		  (< b c))
	     (or (and (< (idfn a) (idfn b))
		      (< (idfn b) (idfn c)))
		 (and (> (idfn a) (idfn b))
		      (> (idfn b) (idfn c)))))
  :hints (("Goal"
	   :by (:functional-instance icfn-is-monotonic
				     (icfn idfn)
				     (icfn-inverse idfn-inverse)
				     (icfn-domain (lambda nil (idfn-domain)))
				     (icfn-range (lambda nil (idfn-range)))
				     (icfn-inv-interval idfn-inv-interval))
; Change for tau (after Version  4.3) by Matt K. -- at one point we renumbered
; the subgoals, but then we decided just to turn off tau.
           :in-theory (disable (tau-system)))
	  ("Subgoal 5"
	   :use ((:instance idfn-inv-interval-correctness)))
	  ("Subgoal 4"
	   :use ((:instance idfn-is-1-to-1)))
	  ("Subgoal 2"
	   :use ((:instance idfn-range-non-trivial)))
	  ("Subgoal 1"
	   :use ((:instance idfn-domain-non-trivial)))
	  )
  :rule-classes nil)

; The function maps values that are far apart to results that are far apart

(defthm-std standard-idfn-inverse
    (implies (standardp x)
	     (standardp (idfn-inverse x))))

(defthm idfn-preserves-not-close
    (implies (and (inside-interval-p a (idfn-domain))
		  (inside-interval-p b (idfn-domain))
		  (i-limited a)
		  (not (i-close a b)))
	     (not (i-close (idfn a) (idfn b))))
  :hints (("Goal"
	   :by (:functional-instance icfn-preserves-not-close
				     (icfn idfn)
				     (icfn-inverse idfn-inverse)
				     (icfn-domain (lambda nil (idfn-domain)))
				     (icfn-range (lambda nil (idfn-range)))
				     (icfn-inv-interval idfn-inv-interval)))
	  )
  :rule-classes nil)

; Now, we need to show that idfn-inverse is continuous

(local
 (defthm idfn-inverse-continuous-local
     (implies (and (standardp x1)
		   (inside-interval-p x1 (idfn-range))
		   (i-close x1 x2)
		   (inside-interval-p x2 (idfn-range)))
	      (i-close (idfn-inverse x1) (idfn-inverse x2)))
   :hints (("Goal"
	    :use ((:instance idfn-preserves-not-close
			     (a (idfn-inverse x1))
			     (b (idfn-inverse x2)))
		  (:instance idfn-inverse-exists
			     (y x1))
		  (:instance idfn-inverse-exists
			     (y x2))
		  (:instance standard-idfn-inverse
			     (x x1)))
	    :in-theory (disable ;idfn-preserves-not-close
				idfn-inverse-exists
				standard-idfn-inverse)
		  ))))

; Here is the key lemma:

(defthm convert-inverse-differentials
    (implies (and (inside-interval-p y1 (idfn-range))
		  (inside-interval-p y2 (idfn-range))
		  )
	     (equal (/ (- (idfn-inverse y1) (idfn-inverse y2))
		       (- (idfn (idfn-inverse y1)) (idfn (idfn-inverse y2))))
		    (/ (- (idfn-inverse y1) (idfn-inverse y2))
		       (- y1 y2))))
  :hints (("Goal"
	   :use ((:instance IDFN-INVERSE-EXISTS (y y1))
		 (:instance IDFN-INVERSE-EXISTS (y y2)))
	   :in-theory nil))
  :rule-classes nil)

; Now let's define the differential functions

(encapsulate
 ( ((differential-idfn * *) => *) )

 (local
  (defun differential-idfn (x eps)
    (/ (- (idfn (+ x eps)) (idfn x)) eps)))

 (defthm differential-idfn-definition
   (implies (and (inside-interval-p x (idfn-domain))
		 (inside-interval-p (+ x eps) (idfn-domain)))
	    (equal (differential-idfn x eps)
		   (/ (- (idfn (+ x eps)) (idfn x)) eps))))
 )

;; Here we include the "usual" theorems about differential-idfn

(defthm x+eps-is-close
    (implies (i-limited x)
	     (i-close x (+ (/ (i-large-integer)) x)))
  :hints (("Goal"
	   :in-theory (enable i-close)))
  )

(defthm x-eps-is-close
    (implies (i-limited x)
	     (i-close x (+ (- (/ (i-large-integer))) x)))
  :hints (("Goal"
	   :in-theory (enable i-close)))
  )



(encapsulate
 ( ((derivative-idfn *) => *) )

 (local
  (defthm limited-derivative-idfn-body
    (implies
     (standardp x)
     (standardp
      (if (inside-interval-p x (idfn-domain))
	  (cond ((inside-interval-p (+ x (/ (i-large-integer)))
				    (idfn-domain))
		 (standard-part (differential-idfn x (/ (i-large-integer)))))
		((inside-interval-p (+ x (- (/ (i-large-integer))))
				    (idfn-domain))
		 (standard-part (differential-idfn x (- (/ (i-large-integer))))))
		(t 'error))
	'error)))
    :hints (("Goal"
	     :in-theory (disable standard-part-of-plus))
	    ("Subgoal 2"
	     :use ((:instance idfn-differentiable
			      (x x)
			      (y1 (+ (/ (i-large-integer)) x))
			      (y2 (+ (/ (i-large-integer)) x))))
	     :in-theory (disable idfn-differentiable standard-part-of-plus))
	    ("Subgoal 1"
	     :use ((:instance idfn-differentiable
			      (x x)
			      (y1 (- x (/ (i-large-integer))))
			      (y2 (- x (/ (i-large-integer))))))
	     :in-theory (disable idfn-differentiable standard-part-of-plus))
	    )
    :rule-classes (:built-in-clause)
    ))

 (local (in-theory '(limited-derivative-idfn-body)))

 (local
  (defun-std derivative-idfn (x)
    (if (inside-interval-p x (idfn-domain))
	(if (inside-interval-p (+ x (/ (i-large-integer))) (idfn-domain))
	    (standard-part (differential-idfn x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (idfn-domain))
	      (standard-part (differential-idfn x (- (/ (i-large-integer)))))
	    'error))
      'error)))

 (defthm derivative-idfn-definition
   (implies (and (inside-interval-p x (idfn-domain))
		 (standardp x))
	    (equal (derivative-idfn x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (idfn-domain))
		       (standard-part (differential-idfn x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (idfn-domain))
			 (standard-part (differential-idfn x (- (/ (i-large-integer)))))
		       'error)))))
 )

(defun differential-idfn-inverse-local (x eps)
  (/ (differential-idfn (idfn-inverse x)
			(- (idfn-inverse (+ x eps))
			   (idfn-inverse x)))))

; So the important lemma is that the definition of differential-idfn-inverse-local is appropriate

(defthm expand-differential-idfn-inverse-local
    (implies (and (inside-interval-p x (idfn-range))
		  (inside-interval-p (+ x eps) (idfn-range))
		  (realp eps)
		  )
	     (equal (differential-idfn-inverse-local x eps)
		    (/ (- (idfn-inverse (+ x eps)) (idfn-inverse x)) eps)))
  :hints (("Goal"
	   :use ((:instance convert-inverse-differentials (y1 (+ x eps)) (y2 x))
		 (:instance IDFN-INVERSE-EXISTS (y x))
		 (:instance IDFN-INVERSE-EXISTS (y (+ x eps)))
		 )
	   :in-theory '(differential-idfn-inverse-local
			differential-idfn-definition
			commutativity-of-+
			commutativity-2-of-+
			associativity-of-+
			minus-cancellation-on-left
			minus-cancellation-on-right
			fix
			distributivity-of-/-over-*
			functional-self-inversion-of-/
			commutativity-of-*
			idfn-inverse-is-real
			IDFN-INVERSE-EXISTS
			)
	   )))

(local
 (defthm small-eps-close-x
     (implies (and (i-small eps)
		   (acl2-numberp x))
	      (i-close x (+ x eps)))
   :hints (("Goal"
	    :in-theory (enable i-close)))
   ))

(local
 (defthm lemma-1
     (implies (and (i-small eps)
		   (equal x (+ x eps)))
	      (equal (equal eps 0) t))
   ))

(local
 (defthm lemma-2
     (equal (* (+ a (- b)) (/ (- c)))
	    (* (+ b (- a)) (/ c)))))

(defthm idfn-differential-actual-not-small
   (implies (and (standardp x)
		 (inside-interval-p x (idfn-domain))
		 (inside-interval-p (+ x eps) (idfn-domain))
		 (i-small eps)
		 (not (= eps 0)))
	    (not (i-small (differential-idfn x eps))))
  :hints (("Goal"
	   :use ((:instance idfn-differential-not-small
			    (x x)
			    (y1 (+ x eps))))
	   :in-theory '(differential-idfn-definition
			small-eps-close-x
			inside-interval-is-real
			(:type-prescription i-small)
			lemma-1
			lemma-2
			distributivity-of-minus-over-+
			minus-cancellation-on-left
			fix
			=)
	   ))
  )

(local
 (defthm close-into-small
     (implies (i-close x y)
	      (i-small (+ (- x) y)))
   :hints (("Goal"
	    :use ((:instance i-small-uminus
			     (x (+ (- x) y))))
	    :in-theory (enable-disable (i-close) (i-small-uminus))))
   ))

(local
 (defthm lemma-3
     (implies (and (acl2-numberp x)
		   (acl2-numberp y)
		   (not (equal x y)))
	      (not (equal (+ (- x) y) 0)))))

(local
 (defthm lemma-4
     (implies (inside-interval-p x (idfn-range))
	      (realp (idfn-inverse x)))
   :rule-classes (:type-prescription :rewrite)))

(defthm idfn-inverse-differentiable-part1-lemma
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-range))
		  (inside-interval-p y1 (idfn-range))
		  (i-close x y1) (not (= x y1)))
	     (i-limited (differential-idfn-inverse-local x (- y1 x))))
  :hints (("Goal"
	   :use ((:instance idfn-differential-actual-not-small
			    (x (idfn-inverse x))
			    (eps (- (idfn-inverse y1) (idfn-inverse x))))
		 (:instance idfn-inverse-continuous-local
			    (x1 x)
			    (x2 y1))
		 (:instance IDFN-INVERSE-IS-1-TO-1
			    (y1 x)
			    (y2 y1))
		 )
	   :in-theory '(differential-idfn-inverse-local
			standard-idfn-inverse
			IDFN-INVERSE-EXISTS
			commutativity-of-+
			commutativity-2-of-+
			associativity-of-+
			minus-cancellation-on-left
			minus-cancellation-on-right
			fix
			close-into-small
			=
			lemma-4
			i-large
			functional-self-inversion-of-/
			inside-interval-is-real)))
  )

(local
 (defthm lemma-5
     (equal (* (+ (- x1) y1)
	       (/ (+ (- x) y)))
	    (* (+ x1 (- y1))
	       (/ (+ x (- y)))))
   :hints (("Goal"
	    :use ((:instance lemma-2
			     (a y1)
			     (b x1)
			     (c (+ x (- y)))))
	    :in-theory (disable lemma-2)))
   ))

(defthm idfn-inverse-differentiable-part1
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-range))
		  (inside-interval-p y1 (idfn-range))
		  (i-close x y1) (not (= x y1)))
	     (i-limited (/ (- (idfn-inverse x) (idfn-inverse y1)) (- x y1))))
  :hints (("Goal"
	   :use ((:instance idfn-inverse-differentiable-part1-lemma)
		 (:instance expand-differential-idfn-inverse-local
			    (x x)
			    (eps (- y1 x))))
	   :in-theory '(commutativity-of-+
			associativity-of-+
			minus-cancellation-on-left
			fix
			inside-interval-is-real
			lemma-5))))

(local
 (defthm lemma-6
     (implies (and (i-small eps)
		   (equal x (+ eps x)))
	      (equal (equal eps 0) t))
   ))

(defthm close-differential-idfn
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-domain))
		  (inside-interval-p (+ x eps1) (idfn-domain))
		  (inside-interval-p (+ x eps2) (idfn-domain))
		  (i-small eps1) (not (= eps1 0))
		  (i-small eps2) (not (= eps2 0)))
	     (i-close (differential-idfn x eps1)
		      (differential-idfn x eps2)))
  :hints (("Goal"
	   :use ((:instance idfn-differentiable
			    (x x)
			    (y1 (+ x eps1))
			    (y2 (+ x eps2)))
		 (:instance i-close-to-small-sum
			    (x x)
			    (eps eps1))
		 (:instance i-close-to-small-sum
			    (x x)
			    (eps eps2))
		 )
	   :in-theory '(idfn-differentiable
			differential-idfn-definition
			inside-interval-is-real
			lemma-1
			lemma-2
			lemma-6
			=
			fix
			commutativity-of-+
			commutativity-2-of-+
			associativity-of-+
			minus-cancellation-on-left
			distributivity-of-minus-over-+
			))))

(local
 (defthm simplify-minus-/
     (implies (and (acl2-numberp x)
		   (not (equal x 0))
		   (acl2-numberp y)
		   (not (equal y 0)))
	      (equal (+ (/ x) (- (/ y)))
		     (/ (- y x) (* x y))))))

(defthm non-small-non-zero
    (implies (not (i-small x))
	     (equal (equal x 0) nil))
  :rule-classes (:type-prescription :forward-chaining))

(defthm products-of-non-small
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (not (i-small x))
		  (not (i-small y)))
	     (not (i-small (* x y))))
  :hints (("Goal"
	   :use ((:instance small*limited->small
			    (x (* x y))
			    (y (/ x))))
	   :in-theory (enable-disable (i-large) (small*limited->small)))))

(defthm i-close-/-lemma
    (implies (and (i-close x y)
		  (acl2-numberp x)
		  (acl2-numberp y)
		  (not (i-small x))
		  (not (i-small y)))
	     (i-close (/ x) (/ y)))
  :hints (("Goal"
	   :use ((:instance simplify-minus-/)
		 (:instance small*limited->small
			    (x (- y x))
			    (y (/ (* x y)))))
	   :in-theory (enable-disable (i-large
				       i-close)
				      (simplify-minus-/
				       small*limited->small
				       DISTRIBUTIVITY-OF-/-OVER-*))))
  )


(defthm i-close-/
    (implies (and (i-close x y)
		  (not (i-small x))
		  (not (i-small y)))
	     (i-close (/ x) (/ y)))
  :hints (("Goal"
	   :use ((:instance i-close-/-lemma))
	   :in-theory '(i-close))))

(defthm not-small-differential-idfn
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-domain))
		  (inside-interval-p (+ x eps) (idfn-domain))
		  (i-small eps) (not (= eps 0)))
	     (not (i-small (differential-idfn x eps))))
  :hints (("Goal"
	   :use ((:instance idfn-differential-not-small
			    (x x)
			    (y1 (+ x eps)))
		 (:instance i-close-to-small-sum
			    (x x)
			    (eps eps)))
	   :in-theory '(differential-idfn-definition
			inside-interval-is-real
			lemma-2
			lemma-6
			=
			commutativity-of-+
			commutativity-2-of-+
			associativity-of-+
			minus-cancellation-on-left
			distributivity-of-minus-over-+
			fix
			))))

(defthm close-differential-/-idfn
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-domain))
		  (inside-interval-p (+ x eps1) (idfn-domain))
		  (inside-interval-p (+ x eps2) (idfn-domain))
		  (i-small eps1) (not (= eps1 0))
		  (i-small eps2) (not (= eps2 0)))
	     (i-close (/ (differential-idfn x eps1))
		      (/ (differential-idfn x eps2))))
  :hints (("Goal"
	   :use ((:instance close-differential-idfn)
		 (:instance i-close-/
			    (x (differential-idfn x eps1))
			    (y (differential-idfn x eps2))))
	   :in-theory '(not-small-differential-idfn)
	   )))

(local
 (defthm close-small-uminus
     (implies (i-close x y)
	      (i-small (+ (- x) y)))
   :hints (("Goal"
	    :use ((:instance i-small-uminus (x (- x y))))
	    :in-theory (enable-disable (i-close) (i-small-uminus))))))

(defthm idfn-inverse-differentiable-part2-lemma
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-range))
		  (inside-interval-p y1 (idfn-range))
		  (inside-interval-p y2 (idfn-range))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (differential-idfn-inverse-local x (- y1 x))
		      (differential-idfn-inverse-local x (- y2 x))))
  :hints (("Goal"
	   :use ((:instance close-differential-/-idfn
			    (x (idfn-inverse x))
			    (eps1 (- (idfn-inverse y1)
				     (idfn-inverse x)))
			    (eps2 (- (idfn-inverse y2)
				     (idfn-inverse x))))
		 (:instance idfn-inverse-continuous-local
			    (x1 x)
			    (x2 y1))
		 (:instance idfn-inverse-continuous-local
			    (x1 x)
			    (x2 y2))
		 (:instance idfn-inverse-is-1-to-1
			    (y1 x)
			    (y2 y1))
		 (:instance idfn-inverse-is-1-to-1
			    (y1 x)
			    (y2 y2))
		 )
	   :in-theory '(differential-idfn-inverse-local
			standard-idfn-inverse
			idfn-inverse-exists
			commutativity-of-+
			commutativity-2-of-+
			associativity-of-+
			minus-cancellation-on-left
			minus-cancellation-on-right
			fix
			=
			inside-interval-is-real
			idfn-inverse-is-real
			close-small-uminus
			)
	   )))

(defthm idfn-inverse-differentiable-part2
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-range))
		  (inside-interval-p y1 (idfn-range))
		  (inside-interval-p y2 (idfn-range))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (idfn-inverse x) (idfn-inverse y1)) (- x y1))
		      (/ (- (idfn-inverse x) (idfn-inverse y2)) (- x y2))))
  :hints (("Goal"
	   :use ((:instance idfn-inverse-differentiable-part2-lemma)
		 (:instance expand-differential-idfn-inverse-local
			    (x x)
			    (eps (- y1 x)))
		 (:instance expand-differential-idfn-inverse-local
			    (x x)
			    (eps (- y2 x)))
		 )
	   :in-theory '(commutativity-of-+
			associativity-of-+
			minus-cancellation-on-left
			fix
			inside-interval-is-real
			lemma-5))))

(defthm idfn-inverse-differentiable
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-range))
		  (inside-interval-p y1 (idfn-range))
		  (inside-interval-p y2 (idfn-range))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited (/ (- (idfn-inverse x) (idfn-inverse y1)) (- x y1)))
		  (i-close (/ (- (idfn-inverse x) (idfn-inverse y1)) (- x y1))
			   (/ (- (idfn-inverse x) (idfn-inverse y2)) (- x y2)))))
  :hints (("Goal"
	   :use (idfn-inverse-differentiable-part1
		 idfn-inverse-differentiable-part2)
	   :in-theory nil)))

;; Now we define the differential and derivative functions and get the correctness results

(encapsulate
 ( ((differential-idfn-inverse * *) => *) )

 (local
  (defun differential-idfn-inverse (x eps)
    (/ (- (idfn-inverse (+ x eps)) (idfn-inverse x)) eps)))

 (defthm differential-idfn-inverse-definition
   (implies (and (inside-interval-p x (idfn-range))
		 (inside-interval-p (+ x eps) (idfn-range)))
	    (equal (differential-idfn-inverse x eps)
		   (/ (- (idfn-inverse (+ x eps)) (idfn-inverse x)) eps))))
 )

(encapsulate
 ( ((derivative-idfn-inverse *) => *) )

 (defthm limited-derivative-idfn-inverse-body
   (implies
    (standardp x)
    (standardp
     (if (inside-interval-p x (idfn-range))
	 (cond ((inside-interval-p (+ x (/ (i-large-integer)))
				   (idfn-range))
		(standard-part (differential-idfn-inverse x (/ (i-large-integer)))))
	       ((inside-interval-p (+ x (- (/ (i-large-integer))))
				   (idfn-range))
		(standard-part (differential-idfn-inverse x (- (/ (i-large-integer))))))
	       (t 'error))
       'error)))
   :hints (("Goal"
	    :in-theory (disable standard-part-of-plus))
	   ("Subgoal 2"
	    :use ((:instance idfn-inverse-differentiable
			     (x x)
			     (y1 (+ (/ (i-large-integer)) x))
			     (y2 (+ (/ (i-large-integer)) x))))
	    :in-theory (disable idfn-inverse-differentiable standard-part-of-plus))
	   ("Subgoal 1"
	    :use ((:instance idfn-inverse-differentiable
			     (x x)
			     (y1 (- x (/ (i-large-integer))))
			     (y2 (- x (/ (i-large-integer))))))
	    :in-theory (disable idfn-inverse-differentiable standard-part-of-plus))
	   )
   :rule-classes (:built-in-clause)
   )

 (local (in-theory '(limited-derivative-idfn-inverse-body)))

 (local
  (defun-std derivative-idfn-inverse (x)
    (if (inside-interval-p x (idfn-range))
	(if (inside-interval-p (+ x (/ (i-large-integer))) (idfn-range))
	    (standard-part (differential-idfn-inverse x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (idfn-range))
	      (standard-part (differential-idfn-inverse x (- (/ (i-large-integer)))))
	    'error))
      'error)))

 (defthm derivative-idfn-inverse-definition
   (implies (and (inside-interval-p x (idfn-range))
		 (standardp x))
	    (equal (derivative-idfn-inverse x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (idfn-range))
		       (standard-part (differential-idfn-inverse x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (idfn-range))
			 (standard-part (differential-idfn-inverse x (- (/ (i-large-integer)))))
		       'error)))))
 )

(defthm idfn-inverse-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (idfn-range))
		 (i-close x y)
		 (inside-interval-p y (idfn-range)))
	    (i-close (idfn-inverse x) (idfn-inverse y)))

  :hints (("Goal"
	   :by (:functional-instance rdfn-continuous
				     (rdfn idfn-inverse)
				     (rdfn-domain idfn-range)))
	  ("Subgoal 3"
	   :use ((:instance idfn-inverse-differentiable))
	   :in-theory (disable idfn-inverse-differentiable))
	  ("Subgoal 2"
	   :use ((:instance idfn-range-non-trivial)))))

(defthm realp-differential-idfn-inverse
  (implies (and (inside-interval-p x (idfn-range))
		(inside-interval-p (+ x eps) (idfn-range))
		(realp eps))
	   (realp (differential-idfn-inverse x eps)))
  :hints (("Goal"
	   :by (:functional-instance realp-differential-rdfn
				     (differential-rdfn differential-idfn-inverse)
				     (rdfn idfn-inverse)
				     (rdfn-domain idfn-range))
	   :in-theory (enable differential-idfn-inverse-local)
	   )
	  ))

(defthm differential-idfn-inverse-limited
    (implies (and (standardp x)
		  (inside-interval-p x (idfn-range))
		  (inside-interval-p (+ x eps) (idfn-range))
		  (i-small eps))
	     (i-limited (differential-idfn-inverse x eps)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-limited
				     (differential-rdfn differential-idfn-inverse)
				     (rdfn idfn-inverse)
				     (rdfn-domain idfn-range)))))

(in-theory (disable differential-idfn-inverse-definition))

(defthm real-derivative-idfn-inverse
    (implies (inside-interval-p x (idfn-range))
	     (realp (derivative-idfn-inverse x)))
  :hints (("Goal"
	   :by (:functional-instance derivative-well-defined
				     (derivative-rdfn derivative-idfn-inverse)
				     (differential-rdfn differential-idfn-inverse)
				     (rdfn idfn-inverse)
				     (rdfn-domain idfn-range)))))

(defthm differential-idfn-inverse-close
   (implies (and (inside-interval-p x (idfn-range))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (idfn-range))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-idfn-inverse x eps))
		   (derivative-idfn-inverse x)))
  :hints (("Goal"
	   :by (:functional-instance differential-rdfn-close
				     (derivative-rdfn derivative-idfn-inverse)
				     (differential-rdfn differential-idfn-inverse)
				     (rdfn idfn-inverse)
				     (rdfn-domain idfn-range)))))

(in-theory (disable derivative-idfn-inverse-definition))

