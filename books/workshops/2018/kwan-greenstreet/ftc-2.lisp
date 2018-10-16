;; This book is mostly the same as ftc-2.lisp from the integral books
;; with some minor modifications to pass the FTC for the desired 
;; functions.

; cert_param: (uses-acl2r)

(in-package "ACL2")

;;
;; A rather inelegant work-around for passing some theorems that don't
;; pass when including the nsa books.
;;

(local (defthm i-close-sums
        (implies (and (realp a) (realp b) (realp c) 
		      (i-close b c))
		 (i-close (+ a b) (+ a c)))
	:rule-classes nil))


(encapsulate
 ()

(local (include-book "arithmetic/idiv" :dir :system))
(local (defthm lemma-1
        (implies (and (realp a) (i-limited a))
		 (= (standard-part (* (/ 2) a))
		    (* (/ 2) (standard-part a))))
	:rule-classes nil))

(local (defthm i-small-udivide
  (implies (and (i-small x)
		(not (equal x 0)))
	   (i-large (/ x)))
 :rule-classes nil))

(defthm i-close-coeff
        (implies (and (realp b) (realp c) (i-limited b) (i-limited c)
		      (i-close b c))
		 (i-close (* (/ 2) b) (* (/ 2) c)))
	:rule-classes nil
	:hints (("GOAL" :use ((:instance lemma-1 (a b))
			      (:instance i-small-udivide (x (/ c)))
			      (:instance lemma-1 (a c))))))
)
;; inelegant work-around done
;;
;;

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))
(include-book "nonstd/nsa/derivatives" :dir :system)
(include-book "nonstd/integrals/continuous-function" :dir :system)
(include-book "nonstd/integrals/ftc-1" :dir :system)

(in-theory (disable expt))
(defun svfn-2 (x)  (* (realfix x) (realfix x) (/ 2)))
(defun svfn-2-domain () (interval 0 1))

(encapsulate
 ()

(encapsulate
 ( ((rcdfn *) => *)
   ((rcdfn-prime *) => *)
   ((rcdfn-domain) => *)
   )

   (local (defun rcdfn (x)  (* (realfix x) (realfix x) (/ 2))))
   (local (defun rcdfn-prime (x)  (realfix x)))
   (local (defun rcdfn-domain () (interval 0 1)))

   (defthm svfn-2-rcdfn-equivalence 
    (= (svfn-2 x) (rcdfn x)))

   (defthm svfn-rcdfn-domain-equivalence 
    (= (rcdfn-domain) (svfn-2-domain)))
   (in-theory (disable svfn-rcdfn-domain-equivalence))

   (defthm intervalp-rcdfn-domain
     (interval-p (rcdfn-domain))
   :rule-classes (:type-prescription :rewrite))

   (defthm rcdfn-domain-real
     (implies (inside-interval-p x (rcdfn-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

   (defthm rcdfn-domain-non-trivial
     (or (null (interval-left-endpoint (rcdfn-domain)))
	 (null (interval-right-endpoint (rcdfn-domain)))
	 (< (interval-left-endpoint (rcdfn-domain))
	    (interval-right-endpoint (rcdfn-domain))))
     :rule-classes nil)

   (defthm rcdfn-real
     (realp (rcdfn x))
   :rule-classes (:rewrite :type-prescription))

   (defthm rcdfn-prime-real
     (realp (rcdfn-prime x))
   :rule-classes (:rewrite :type-prescription))

(local 
(defthm lemma-1 
 (implies (and (standardp X)
 	       (I-CLOSE X X1)
	       (realp X)
	       (realp X1)
               (NOT (EQUAL X X1)))
          (equal (- (* x x (/ 2))
                    (* x1 x1 (/ 2)))
		 (* (/ 2) (- x x1) (+ x x1))))))

(local (defthm lemma-2
	(implies (and (realp a) (realp b) (realp c) (not (= c 0)) (= a b))
		 (= (/ a c) (/ b c)))
	:rule-classes nil))

(local 
(defthm lemma-3
 (implies (and (standardp X)
 	       (I-CLOSE X X1)
	       (realp X)
	       (realp X1)
               (NOT (EQUAL X X1)))
          (equal (/ (- (* x x (/ 2)) 
                       (* x1 x1 (/ 2)))
		    (- x x1))
		 (/ (* (/ 2) (- x x1) (+ x x1))
		    (- x x1))))
 :hints (("GOAL" :use ((:instance lemma-1)
		       (:instance lemma-2 (a (- (* x x (/ 2))
                    			     	(* x1 x1 (/ 2))))
					  (b (* (/ 2) (- x x1) (+ x x1)))
					  (c (- x x1))))))))

(local 
(defthm lemma-4
 (implies (and (standardp X)
 	       (I-CLOSE X X1)
	       (realp X)
	       (realp X1)
               (NOT (EQUAL X X1)))
          (equal (/ (- (* x x (/ 2)) 
                       (* x1 x1 (/ 2)))
		    (- x x1))
		 (* (/ 2) (+ x x1))))
 :hints (("GOAL" :use (:instance lemma-3)))))

(local 
(defthm lemma-5
 (implies (and (standardp X)
 	       (I-CLOSE X X1)
	       (realp X)
	       (realp X1)
               (NOT (EQUAL X X1)))
          (i-close (/ (- (* x x (/ 2)) 
                         (* x1 x1 (/ 2)))
		      (- x x1))
		   (* (/ 2) (+ x x1))))
 :hints (("GOAL" :use (:instance lemma-4)))))

(local 
(defthm lemma-8
 (implies (and (standardp X)
 	       (I-CLOSE X X1)
	       (realp X)
	       (realp X1)
               (NOT (EQUAL X X1)))
          (i-close (+ x x1) (+ x x)))
 :hints (("GOAL" :use ((:instance i-close-sums (a x) (b x1) (c x)))))))

(local 
(defthm lemma-9
 (implies (and (standardp X)
 	       (I-CLOSE X X1)
	       (realp X)
	       (realp X1)
               (NOT (EQUAL X X1)))
          (i-close (* (/ 2) (+ x x1)) (* (/ 2) (+ x x))))
 :hints (("GOAL" 
		 :use ((:instance lemma-8)
		       (:instance standards-are-limited-forward)
		       (:instance i-close-limited (y x1))
		       (:instance i-close-coeff (b (+ x x1)) (c (+ x x))))))))

(local 
(defthm lemma-10
 (implies (and (standardp X)
 	       (I-CLOSE X X1)
	       (realp X)
	       (realp X1)
               (NOT (EQUAL X X1)))
          (i-close (/ (- (* x x (/ 2)) 
                         (* x1 x1 (/ 2)))
		      (- x x1))
		   (* (/ 2) (+ x x))))
 :hints (("GOAL" :use ((:instance lemma-5)
		       (:instance lemma-9))))))

   (defthm rcdfn-prime-is-derivative
     (implies (and (standardp x)
		   (inside-interval-p x (rcdfn-domain))
		   (inside-interval-p x1 (rcdfn-domain))
		   (i-close x x1) (not (= x x1)))
	      (i-close (/ (- (rcdfn x) (rcdfn x1)) (- x x1))
		       (rcdfn-prime x)))
     :hints (("GOAL" :use ((:instance lemma-10)))))

   (defthm rcdfn-prime-continuous
     (implies (and (standardp x)
		   (inside-interval-p x (rcdfn-domain))
		   (i-close x x1)
		   (inside-interval-p x1 (rcdfn-domain)))
	      (i-close (rcdfn-prime x)
		       (rcdfn-prime x1))))
   )

(defun map-rcdfn-prime (p)
  (if (consp p)
      (cons (rcdfn-prime (car p))
	    (map-rcdfn-prime (cdr p)))
    nil))

(defun riemann-rcdfn-prime (p)
  (dotprod (deltas p)
	   (map-rcdfn-prime (cdr p))))

(defthm realp-riemann-rcdfn-prime
  (implies (partitionp p)
	   (realp (riemann-rcdfn-prime p))))

(encapsulate
 nil

 (local
  (defthm limited-riemann-rcdfn-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (rcdfn-domain))
		  (inside-interval-p b (rcdfn-domain))
		  (< a b))
	     (i-limited (riemann-rcdfn-prime (make-small-partition a b))))
    :hints (("Goal"
	     :by (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain rcdfn-domain)
				       (rcfn rcdfn-prime)
				       (map-rcfn map-rcdfn-prime)
				       (riemann-rcfn riemann-rcdfn-prime)))
	    ("Subgoal 2"
	     :use ((:instance rcdfn-domain-non-trivial))))))

 (local (in-theory (disable riemann-rcdfn-prime)))



 (defun-std strict-int-rcdfn-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (rcdfn-domain))
	    (inside-interval-p b (rcdfn-domain))
	    (< a b))
       (standard-part (riemann-rcdfn-prime (make-small-partition a b)))
     0))
 )

(defun int-rcdfn-prime (a b)
  (if (<= a b)
      (strict-int-rcdfn-prime a b)
    (- (strict-int-rcdfn-prime b a))))

(defthm strict-int-rcdfn-prime-is-integral-of-rcdfn-prime
  (implies (and (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (rcdfn-domain))
		(inside-interval-p b (rcdfn-domain))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rcdfn-prime p)
		    (strict-int-rcdfn-prime a b)))
  :hints (("Goal"
	   :do-not-induct t
	   :by (:functional-instance strict-int-rcfn-is-integral-of-rcfn
				     (rcfn-domain rcdfn-domain)
				     (int-rcfn int-rcdfn-prime)
				     (rcfn rcdfn-prime)
				     (map-rcfn map-rcdfn-prime)
				     (riemann-rcfn riemann-rcdfn-prime)
				     (strict-int-rcfn strict-int-rcdfn-prime))
	   )
	  ("Subgoal 2"
	   :use ((:instance rcdfn-domain-non-trivial)))
	  ))

(defthmd ftc-1-for-rcdfn
  (implies (and (inside-interval-p a (rcdfn-domain))
		(inside-interval-p b (rcdfn-domain))
		(inside-interval-p c (rcdfn-domain))
		(standardp b)
		(i-close b c)
		(not (equal b c)))
	   (i-close (/ (- (int-rcdfn-prime a b) (int-rcdfn-prime a c))
		       (- b c))
		    (rcdfn-prime b)))
  :hints (("Goal"
	   :by (:functional-instance ftc-1
				     (rcfn-domain rcdfn-domain)
				     (int-rcfn int-rcdfn-prime)
				     (rcfn rcdfn-prime)
				     (map-rcfn map-rcdfn-prime)
				     (riemann-rcfn riemann-rcdfn-prime)
				     (strict-int-rcfn strict-int-rcdfn-prime)
				     ))
	   ))

(local
 (defun diff-fn (a x)
   (if (inside-interval-p a (rcdfn-domain))
       (- (int-rcdfn-prime a x) (rcdfn x))
     0
     )))

(local
 (defthmd close-plus-constant
   (implies (i-close x y)
	    (i-close (+ x z) (+ y z)))
 :hints (("Goal"
	  :use ((:instance i-small-plus
			   (x (- x y))
			   (y z)))
	  :in-theory (e/d (i-close)
			  (i-small-plus))))
 ))

(local
 (defthmd close-plus
   (implies (and (i-close x1 x2)
		 (i-close y1 y2))
	    (i-close (+ x1 y1) (+ x2 y2)))
 :hints (("Goal"
	  :use ((:instance i-small-plus
			   (x (- x1 x2))
			   (y (- y1 y2))))
	  :in-theory (e/d (i-close)
			  (i-small-plus))))
 ))

(local
 (defthmd close-minus
   (implies (and (i-close x1 x2)
		 (i-close y1 y2))
	    (i-close (- x1 y1) (- x2 y2)))
 :hints (("Goal"
	  :use ((:instance i-small-plus
			   (x (- x1 x2))
			   (y (- (- y1 y2))))
		(:instance i-small-uminus
			   (x (- y1 y2)))
		)
	  :in-theory (e/d (i-close)
			  (i-small-plus i-small-uminus))))
 ))

(local
 (defthmd diff-fn-has-zero-derivative-1
   (implies (and (standardp x)
		 (inside-interval-p x (rcdfn-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (rcdfn-domain))
		 (not (equal x x1)))
	    (i-close (/ (- (diff-fn a x) (diff-fn a x1)) (- x x1))
		     0))
   :hints (("Goal"
	    :use ((:instance ftc-1-for-rcdfn
			     (a a)
			     (b x)
			     (c x1))
		  (:instance rcdfn-prime-is-derivative)
		  (:instance close-minus
			     (y1 (+ (* (rcdfn x) (/ (+ x (- x1))))
				    (- (* (rcdfn x1) (/ (+ x (- x1)))))))
			     (y2 (rcdfn-prime x))
			     (x1 (+ (* (int-rcdfn-prime a x)
				       (/ (+ x (- x1))))
				    (- (* (int-rcdfn-prime a x1)
					  (/ (+ x (- x1)))))))
			     (x2 (rcdfn-prime x))))
	    :in-theory (disable rcdfn-prime-is-derivative
				i-small-uminus
				int-rcdfn-prime
				)))
   ))

(local
 (encapsulate
  nil

  (local
   (defthm derivative-diff-fn-lemma
     (IMPLIES
      (AND (STANDARDP A) (STANDARDP X))
      (STANDARDP
       (IF (INSIDE-INTERVAL-P X (RCDFN-DOMAIN))
	   (COND ((INSIDE-INTERVAL-P (+ X (/ (I-LARGE-INTEGER)))
				     (RCDFN-DOMAIN))
		  (STANDARD-PART (* (+ (DIFF-FN A (+ X (/ (I-LARGE-INTEGER))))
				       (- (DIFF-FN A X)))
				    (/ (/ (I-LARGE-INTEGER))))))
		 ((INSIDE-INTERVAL-P (+ X (- (/ (I-LARGE-INTEGER))))
				     (RCDFN-DOMAIN))
		  (STANDARD-PART (* (+ (DIFF-FN A (+ X (- (/ (I-LARGE-INTEGER)))))
				       (- (DIFF-FN A X)))
				    (/ (- (/ (I-LARGE-INTEGER)))))))
		 (T 'error))
	   'error)))
     :hints (("Goal"
	      :use ((:instance diff-fn-has-zero-derivative-1
			       (a a)
			       (x x)
			       (x1 (+ x (/ (i-large-integer)))))
		    (:instance diff-fn-has-zero-derivative-1
			       (a a)
			       (x x)
			       (x1 (- x (/ (i-large-integer)))))
		    (:instance i-close-to-small-sum
			       (x x)
			       (eps (/ (i-large-integer))))
		    (:instance i-close-to-small-sum
			       (x x)
			       (eps (- (/ (i-large-integer)))))
		    (:instance i-close-limited
			       (x 0)
			       (y (/ (+ (DIFF-FN A X)
					(- (DIFF-FN A (+ X (/ (I-LARGE-INTEGER))))))
				     (- (/ (I-LARGE-INTEGER))))))
		    (:instance i-close-limited
			       (x 0)
			       (y (/ (+ (DIFF-FN A X)
					(- (DIFF-FN A (+ X (- (/ (I-LARGE-INTEGER)))))))
				     (/ (I-LARGE-INTEGER)))))
		    )
	      :in-theory (disable diff-fn
				  i-close-to-small-sum
				  i-close-limited
				  standard-part-of-plus
				  standard-part-of-uminus)
	      ))
     ;:rule-classes :rewrite
     ))

  (defun differential-diff-fn (a x eps)
    (/ (- (diff-fn a (+ x eps)) (diff-fn a x)) eps))

  (local
   (in-theory '(derivative-diff-fn-lemma
		differential-diff-fn)))

  (defun-std derivative-diff-fn (a x)
    (if (inside-interval-p x (rcdfn-domain))
	(if (inside-interval-p (+ x (/ (i-large-integer))) (rcdfn-domain))
	    (standard-part (differential-diff-fn a x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (rcdfn-domain))
	      (standard-part (differential-diff-fn a x (- (/ (i-large-integer)))))
	    'error))
      'error)
    )
  )
 )

(local
 (defthm-std standard-rcdfn-domain
   (standardp (rcdfn-domain))))

(local
 (defthm-std standard-rcdfn-domain-left-endpoint
   (standardp (interval-left-endpoint (rcdfn-domain)))))

(local
 (defthm-std standard-rcdfn-domain-right-endpoint
   (standardp (interval-right-endpoint (rcdfn-domain)))))

(local
 (defthm standard-part-eps
   (implies (i-small eps)
	    (equal (standard-part eps) 0))
   :hints (("Goal"
	    :in-theory (enable i-small)))
   ))

(local
 (defthmd x-in-interval-implies-x+-eps-in-interval-1
   (implies (and (realp x)
		 (standardp x)
		 (realp x1)
		 (standardp x1)
		 (< x1 x)
		 (realp eps)
		 (i-small eps))
	    (< x1
	       (+ x eps)))
   :hints (("Goal"
	    :use ((:instance standard-part-<-2
			     (x x1)
			     (y (+ x eps))))))))

(local
 (defthmd x-in-interval-implies-x+-eps-in-interval-2
   (implies (and (realp x)
		 (standardp x)
		 (realp x2)
		 (standardp x2)
		 (< x x2)
		 (realp eps)
		 (i-small eps))
	    (< (+ x eps)
	       x2))
   :hints (("Goal"
	    :use ((:instance standard-part-<-2
			     (x (+ x eps))
			     (y x2)))))))

(local
 (defthm x-in-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-left-endpoint interval)))
		 (not (realp (interval-right-endpoint interval))))
	    (inside-interval-p x interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-left-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-left-endpoint interval)))
		 (inside-interval-p y interval)
		 (< x y))
	    (inside-interval-p x interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-right-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-right-endpoint interval)))
		 (inside-interval-p y interval)
		 (> x y))
	    (inside-interval-p x interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm nil-not-in-interval
   (implies (and (not x)
		 (interval-p interval))
	    (not (inside-interval-p x interval)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-interval-implies-x+-eps-in-interval
   (implies (and (inside-interval-p x (rcdfn-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (rcdfn-domain))
		(inside-interval-p (- x eps) (rcdfn-domain))))
   :hints (("Goal"
	    :use ((:instance rcdfn-domain-non-trivial)
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps eps)
			     (x1 (interval-left-endpoint (rcdfn-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps (- eps))
			     (x1 (interval-left-endpoint (rcdfn-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps eps)
			     (x2 (interval-right-endpoint (rcdfn-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps (- eps))
			     (x2 (interval-right-endpoint (rcdfn-domain))))
		  )
	    )
	   ("Subgoal 7"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 4"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 3"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 1"
	    :in-theory (enable interval-definition-theory))
	   )
   :rule-classes nil
   ))


(local
 (defthmd close-minus-0
   (equal (i-close (- x) 0)
	  (i-close (fix x) 0))
   :hints (("Goal"
	    :in-theory (enable i-close)))))

(local
 (defthm close-0-standard-part-0
   (implies (i-close x 0)
	    (equal (standard-part x) 0))
   :hints (("Goal"
	    :use ((:instance close-x-y->same-standard-part
			     (x 0)
			     (y x)))
	    :in-theory (disable close-x-y->same-standard-part)))))

(local
 (defthm-std derivative-diff-is-zero
   (implies (inside-interval-p x (rcdfn-domain))
	    (equal (derivative-diff-fn a x) 0))
   :hints (("Goal"
	    :use ((:instance x-in-interval-implies-x+-eps-in-interval
			     (eps (/ (i-large-integer))))
		  (:instance diff-fn-has-zero-derivative-1
			     (x x)
			     (x1 (+ x (/ (i-large-integer)))))
		  (:instance diff-fn-has-zero-derivative-1
			     (x x)
			     (x1 (+ x (- (/ (i-large-integer))))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (- (/ (i-large-integer)))))
		  (:instance close-minus-0
			     (x (+ (- (* (i-large-integer) (diff-fn a x)))
				   (* (i-large-integer)
				      (diff-fn a (+ (/ (i-large-integer)) x))))))
		  (:instance close-minus-0
			     (x (+ (- (* (i-large-integer) (diff-fn a x)))
				   (* (i-large-integer)
				      (diff-fn a (+ (- (/ (i-large-integer))) x)))))))
	    :in-theory (disable diff-fn
				standard-part-of-plus
				i-close-to-small-sum)
	    ))))

(encapsulate
 ((rcdfn-subdomain () t))

 (local
  (defun rcdfn-subdomain ()
    (let ((left (interval-left-endpoint (rcdfn-domain)))
	  (right (interval-right-endpoint (rcdfn-domain))))
      (if (null left)
	  (if (null right)
	      (interval 0 1)
	      (interval (- right 2) (- right 1)))
	  (if (null right)
	      (interval (+ left 1) (+ left 2))
	      (interval (+ left (* 1/3 (- right left)))
			(+ left (* 2/3 (- right left)))))))))

 (defthm rcdfn-subdomain-is-subdomain
     (subinterval-p (rcdfn-subdomain) (rcdfn-domain))
   :hints (("Goal"
	    :use ((:instance interval-p (interval (rcdfn-domain))))
	    :in-theory (enable interval-definition-theory))
	   ))

 (defthm rcdfn-subdomain-closed-bounded
     (and (interval-left-inclusive-p (rcdfn-subdomain))
	  (interval-right-inclusive-p (rcdfn-subdomain))))

 (defthm rcdfn-subdomain-real-left
     (realp (interval-left-endpoint (rcdfn-subdomain)))
   :rule-classes (:rewrite :type-prescription))

 (defthm rcdfn-subdomain-real-right
     (realp (interval-right-endpoint (rcdfn-subdomain)))
   :rule-classes (:rewrite :type-prescription))

 (defthm rcdfn-subdomain-non-trivial
     (< (interval-left-endpoint (rcdfn-subdomain))
	(interval-right-endpoint (rcdfn-subdomain)))
   :hints (("Goal"
	    :use (:instance rcdfn-domain-non-trivial)))
   )
 )

(local
 (defun-sk exists-mvt-point-for-diff-fn ()
   (exists (x)
	   (and (inside-interval-p x (rcdfn-subdomain))
		(not (equal x (interval-left-endpoint (rcdfn-subdomain))))
		(not (equal x (interval-right-endpoint (rcdfn-subdomain))))
		(equal (derivative-diff-fn (interval-left-endpoint (rcdfn-subdomain)) x)
		       (/ (- (diff-fn (interval-left-endpoint (rcdfn-subdomain))
				      (interval-right-endpoint (rcdfn-subdomain)))
			     (diff-fn (interval-left-endpoint (rcdfn-subdomain))
				      (interval-left-endpoint (rcdfn-subdomain))))
			  (- (interval-right-endpoint (rcdfn-subdomain))
			     (interval-left-endpoint (rcdfn-subdomain)))))))))

(local
 (defthm-std rcdfn-prime-standard
   (implies (standardp x)
	    (standardp (rcdfn-prime x)))))

(local
 (defthm left-endpoint-in-domain
   (inside-interval-p (interval-left-endpoint (rcdfn-subdomain))
                                  (rcdfn-domain))
   :hints (("Goal"
	    :use ((:instance rcdfn-subdomain-is-subdomain)
		  (:instance rcdfn-subdomain-closed-bounded)
		  (:instance rcdfn-subdomain-real-left))
	    :in-theory (e/d (interval-definition-theory)
			    (rcdfn-subdomain-is-subdomain
			     rcdfn-subdomain-closed-bounded
			     rcdfn-subdomain-real-left))))))

(local
 (defthm close-0-not-large
   (implies (i-close x 0)
	    (not (i-large x)))
   :hints (("Goal"
	    :in-theory (enable i-close)))))

(local
 (defthm realp-strict-int-rcdfn-prime
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rcdfn-prime a b)))
   :hints (("Goal"
	    :by (:functional-instance realp-strict-int-rcfn
				      (strict-int-rcfn strict-int-rcdfn-prime)
                                      (rcfn-domain rcdfn-domain)
                                      (rcfn rcdfn-prime)
				      (riemann-rcfn riemann-rcdfn-prime)
				      (map-rcfn map-rcdfn-prime))))))

(local
 (defthm-std realp-strict-int-rcdfn-prime-stronger
   (realp (strict-int-rcdfn-prime a b))
   :hints (("Goal"
	    :cases ((not (realp a))
		    (not (realp b))))
	   ("Subgoal 3"
	    :use ((:instance realp-strict-int-rcdfn-prime)))
	   )))

(local
 (defthm realp-int-rcdfn-prime
   (realp (int-rcdfn-prime a b))
   ))

(local
 (defthm realp-left-endpoint
   (realp (interval-left-endpoint (rcdfn-subdomain)))
   ))

(local
 (defthm-std standard-left-endpoint-subdomain
   (standardp (INTERVAL-LEFT-ENDPOINT (RCDFN-SUBDOMAIN)))))

(local
 (defthm mvt-theorem-sk-for-diff-fn
   (exists-mvt-point-for-diff-fn)
   :hints (("Goal"
	    :by (:functional-instance mvt-theorem-sk
				      (exists-mvt-point exists-mvt-point-for-diff-fn)
				      (exists-mvt-point-witness exists-mvt-point-for-diff-fn-witness)
				      (rdfn-domain rcdfn-domain)
				      (rdfn-subdomain rcdfn-subdomain)
				      (rdfn (lambda (x)
					      (diff-fn (interval-left-endpoint (rcdfn-subdomain))
						       x)))
				      (derivative-rdfn (lambda (x)
							 (derivative-diff-fn
							  (interval-left-endpoint (rcdfn-subdomain))
							  x)))
				      (differential-rdfn
				       (lambda (x eps)
					 (differential-diff-fn
					  (interval-left-endpoint (rcdfn-subdomain))
					  x
					  eps)))
				      )
	    )
	   ("Subgoal 8"
	    :use ((:instance exists-mvt-point-for-diff-fn-suff))
	    :in-theory (disable exists-mvt-point-for-diff-fn-suff)
	    )
	   ("Subgoal 6"
	    :use ((:instance diff-fn-has-zero-derivative-1
			     (a (interval-left-endpoint (rcdfn-subdomain)))
			     (x x)
			     (x1 y1))
		  (:instance diff-fn-has-zero-derivative-1
			     (a (interval-left-endpoint (rcdfn-subdomain)))
			     (x x)
			     (x1 y2))
		  )
	    :in-theory (disable diff-fn-has-zero-derivative-1
				diff-fn)
	    )
	   ("Subgoal 4"
	    :use ((:instance rcdfn-domain-non-trivial)))
	   ("Subgoal 2"
	    :in-theory (disable differential-diff-fn
				derivative-diff-is-zero))
	   )))

(local
 (defthm strict-int-rcdfn-prime-a-a
   (implies (inside-interval-p a (rcdfn-domain))
	    (equal (strict-int-rcdfn-prime a a) 0))
   :hints (("Goal"
	    :by (:functional-instance strict-int-a-a
				      (strict-int-rcfn strict-int-rcdfn-prime)
				      (rcfn-domain rcdfn-domain)
				      (rcfn rcdfn-prime)
				      (riemann-rcfn riemann-rcdfn-prime)
				      (map-rcfn map-rcdfn-prime))))))

(local
 (defthm diff-fn-of-a
   (equal (diff-fn a a)
	  (if (inside-interval-p a (rcdfn-domain))
	      (- (rcdfn a))
	    0))))


(local
 (defthm int-rcdfn-prime-a-a
   (implies (inside-interval-p a (rcdfn-domain))
	    (equal (int-rcdfn-prime a a) 0))
   :hints (("Goal"
	    :use ((:instance strict-int-rcdfn-prime-a-a))
	    :in-theory (e/d (int-rcdfn-prime)
			    (strict-int-rcdfn-prime-a-a
			     strict-int-rcdfn-prime
			     (int-rcdfn-prime)))))
   ))

(local
 (defthm diff-fn-inside-interval
   (equal (diff-fn (interval-left-endpoint (rcdfn-subdomain))
		   (interval-right-endpoint (rcdfn-subdomain)))
	  (- (rcdfn (interval-left-endpoint (rcdfn-subdomain)))))
   :hints (("Goal"
	    :use ((:instance mvt-theorem-sk-for-diff-fn)
		  (:instance exists-mvt-point-for-diff-fn)
		  (:instance derivative-diff-is-zero
			     (a (interval-left-endpoint (rcdfn-subdomain)))
			     (x (exists-mvt-point-for-diff-fn-witness))))
	    :in-theory (disable int-rcdfn-prime))
	   ("Subgoal 2"
	    :use ((:instance rcdfn-subdomain-non-trivial))
	    :in-theory (disable rcdfn-subdomain-non-trivial))
	   )
   ))



(local
 (defthm diff-fn-expander
   (implies (and (inside-interval-p a (rcdfn-domain))
		 (inside-interval-p b (rcdfn-domain))
		 (< a b))
	    (equal (diff-fn a b)
		   (- (rcdfn a))))
   :hints (("Goal"
	    :use ((:functional-instance diff-fn-inside-interval
					(rcdfn-subdomain (lambda ()
							   (if (and (inside-interval-p a (rcdfn-domain))
								    (inside-interval-p b (rcdfn-domain))
								    (< a b))
							       (interval a b)
							     (rcdfn-subdomain))
							     ))))))))


(local
 (defthm ftc-2-lemma
   (implies (and (inside-interval-p a (rcdfn-domain))
		 (inside-interval-p b (rcdfn-domain))
		 (< a b))
	    (equal (int-rcdfn-prime a b)
		   (- (rcdfn b)
		      (rcdfn a))))
   :hints (("Goal"
	    :use ((:instance diff-fn-expander))
	    :in-theory (disable int-rcdfn-prime
				diff-fn-expander)
	    ))))

(local
 (defthmd int-rcdfn-reverse-bounds
   (implies (and (inside-interval-p a (rcdfn-domain))
		 (inside-interval-p b (rcdfn-domain)))
	    (equal (- (int-rcdfn-prime b a))
		   (int-rcdfn-prime a b)))))

(local
 (defthm ftc-2-lemma-2
   (implies (and (inside-interval-p a (rcdfn-domain))
		 (inside-interval-p b (rcdfn-domain))
		 (> a b))
	    (equal (int-rcdfn-prime a b)
		   (- (rcdfn b)
		      (rcdfn a))))
   :hints (("Goal"
	    :use ((:instance ftc-2-lemma (a b) (b a))
		  (:instance int-rcdfn-reverse-bounds)
		  )
	    :in-theory (disable int-rcdfn-prime
				ftc-2-lemma)
	    ))))

(defthm ftc-2
  (implies (and (inside-interval-p a (rcdfn-domain))
		(inside-interval-p b (rcdfn-domain)))
	   (equal (int-rcdfn-prime a b)
		  (- (rcdfn b)
		     (rcdfn a))))
   :hints (("Goal"
	    :cases ((< a b) (> a b))
	    :in-theory (disable int-rcdfn-prime
				(int-rcdfn-prime)))))


(defthm svfn-2-ftc-2
  (implies (and (inside-interval-p a (rcdfn-domain))
		(inside-interval-p b (rcdfn-domain)))
	   (equal (int-rcdfn-prime a b)
		  (- (svfn-2 b)
		     (svfn-2 a))))
   :hints (("Goal"
	    :use ((:instance ftc-2)
		  (:instance svfn-2-rcdfn-equivalence))
	    :in-theory (disable svfn-2))))
		
)
