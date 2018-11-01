;;
;; This book provides some examples of multivariate continuous functions
;;

; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "metric")

;;
;; f(x, y , z) = x + y + z is continuous
;;
(defun sum (x)
 (+ (nth 0 x) (nth 1 x) (nth 2 x)))

(defthm lemma-1
 (equal (- (sum x) (sum y))
	(+ (- (nth 0 x) (nth 0 y))
	   (- (nth 1 x) (nth 1 y))
	   (- (nth 2 x) (nth 2 y)))))

(defthm lemma-2
 (implies (and (i-small x) (i-small y) (i-small z))
	  (i-small (+ x y z))))

(defthm sum-is-continuous
 (implies (and (real-listp x) (real-listp y) (= (len x) 3) (= (len y) (len x)) 
	       (i-small (eu-metric x y)))
	  (i-small (- (sum x) (sum y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable eu-metric-metric-sq-equivalence)
		 :use ((:instance lemma-1)
		       (:instance lemma-2 
		        	  (x (- (nth 0 x) (nth 0 y)))
		        	  (y (- (nth 1 x) (nth 1 y)))
		        	  (z (- (nth 2 x) (nth 2 y))))
		       (:instance eu-metric-i-small-implies-difference-of-entries-i-small (i 0))
		       (:instance eu-metric-i-small-implies-difference-of-entries-i-small (i 1))
		       (:instance eu-metric-i-small-implies-difference-of-entries-i-small (i 2))))))


;;
;; g(x,y) = xy is continuous
;;
(defun prod (x)
 (* (nth 0 x) (nth 1 x)))


(defthm lemma-3
 (implies (and (realp x) (realp a) (realp y) (realp b))
	  (equal (- (* x y) (* a b))
		 (+ (* x (- y b)) (* b (- x a))))))
(defthm lemma-4
 (implies (and (realp x) (realp a) (realp y) (realp b) 
	       (i-limited x) (i-limited b)
	       (i-small (- x a)) (i-small (- y b)))
	  (i-small (+ (* x (- y b)) (* b (- x a)))))
 :hints (("GOAL" :in-theory (disable distributivity)
		 :use ((:instance limited*small->small (y (- y b)))
		       (:instance limited*small->small (x b) (y (- x a))))))
 :rule-classes nil)

(defthm lemma-5
 (implies (and (realp x) (realp a) (realp y) (realp b) 
	       (i-limited x) (i-limited b)
	       (i-small (- x a)) (i-small (- y b)))
	  (i-small (- (* x y) (* a b))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable distributivity)
		 :use ((:instance lemma-3)
		       (:instance lemma-4))))
 :rule-classes nil)

(defthm prod-is-continuous
 (implies (and (real-listp x) (real-listp y) 
	       (= (len x) 2) (= (len y) (len x))
	       (i-limited (eu-norm x)) (i-limited (eu-norm y))
	       (i-small (eu-metric x y)))
	  (i-small (- (prod x) (prod y))))
 :hints (("GOAL" :use ((:instance eu-metric-i-small-implies-difference-of-entries-i-small (i 0))
		       (:instance eu-metric-i-small-implies-difference-of-entries-i-small (i 1))
		       (:instance eu-norm-i-limited-implies-entries-i-limited (vec x) (i 0))
		       (:instance eu-norm-i-limited-implies-entries-i-limited (vec y) (i 0))
		       (:instance lemma-5 
				  (x (nth 0 x))
				  (y (nth 1 x))
				  (a (nth 0 y))
				  (b (nth 1 y)))))))

