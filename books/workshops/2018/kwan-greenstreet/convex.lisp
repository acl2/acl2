; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "metric")

;;
;; The identity function is convex 
;;

(defun id-fn (x) (realfix x))

(defthm id-fn-is-convex
 (implies (and (realp x) (realp y) (realp a) (<= 0 a) (<= a 1))
  	  (<= (id-fn (+ (* a x) (* (- 1 a) y)))
	      (+ (* a (id-fn x)) (* (- 1 a) (id-fn y))))))

;;
;; The square function is convex
;;

(defun square-fn (x) (* (realfix x) (realfix x)))

;; to show square-fn is convex, we show
;; 0 <= a x^2 + ( 1 - a ) y^2 - ( a x + ( 1 - a ) y )^2
(encapsulate
 nil

;; ax^2 + (1-a)y^2 - (ax + (1-a)y)^2 = a(1-a)(x-y)^2 
(local (defthm lemma-1
 (implies (and (realp x) (realp y) (realp a) (<= 0 a) (<= a 1))
	  (equal (- (+ (* a (square-fn x)) (* (- 1 a) (square-fn y)))
		    (square-fn (+ (* a x) (* (- 1 a) y))))
		 (* a (- 1 a) (square-fn (- x y)))))))

(defthm square-fn-positivity
 (<= 0 (square-fn x)))

(local (defthm lemma-2
 (implies (and (realp a) (<= 0 a))
	  (<= 0 (* a (square-fn x))))))

(defthm square-fn-is-convex
 (implies (and (realp x) (realp y) (realp a) (<= 0 a) (<= a 1))
	  (<= (square-fn (+ (* a x) (* (- 1 a) y)))
	      (+ (* a (square-fn x)) (* (- 1 a) (square-fn y)))))
 :hints (("GOAL" :use ((:instance lemma-2
				  (a (* a (- 1 a)))
				  (x (- x y)))))))
)

 
;;
;; the Euclidean norm, eu-norm, is convex
;;

(encapsulate
 nil

(in-theory (disable eu-metric-metric-sq-equivalence eu-norm))

;; apply triange inequality to obtain
;; || a x + ( 1 - a ) y || <= || a x || + || ( 1 - a ) y ||
(local (defthm lemma-1
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) 
	       (realp a) (<= 0 a)); (<= a 1))
	  (<= (eu-norm (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))
	      (+ (eu-norm (scalar-* a x)) (eu-norm (scalar-* (- 1 a) y)))))
 :hints (("GOAL" :use ((:instance scalar-*-closure (a (- 1 a)) (vec y))
		       (:instance scalar-*-closure (vec x))
		       (:instance triangle-inequality 
				  (x (scalar-* a x)) 
				  (y (scalar-* (- 1 a) y))))))))

;; || ax + (1-a)y || <= a || x || + (1-a) || y ||
(defthm eu-norm-is-convex
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) 
	       (realp a) (<= 0 a) (<= a 1))
	  (<= (eu-norm (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))
	      (+ (* a (eu-norm x)) (* (- 1 a) (eu-norm y)))))
 :hints (("GOAL" :use ((:instance lemma-1)))))
)


;;
;; sum of convex functions is convex
;; affine composition of convex functions is convex 
;; 	(under certain conditions)
;;

(encapsulate
 (((cvfn-1 *) => *)
  ((cvfn-2 *) => *)
  ((cvndfn *) => *)) ;; Convex non-decreasing function

 (local (defun cvndfn (x) (realfix x)))
 (local (defun cvfn-1 (x) (declare (ignore x)) 4141414111))
 (local (defun cvfn-2 (x) (declare (ignore x)) 21))

 (defthm realp-of-cvfn-1 (realp (cvfn-1 x)))
 (defthm realp-of-cvfn-2 (realp (cvfn-2 x)))

 ;; 
 ;; proving cvfn-1, cvfn-2, cvndfn are convex
 ;;
 (defthm cvfn-1-convex
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x))
		(realp a) (<= 0 a) (<= a 1))
	   (<= (cvfn-1 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))
	       (+ (* a (cvfn-1 x)) (* (- 1 a) (cvfn-1 y))))))

 (defthm cvfn-2-convex
  (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) 
		(realp a) (<= 0 a) (<= a 1))
	   (<= (cvfn-2 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))
	       (+ (* a (cvfn-2 x)) (* (- 1 a) (cvfn-2 y))))))

 (defthm cvndfn-convex
  (implies (and (realp x) (realp y) (realp a) (<= 0 a) (<= a 1))
	   (<= (cvndfn (+ (* a x) (* (- 1 a) y)))
	       (+ (* a (cvndfn x)) (* (- 1 a) (cvndfn y))))))
 ;;
 ;; cvndfn is non-decreasing
 ;;
 (defthm cvndfn-non-decreasing
  (implies (and (realp a) (realp b) (<= a b))
	   (<= (cvndfn a) (cvndfn b))))

 ;; Disable definitions
 (local (in-theory (disable (:d cvfn-1) (:e cvfn-1) (:t cvfn-1))))
 (local (in-theory (disable (:d cvfn-2) (:e cvfn-2) (:t cvfn-2))))
 (local (in-theory (disable (:d cvndfn) (:e cvndfn) (:t cvndfn))))

 ;; sum of convex functions is convex
 (defthm cvfn-1-+-cvfn-2-convex
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x))
       	 	(realp a) (<= 0 a) (<= a 1))
           (<= (+ (cvfn-1 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))
       	   	  (cvfn-2 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y))))
       	       (+ (* a (+ (cvfn-1 x) (cvfn-2 x)))
       	   	  (* (- 1 a) (+ (cvfn-1 y) (cvfn-2 y))))))
  :hints (("GOAL" :use ((:instance cvfn-1-convex)
       		 	(:instance cvfn-2-convex)))))

 ;; alpha*f(x) is convex for alpha >= 0
 (encapsulate 
  nil
  
  ;;  factor out alpha
  (local (defthm lemma-1
   (implies (and (real-listp x) (real-listp y) (= (len y) (len x))
       	 	 (realp a) (<= 0 a) (<= a 1)
		 (realp alpha) (<= 0 alpha))
	    (= (+ (* a (* alpha (cvfn-1 x)))
		  (* (- 1 a) (* alpha (cvfn-1 y))))
	       (* alpha
		  (+ (* a (cvfn-1 x))
		     (* (- 1 a) (cvfn-1 y))))))))

  (defthm a-*-cvfn-1-convex
   (implies (and (real-listp x) (real-listp y) (= (len y) (len x))
        	 (realp a) (<= 0 a) (<= a 1)
 		 (realp alpha) (<= 0 alpha))
 	    (<= (* alpha (cvfn-1 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y))))
 	        (+ (* a (* alpha (cvfn-1 x)))
 		   (* (- 1 a) (* alpha (cvfn-1 y))))))
   :hints (("GOAL" :in-theory (disable distributivity)
 		   :use ((:instance cvfn-1-convex)
 			 (:instance lemma-1)))))
 )

 ;; intermediate step combining cvndfn-non-decreasing and cvfn-2-is-convex
 (defthm cvndfn-monotonic-cvfn-2-convex
  (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) (realp a) (<= 0 a) (<= a 1))
	   (<= (cvndfn (cvfn-2 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y))))
	       (cvndfn (+ (* a (cvfn-2 x)) (* (- 1 a) (cvfn-2 y))))))
  :hints (("GOAL" ;:do-not-induct t
		  :use ((:instance cvfn-2-convex)
			(:instance cvndfn-non-decreasing
				   (a (cvfn-2 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y))))
				   (b (+ (* a (cvfn-2 x)) (* (- 1 a) (cvfn-2 y)))))))))
	
 ;; desired inequality
 (defthm cvndfn-cvfn-2-is-convex
  (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) (realp a) (<= 0 a) (<= a 1))
	   (<= (cvndfn (cvfn-2 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y))))
	       (+ (* a (cvndfn (cvfn-2 x))) (* (- 1 a) (cvndfn (cvfn-2 y))))))
  :hints (("GOAL" :use ((:instance cvndfn-monotonic-cvfn-2-convex)
			(:instance cvndfn-convex
				   (x (cvfn-2 x))
				   (y (cvfn-2 y)))))))
)

;;
;; squared Euclidean norm, norm-sq, is convex
;;

(encapsulate
 nil
 ;;
 ;; first need to show f(x) = x^2 on [0,\infty] 
 ;; is monotonically increasing and convex
 ;;
 (local 
  (defun strict-square-fn (x)
   (if (< x 0) 0 (square-fn x))))

 (local (defthm strict-square-fn-non-decreasing
  (implies (and (realp a) (realp b) (<= a b))
	   (<= (strict-square-fn a) (strict-square-fn b)))))

 (local (defthm square-fn-non-decreasing-on-positives
  (implies (and (realp a) (realp b) (<= a b) (<= 0 a) (<= 0 b))
	   (<= (square-fn a) (square-fn b)))))

 (local (defthm strict-square-fn-is-strict
  (implies (and (realp x) (<= x 0))
	   (equal (strict-square-fn x) 0))))

 ;;
 ;; monotonicity taken care of - now for convexity (harder than expected)
 ;;
 (local (defthm lemma-1
  (implies (and (realp a) (<= 0 a) (realp x) (< x 0))
	   (<= (* a x) 0))))

 (local (defthm lemma-2
  (implies (and (realp a) (realp b) (<= a 0) (<= b 0))
	   (<= (+ a b) 0))))

 (local (defthm lemma-3
  (implies (and (realp a) (<= 0 a) (<= a 1) (realp x) (< x 0) (realp y) (< y 0))
	   (<= (+ (* a x) (* (- 1 a) y)) 0))
  :hints (("GOAL" :in-theory (disable distributivity)
		  :use ((:instance lemma-1)
			(:instance lemma-1 (x y) (a (- 1 a)))
			(:instance lemma-2 (a (* a x)) (b (* (- 1 a) y))))))))

 (local (defthm lemma-4
  (implies (and (realp a) (<= 0 a) (realp x) (<= 0 x))
	   (<= 0 (* a x)))))

 (local (defthm lemma-5
  (implies (and (realp x) (realp y) (<= 0 x) (<= 0 y))
	   (<= 0 (+ x y)))))

 (local (defthm lemma-6 
  (implies (and (realp a) (<= 0 a) (<= a 1) (realp x) (realp y) (<= 0 x) (<= 0 y))
	   (<= 0 (+ (* a x) (* (- 1 a) y))))
  :hints (("GOAL" :in-theory (disable distributivity commutativity-of-*)
		  :use ((:instance lemma-5 (x (* a x)) (y (* (- 1 a) y))) 
			(:instance lemma-4)
			(:instance lemma-4 (a (- 1 a)) (x y)))))))

 (local (defthm lemma-7
  (implies (and (realp x) (realp y) (<= 0 x) (<= y 0))
	   (<= (+ x y) x))))

 (local (defthm lemma-8 
  (implies (and (realp a) (realp x) (realp y)
		(<= 0 a) (<= a 1) (<= 0 x) (< y 0))
	   (<= (+ (* a x) (* (- 1 a) y))
	       (* a x)))
  :hints (("GOAL" :use ((:instance lemma-1 (a (- 1 a)) (x y))
			(:instance lemma-4)
			(:instance lemma-7 (x (* a x)) (y (* (- 1 a) y))))))))

 (local (defthm lemma-9
  (implies (and (realp a) (realp x) (realp y)
		(<= 0 a) (<= a 1) (<= 0 x) (< y 0)
		(<= 0 (+ (* a x) (* (- 1 a) y))))
	   (<= (square-fn (+ (* a x) (* (- 1 a) y)))
	       (square-fn (* a x))))
  :hints (("GOAL" :in-theory (disable square-fn)
		  :use ((:instance lemma-8)
			(:instance square-fn-non-decreasing-on-positives
				   (a (+ (* a x) (* (- 1 a) y)))
				   (b (* a x)))
			(:instance lemma-4))))))

 (local (defthm lemma-10
  (implies (and (realp a) (realp x)
		(<= 0 a) (<= a 1) (<= 0 x))
	   (<= (square-fn (* a x))
	       (* a (square-fn x))))))

 (local (defthm lemma-11
  (implies (and (realp a) (realp b) (realp c) (<= a b) (<= b c))
	   (<= a c))))

 (local (defthm lemma-12
  (implies (and (realp a) (realp x) (realp y)
		(<= 0 a) (<= a 1) (<= 0 x) (< y 0)
		(<= 0 (+ (* a x) (* (- 1 a) y))))
	   (<= (square-fn (+ (* a x) (* (- 1 a) y)))
	       (* a (square-fn x))))
  :hints (("GOAL" :in-theory (disable square-fn commutativity-of-* distributivity)
	  	  :use ((:instance lemma-11
				   (a (square-fn (+ (* a x) (* (- 1 a) y))))
				   (b (square-fn (* a x)))
				   (c (* a (square-fn x))))
			(:instance lemma-10)
			(:instance lemma-9))))))


 (local (defthm strict-square-fn-is-convex
  (implies (and (realp x) (realp y) (realp a) (<= 0 a) (<= a 1))
	   (<= (strict-square-fn (+ (* a x) (* (- 1 a) y)))
	       (+ (* a (strict-square-fn x)) 
		  (* (- 1 a) (strict-square-fn y)))))
  :hints (("GOAL" :in-theory (disable square-fn 
		        	      distributivity)
		  :cases (and (<= 0 x) (<= 0 y))
		  :use ((:instance lemma-3)
			(:instance lemma-12)
			(:instance square-fn-is-convex)
			(:instance lemma-12 (x y) (y x) (a (- 1 a))))))))

 (local (defthm lemma-13
  (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) (realp a) (<= 0 a) (<= a 1))
	   (<= (strict-square-fn (eu-norm (vec-+ (scalar-* a x) (scalar-* (- 1 a) y))))
	       (strict-square-fn (+ (* a (eu-norm x)) 
				    (* (- 1 a) (eu-norm y))))))
  :hints (("GOAL" :use ((:instance eu-norm-is-convex)
			(:instance strict-square-fn-non-decreasing
				   (a (eu-norm (vec-+ (scalar-* a x) (scalar-* (- 1 a) y))))
				   (b (+ (* a (eu-norm x)) (* (- 1 a) (eu-norm y))))))))))

 (local (defthm strict-square-fn-eu-norm-is-convex
  (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) (realp a) (<= 0 a) (<= a 1))
	   (<= (strict-square-fn (eu-norm (vec-+ (scalar-* a x) (scalar-* (- 1 a) y))))
	       (+ (* a (strict-square-fn (eu-norm x)))
		  (* (- 1 a) (strict-square-fn (eu-norm y))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable not lemma-11 strict-square-fn eu-norm distributivity commutativity-of-*)
		  :use ((:instance strict-square-fn-is-convex (x (eu-norm x)) (y (eu-norm y)))
			(:instance lemma-11 
				   (a (strict-square-fn (eu-norm (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))))
				   (b (strict-square-fn (+ (* a (eu-norm x)) 
				    			   (* (- 1 a) (eu-norm y)))))
				   (c (+ (* a (strict-square-fn (eu-norm x)))
		  			 (* (- 1 a) (strict-square-fn (eu-norm y))))))
			(:instance lemma-13))))))


 (local (defthm norm-sq-strict-square-fn-eu-norm-equivalence
  (equal (strict-square-fn (eu-norm x))
	 (norm^2 x))
  :hints (("GOAL" :in-theory (enable norm^2 eu-norm)))))

 (defthm norm-sq-is-convex
  (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) (realp a) (<= 0 a) (<= a 1))
	   (<= (norm^2 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))
	       (+ (* a (norm^2 x))
		  (* (- 1 a) (norm^2 y)))))
  :hints (("GOAL" :use ((:instance strict-square-fn-eu-norm-is-convex)
			(:instance norm-sq-strict-square-fn-eu-norm-equivalence)))))

)



;;
;; a useful inequality:
;;  a ( 1 - a ) || x - y ||^2 <= a || x ||^2 + ( 1 - a ) || y ||^2
;;
;; This is used twice in Nesterov's theorem 
;;  ineq. 1 implies ineq. 6 
;;  ineq. 2 implies ineq. 5
;;
(encapsulate
 nil 

 ;; simple property of squares
 (local (defthm lemma-1
  (implies (and (realp a) (realp b) (<= a b) (<= 0 a) (<= 0 b))
	   (<= (* a a) (* b b)))))

 (local (defthm lemma-2
  (implies (and (realp a) (realp b) (realp c) (<= 0 a) (<= b c))
	   (<= (* a b) (* a c)))))

 ;; by the triangle inequality 
 ;;   a || x - y ||^2 <= a (|| x | + || y ||)^2
 (local (defthm lemma-3
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x))
		(realp a) (<= 0 a))
	   (<= (* a (* (eu-norm (vec-- x y)) (eu-norm (vec-- x y))))
	       (* a (* (+ (eu-norm x) (eu-norm y))
		       (+ (eu-norm x) (eu-norm y))))))
  :hints (("GOAL" :in-theory (disable expt) 
		  :use ((:instance triangle-inequality (y (scalar-* -1 y)))
			(:instance lemma-1 
				   (a (eu-norm (vec-- x y)))
				   (b (+ (eu-norm x) (eu-norm (scalar-* -1 y)))))

			(:instance lemma-2 
				   (b (* (eu-norm (vec-- x y)) (eu-norm (vec-- x y))))
				   (c (* (+ (eu-norm x) (eu-norm y))
		       			 (+ (eu-norm x) (eu-norm y))))))))))

 ;; 
 ;; ( a x - ( 1 - a ) y )^2 = a x^2 + ( 1 - a ) y^2 - a ( 1 - a ) ( x + y )^2
 ;;   - somewhat surprised this passed without issues
 ;;
 (local (defthm lemma-4
  (implies (and (realp a) (realp x) (realp y))
	   (equal (* (- (* a x) (* (- 1 a) y)) 
		     (- (* a x) (* (- 1 a) y)))
		  (+ (* a (* x x)) 
		     (* (- 1 a) (* y y))
		     (- (* a (- 1 a) (* (+ x y) (+ x y)))))))))

 (local (defthm lemma-5
  (implies (realp a)
	   (<= 0 (* a a)))))
 
 ;; a (1-a) (x+y)^2 <= a x^2 + (1-a) y^2
 (local (defthm lemma-6
  (implies (and (realp a) (realp x) (realp y))
	   (<= (* a (- 1 a) (* (+ x y) (+ x y)))
	       (+ (* a (* x x)) 
		  (* (- 1 a) (* y y)))))
  :hints (("GOAL" :use (:instance lemma-5 (a (- (* a x) (* (- 1 a) y))))))))

 ;; 
 ;; set x = ||x|| and y = ||y|| to show
 ;;   a (1-a) (||x|| + ||y||)^2 <= a ||x||^2 + (1-a) ||y||^2
 ;;
 (local (defthm lemma-7
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (realp a))
	   (<= (* a (- 1 a) (* (+ (eu-norm x) (eu-norm y)) 
			       (+ (eu-norm x) (eu-norm y))))
	       (+ (* a (* (eu-norm x) (eu-norm x)))
		  (* (- 1 a) (* (eu-norm y) (eu-norm y))))))
  :hints (("GOAL" :use (:instance lemma-6 (x (eu-norm x)) (y (eu-norm y)))))))

 ;; 
 ;; combine lemma-7 triangle inequality from lemma-3 to obtain
 ;;   a (1-a) || x - y ||^2 <= a ||x||^2 + (1-a) ||y||^2
 ;;
 (defthm quasi-triangle-inequality
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) 
		(realp a) (<= 0 a) (<= a 1))
	   (<= (* a (- 1 a) (* (eu-norm (vec-- x y)) (eu-norm (vec-- x y))))
	       (+ (* a (* (eu-norm x) (eu-norm x)))
		  (* (- 1 a) (* (eu-norm y) (eu-norm y))))))
  :hints (("GOAL" :use ((:instance lemma-7)
			(:instance lemma-3 (a (* a (- 1 a))))))))

 (defthm quasi-triangle-inequality-norm-sq
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) 
		(realp a) (<= 0 a) (<= a 1))
	   (<= (* a (- 1 a) (metric^2 x y))
	       (+ (* a (norm^2 x))
		  (* (- 1 a) (norm^2 y)))))
  :hints (("GOAL" :use ((:instance quasi-triangle-inequality)
			(:instance eu-norm-*-eu-norm (vec x))
			(:instance eu-norm-*-eu-norm (vec y))
			(:instance eu-metric-metric-sq-equivalence)))))
)

