;; 
;; This book contains the proofs for
;;  ineq. 2 implies 5
;;  ineq. 1 implies 6
;;

; cert_param: (uses-acl2r)

(in-package "ACL2")

(include-book "nesterov-2")

;; useful inequality for ineq 2 implies ineq 5 and ineq 1 implies ineq 6
(local (defthm random-inequality
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x))
		(realp alpha) (<= alpha 1) (<= 0 alpha))
	   (<= (* alpha 
		  (- 1 alpha) 
		  (metric^2 x y))
	       (+ (* alpha (norm^2 x)) 
		  (* (- 1 alpha) (norm^2 y)))))
  :hints (("GOAL" :use ((:instance quasi-triangle-inequality-norm-sq (a alpha)))))))

;; 
;; ineq 2 implies ineq 5
;;
;; 2.1.7 implies 2.1.10 in Nesterov's text
;;
(encapsulate
 ()

(local (defthm lemma-1
 (implies (and (realp alpha) (realp x) (realp y) (<= x y) (<= 0 alpha))
	  (<= (* alpha x) (* alpha y)))))

(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))
	       (<= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- x z))
		      (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z))))
		   (mvfn x))
	       (<= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- y z))
		      (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))
		   (mvfn y)))
	  (and (<= (* alpha
		      (+ (mvfn z) 
		       	 (dot (nabla-mvfn z) (vec-- x z))
		       	 (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
		   (* alpha (mvfn x)))
	       (<= (* (- 1 alpha) 
		      (+ (mvfn z) 
		      	 (dot (nabla-mvfn z) (vec-- y z))
		      	 (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z)))))
		   (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-1 
				   (x (+ (mvfn z) 
		      			 (dot (nabla-mvfn z) (vec-- x z))
		      			 (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
				   (y (mvfn x)))
			(:instance lemma-1 
				   (x (+ (mvfn z) 
		      			 (dot (nabla-mvfn z) (vec-- y z))
		      			 (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z)))))
				   (y (mvfn y))
				   (alpha (- 1 alpha))))))))

(local (defthm lemma-3
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))
	       (<= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- x z))
		      (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z))))
		   (mvfn x))
	       (<= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- y z))
		      (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))
		   (mvfn y)))
	  (and (<= (+ (* alpha
		         (+ (mvfn z) 
		       	    (dot (nabla-mvfn z) (vec-- x z))
		       	    (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
		      (* (- 1 alpha) 
		      	 (+ (mvfn z) 
		      	    (dot (nabla-mvfn z) (vec-- y z))
		      	    (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))
		   (+ (* alpha (mvfn x))
		      (* (- 1 alpha) (mvfn y))))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-2))))))

(local (defthm lemma-4
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))
		 (+ (+ (* alpha (mvfn z))
		       (* (- 1 alpha) (mvfn z)))
		    (+ (* alpha (dot (nabla-mvfn z) (vec-- x z)))
		       (* (- 1 alpha) (dot (nabla-mvfn z) (vec-- y z))))
		    (+ (* alpha (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z))))
		       (* (- 1 alpha) (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))))))

;; eliminating coefficients of (mvfn z)
(local (defthm lemma-5
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))
		 (+ (mvfn z)
		    (+ (* alpha (dot (nabla-mvfn z) (vec-- x z)))
		       (* (- 1 alpha) (dot (nabla-mvfn z) (vec-- y z))))
		    (+ (* alpha (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z))))
		       (* (- 1 alpha) (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))))))

;; simplifying dot product by moving coefficients inside the inner product
(local (defthm lemma-6
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))
		 (+ (mvfn z)
		    (+ (dot (nabla-mvfn z) (scalar-* alpha (vec-- x z)))
		       (dot (nabla-mvfn z) (scalar-* (- 1 alpha) (vec-- y z))))
		    (+ (* alpha (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z))))
		       (* (- 1 alpha) (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable dot-linear-first-coordinate-1)
		  :use ((:instance lemma-5)
			(:instance dot-linear-second-coordinate-1
				   (a alpha) 
				   (vec1 (nabla-mvfn z))
				   (vec2 (vec-- x z)))
			(:instance dot-linear-second-coordinate-1
				   (a (- 1 alpha))
				   (vec1 (nabla-mvfn z))
				   (vec2 (vec-- y z))))))))

;; simplifying dot product by linearity in the second coordinate
(local (defthm lemma-7
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha 
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))
		 (+ (mvfn z)
		    (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	       (scalar-* (- 1 alpha) (vec-- y z))))
		    (+ (* alpha (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z))))
		       (* (- 1 alpha) (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable dot-linear-first-coordinate-1)
		  :use ((:instance lemma-6)
			(:instance scalar-*-closure 
				   (a alpha)
				   (vec (vec-- x z)))
			(:instance scalar-*-closure 
				   (a (- 1 alpha))
				   (vec (vec-- y z)))
			(:instance dot-linear-second-coordinate-2
				   (vec1 (nabla-mvfn z))
				   (vec2 (scalar-* alpha (vec-- x z)))
				   (vec3 (scalar-* (- 1 alpha) (vec-- y z)))))))))

;; lemma to factor things out
(local (defthm lemma-8
 (implies (and (realp a) (realp b) (realp c) (realp d) (realp e))
	  (equal (+ (* a b c)
		    (* d b e))
		 (* b (+ (* a c)
			 (* d e)))))))

;; factoring out 1/2L
(local (defthm lemma-10
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))
		 (+ (mvfn z)
		    (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	       (scalar-* (- 1 alpha) (vec-- y z))))
		    (* (* (/ 2) (/ (L)))
		       (+ (* alpha (metric^2 (nabla-mvfn x) (nabla-mvfn z)))
		       	  (* (- 1 alpha) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable dot-linear-first-coordinate-1 distributivity)
		  :use ((:instance lemma-7)
			(:instance lemma-8
				   (a alpha)
				   (b (* (/ 2) (/ (L))))
				   (c (metric^2 (nabla-mvfn x) (nabla-mvfn z)))
				   (d (- 1 alpha))
				   (e (metric^2 (nabla-mvfn y) (nabla-mvfn z)))))))))

;; applying the random inequality
(local (defthm lemma-11
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (real-listp z) (= (len z) (len x)))
	   (<= (* alpha
		  (- 1 alpha) 
		  (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
			  (vec-- (nabla-mvfn y) (nabla-mvfn z))))
	       (+ (* alpha (norm^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))))
		  (* (- 1 alpha) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn z)))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance random-inequality
				  (x (vec-- (nabla-mvfn x) (nabla-mvfn z)))
				  (y (vec-- (nabla-mvfn y) (nabla-mvfn z)))))))))

(local (in-theory (disable eu-metric eu-metric-metric-sq-equivalence eu-metric-positive-definite-2)))

;; showing the inequality with "metric"s
(local (defthm lemma-12
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (real-listp z) (= (len z) (len x)))
	   (<= (* alpha
		  (- 1 alpha) 
		  (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
			  (vec-- (nabla-mvfn y) (nabla-mvfn z))))
	       (+ (* alpha (metric^2 (nabla-mvfn x) (nabla-mvfn z)))
		  (* (- 1 alpha) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))
 :hints (("GOAL" :expand ((metric^2 (nabla-mvfn y) (nabla-mvfn z))
			  (metric^2 (nabla-mvfn x) (nabla-mvfn z)))
 		 :use ((:instance lemma-11))))))

(local (defthm lemma-13
 (implies (and (realp a) (realp b) (realp c) (<= b c) (<= 0 a))
	  (<= (* a b) (* a c)))))

(local (defthm lemma-14
 (implies (and (realp a) (realp b) (realp c) (<= b c))
	  (<= (+ a b) (+ a c)))))

(local (defthm lemma-15
 (implies (and (realp a) (realp b) (realp c) (realp d) (realp e) (<= d e) (<= 0 c))
	  (<= (+ a b (* c d)) 
	      (+ a b (* c e))))
 :hints (("GOAL" :use ((:instance lemma-13 (a c) (b d) (c e))
		       (:instance lemma-14 (a a) (b (+ b (* c d))) (c (+ b (* c e))))
		       (:instance lemma-14 (a b) (b (* c d)) (c (* c e))))))))

(local (defthm lemma-16
 (<= 0 (* (/ 2) (/ (L))))
 :hints (("GOAL" :use ((:instance L-is-standard)
		       (:instance L->=-0))))))

(local (defthm lemma-17
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (<= (+ (mvfn z)
		 (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	    (scalar-* (- 1 alpha) (vec-- y z)))) 
		 (* (* (/ 2) (/ (L))) 
		    (+ (* alpha
			   (- 1 alpha) 
			   (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	  	   (vec-- (nabla-mvfn y) (nabla-mvfn z)))))))
	      (+ (mvfn z) 
		 (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	    (scalar-* (- 1 alpha) (vec-- y z))))  
		 (* (* (/ 2) (/ (L))) 
		    (+ (* alpha  (metric^2 (nabla-mvfn x) (nabla-mvfn z)))
		       (* (- 1 alpha) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable lemma-8)
		  :use ((:instance L->=-0)
			(:instance lemma-16)
			(:instance lemma-15
				   (a (mvfn z))
				   (b (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	     			 (scalar-* (- 1 alpha) (vec-- y z)))))
				   (c (* (/ 2) (/ (L))))
				   (d (+ (* alpha
			   		 (- 1 alpha) 
			   		 (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	  	   		 (vec-- (nabla-mvfn y) (nabla-mvfn z))))))
				   (e (+ (* alpha  (metric^2 (nabla-mvfn x) (nabla-mvfn z)))
		       			 (* (- 1 alpha) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))
			(:instance lemma-12))))))
	
(local (in-theory (disable lemma-8)))

(local (defthm lemma-18
 (implies (and (realp a) (realp b) (realp c) (<= a b) (<= b c))
	  (<= a c))))

;; showing intermediate inequality
(local (defthm lemma-19
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (<= (+ (mvfn z)
		 (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	    (scalar-* (- 1 alpha) (vec-- y z)))) 
		 (* (* (/ 2) (/ (L))) 
		    (+ (* alpha
			   (- 1 alpha) 
			   (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	  	   (vec-- (nabla-mvfn y) (nabla-mvfn z))))))) 
	      (+ (* alpha
		    (+ (mvfn z) 
		       (dot (nabla-mvfn z) (vec-- x z))
		       (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z)))))
		 (* (- 1 alpha) 
		    (+ (mvfn z) 
		    (dot (nabla-mvfn z) (vec-- y z))
		    (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-10)
			(:instance lemma-17))))))

; showing the desired inequality
(local (defthm lemma-20
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))
	       (<= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- x z))
		      (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn z))))
		   (mvfn x))
	       (<= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- y z))
		      (* (/ 2) (/ (L)) (metric^2 (nabla-mvfn y) (nabla-mvfn z))))
		   (mvfn y)))
	  ;; almost forgot to include the above hypotheses
	  (<= (+ (mvfn z)
		 (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	    (scalar-* (- 1 alpha) (vec-- y z)))) 
		 (* (* (/ 2) (/ (L))) 
		    (+ (* alpha
			   (- 1 alpha) 
			   (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	  	   (vec-- (nabla-mvfn y) (nabla-mvfn z))))))) 
	      (+ (* alpha (mvfn x))
		      (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-3)
			(:instance lemma-19))))))

;;; beginning to prove identity to simplify (1 - alpha)(y - z) = (1 - alpha)y - z + alpha z
(local (in-theory (enable scalar-*-distributivity vec-+-distributivity)))

(local (defthm lemma-21
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (scalar-* alpha (vec-- x z))
		 (vec-- (scalar-* alpha x) (scalar-* alpha z))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-distributivity
				  (vec1 x)
				  (vec2 (scalar-* -1 z))
				  (a alpha))
		       (:instance scalar-*-closure (a -1) (vec z)))))))

(local (in-theory (disable scalar-*-distributivity vec-+-distributivity)))

(local (defthm lemma-22
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (scalar-* (- 1 alpha) (vec-- y z))
		 (vec-- (scalar-* (- 1 alpha) y) 
			(scalar-* (- 1 alpha) z))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-distributivity
				  (vec1 y)
				  (vec2 (scalar-* -1 z))
				  (a (- 1 alpha)))
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-of-scalar-* (a -1) (b (- alpha)) (vec z))
		       (:instance vec-+-distributivity
				  (a 1)
				  (b (- alpha))
				  (vec z)))))))

;; identity to simplify (1 - alpha)(y - z)
(local (defthm lemma-23
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (scalar-* (- 1 alpha) (vec-- y z))
		 (vec-+ (scalar-* (- 1 alpha) y) 
			(vec-+ (scalar-* -1 z) (scalar-* alpha z)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-22)
		       (:instance scalar-*-identity (vec z))
		       (:instance vec-+-distributivity 
				  (vec z)
				  (a -1)
				  (b alpha))
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-of-scalar-* 
		       		  (a 1) (b (- alpha)) (vec z)))))))

;; expanding all coefficents related to z
(local (defthm lemma-24 
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (vec-+ (scalar-* alpha x) 
			       (scalar-* -1 (scalar-* alpha z)))
			(vec-+ (scalar-* (- 1 alpha) y) 
			       (vec-+ (scalar-* -1 z) 
				      (scalar-* alpha z))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-23)
		       (:instance scalar-*-distributivity 
				  (a alpha)
				  (vec1 x) 
				  (vec2 (scalar-* -1 z)))
		       (:instance scalar-*-of-scalar-*
				  (a -1)
				  (b alpha)
				  (vec z)))))))

;; slowly collecting z terms via associativity/commutativity
(local (defthm lemma-25 
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (vec-+ (scalar-* alpha x) 
			       (scalar-* -1 (scalar-* alpha z)))
			(vec-+ (scalar-* alpha z)
			       (vec-+ (scalar-* (- 1 alpha) y)
				      (scalar-* -1 z))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-24)
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec z))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* (- 1 alpha) y))
				  (vec2 (scalar-* alpha z))
				  (vec3 (scalar-* -1 z))))))))

;; slowly collecting z terms via associativity
(local (defthm lemma-26 
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* -1 (scalar-* alpha z))
			       (vec-+ (scalar-* alpha z)
			       	      (vec-+ (scalar-* (- 1 alpha) y)
				      	     (scalar-* -1 z)))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-25)
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-closure (a (- alpha)) (vec z))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* alpha x))
				  (vec2 (scalar-* -1 (scalar-* alpha z)))
				  (vec3 (vec-+ (scalar-* alpha z)
			       	      	       (vec-+ (scalar-* (- 1 alpha) y)
				      	     	      (scalar-* -1 z))))))))))

;; more associativity
(local (defthm lemma-27 
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (vec-+ (scalar-* -1 (scalar-* alpha z))
			       	      (scalar-* alpha z))
			       (vec-+ (scalar-* (- 1 alpha) y)
				      (scalar-* -1 z))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-25)
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-closure (a (- alpha)) (vec z))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* -1 (scalar-* alpha z)))
				  (vec2 (scalar-* alpha z))
				  (vec3 (vec-+ (scalar-* (- 1 alpha) y)
				      	       (scalar-* -1 z)))))))))

;; eliminate z term
(local (defthm lemma-28
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 z)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-27)
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-closure (a (- alpha)) (vec z))
		       (:instance vec-+-commutativity
				  (vec2 (scalar-* -1 (scalar-* alpha z)))
				  (vec1 (scalar-* alpha z)))
		       (:instance vec---zero-inverse
				  (vec1 (scalar-* alpha z))
				  (vec2 (scalar-* alpha z)))
		       (:instance zvecp-is-additive-identity-2
				  (vec1 (vec-- (scalar-* alpha z) (scalar-* alpha z)))
				  (vec2 (vec-+ (scalar-* (- 1 alpha) y)
			       		       (scalar-* -1 z)))))))))

;; now replace z with alpha x + (1 - alpha) y
(local (defthm lemma-29
 (implies (and (real-listp x) (real-listp y)
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (vec-+ (scalar-* alpha
				  (vec-- x 
					 (vec-+ (scalar-* alpha x) 
						(scalar-* (- 1 alpha) y))))
		        (scalar-* (- 1 alpha) 
				  (vec-- y 
					 (vec-+ (scalar-* alpha x) 
						(scalar-* (- 1 alpha) y)))))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 (vec-+ (scalar-* alpha x) 
						   (scalar-* (- 1 alpha) y)))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-28
				  (z (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y)))))))

;; slowly go back and eliminate things eliminate everything 
(local (defthm lemma-30
 (implies (and (real-listp x) (real-listp y) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 (vec-+ (scalar-* alpha x) 
						   (scalar-* (- 1 alpha) y)))))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (vec-+ (scalar-* -1 (scalar-* alpha x))
				      (scalar-* -1 (scalar-* (- 1 alpha) y)))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable scalar-*-distributivity vec---zero-inverse scalar-*-of-scalar-*)
		 :use ((:instance lemma-29)
		       (:instance lemma-28 (z (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		       (:instance scalar-*-closure (a (- alpha)) (vec x))
		       (:instance scalar-*-closure (a (+ -1 alpha)) (vec y))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-closure (a -1) (vec (scalar-* alpha x)))
		       (:instance scalar-*-closure 
				  (a -1) 
				  (vec (scalar-* (- 1 alpha) y)))
		       (:instance scalar-*-distributivity 
				  (a -1)
				  (vec1 (scalar-* alpha x))
				  (vec2 (scalar-* (- 1 alpha) y))))))))

;; slowly eliminate everything 
(local (defthm lemma-31
 (implies (and (real-listp x) (real-listp y)
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 (vec-+ (scalar-* alpha x) 
						   (scalar-* (- 1 alpha) y)))))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (vec-+ (scalar-* (- 1 alpha) y)
				      (scalar-* -1 (scalar-* (- 1 alpha) y)))
			       (scalar-* -1 (scalar-* alpha x))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-29)
		       (:instance scalar-*-closure (a (- alpha)) (vec x))
		       (:instance scalar-*-closure (a (+ -1 alpha)) (vec y))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-distributivity 
				  (a -1)
				  (vec2 (scalar-* alpha x))
				  (vec1 (scalar-* -1 (scalar-* (- 1 alpha) y))))
		       (:instance vec-+-commutativity
				  (vec1 (scalar-* -1 (scalar-* (- 1 alpha) y)))
				  (vec2 (scalar-* -1 (scalar-* alpha x))))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* (- 1 alpha) y))
				  (vec2 (scalar-* -1 (scalar-* (- 1 alpha) y)))
				  (vec3 (scalar-* -1 (scalar-* alpha x)))))))))

;; slowly eliminate everything 
(local (defthm lemma-32
 (implies (and (real-listp x) (real-listp y) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x))) 
	  (equal (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 (vec-+ (scalar-* alpha x) 
						   (scalar-* (- 1 alpha) y)))))
		 (vec-+ (scalar-* alpha x) 
			(scalar-* -1 (scalar-* alpha x)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-31)
		       (:instance scalar-*-closure (a (- alpha)) (vec x))
		       (:instance scalar-*-closure (a (+ -1 alpha)) (vec y))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance vec---zero-inverse
				  (vec1 (scalar-* (- 1 alpha) y))
				  (vec2 (scalar-* (- 1 alpha) y)))
		       (:instance zvecp-is-additive-identity-2
				  (vec1 (vec-- (scalar-* (- 1 alpha) y)
					       (scalar-* (- 1 alpha) y)))
				  (vec2 (scalar-* -1 (scalar-* alpha x)))))))))

(local (defthm lemma-33
 (implies (and (real-listp x) (real-listp y) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x))) 
	  (equal (vec-+ (scalar-* alpha
				  (vec-- x 
					 (vec-+ (scalar-* alpha x) 
						(scalar-* (- 1 alpha) y))))
		        (scalar-* (- 1 alpha) 
				  (vec-- y 
					 (vec-+ (scalar-* alpha x) 
						(scalar-* (- 1 alpha) y)))))
		 (vec-- (scalar-* alpha x) 
			(scalar-* alpha x))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-32)
		       (:instance lemma-29))))))

;; showing the desired inequality for different value of z
;; (vec-+ (scalar-* (ALPHA) x) (scalar-* (- 1 (ALPHA)) y))
(local (defthm lemma-34
 (implies (and (real-listp x) (real-listp y)
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x))
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ 2) 
			 (/ (L)) 
			 (metric^2 (nabla-mvfn x) 
				 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
		   (mvfn x))
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ 2) 
			 (/ (L)) 
			 (metric^2 (nabla-mvfn y) 
				 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
		   (mvfn y)))
	  ;; break between hypotheses and conclusion
	  (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (vec-+ (scalar-* alpha 
				       (vec-- x 
					      (vec-+ (scalar-* alpha x) 	
						     (scalar-* (- 1 alpha) y))))
		             (scalar-* (- 1 alpha) 
				       (vec-- y 
					     (vec-+ (scalar-* alpha x) 
						    (scalar-* (- 1 alpha) y)))))) 
		 (* (* (/ 2) (/ (L))) 
		    (+ (* alpha 
			   (- 1 alpha) 
			   (metric^2 (vec-- (nabla-mvfn x) 
					  (nabla-mvfn (vec-+ (scalar-* alpha x) 
						      (scalar-* (- 1 alpha) y))))
		       	  	   (vec-- (nabla-mvfn y) 
					  (nabla-mvfn (vec-+ (scalar-* alpha x) 
						      (scalar-* (- 1 alpha) y))))))))) 
	      (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance scalar-*-closure 
				   (a alpha)
				   (vec x))
			(:instance scalar-*-closure 
				   (a (- 1 alpha))
				   (vec y))
			(:instance lemma-20
				   (z (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))))))))

;; Replacing the second entry in the dot product to a zero vector
(local (defthm lemma-35
 (implies (and (real-listp x) (real-listp y) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) 
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ 2) 
			 (/ (L)) 
			 (metric^2 (nabla-mvfn x) 
				 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
		   (mvfn x))
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ 2) 
			 (/ (L)) 
			 (metric^2 (nabla-mvfn y) 
				 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
		   (mvfn y)))
	  ;; break between hypotheses and conclusion
	  (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (vec-- (scalar-* alpha x) 
			     (scalar-* alpha x)))
		 (* (* (/ 2) (/ (L))) 
		    (+ (* alpha 
			   (- 1 alpha) 
			   (metric^2 (vec-- (nabla-mvfn x) 
					  (nabla-mvfn (vec-+ (scalar-* alpha x) 
						      (scalar-* (- 1 alpha) y))))
		       	  	   (vec-- (nabla-mvfn y) 
					  (nabla-mvfn (vec-+ (scalar-* alpha x) 
						      (scalar-* (- 1 alpha) y))))))))) 
	      (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-34)
			(:instance lemma-33))))))

;; dotting with a zero vector results in zero
(local (defthm lemma-36
 (implies (and (real-listp x) (real-listp y)
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x))
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ 2) 
			 (/ (L)) 
			 (metric^2 (nabla-mvfn x) 
				 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
		   (mvfn x))
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ 2) 
			 (/ (L)) 
			 (metric^2 (nabla-mvfn y) 
				 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
		   (mvfn y)))
	  ;; break between hypotheses and conclusion
	  (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (* (* (/ 2) (/ (L))) 
		    (+ (* alpha 
			   (- 1 alpha) 
			   (metric^2 (vec-- (nabla-mvfn x) 
					  (nabla-mvfn (vec-+ (scalar-* alpha x) 
						      (scalar-* (- 1 alpha) y))))
		       	  	   (vec-- (nabla-mvfn y) 
					  (nabla-mvfn (vec-+ (scalar-* alpha x) 
						      (scalar-* (- 1 alpha) y))))))))) 
	      (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-35)
			(:instance scalar-*-closure (a alpha) (vec x))
			(:instance scalar-*-closure (a (- alpha)) (vec x))
			(:instance dot-with-zvec-is-zero-2
				   (x (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
				   (y (vec-- (scalar-* alpha x) 
			     		     (scalar-* alpha x))))
			(:instance vec---zero-inverse
				   (vec1 (scalar-* alpha x))
				   (vec2 (scalar-* alpha x))))))))

;; begining identity for removing things inside the metric
(local (defthm lemma-37
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))) 
	  (equal  (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	  (vec-- (nabla-mvfn y) (nabla-mvfn z)))
		 (norm^2 (vec-+ (vec-+ (nabla-mvfn x) 
			      	     (scalar-* -1 (nabla-mvfn z)))
			      (scalar-* -1 (vec-+ (nabla-mvfn y)
						  (scalar-* -1 (nabla-mvfn z))))))))
 :hints (("GOAL" :in-theory (enable metric^2)))))

;; using associativity/distributivity/commutativity to kill of terms
(local (defthm lemma-38
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))) 
	  (equal  (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	  (vec-- (nabla-mvfn y) (nabla-mvfn z)))
		 (norm^2 (vec-+ (vec-+ (nabla-mvfn x) 
			      	     (scalar-* -1 (nabla-mvfn z)))
			      (vec-+ (scalar-* -1 (nabla-mvfn y))
				     (nabla-mvfn z))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-37)
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn z)))
		       (:instance scalar-*-distributivity
				  (a -1)
				  (vec1 (nabla-mvfn y))
				  (vec2 (scalar-* -1 (nabla-mvfn z))))
		       (:instance scalar-*-of-scalar-* (a -1) (b -1) (vec (nabla-mvfn z)))
		       (:instance scalar-*-identity (vec (nabla-mvfn z))))))))

;; more commutativity
(local (defthm lemma-39
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))) 
	  (equal  (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	  (vec-- (nabla-mvfn y) (nabla-mvfn z)))
		 (norm^2 (vec-+ (vec-+ (nabla-mvfn x)
			      	     (scalar-* -1 (nabla-mvfn z)))
			      (vec-+ (nabla-mvfn z)
				     (scalar-* -1 (nabla-mvfn y)))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-38)
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn z)))
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn y)))
		       (:instance vec-+-commutativity 
				  (vec2 (scalar-* -1 (nabla-mvfn y)))
				  (vec1 (nabla-mvfn z))))))))

;; more associativity
(local (defthm lemma-40
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))) 
	  (equal  (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	  (vec-- (nabla-mvfn y) (nabla-mvfn z)))
		 (norm^2 (vec-+ (nabla-mvfn x)
			      (vec-+ (vec-+ (scalar-* -1 (nabla-mvfn z))
					    (nabla-mvfn z))
				     (scalar-* -1 (nabla-mvfn y)))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-39)
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn z)))
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn y)))
		       (:instance vec-+-associativity
				  (vec2 (scalar-* -1 (nabla-mvfn z)))
				  (vec1 (nabla-mvfn x))
				  (vec3 (vec-+ (nabla-mvfn z)
				     	       (scalar-* -1 (nabla-mvfn y)))))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* -1 (nabla-mvfn z)))
				  (vec2 (nabla-mvfn z))
				  (vec3 (scalar-* -1 (nabla-mvfn y)))))))))

;; more killing
(local (defthm lemma-41
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))) 
	  (equal (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	 (vec-- (nabla-mvfn y) (nabla-mvfn z)))
		 (norm^2 (vec-+ (nabla-mvfn x)
			      (scalar-* -1 (nabla-mvfn y))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-40)
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn z)))
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn y)))
		       (:instance vec-+-commutativity (vec2 (scalar-* -1 (nabla-mvfn z))) (vec1 (nabla-mvfn z)))
		       (:instance vec---zero-inverse (vec1 (nabla-mvfn z)) (vec2 (nabla-mvfn z)))
		       (:instance zvecp-is-additive-identity-2
				  (vec1 (vec-- (nabla-mvfn z) (nabla-mvfn z)))
				  (vec2 (scalar-* -1 (nabla-mvfn y)))))))))

;; returning to metric stuff
(local (defthm lemma-42
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))) 
	  (equal (metric^2 (vec-- (nabla-mvfn x) (nabla-mvfn z))
		       	 (vec-- (nabla-mvfn y) (nabla-mvfn z)))
		 (metric^2 (nabla-mvfn x)
			 (nabla-mvfn y))))
 :hints (("GOAL" :use ((:instance lemma-41))
		 :expand (metric^2 (nabla-mvfn x) (nabla-mvfn y))))))

;; turning the metric thing into what we want
(local (defthm lemma-43 ;ineq-2-implies-ineq-5-expanded ;2.1.7-implies-2.1.10
 (implies (and (real-listp x) (real-listp y) 
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) 
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ 2) 
			 (/ (L)) 
			 (metric^2 (nabla-mvfn x) 
				 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
		   (mvfn x))
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ 2) 
			 (/ (L)) 
			 (metric^2 (nabla-mvfn y) 
				 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
		   (mvfn y)))
	  ;; break between hypotheses and conclusion
	  (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (* (* (/ 2) (/ (L))) 
		    (+ (* alpha 
			   (- 1 alpha) 
			   (metric^2 (nabla-mvfn x) (nabla-mvfn y))))))
	      (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-36)
			(:instance scalar-*-closure (a alpha) (vec x))
			(:instance scalar-*-closure (a (- 1 alpha)) (vec y))
			(:instance lemma-42 
				   (z (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))))))))

;; turning the metric thing into what we want
(defthm ineq-2-implies-ineq-5-expanded ;2.1.7-implies-2.1.10
 (implies (and (real-listp x) (real-listp y)
 	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) 
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ (* 2 (L)))
			 (metric^2 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
				 (nabla-mvfn x) )))
		   (mvfn x))
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ (* 2 (L))) 
			 (metric^2 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
				 (nabla-mvfn y))))
		   (mvfn y)))
	  ;; break between hypotheses and conclusion
	  (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (* (/ (* 2 (L)))
		    (+ (* alpha 
			   (- 1 alpha) 
			   (metric^2 (nabla-mvfn x) (nabla-mvfn y))))))
	      (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))))
 :hints (("GOAL" :use ((:instance lemma-43)
		       (:instance metric-commutativity
				  (vec1 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
				  (vec2 (nabla-mvfn x)))
		       (:instance metric-commutativity
				  (vec1 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
				  (vec2 (nabla-mvfn y)))))))
		) ;; end of encapsulation for 2.1.7 => 2.1.10



;; 
;; ineq 1 implies ineq 6
;;  a lot of this mimics ineq. 2 implies ineq. 5 and can probably be reused
;;
;; 2.1.6 implies 2.1.11 in Nesterov's theorem
;;
(encapsulate
 ()

(local (defthm lemma-1
 (implies (and (realp alpha) (realp x) (realp y) (>= x y) (<= 0 alpha))
	  (>= (* alpha x) (* alpha y)))))

(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))
	       (>= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- x z))
		      (* (L) (/ 2) (metric^2 z x)))
		   (mvfn x))
	       (>= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- y z))
		      (* (L) (/ 2) (metric^2 z y)))
		   (mvfn y)))
	  (and (>= (* alpha
		      (+ (mvfn z) 
		       	 (dot (nabla-mvfn z) (vec-- x z))
		       	 (* (L) (/ 2) (metric^2 z x))))
		   (* alpha (mvfn x)))
	       (>= (* (- 1 alpha) 
		      (+ (mvfn z) 
		      	 (dot (nabla-mvfn z) (vec-- y z))
		      	 (* (L) (/ 2) (metric^2 z y))))
		   (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-1 
				   (x (+ (mvfn z) 
		      			 (dot (nabla-mvfn z) (vec-- x z))
		      			 (* (L) (/ 2) (metric^2 z x))))
				   (y (mvfn x))
				   (alpha alpha))
			(:instance lemma-1 
				   (x (+ (mvfn z) 
		      			 (dot (nabla-mvfn z) (vec-- y z))
		      			 (* (L) (/ 2) (metric^2 z y))))
				   (y (mvfn y))
				   (alpha (- 1 alpha))))))))

(local (defthm lemma-3
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x))
	       (>= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- x z))
		      (* (L) (/ 2) (metric^2 z x)))
		   (mvfn x))
	       (>= (+ (mvfn z) 
		      (dot (nabla-mvfn z) (vec-- y z))
		      (* (L) (/ 2) (metric^2 z y)))
		   (mvfn y)))
	  (and (>= (+ (* alpha
		         (+ (mvfn z) 
		       	    (dot (nabla-mvfn z) (vec-- x z))
		       	    (* (L) (/ 2) (metric^2 z x))))
		      (* (- 1 alpha) 
		      	 (+ (mvfn z) 
		      	    (dot (nabla-mvfn z) (vec-- y z))
		      	    (* (L) (/ 2) (metric^2 z y)))))
		   (+ (* alpha (mvfn x))
		      (* (- 1 alpha) (mvfn y))))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-2))))))

;; eliminating coefficients of (mvfn z)
(local (defthm lemma-5
 (implies (and (real-listp x) (real-listp y) (real-listp z)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (L) (/ 2) (metric^2 z x))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (L) (/ 2) (metric^2 z y)))))
		 (+ (mvfn z)
		    (+ (* alpha (dot (nabla-mvfn z) (vec-- x z)))
		       (* (- 1 alpha) (dot (nabla-mvfn z) (vec-- y z))))
		    (+ (* alpha (* (L) (/ 2) (metric^2 z x)))
		       (* (- 1 alpha) (* (L) (/ 2) (metric^2 z y)))))))))
	     
;; simplifying dot product by moving coefficients inside the inner product
(local (defthm lemma-6
 (implies (and (real-listp x) (real-listp y) (real-listp z)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (L) (/ 2) (metric^2 z x))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (L) (/ 2) (metric^2 z y)))))
		 (+ (mvfn z)
		    (+ (dot (nabla-mvfn z) (scalar-* alpha (vec-- x z)))
		       (dot (nabla-mvfn z) (scalar-* (- 1 alpha) (vec-- y z))))
		    (+ (* alpha (* (L) (/ 2) (metric^2 z x)))
		       (* (- 1 alpha) (* (L) (/ 2) (metric^2 z y)))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable dot-linear-first-coordinate-1)
		  :use ((:instance lemma-5)
			(:instance dot-linear-second-coordinate-1
				   (a alpha) 
				   (vec1 (nabla-mvfn z))
				   (vec2 (vec-- x z)))
			(:instance dot-linear-second-coordinate-1
				   (a (- 1 alpha))
				   (vec1 (nabla-mvfn z))
				   (vec2 (vec-- y z))))))))

;; simplifying dot product by linearity in the second coordinate
(local (defthm lemma-7
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (L) (/ 2) (metric^2 z x))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (L) (/ 2) (metric^2 z y)))))
		 (+ (mvfn z)
		    (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	       (scalar-* (- 1 alpha) (vec-- y z))))
		    (+ (* alpha (* (L) (/ 2) (metric^2 z x)))
		       (* (- 1 alpha) (* (L) (/ 2) (metric^2 z y)))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable dot-linear-first-coordinate-1)
		  :use ((:instance lemma-6)
			(:instance scalar-*-closure 
				   (a alpha)
				   (vec (vec-- x z)))
			(:instance scalar-*-closure 
				   (a (- 1 alpha))
				   (vec (vec-- y z)))
			(:instance dot-linear-second-coordinate-2
				   (vec1 (nabla-mvfn z))
				   (vec2 (scalar-* alpha (vec-- x z)))
				   (vec3 (scalar-* (- 1 alpha) (vec-- y z)))))))))

;; lemma to factor things out
(local (defthm lemma-8
 (implies (and (realp a) (realp b) (realp c) (realp d) (realp e))
	  (equal (+ (* a b c)
		    (* d b e))
		 (* b (+ (* a c)
			 (* d e)))))))

;; factoring out L/2
(local (defthm lemma-10
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn z) 
		       	  (dot (nabla-mvfn z) (vec-- x z))
		       	  (* (L) (/ 2) (metric^2 z x))))
		    (* (- 1 alpha) 
		       (+ (mvfn z) 
		      	  (dot (nabla-mvfn z) (vec-- y z))
		      	  (* (L) (/ 2) (metric^2 z y)))))
		 (+ (mvfn z)
		    (dot (nabla-mvfn z) (vec-+ (scalar-* alpha (vec-- x z))
		        	 	       (scalar-* (- 1 alpha) (vec-- y z))))
		    (* (* (L) (/ 2))
		       (+ (* alpha  (metric^2 z x))
		       	  (* (- 1 alpha) (metric^2 z y)))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable dot-linear-first-coordinate-1 lemma-8)
		  :use ((:instance lemma-7)
			(:instance lemma-8
				   (a alpha)
				   (b (* (L) (/ 2)))
				   (c (metric^2 (nabla-mvfn x) (nabla-mvfn z)))
				   (d (- 1 alpha))
				   (e (metric^2 (nabla-mvfn y) (nabla-mvfn z)))))))))
(local (in-theory (disable lemma-8)))

;; simplifying || z - x ||
(local (defthm lemma-11
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
	       (realp alpha) (<= 0 alpha) (<= alpha 1))
	  (equal (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) x)
		 (norm^2 (vec-+ (vec-+ (scalar-* alpha x) 
				     (scalar-* (- 1 alpha) y))
			      (scalar-* -1 x)))))
 :hints (("GOAL" :in-theory (enable metric^2)))))

(local (in-theory (disable eu-metric eu-metric-metric-sq-equivalence eu-metric-positive-definite-2)))

;; showing some things
(local (defthm lemma-12
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
	       (realp alpha) (<= 0 alpha) (<= alpha 1))
	  (equal (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) x)
		 (norm^2 (vec-+ (scalar-* (- 1 alpha) y)
			      (vec-+ (scalar-* alpha x)
				     (scalar-* -1 x))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-11)
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a -1) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance vec-+-commutativity
				  (vec2 (scalar-* alpha x))
				  (vec1 (scalar-* (- 1 alpha) y)))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* (- 1 alpha) y))
				  (vec2 (scalar-* alpha x))
				  (vec3 (scalar-* -1 x))))))))

(local (defthm lemma-13
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
	       (realp alpha) (<= 0 alpha) (<= alpha 1))
	     
	  (equal (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) x)
		 (norm^2 (vec-+ (scalar-* (- 1 alpha) y)
			      (scalar-* (- 1 alpha)
					(scalar-* -1 x))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-12)
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a -1) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance vec-+-distributivity (a alpha) (b -1) (vec x))
		       (:instance scalar-*-of-scalar-* (a (- 1 alpha)) (b -1) (vec x)))))))

(local (defthm lemma-14
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
	       (realp alpha) (<= 0 alpha) (<= alpha 1))
	  (equal (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) x)
		 (* (- 1 alpha) (- 1 alpha) (norm^2 (vec-- y x)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-13)
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a -1) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance norm-scalar-* (a (- 1 alpha)) (vec (vec-- y x)))
		       (:instance scalar-*-distributivity (a (- 1 alpha)) (vec1 y) (vec2 (scalar-* -1 x))))))))

;; || z - x ||^2 = (alpha - 1)^2 || y - x ||^2
;; simplified to (alpha - 1)^2 || y - x ||^2
(local (defthm lemma-15
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
	       (realp alpha) (<= 0 alpha) (<= alpha 1))
	  (equal (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) x)
		 (* (- 1 alpha) (- 1 alpha) (metric^2 x y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (enable metric^2)
		 :use ((:instance lemma-14)
		       (:instance metric-commutativity (vec1 y) (vec2 x)))))))

;; beginning to simplify || z - y || to alpha^2 || y - x || or || x - y || idr doesnt matter
(local (defthm lemma-16
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
	       (realp alpha) (<= 0 alpha) (<= alpha 1))
	  (equal (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) y)
		 (norm^2 (vec-+ (vec-+ (scalar-* alpha x) 
				     (scalar-* (- 1 alpha) y))
			      (scalar-* -1 y)))))
 :hints (("GOAL" :in-theory (enable metric^2)))))

;; || z - y || = alpha^2 || x - y ||
;; applying associativity and then vec-+-distributivity and then a bunch of other stuff
(local (defthm lemma-17
 (implies (and (real-listp x) (real-listp y) (= (len x) (DIM)) (= (len y) (len x))
	       (realp alpha) (<= 0 alpha) (<= alpha 1))
	     
	  (equal (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) y)
		 (* alpha alpha (metric^2 x y))))
 :hints (("GOAL" :do-not-induct t
		 :expand (metric^2 x y)
		 :use ((:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a -1) (vec y))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-distributivity
				  (a alpha)
				  (vec1 x)
				  (vec2 (scalar-* -1 y)))
		       (:instance scalar-*-of-scalar-* 
				  (a alpha)
				  (b -1)
				  (vec y))
		       (:instance norm-scalar-* (a alpha) (vec (vec-- x y)))
		       (:instance vec-+-associativity 
				  (vec1 (scalar-* alpha x))
				  (vec2 (scalar-* (- 1 alpha) y))
				  (vec3 (scalar-* -1 y)))
		       (:instance vec-+-distributivity 
				  (a (- 1 alpha))
				  (b -1)
				  (vec y)))))))

;; replacing z in equation thing with (vec-+ (scalar-* (ALPHA) x) (scalar-* (- 1 (ALPHA)) y))
(local (defthm lemma-18
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		       	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   (scalar-* (- 1 alpha) y))) 
			       (vec-- x 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		       	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     x))))
		    (* (- 1 alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		      	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   	  (scalar-* (- 1 alpha) y))) 
			       (vec-- y 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		      	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     y)))))
		 (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		    (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y))) 
			 (vec-+ (scalar-* alpha (vec-- x 
							 (vec-+ (scalar-* alpha x) 
								(scalar-* (- 1 alpha) y))))
		        	(scalar-* (- 1 alpha) 
					  (vec-- y 
						 (vec-+ (scalar-* alpha x) 
							(scalar-* (- 1 alpha) y))))))
		    (* (* (L) (/ 2))
		       (+ (* alpha  
			     (* (- 1 alpha) (- 1 alpha) (metric^2 x y)))
		       	  (* (- 1 alpha) 
			     (* alpha alpha (metric^2 x y))))))))
  :hints (("GOAL" :do-not-induct t
		  ;; for some reason i need to disable associativity-of-*
		  :in-theory (disable dot-linear-first-coordinate-1 vec---zero-inverse associativity-of-*)
		  :use ((:instance lemma-10
				   (z (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
			(:instance scalar-*-closure (a alpha) (vec x))
			(:instance scalar-*-closure (a (- 1 alpha)) (vec y))
			(:instance vec-+-closure-2 
				   (vec1 (scalar-* alpha x))
				   (vec2 (scalar-* (- 1 alpha) y)))
			(:instance lemma-15)
			(:instance lemma-17))))))

;; rewriting the coefficients of || x - y ||^2
(local (defthm lemma-19
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		       	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   (scalar-* (- 1 alpha) y))) 
			       (vec-- x 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		       	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     x))))
		    (* (- 1 alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		      	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   	  (scalar-* (- 1 alpha) y))) 
			       (vec-- y 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		      	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     y)))))
		 (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		    (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y))) 
			 (vec-+ (scalar-* alpha (vec-- x 
							 (vec-+ (scalar-* alpha x) 
								(scalar-* (- 1 alpha) y))))
		        	(scalar-* (- 1 alpha) 
					  (vec-- y 
						 (vec-+ (scalar-* alpha x) 
							(scalar-* (- 1 alpha) y))))))
		    (* (* (L) (/ 2))
		       (+ (* (* alpha (- 1 alpha) (- 1 alpha)) 
			     (metric^2 x y))
		       	  (* (* (- 1 alpha) alpha alpha)
			     (metric^2 x y)))))))
  :hints (("GOAL" :do-not-induct t
		  ;; for some reason i need to disable associativity-of-*
		  :in-theory (disable dot-linear-first-coordinate-1 vec---zero-inverse)
		  :use ((:instance lemma-18))))))

(local (defthm factor-the-thing
 (implies (and (realp a) (realp b) (realp c))
	  (equal (+ (* a c) (* b c))
		 (* (+ a b) c)))))

(local (defthm distribute-the-thing
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (+ (* (* alpha (- 1 alpha) (- 1 alpha))
			     (metric^2 x y))
		    (* (* (- 1 alpha) alpha alpha)
		       (metric^2 x y)))
		 (* (+ (* alpha (- 1 alpha) (- 1 alpha)) 
		       (* (- 1 alpha) alpha alpha))
		    (metric^2 x y))))
 :hints (("GOAL" :use ((:instance factor-the-thing 
				  (a (* alpha (- 1 alpha) (- 1 alpha)))
				  (b (* (- 1 alpha) alpha alpha))
				  (c (metric^2 x y))))
		 :do-not-induct t))))

(local (defthm eliminate-the-thing
 (implies (realp a)
	  (equal (+ (* a (- 1 a) (- 1 a))
		    (* (- 1 a) a a))
		 (* a (- 1 a))))))

(local (defthm reduce-the-thing
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (+ (* (* alpha (- 1 alpha) (- 1 alpha)) 
			     (metric^2 x y))
		       	  (* (* (- 1 alpha) alpha alpha)
			     (metric^2 x y)))
		 (* alpha (- 1 alpha) (metric^2 x y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable distributivity)
		 :use ((:instance eliminate-the-thing (a alpha))
		       (:instance distribute-the-thing))))))

;;; beginning to prove identity to simplify (1 - alpha)(y - z) = (1 - alpha)y - z + alpha z
(local (in-theory (enable scalar-*-distributivity vec-+-distributivity)))

(local (defthm lemma-21
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (scalar-* alpha (vec-- x z))
		 (vec-- (scalar-* alpha x) (scalar-* alpha z))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-distributivity
				  (vec1 x)
				  (vec2 (scalar-* -1 z))
				  (a alpha))
		       (:instance scalar-*-closure (a -1) (vec z)))))))

(local (in-theory (disable scalar-*-distributivity vec-+-distributivity)))

(local (defthm lemma-22
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (scalar-* (- 1 alpha) (vec-- y z))
		 (vec-- (scalar-* (- 1 alpha) y) 
			(scalar-* (- 1 alpha) z))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-distributivity
				  (vec1 y)
				  (vec2 (scalar-* -1 z))
				  (a (- 1 alpha)))
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-of-scalar-* (a -1) (b (- alpha)) (vec z))
		       (:instance vec-+-distributivity
				  (a 1)
				  (b (- alpha))
				  (vec z)))))))

;; identity to simplify (1 - alpha)(y - z)
(local (defthm lemma-23
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (scalar-* (- 1 alpha) (vec-- y z))
		 (vec-+ (scalar-* (- 1 alpha) y) 
			(vec-+ (scalar-* -1 z) (scalar-* alpha z)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-22)
		       (:instance scalar-*-identity (vec z))
		       (:instance vec-+-distributivity 
				  (vec z)
				  (a -1)
				  (b alpha))
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-of-scalar-* 
		       		  (a 1) (b (- alpha)) (vec z)))))))

;; expanding all coefficents related to z
(local (defthm lemma-24 
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (vec-+ (scalar-* alpha x) 
			       (scalar-* -1 (scalar-* alpha z)))
			(vec-+ (scalar-* (- 1 alpha) y) 
			       (vec-+ (scalar-* -1 z) 
				      (scalar-* alpha z))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-23)
		       (:instance scalar-*-distributivity 
				  (a alpha)
				  (vec1 x) 
				  (vec2 (scalar-* -1 z)))
		       (:instance scalar-*-of-scalar-*
				  (a -1)
				  (b alpha)
				  (vec z)))))))

;; slowly collecting z terms via associativity/commutativity
(local (defthm lemma-25 
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (vec-+ (scalar-* alpha x) 
			       (scalar-* -1 (scalar-* alpha z)))
			(vec-+ (scalar-* alpha z)
			       (vec-+ (scalar-* (- 1 alpha) y)
				      (scalar-* -1 z))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-24)
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec z))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* (- 1 alpha) y))
				  (vec2 (scalar-* alpha z))
				  (vec3 (scalar-* -1 z))))))))

;; slowly collecting z terms via associativity
(local (defthm lemma-26 
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* -1 (scalar-* alpha z))
			       (vec-+ (scalar-* alpha z)
			       	      (vec-+ (scalar-* (- 1 alpha) y)
				      	     (scalar-* -1 z)))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-25)
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-closure (a (- alpha)) (vec z))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* alpha x))
				  (vec2 (scalar-* -1 (scalar-* alpha z)))
				  (vec3 (vec-+ (scalar-* alpha z)
			       	      	       (vec-+ (scalar-* (- 1 alpha) y)
				      	     	      (scalar-* -1 z))))))))))

;; more associativity
(local (defthm lemma-27 
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (vec-+ (scalar-* -1 (scalar-* alpha z))
			       	      (scalar-* alpha z))
			       (vec-+ (scalar-* (- 1 alpha) y)
				      (scalar-* -1 z))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-25)
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-closure (a (- alpha)) (vec z))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* -1 (scalar-* alpha z)))
				  (vec2 (scalar-* alpha z))
				  (vec3 (vec-+ (scalar-* (- 1 alpha) y)
				      	       (scalar-* -1 z)))))))))

;; eliminate z term
(local (defthm lemma-28
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-+ (scalar-* alpha (vec-- x z))
		        (scalar-* (- 1 alpha) (vec-- y z)))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 z)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-27)
		       (:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec z))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-closure (a (- alpha)) (vec z))
		       (:instance vec-+-commutativity
				  (vec2 (scalar-* -1 (scalar-* alpha z)))
				  (vec1 (scalar-* alpha z)))
		       (:instance vec---zero-inverse
				  (vec1 (scalar-* alpha z))
				  (vec2 (scalar-* alpha z)))
		       (:instance zvecp-is-additive-identity-2
				  (vec1 (vec-- (scalar-* alpha z) (scalar-* alpha z)))
				  (vec2 (vec-+ (scalar-* (- 1 alpha) y)
			       		       (scalar-* -1 z)))))))))

;; now replace z with alpha x + (1 - alpha) y
(local (defthm lemma-29
 (implies (and (real-listp x) (real-listp y) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (vec-+ (scalar-* alpha
				  (vec-- x 
					 (vec-+ (scalar-* alpha x) 
						(scalar-* (- 1 alpha) y))))
		        (scalar-* (- 1 alpha) 
				  (vec-- y 
					 (vec-+ (scalar-* alpha x) 
						(scalar-* (- 1 alpha) y)))))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 (vec-+ (scalar-* alpha x) 
						   (scalar-* (- 1 alpha) y)))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-28
				  (z (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y)))))))

;; slowly go back and eliminate things eliminate everything 
(local (defthm lemma-30
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x))) 
	  (equal (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 (vec-+ (scalar-* alpha x) 
						   (scalar-* (- 1 alpha) y)))))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (vec-+ (scalar-* -1 (scalar-* alpha x))
				      (scalar-* -1 (scalar-* (- 1 alpha) y)))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable scalar-*-distributivity vec---zero-inverse scalar-*-of-scalar-*)
		 :use ((:instance lemma-29)
		       (:instance lemma-28 (z (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		       (:instance scalar-*-closure (a (- alpha)) (vec x))
		       (:instance scalar-*-closure (a (+ -1 alpha)) (vec y))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-closure (a -1) (vec (scalar-* alpha x)))
		       (:instance scalar-*-closure 
				  (a -1) 
				  (vec (scalar-* (- 1 alpha) y)))
		       (:instance scalar-*-distributivity 
				  (a -1)
				  (vec1 (scalar-* alpha x))
				  (vec2 (scalar-* (- 1 alpha) y))))))))

;; slowly eliminate everything 
(local (defthm lemma-31
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 (vec-+ (scalar-* alpha x) 
						   (scalar-* (- 1 alpha) y)))))
		 (vec-+ (scalar-* alpha x) 
			(vec-+ (vec-+ (scalar-* (- 1 alpha) y)
				      (scalar-* -1 (scalar-* (- 1 alpha) y)))
			       (scalar-* -1 (scalar-* alpha x))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-29)
		       (:instance scalar-*-closure (a (- alpha)) (vec x))
		       (:instance scalar-*-closure (a (+ -1 alpha)) (vec y))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance scalar-*-distributivity 
				  (a -1)
				  (vec2 (scalar-* alpha x))
				  (vec1 (scalar-* -1 (scalar-* (- 1 alpha) y))))
		       (:instance vec-+-commutativity
				  (vec1 (scalar-* -1 (scalar-* (- 1 alpha) y)))
				  (vec2 (scalar-* -1 (scalar-* alpha x))))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* (- 1 alpha) y))
				  (vec2 (scalar-* -1 (scalar-* (- 1 alpha) y)))
				  (vec3 (scalar-* -1 (scalar-* alpha x)))))))))

;; slowly eliminate everything 
(local (defthm lemma-32
 (implies (and (real-listp x) (real-listp y) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (vec-+ (scalar-* alpha x) 
			(vec-+ (scalar-* (- 1 alpha) y)
			       (scalar-* -1 (vec-+ (scalar-* alpha x) 
						   (scalar-* (- 1 alpha) y)))))
		 (vec-+ (scalar-* alpha x) 
			(scalar-* -1 (scalar-* alpha x)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance lemma-31)
		       (:instance scalar-*-closure (a (- alpha)) (vec x))
		       (:instance scalar-*-closure (a (+ -1 alpha)) (vec y))
		       (:instance scalar-*-closure (a alpha) (vec x))
		       (:instance scalar-*-closure (a (- 1 alpha)) (vec y))
		       (:instance vec---zero-inverse
				  (vec1 (scalar-* (- 1 alpha) y))
				  (vec2 (scalar-* (- 1 alpha) y)))
		       (:instance zvecp-is-additive-identity-2
				  (vec1 (vec-- (scalar-* (- 1 alpha) y)
					       (scalar-* (- 1 alpha) y)))
				  (vec2 (scalar-* -1 (scalar-* alpha x)))))))))

(local (defthm lemma-33
 (implies (and (real-listp x) (real-listp y) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x))) 
	  (equal (vec-+ (scalar-* alpha
				  (vec-- x 
					 (vec-+ (scalar-* alpha x) 
						(scalar-* (- 1 alpha) y))))
		        (scalar-* (- 1 alpha) 
				  (vec-- y 
					 (vec-+ (scalar-* alpha x) 
						(scalar-* (- 1 alpha) y)))))
		 (vec-- (scalar-* alpha x) 
			(scalar-* alpha x))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-32)
		       (:instance lemma-29))))))

;; killing off the dot product
(local (defthm lemma-34
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (+ (* alpha 
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		       	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   (scalar-* (- 1 alpha) y))) 
			       (vec-- x 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		       	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     x))))
		    (* (- 1 alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		      	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   	  (scalar-* (- 1 alpha) y))) 
			       (vec-- y 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		      	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     y)))))
		 (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		    (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y))) 
			 (vec-- (scalar-* alpha x) 
				(scalar-* alpha x)))
		    (* (* (L) (/ 2))
		       (+ (* (* alpha (- 1 alpha) (- 1 alpha)) 
			     (metric^2 x y))
		       	  (* (* (- 1 alpha) alpha alpha)
			     (metric^2 x y)))))))
  :hints (("GOAL" :do-not-induct t
		  ;; for some reason i need to disable associativity-of-*
		  :in-theory (disable dot-linear-first-coordinate-1 vec---zero-inverse associativity-of-*)
		  :use ((:instance lemma-19)
			(:instance lemma-33))))))

;; killing off the dot product
(local (defthm lemma-35
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (+ (* alpha 
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		       	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   (scalar-* (- 1 alpha) y))) 
			       (vec-- x 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		       	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     x))))
		    (* (- 1 alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		      	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   	  (scalar-* (- 1 alpha) y))) 
			       (vec-- y 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		      	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     y)))))
		 (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		    (* (* (L) (/ 2))
		       (+ (* (* alpha (- 1 alpha) (- 1 alpha)) 
			     (metric^2 x y))
		       	  (* (* (- 1 alpha) alpha alpha)
			     (metric^2 x y)))))))
  :hints (("GOAL" :do-not-induct t
		  ;; for some reason i need to disable associativity-of-*
		  :in-theory (disable dot-linear-first-coordinate-1 vec---zero-inverse associativity-of-*)
		  :use ((:instance vec---zero-inverse
				   (vec1 (scalar-* alpha x))
				   (vec2 (scalar-* alpha x)))
			(:instance scalar-*-closure (a alpha) (vec x))
			(:instance scalar-*-closure (a (- alpha)) (vec x))
			(:instance lemma-34)
			(:instance dot-with-zvec-is-zero-2
				   (x (nabla-mvfn (vec-+ (scalar-* alpha x) 
					    		 (scalar-* (- 1 alpha) y))))
				   (y (vec-- (scalar-* alpha x) 
					     (scalar-* alpha x)))))))))

;; simplifing alpha stuff
(local (defthm lemma-36
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		    (* (* (L) (/ 2))
		       (+ (* (* alpha (- 1 alpha) (- 1 alpha)) 
			     (metric^2 x y))
		       	  (* (* (- 1 alpha) alpha alpha)
			     (metric^2 x y)))))
		 (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		    (* (* (L) (/ 2))
		       (* alpha (- 1 alpha) (metric^2 x y))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable dot-linear-first-coordinate-1 vec---zero-inverse associativity-of-*)
		  :use ((:instance lemma-35)
			(:instance reduce-the-thing))))))

;; more simplifying stuff
(local (defthm lemma-37
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (+ (* alpha
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		       	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   (scalar-* (- 1 alpha) y))) 
			       (vec-- x 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		       	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     x))))
		    (* (- 1 alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		      	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   	  (scalar-* (- 1 alpha) y))) 
			       (vec-- y 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		      	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     y)))))
		 (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		    (* (* (L) (/ 2))
		       (* alpha (- 1 alpha) (metric^2 x y))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable dot-linear-first-coordinate-1 vec---zero-inverse associativity-of-*)
		  :use ((:instance lemma-36)
			(:instance lemma-35))))))
			
;; introducing z = (vec-+ (scalar-* (ALPHA) x) (scalar-* (- 1 (ALPHA)) y)) to the inequality
(local (defthm lemma-38
 (implies (and (real-listp x) (real-listp y) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) 
	       (>= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (L) (/ 2) (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) x)))
		   (mvfn x))
	       (>= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (L) (/ 2) (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) y)))
		   (mvfn y)))
	  (>= (+ (* alpha
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		       	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   (scalar-* (- 1 alpha) y))) 
			       (vec-- x 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		       	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     x))))
		    (* (- 1 alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha x) 
				       (scalar-* (- 1 alpha) y))) 
		      	  (dot (nabla-mvfn (vec-+ (scalar-* alpha x) 
					   	  (scalar-* (- 1 alpha) y))) 
			       (vec-- y 
				      (vec-+ (scalar-* alpha x) 
					     (scalar-* (- 1 alpha) y))))
		      	  (* (L) 
			     (/ 2) 
			     (metric^2 (vec-+ (scalar-* alpha x) 
					    (scalar-* (- 1 alpha) y)) 
				     y)))))
		  (+ (* alpha (mvfn x))
		     (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance scalar-*-closure (a alpha) (vec x))
		  	(:instance scalar-*-closure (a (- 1 alpha)) (vec y))
			(:instance lemma-3 
				   (z (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))))))))

(local (defthm lemma-39
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) 
	       (>= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (L) (/ 2) (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) x)))
		   (mvfn x))
	       (>= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (L) (/ 2) (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) y)))
		   (mvfn y)))
	  (>= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (* (* (L) (/ 2))
		    (* alpha (- 1 alpha) (metric^2 x y))))
	      (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-37)
			(:instance lemma-38))))))

(local (defthm lemma-40
 (implies (and (real-listp x) (real-listp y)
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)))
	  (equal (* (* (L) (/ 2))
		    (* alpha (- 1 alpha) (metric^2 x y)))
		 (* (L) (/ 2) alpha (- 1 alpha) (metric^2 x y))))))

(local (defthm lemma-41 
 (implies (and (real-listp x) (real-listp y) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) 
	       (>= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (L) (/ 2) (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) x)))
		   (mvfn x))
	       (>= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (L) (/ 2) (metric^2 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)) y)))
		   (mvfn y)))
	  (>= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (* (L) (/ 2) alpha (- 1 alpha) (metric^2 x y)))
	      (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-39)
			(:instance lemma-40))))))

(defthm ineq-1-implies-ineq-6-expanded ; 2.1.6-implies-2.1.11
 (implies (and (real-listp x) (real-listp y) 
	       (realp alpha) (<= 0 alpha) (<= alpha 1)
	       (= (len x) (DIM)) (= (len y) (len x)) 
	       (<= (mvfn x)
		   (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ (L) 2) (metric^2 x 
					   (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))
	       (<= (mvfn y)
		   (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		      (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			   (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
		      (* (/ (L) 2) (metric^2 y 
					   (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))))))
	  (<= (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))
	      (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (* (/ (L) 2) alpha (- 1 alpha) (metric^2 x y)))))
  :hints (("GOAL" :do-not-induct t
	
		  :use ((:instance lemma-41)
			(:instance scalar-*-closure (a alpha) (vec x))
			(:instance scalar-*-closure (a (- 1 alpha)) (vec y))
			(:instance metric-commutativity
				   (vec1 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
				   (vec2 x))
			(:instance metric-commutativity
				   (vec1 (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
				   (vec2 y))))))
		) ;; end of encapsulation for 2.1.6 => 2.1.11

