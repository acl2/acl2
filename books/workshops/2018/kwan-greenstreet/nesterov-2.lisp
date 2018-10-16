;;
;; This book contains the proofs of 
;;  ineq. 0 implies ineq. 4
;;  ineq. 4 implies ineq. 1
;;  ineq. 1 implies ineq. 2
;;  ineq. 2 implies ineq. 3
;;  ineq. 3 implies ineq. 0
;;

; cert_param: (uses-acl2r)

(in-package "ACL2")

;; The necessary lemma that doesn't pass if nsa books are loaded
(local (defthm i-small-standard-part-zero
 (implies (and (realp alpha) (i-small alpha))
	  (equal (standard-part alpha) 0))))

(include-book "nesterov-1")

;;
;; ineq 0 implies ineq 4
;;
(encapsulate
 nil

(local (defthm lemma-1
 (implies (and (realp a) (realp b) (realp c) (<= 0 c) (<= a b))
	  (<= (* a c) (* b c)))))

(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (<= (eu-norm (vec-- (nabla-mvfn x) (nabla-mvfn y))) 
		   (* (L) (eu-norm (vec-- x y)))))
	  (<= (* (eu-norm (vec-- (nabla-mvfn x) (nabla-mvfn y))) (eu-norm (vec-- x y)))
	      (* (L) (eu-norm (vec-- x y)) (eu-norm (vec-- x y)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable eu-norm eu-norm-*-eu-norm)
		 :use ((:instance lemma-1 
				  (a (eu-norm (vec-- (nabla-mvfn x) (nabla-mvfn y))))
				  (b (* (L) (eu-norm (vec-- x y))))
				  (c (eu-norm (vec-- x y))))
		       (:instance eu-norm->=-0 (vec (vec-- x y))))))))

(local (defthm lemma-3
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (<= (eu-norm (vec-- (nabla-mvfn x) (nabla-mvfn y))) 
		   (* (L) (eu-norm (vec-- x y)))))
	 (<= (abs (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y)))
	     (* (L) (eu-norm (vec-- x y)) (eu-norm (vec-- x y)))))
 :hints (("GOAL" :use ((:instance lemma-2)
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn y)))
		       (:instance vec-+-closure-2 (vec1 (nabla-mvfn x)) (vec2 (scalar-* -1 (nabla-mvfn y))))
		       (:instance cauchy-schwarz-2
				  (u (vec-- (nabla-mvfn x) (nabla-mvfn y)))
				  (v (vec-- x y))))))))

(local (defthm lemma-4
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (<= (eu-norm (vec-- (nabla-mvfn x) (nabla-mvfn y))) 
		   (* (L) (eu-metric x y))))
	 (<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
	     (* (L) (eu-metric x y) (eu-metric x y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (enable eu-metric)
		 :use ((:instance lemma-3))))))

(defthm ineq-0-implies-ineq-4-expanded
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (<= (eu-metric (nabla-mvfn x) (nabla-mvfn y))
		   (* (L) (eu-metric x y))))
	 (<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
	     (* (L) (metric^2 x y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (enable eu-metric)
		 :use ((:instance eu-metric-metric-sq-equivalence)
		       (:instance lemma-4)))))
) ;; end of ineq 0 implies ineq 4


;;
;; ineq 4 implies ineq 1
;;
(encapsulate
 nil

 (local (defthm lemma-1
  (implies (and (real-listp x) (real-listp y) 
		(= (len y) (len x)) (= (len x) (DIM))
		(<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
		    (* (L) (metric^2 x y))))
	   (<= (abs (+ (mvfn y) (- (mvfn x)) (- (dot (nabla-mvfn x) (vec-- y x)))))
 	       (* (/ (L) 2) (metric^2 y x))))
  :hints (("GOAL" :use ((:instance lemma-ineq-4))))))

 (local (defthm lemma-2
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
		(<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
		    (* (L) (metric^2 x y))))
	   (<= (+ (mvfn y) (- (mvfn x)) (- (dot (nabla-mvfn x) (vec-- y x))))
 	       (* (/ (L) 2) (metric^2 y x))))
  :hints (("GOAL" :use ((:instance lemma-1))))))

 (defthm ineq-4-implies-ineq-1-expanded
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
		(<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
		    (* (L) (metric^2 x y))))
	   (<= (mvfn y) 
 	       (+ (mvfn x) (dot (nabla-mvfn x) (vec-- y x)) (* (/ (L) 2) (metric^2 y x)))))
  :hints (("GOAL" :use ((:instance lemma-2)))))
) ;; end ineq. 4 implies ineq. 1



;;
;; ineq 1 implies ineq 2
;;
;; 2.1.6 => 2.1.7 in Nesterov's text
;;
(local (in-theory (disable scalar-*-distributivity vec-+-distributivity)))
(encapsulate 
 nil

(local (in-theory (disable phi-identity)))
 
(local (defthm ineq-2.1.6-for-phi
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       (<= (+ (phi x0 y) 
		      (- (phi x0 x)) 
		      (- (dot (nabla-phi x0 x) (vec-- y x))))
	      	   (* (/ (L) 2) (metric^2 x y))))
	  (<= (phi x0 y) 
	      (+ (phi x0 x) 
		 (dot (nabla-phi x0 x) (vec-- y x)) 
		 (* (/ (L) 2) (metric^2 x y)))))))

; substitute y for (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))) and x for y
(local (defthm lemma-10
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 y*) 
	      (+ (phi x0 x) 
		 (dot (nabla-phi x0 x) (vec-- y* x)) (* (/ (L) 2) (metric^2 x y*)))))))

;; last phi thing before vec-- rewrite
(local (defthm lemma-11
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))) 
	      (+ (phi x0 y) 
		 (dot (nabla-phi x0 y) (vec-- (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))) y)) 
		 (* (/ (L) 2) (metric^2 y (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))))))))

;;start of vec-- rewrite
(local (defthm lemma-12
 (implies (and (real-listp y) (= (len y) (DIM)) (real-listp x0))
	  (equal (vec-- (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))) y)
		 (vec-- (vec-+ (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y)))
			       y)
			y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure 
				  (a -1) 
				  (vec (scalar-* (/ (L)) (nabla-phi x0 y))))
		       (:instance scalar-*-closure (a (/ (L))) (vec (nabla-phi x0 y))))))))

;; applying associativity so that we gather y - y together
(local (defthm lemma-13
 (implies (and (real-listp y) (= (len y) (DIM)) (real-listp x0))
	  (equal (vec-- (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))) y)
		 (vec-+ (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y)))
			(vec-- y y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable lemma-12)
		 :use ((:instance scalar-*-closure 
		        	  (a -1) 
		        	  (vec (scalar-* (/ (L)) (nabla-phi x0 y))))
		       (:instance scalar-*-closure (a (/ (L))) (vec (nabla-phi x0 y)))
		       (:instance scalar-*-closure (a -1) (vec y))
		       (:instance lemma-12)
		       (:instance vec-+-associativity
				  (vec1 (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y))))
				  (vec2 y)
				  (vec3 (scalar-* -1 y))))))))

(local (in-theory (disable scalar-*--1)))

;; cancelling y - y
(local (defthm lemma-14
 (implies (and (real-listp y) (= (len y) (DIM)) (real-listp x0))
	  (equal (vec-- (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))) y)
		 (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure 
		        	  (a -1) 
		        	  (vec (scalar-* (/ (L)) (nabla-phi x0 y))))
		       (:instance scalar-*-closure (a (/ (L))) (vec (nabla-phi x0 y)))
		       (:instance lemma-13)
		       (:instance vec---zero-inverse (vec1 y) (vec2 y))
		       (:instance zvecp-is-additive-identity-1 
				  (vec1 (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y))))
				  (vec2 (vec-- y y))))))))
 
;; swapping the entries in metric so we can use previous identity
;;  this one takes a long time to pass  for some reason
(local (defthm lemma-15
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))) 
	      (+ (phi x0 y) 
		 (dot (nabla-phi x0 y) (vec-- (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))) y)) 
		 (* (/ (L) 2) (metric^2 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))) y)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-11)
		       (:instance scalar-*-closure 
		        	  (a -1) 
		        	  (vec (scalar-* (/ (L)) (nabla-phi x0 y))))
		       (:instance scalar-*-closure (a (/ (L))) (vec (nabla-phi x0 y)))
		       (:instance metric-commutativity 
				  (vec1 y)
				  (vec2 (vec-- y (* (/ (L)) (nabla-phi x0 y))))))))))

;; simplifying by cancelling out y-y
(local (defthm lemma-16
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))) 
	      (+ (phi x0 y) 
		 (dot (nabla-phi x0 y) (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y))))
		 (* (/ (L) 2) (norm^2 (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y))))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (enable metric^2)
		 :use ((:instance lemma-15)
		       (:instance lemma-14)
		       (:instance scalar-*-closure 
		        	  (a -1) 
		        	  (vec (scalar-* (/ (L)) (nabla-phi x0 y))))
		       (:instance scalar-*-closure (a (/ (L))) (vec (nabla-phi x0 y))))))))

;; simplifying the coefficients 
(local (defthm lemma-17
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))) 
	      (+ (phi x0 y) 
		 (dot (nabla-phi x0 y) (scalar-* (* -1 (/ (L))) (nabla-phi x0 y)))
		 (* (/ (L) 2) (norm^2 (scalar-* (* -1 (/ (L))) (nabla-phi x0 y)))))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (enable metric^2) 
		 :use ((:instance lemma-16)
		       (:instance scalar-*-of-scalar-*
				  (a -1)
				  (b (/ (L)))
				  (vec (nabla-phi x0 y)))
		       (:instance scalar-*-closure 
		        	  (a -1) 
		        	  (vec (scalar-* (/ (L)) (nabla-phi x0 y))))
		       (:instance scalar-*-closure (a (/ (L))) (vec (nabla-phi x0 y))))))))	       
(local (defthm lemma-18
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))) 
	      (+ (phi x0 y) 
		 (* (/ -1 (L)) (dot (nabla-phi x0 y) (nabla-phi x0 y)))
		 (* (/ (L) 2) (/ (* (L) (L))) (norm^2 (nabla-phi x0 y))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-17)
		       (:instance dot-linear-second-coordinate-1 
				  (a (* -1 (/ (L))))
				  (vec1 (nabla-phi x0 y))
				  (vec2 (nabla-phi x0 y)))
		       (:instance norm-scalar-*
			  	  (a (* -1 (/ (L))))
				  (vec (nabla-phi x0 y)))
		       (:instance scalar-*-of-scalar-*
				  (a -1)
				  (b (/ (L)))
				  (vec (nabla-phi x0 y)))
		       (:instance scalar-*-closure 
		        	  (a -1) 
		        	  (vec (scalar-* (/ (L)) (nabla-phi x0 y))))
		       (:instance scalar-*-closure (a (/ (L))) (vec (nabla-phi x0 y))))))))

;; identities to simplify cooeficients
(local (defthm lemma-19
 (implies (and (realp a) (not (= a 0)) (realp b))
	  (= (* a (/ a) (/ a) b)
	     (* (/ a) b)))))

(local (defthm lemma-20
 (implies (and (realp a))
	  (= (* (L) (/ (L)) (/ (L)) a)
	     (* (/ (L)) a)))
 :hints (("GOAL" :nonlinearp t
		 ;:do-not '(preprocess)
		 :use ((:instance L-nonzero)
		       (:instance realp-L)
		       (:instance lemma-19 (b a) (a (L))))))))

(local (defthm lemma-21
 (equal (* (/ (L) 2) (/ (* (L) (L))) (norm^2 (nabla-phi x0 y)))
	(* (/ (* 2 (L))) (norm^2 (nabla-phi x0 y))))
 :hints (("GOAL" :nonlinearp t
		 :use ((:instance lemma-20 (a (norm^2 (nabla-phi x0 y))))
		       (:instance L-nonzero)
		       (:instance realp-L))))
 :rule-classes nil))

;; simplifying all the cooeficients
(local (defthm lemma-22
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))) 
	      (+ (phi x0 y) 
		 (* (/ -1 (L)) (dot (nabla-phi x0 y) (nabla-phi x0 y)))
		 (* (/ (* 2 (L))) (norm^2 (nabla-phi x0 y))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-21)
		       (:instance lemma-18))))))

;; applying norm/dot product equivalence
(local (defthm lemma-23
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))) 
	      (+ (phi x0 y) 
		 (* (/ -1 (L)) (norm^2 (nabla-phi x0 y)))
		 (* (/ (* 2 (L))) (norm^2 (nabla-phi x0 y))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-22)
		       (:instance norm-inner-product-equivalence
				  (vec (nabla-phi x0 y))))))))

;; claiming that phi of anything is larger than the minimizer of phi
(local (defthm lemma-24 
 (implies (and (real-listp y)  (= (len y) (DIM))
	       (real-listp x0) (= (len x0) (len y)))
	  (<= (phi x0 x0) 
	      (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance vec-+-closure-1
				 (vec1 y)
				 (vec2 (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y)))))
			(:instance vec-+-closure-2
				 (vec1 y)
				 (vec2 (scalar-* -1 (scalar-* (/ (L)) (nabla-phi x0 y)))))
		       (:instance scalar-*-closure 
				  (a (/ (L)))
				  (vec (nabla-phi x0 y)))
		       (:instance scalar-*-closure 
				  (a -1)
				  (vec (scalar-* (/ (L)) (nabla-phi x0 y))))
		       (:instance minimizer-of-phi 
		           	 (x x0)
				 (y (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))) ))))))

;; a quick lemma involving inequalities
(local (defthm lemma-25
 (implies (and (realp x) (realp y) (realp z)
	       (<= x y) (<= y z))
	  (<= x z))))

;; a quick lemma about what is real
(local (defthm lemma-26
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x)))
	  (realp (+ (PHI X0 X)
                    (- (* (/ (L)) (NORM^2 (NABLA-PHI X0 X))))
                    (* 1/2 (/ (L)) (NORM^2 (NABLA-PHI X0 X))))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance phi-is-real (x x0) (y x))
			(:instance norm-is-real (vec (nabla-phi x0 x)))
			(:instance realp-L))))))

;; our thing is larger than the minimizer
(local (defthm lemma-27
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 x0)
	      (+ (phi x0 y) 
		 (* (/ -1 (L)) (norm^2 (nabla-phi x0 y)))
		 (* (/ (* 2 (L))) (norm^2 (nabla-phi x0 y))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-23)
		       (:instance phi-is-real (x x0) (y x))
		       (:instance lemma-26)
		       (:instance lemma-25
				  (x (phi x0 x0))
				  (y (phi x0 (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))))
				  (z (+ (phi x0 y) 
		 			(* (/ -1 (L)) (norm^2 (nabla-phi x0 y)))
		 			(* (/ (* 2 (L))) (norm^2 (nabla-phi x0 y))))))
		       (:instance lemma-24))))))

;; lemma for combining like terms involving norm
(local (defthm lemma-28
 (implies (and (realp x) (realp y))
	  (equal (+ x
		    (* (/ -1 (L)) y)
		    (* (/ (* 2 (L))) y))
		 (+ x (* (/ -1 2) (/ (L)) y))))))

;; combining like terms involving norm
(local (defthm lemma-29
 (implies (and (real-listp x0) (real-listp y) (= (len x0) (len y)))
	  (equal (+ (phi x0 y) 
		    (* (/ -1 (L)) (norm^2 (nabla-phi x0 y)))
		    (* (/ (* 2 (L)))  (norm^2 (nabla-phi x0 y))))
		 (+ (phi x0 y) 
		    (* (/ -1 2) (/ (L)) (norm^2 (nabla-phi x0 y))))))
 :hints (("GOAL" :use ((:instance lemma-28
				  (x (phi x0 y))
				  (y (norm^2 (nabla-phi x0 y)))))))))

;; actually combining like terms involving norm
(local (defthm lemma-30
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (phi x0 x0)
	      (+ (phi x0 y) 
		 (* (/ -1 2) (/ (L)) (norm^2 (nabla-phi x0 y))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-27)
		       (:instance lemma-29))))))

;; identities to substitute phi
(local (defthm lemma-31
 (implies (and (real-listp x0) (= (len x0) (DIM))
	       ;; replace y with y* and x with y
	       (real-listp y) (= (len y) (len x0)))
  	  (and (equal (phi x0 x0) (- (mvfn x0) (dot (nabla-mvfn x0) x0)))
	       (equal (phi x0 y) (- (mvfn y) (dot (nabla-mvfn x0) y)))
	       (equal (nabla-phi x0 y) (vec-- (nabla-mvfn y) (nabla-mvfn x0)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance nabla-phi-identity (x x0) (y y))
		       (:instance phi-identity (x x0) (y x0))
		       (:instance phi-identity (x x0)))))))
		 

;; actually combining like terms involving norm
(local (defthm lemma-32
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (- (mvfn x0) (dot (nabla-mvfn x0) x0))
	      (+ (- (mvfn y) 
		    (dot (nabla-mvfn x0) y))
		 (* (/ -1 2) (/ (L)) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x0))))))) 
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-30)
		       (:instance lemma-31)
 		       (:instance phi-identity (x x0) (y x0))
		       (:instance phi-identity (x x0)))))))

;; moving to the other side of the inequality
(local (defthm lemma-33
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (+ (mvfn x0) 
		 (dot (nabla-mvfn x0) y)
		 (- (dot (nabla-mvfn x0) x0)) 
		 (* (/ 2) (/ (L)) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x0)))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-32))))))

;; beginning to combine the inner products
(local (defthm lemma-34
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (+ (mvfn x0) 
		 (dot (nabla-mvfn x0) y)
		 (dot (nabla-mvfn x0) (scalar-* -1 x0))
		 (* (/ 2) (/ (L)) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x0)))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-32)
		       (:instance dot-linear-second-coordinate-1 
				  (a -1)
				  (vec2 x0)
				  (vec1 (nabla-mvfn x0))))))))

(local (defthm lemma-35 ;ineq-1-implies-ineq-2
 (implies (and (real-listp x) (real-listp y*) (= (len y*) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (= y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y))))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (+ (mvfn x0) 
		 (dot (nabla-mvfn x0) (vec-- y x0))
		 (* (/ 2) (/ (L)) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x0)))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-34)
		       (:instance scalar-*-closure (a -1) (vec (nabla-mvfn x0)))
		       (:instance scalar-*-closure (a -1) (vec x0))
		       (:instance dot-linear-second-coordinate-2
				  (vec1 (nabla-mvfn x0))
				  (vec2 y)
				  (vec3 (scalar-* -1 x0))))))))

;; getting rid of y*
(local (defthm lemma-36
 (let ((y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))))
 (implies (and (real-listp x) 
	       (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       ;; replace y with y* and x with y
	       (= x y)
	       (real-listp y) (= (len y) (len x))
	       (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*))))
	  (<= (+ (mvfn x0) 
		 (dot (nabla-mvfn x0) (vec-- y x0))
		 (* (/ 2) (/ (L)) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x0)))))
	      (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-35 (y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))))
		       (:instance scalar-*-closure 
				  (a (- (/ (L))))
				  (vec (vec-+ (nabla-mvfn x) (scalar-* -1 (nabla-mvfn x0))))))))))

(local (defthm lemma-37
 (let ((y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))))
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       (<= (mvfn y*) 
       		   (+ (mvfn x) (dot (nabla-mvfn x) (vec-- y* x)) (* (/ (L) 2) (metric^2 y* x)))))
	  (<= (+ (phi x0 y*) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y* x))))
	      	   (* (/ (L) 2) (metric^2 x y*)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance mvfn-ineq-1-implies-phi-ineq-1 (y (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))))
		       (:instance scalar-*-closure 
				  (a (- (/ (L))))
				  (vec (vec-- (nabla-mvfn y) (nabla-mvfn x0))))
		       (:instance scalar-*-closure 
				  (a (- (/ (L))))
				  (vec (vec-+ (nabla-mvfn x) (scalar-* -1 (nabla-mvfn x0))))))))))

;; replacing phi-ineq with ineq-1
(local (defthm lemma-38
 (let ((y* (vec-- y (scalar-* (/ (L)) (nabla-phi x0 y)))))
 (implies (and (real-listp x) (real-listp y) 
	       (= (len y) (len x)) (= (len x) (DIM))
	       (= x y)
	       (real-listp x0) (= (len x0) (len x))
	       (<= (mvfn y*) 
       		   (+ (mvfn x) (dot (nabla-mvfn x) (vec-- y* x)) (* (/ (L) 2) (metric^2 y* x)))))
	  (<= (+ (mvfn x0) 
		 (dot (nabla-mvfn x0) (vec-- y x0))
		 (* (/ 2) (/ (L)) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x0)))))
	      (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-36)
		       (:instance lemma-37))))))

;; replacing x0 with x and x with y
(local (defthm lemma-39 
 (let ((y* (vec-- y (scalar-* (/ (L)) (nabla-phi x y)))))
 (implies (and (real-listp x) (real-listp y) 
	       (= (len y) (len x)) (= (len x) (DIM))
	       (<= (mvfn y*) 
       		   (+ (mvfn y) (dot (nabla-mvfn y) (vec-- y* y)) (* (/ (L) 2) (metric^2 y* y)))))
	  (<= (+ (mvfn x) 
		 (dot (nabla-mvfn x) (vec-- y x))
		 (* (/ 2) (/ (L)) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x)))))
	      (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-38 (x0 x) (x y)))))))

;; random thing to get the proper form
(local (defthm lemma-40
	   (equal (+ (mvfn x) 
		     (dot (nabla-mvfn x) (vec-- y x))
		     (* (/ 2) (/ (L)) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x)))))
		  (+ (mvfn x) 
		     (dot (nabla-mvfn x) (vec-- y x))
		     (* (/ (* 2 (L))) (norm^2 (vec-- (nabla-mvfn y) (nabla-mvfn x))))))))

;; replacing x0 with x and x with y
(defthm ineq-1-implies-ineq-2-expanded
  (implies (and (real-listp x) (real-listp y) 
	        (= (len y) (len x)) (= (len x) (DIM))
	        (<= (mvfn (vec-- y (scalar-* (/ (L)) (nabla-phi x y))))
       	            (+ (mvfn y) 
		       (dot (nabla-mvfn y) (vec-- (vec-- y (scalar-* (/ (L)) (nabla-phi x y))) y))
		       (* (* (L) 1/2) (metric^2 (vec-- y (scalar-* (/ (L)) (nabla-phi x y))) y)))))
	   (<= (+ (mvfn x) 
		  (dot (nabla-mvfn x) (vec-- y x))
		  (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	       (mvfn y)))
  :hints (("GOAL" :in-theory (e/d (metric^2) 
				  (distributivity-of-/-over-*))
		  :do-not-induct t
		  :use ((:instance lemma-40)
			(:instance lemma-39)))))
) ;; end of ineq. 1 implies ineq. 2


(local (in-theory (disable scalar-*--1)))

;; 
;;
;; ineq 2 implies ineq 3
;;
;; 2.1.7 => 2.1.8 in Nesterov's text
;;
;;
 (encapsulate
  ()

  (local (in-theory (disable vec-+-commutativity)))

  ;; slowly just do algebra....
  (local
   (defthm lemma-2
    (implies (and (real-listp x) (real-listp y) 
	   	  (= (len x) (len y)) (= (len y) (DIM))
  	 	  (<= (+ (mvfn x) 
			 (dot (nabla-mvfn x) (vec-- y x)) 
		      	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	     	      (mvfn y))
		  (<= (+ (mvfn y) 
			 (dot (nabla-mvfn y) (vec-- x y)) 
	   	    	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		      (mvfn x)))
	     (<= (+ (dot (nabla-mvfn x) (vec-- y x)) 
		    (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y)))
		    (dot (nabla-mvfn y) (vec-- x y)) 
	   	    (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		 0))))

  ;; simple lemma to guide lemma-4
  (local 
   (defthm lemma-3
    (implies (and (real-listp x) (real-listp y) 
	   	  (= (len x) (len y)) (= (len y) (DIM)))
    	     (= (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x)))
		(* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y)))))
    :hints (("GOAL" :do-not-induct t
		    :use (:instance metric-commutativity (vec1 (nabla-mvfn y)) (vec2 (nabla-mvfn x)))))))
		
  ;; some more algebra
  (local
   (defthm lemma-4
    (implies (and (real-listp x) (real-listp y) 
	   	  (= (len x) (len y)) (= (len y) (DIM))
  	 	  (<= (+ (mvfn x) 
			 (dot (nabla-mvfn x) (vec-- y x)) 
		      	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	     	      (mvfn y))
		  (<= (+ (mvfn y) 
			 (dot (nabla-mvfn y) (vec-- x y)) 
	   	    	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		      (mvfn x)))
	     (<= (+ (dot (nabla-mvfn x) (vec-- y x)) 
		    (dot (nabla-mvfn y) (vec-- x y)) 
	   	    (* (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
		 0))
    :hints (("GOAL" :do-not-induct t
		    :use ((:instance lemma-2)
			  (:instance lemma-3))))))

  ;; some more algebra
  (local
   (defthm lemma-5
    (implies (and (real-listp x) (real-listp y) 
	   	  (= (len x) (len y)) (= (len y) (DIM))
  	 	  (<= (+ (mvfn x) 
			 (dot (nabla-mvfn x) (vec-- y x)) 
		      	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	     	      (mvfn y))
		  (<= (+ (mvfn y) 
			 (dot (nabla-mvfn y) (vec-- x y)) 
	   	    	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		      (mvfn x)))
	     (<= (+ (* -1 (dot (nabla-mvfn x) (vec-- x y)) )
		    (dot (nabla-mvfn y) (vec-- x y)) 
	   	    (* (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
		 0))
    :hints (("GOAL" :do-not-induct t
		    :use ((:instance lemma-4)
			  (:instance vec---anticommutativity (vec1 y) (vec2 x)))))))

  ;; oh look more algebra
  (local
   (defthm lemma-6
    (implies (and (real-listp x) (real-listp y) 
	   	  (= (len x) (len y)) (= (len y) (DIM))
  	 	  (<= (+ (mvfn x) 
			 (dot (nabla-mvfn x) (vec-- y x)) 
		      	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	     	      (mvfn y))
		  (<= (+ (mvfn y) 
			 (dot (nabla-mvfn y) (vec-- x y)) 
	   	    	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		      (mvfn x)))
	     (<= (* (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn y)))
		 (+ (dot (nabla-mvfn x) (vec-- x y))
		    (- (dot (nabla-mvfn y) (vec-- x y))))))
    :hints (("GOAL" :do-not-induct t
		    :use ((:instance lemma-5))))))

  ;; maybe smtlink would be really helpful
  (local
   (defthm lemma-7
    (implies (and (real-listp x) (real-listp y) 
	   	  (= (len x) (len y)) (= (len y) (DIM))
  	 	  (<= (+ (mvfn x) 
			 (dot (nabla-mvfn x) (vec-- y x)) 
		      	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	     	      (mvfn y))
		  (<= (+ (mvfn y) 
			 (dot (nabla-mvfn y) (vec-- x y)) 
	   	    	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		      (mvfn x)))
	     (<= (* (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn y)))
		 (+ (dot (nabla-mvfn x) (vec-- x y))
		    (dot (scalar-* -1 (nabla-mvfn y)) (vec-- x y)))))
    :hints (("GOAL" :do-not-induct t
		    :use ((:instance lemma-6))))))

(in-theory (disable dot-with-zvec-is-zero))

  ;; but we will need a way for smtlink to support inner products
  (local
   (defthm lemma-8
    (implies (and (real-listp x) (real-listp y) 
	   	  (= (len x) (len y)) (= (len y) (DIM))
  	 	  (<= (+ (mvfn x) 
			 (dot (nabla-mvfn x) (vec-- y x)) 
		      	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	     	      (mvfn y))
		  (<= (+ (mvfn y) 
			 (dot (nabla-mvfn y) (vec-- x y)) 
	   	    	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		      (mvfn x)))
	     (<= (* (/ (L)) (metric^2 (nabla-mvfn x) (nabla-mvfn y)))
		 (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
		      (vec-- x y))))
    :hints (("GOAL" :do-not-induct t
		    :in-theory (disable dot-commutativity lemma-6)
		    :use ((:instance lemma-7)
			  (:instance scalar-*-closure (a -1) (vec (nabla-mvfn y)))
			  (:instance dot-linear-first-coordinate-2 (vec1 (nabla-mvfn x)) (vec2 (scalar-* -1 (nabla-mvfn y))) (vec3 (vec-- x y))))))))

;; finally done algebra!
   (defthm ineq-2-implies-ineq-3-expanded 
    (implies (and (real-listp x) (real-listp y) 
	   	  (= (len x) (len y)) (= (len y) (DIM))
  	 	  (<= (+ (mvfn x) 
			 (dot (nabla-mvfn x) (vec-- y x)) 
		      	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	     	      (mvfn y))
		  (<= (+ (mvfn y) 
			 (dot (nabla-mvfn y) (vec-- x y)) 
	   	    	 (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		      (mvfn x)))
	     (<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
		 (* (L) 
		    (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
			 (vec-- x y)))))
    :hints (("GOAL" :do-not-induct t
		    :in-theory (enable realp-L)
		    :use ((:instance lemma-8)
			  (:instance L>0)
			  (:instance realp-L)))))
) ;; end of ineq. 2 implies ineq. 3





;; ineq 3 implies ineq 0
(encapsulate 
 nil 

(local (in-theory (disable eu-metric-metric-sq-equivalence)))

;; random inequality 
 (local (defthm lemma-1
  (implies (and (realp a) (realp b) (realp c) (<= 0 c) (<= (abs a) b))
	   (<= (* c a) (* c b)))))

;; applying cauchy-schwarz
 (local (defthm lemma-2
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
		(<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
	       	    (* (L) (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
			        (vec-- x y)))))
	   (<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
	       (* (L) (* (eu-norm (vec-- (nabla-mvfn x) (nabla-mvfn y))) 
			 (eu-norm (vec-- x y))))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable associativity-of-* <-*-left-cancel)
		  :use ((:instance lemma-1 
				   (a (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
					   (vec-- x y)))
				   (b (* (eu-norm (vec-- (nabla-mvfn x) (nabla-mvfn y)))
					 (eu-norm (vec-- x y))))
				   (c (L)))
			(:instance cauchy-schwarz-2 
				   (u (vec-- (nabla-mvfn x) (nabla-mvfn y)))
				   (v (vec-- x y))))))))

;; expanding definitions
(local (defthm lemma-3
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
		(<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
	       	    (* (L) (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
			        (vec-- x y)))))
	   (<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
	       (* (L) (eu-metric (nabla-mvfn x) (nabla-mvfn y)) (eu-metric x y))))
  :hints (("GOAL" :use ((:instance lemma-2))
		  :expand ((eu-metric (nabla-mvfn x) (nabla-mvfn y)) (eu-metric x y))))))
 
;; more expanding definitions
(local (defthm lemma-4
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
		(<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
	       	    (* (L) (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
			        (vec-- x y)))))
	   (<= (* (eu-metric (nabla-mvfn x) (nabla-mvfn y))
		  (eu-metric (nabla-mvfn x) (nabla-mvfn y)))
	       (* (L) (eu-metric (nabla-mvfn x) (nabla-mvfn y)) (eu-metric x y))))
  :hints (("GOAL" :in-theory (disable eu-metric)
		  :use ((:instance lemma-3)
			(:instance eu-metric-metric-sq-equivalence 
				   (x (nabla-mvfn x))
				   (y (nabla-mvfn y))))))))
		  
;; another random inequality
(local (defthm lemma-5
 (implies (and (realp a) (realp b) (realp c) (<= (* a a) (* b a c)) (<= 0 b) (<= 0 c))
	  (<= a (* b c)))))

;; simplifying to obtain desired inequality 
(defthm ineq-3-implies-ineq-0-expanded
  (implies (and (real-listp x) (real-listp y) 
		(= (len y) (len x)) (= (len x) (DIM))
		(<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
	       	    (* (L) (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
			        (vec-- x y)))))
	   (<= (eu-metric (nabla-mvfn x) (nabla-mvfn y))
	       (* (L) (eu-metric x y))))
  :hints (("GOAL" :use ((:instance lemma-4)
			(:instance lemma-5
				   (a (eu-metric (nabla-mvfn x) (nabla-mvfn y)))
				   (b (L))
			   	   (c (eu-metric x y)))))))
)



