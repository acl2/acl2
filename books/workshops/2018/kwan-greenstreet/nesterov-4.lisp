;;
;; This book defines the Skolem functions of the inequalities 
;; and states the final form of Nesterov's theorem
;;

; cert_param: (uses-acl2r)

(in-package "ACL2")

(include-book "nesterov-3")

;; Preparing for the final form
(encapsulate
 (((hypotheses * *) => *)
  ((alpha-hypotheses * *) => *)
  ((alpha->-0-hypotheses *) => *)
  ((st-hypotheses *) => * :classicalp nil))

;; 
;; Defining Skolem functions for each inequalities and their
;; "expanded form".
;;

;; ineq-0 (Lipschitz Continuity)
(defun-sk ineq-0 (L)
 (forall (x y)
  (<= (eu-metric (nabla-mvfn x) (nabla-mvfn y))
      (* L (eu-metric x y))))
 :rewrite
 :direct
 :classicalp nil)

 (local (defthm ineq-0-expanded 
  (implies (ineq-0 (L))
	   (<= (eu-metric (nabla-mvfn x) (nabla-mvfn y))
      	       (* (L) (eu-metric x y))))
  :hints (("GOAL" :in-theory (disable eu-metric)))))


 ;; ineq-1
 (defun-sk ineq-1 (L)
  (forall (x y)
   (<= (mvfn y) 
       (+ (mvfn x) (dot (nabla-mvfn x) (vec-- y x)) (* (/ L 2) (metric^2 y x)))))
  :rewrite
  :direct
  :classicalp nil)

;; We require two expansions of ineq-1 for both ineq-6 and ineq-2
(encapsulate 
 nil

 (local (defthm lemma-1
  (implies (ineq-1 (L))
	   (<= (mvfn y) 
       	       (+ (mvfn x) (dot (nabla-mvfn x) (vec-- y x)) (* (/ (L) 2) (metric^2 y x)))))
  :hints (("GOAL" :in-theory (disable associativity-of-*
				      commutativity-of-*
				      commutativity-of-+)))))

 (defthm ineq-1-expanded-v1
   (implies (ineq-1 (L))
	    (<= (mvfn (vec-- y (scalar-* (/ (L)) (nabla-phi x y))))
       	        (+ (mvfn y) 
		   (dot (nabla-mvfn y) (vec-- (vec-- y (scalar-* (/ (L)) (nabla-phi x y))) y))
		   (* (/ (L) 2) (metric^2 (vec-- y (scalar-* (/ (L)) (nabla-phi x y))) y)))))
   :hints (("GOAL" :in-theory (disable associativity-of-*
				       commutativity-of-*
				       commutativity-of-+))))

 (defthm ineq-1-expanded-v2
   (implies (ineq-1 (L))
	    (and (<= (mvfn x)
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
					    (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))))
  :hints (("GOAL" :use ((:instance lemma-1 (x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
			(:instance lemma-1 
				   (y x)
				   (x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))))
)

 ;; ineq-2
 (defun-sk ineq-2 (L)
  (forall (x y)
   (<= (+ (mvfn x) 
	  (dot (nabla-mvfn x) (vec-- y x)) 
	  (* (/ (* 2 L)) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
       (mvfn y)))
  :rewrite
  :direct
  :classicalp nil)

;; we again require two expansions of ineq-2 for ineq-5 and ineq-3
(encapsulate 
 nil

 (local (defthm lemma-1
  (implies (ineq-2 (L))
	   (and (<= (+ (mvfn x) 
	  	       (dot (nabla-mvfn x) (vec-- y x))
	  	       (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
       	       	    (mvfn y))))
  :hints (("GOAL" :in-theory (disable unary-/ distributivity-of-/-over-* commutativity-of-+)))))

 ;; used in ineq-2-implies-ineq-3
 (defthm ineq-2-expanded-v1
  (implies (ineq-2 (L))
	   (and (<= (+ (mvfn x) 
	  	       (dot (nabla-mvfn x) (vec-- y x))
	  	       (* (/ (* 2 (L))) (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
       	       	    (mvfn y))
		(<= (+ (mvfn y) 
	  	       (dot (nabla-mvfn y) (vec-- x y))
	  	       (* (/ (* 2 (L))) (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
       	       	    (mvfn x))))
  :hints (("GOAL" :use ((:instance lemma-1)
			(:instance lemma-1 (x y) (y x))))))

 ;; used in ineq-2-implies-ineq-5
 (defthm ineq-2-expanded-v2
  (implies (ineq-2 (L))
	   (and (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
	  	       (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		       	    (vec-- y (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
	  	       (* (/ (* 2 (L))) 
		       	  (metric^2 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			     	  (nabla-mvfn y))))
       	       	    (mvfn y))
		(<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
	  	       (dot (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
		       	    (vec-- x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
	  	       (* (/ (* 2 (L))) 
		       	  (metric^2 (nabla-mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))) 
			     	  (nabla-mvfn x))))
       	       	    (mvfn x))))
  :hints (("GOAL" :in-theory (disable distributivity-of-/-over-* commutativity-of-+)
		  :use ((:instance lemma-1 
				   (y x)
				   (x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))
			(:instance lemma-1 
				   (x (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y))))))))
)

 ;; ineq-3
 (defun-sk ineq-3 (L)
  (forall (x y)
   (<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
       (* L 
	  (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
	       (vec-- x y)))))
  :rewrite
  :direct 
  :classicalp nil)

 (local (defthm ineq-3-expanded
  (implies (ineq-3 (L))
	   (<= (metric^2 (nabla-mvfn x) (nabla-mvfn y))
       	       (* (L)
	  	  (dot (vec-- (nabla-mvfn x) (nabla-mvfn y))
	       	       (vec-- x y)))))))

;; ineq-4
(defun-sk ineq-4 (L)
 (forall (x y)
  (<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
      (* L (metric^2 x y))))
 :rewrite
 :direct
 :classicalp nil)

(local (defthm ineq-4-expanded
 (implies (ineq-4 (L))
	  (<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
	      (* (L) (metric^2 x y))))))

;; ineq-5
(defun-sk ineq-5 (L)
 (forall (x y alpha)
  (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
	 (* (/ (* 2 L))
	    (* alpha (- 1 alpha) (metric^2 (nabla-mvfn x) (nabla-mvfn y)))))
      (+ (* alpha (mvfn x)) (* (- 1 alpha) (mvfn y)))))
 :rewrite
 :direct
 :classicalp nil)

(defthm ineq-5-expanded
 (implies (ineq-5 (L))
  	  (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
	 	 (* (/ (* 2 (L)))
	    	    (* alpha (- 1 alpha) (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
      	      (+ (* alpha (mvfn y)) (* (- 1 alpha) (mvfn x)))))
 :hints (("GOAL" :in-theory (disable associativity-of-*
				     commutativity-of-+
				     commutativity-of-*
				     commutativity-2-of-*
				     distributivity
				     distributivity-of-/-over-*))))

;;
;; ineq-6
;; - oddly enough this doesn't require ":classicalp nil"
;;
(defun-sk ineq-6 (L) 
 (forall (x y alpha)
  (<= (+ (* alpha (mvfn x))
	 (* (- 1 alpha) (mvfn y)))
      (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
	 (* (/ L 2) alpha (- 1 alpha) (metric^2 x y)))))
 :rewrite
 :direct)
 ;:classicalp nil) <----- ?????

(local (defthm ineq-6-expanded
 (implies (ineq-6 (L))
	  (<= (+ (* alpha (mvfn y))
		 (* (- 1 alpha) (mvfn x)))
	      (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		 (* (/ (L) 2) alpha (- 1 alpha) (metric^2 y x)))))
 :hints (("GOAL" :in-theory (disable associativity-of-*
				     commutativity-of-+
				     commutativity-of-*
				     commutativity-2-of-*
				     distributivity
				     distributivity-of-/-over-*)))))

;; 
;; Some functions for stating the hypotheses that maintain the vectors are
;; from the correct dimension of R^n 
;;
(local (defun hypotheses (w dim)
 (and (real-listp (mv-nth 0 w))
      (real-listp (mv-nth 1 w))
      (= (len (mv-nth 1 w))
      	 (len (mv-nth 0 w)))
      (= (len (mv-nth 0 w)) dim))))

(local (defun alpha-hypotheses (w dim)
 (and (real-listp (mv-nth 0 w))
      (real-listp (mv-nth 1 w))
      (= (len (mv-nth 1 w))
      	 (len (mv-nth 0 w)))
      (= (len (mv-nth 0 w)) dim)
      (realp (mv-nth 2 w))
      (<= 0 (mv-nth 2 w))
      (<= (mv-nth 2 w) 1))))

(local (defun alpha->-0-hypotheses (w)
 (and (realp (mv-nth 2 w))
      (< 0 (mv-nth 2 w))
      (<= (mv-nth 2 w) 1))))

(local (defun st-hypotheses (w)
 (and (standard-vecp (mv-nth 0 w))
      (standard-vecp (mv-nth 1 w)))))

;;
;; Finally, stating each edge in the implication graph 
;;
(defthm ineq-0-implies-ineq-4
  (implies (and (hypotheses (ineq-4-witness (L)) (DIM))
		(ineq-0 (L)))
	   (ineq-4 (L)))
  :hints (("GOAL" :use ((:instance ineq-0-expanded
				   (x (mv-nth 0 (ineq-4-witness (L))))
				   (y (mv-nth 1 (ineq-4-witness (L)))))
			(:instance ineq-0-implies-ineq-4-expanded
				   (x (mv-nth 0 (ineq-4-witness (L))))
				   (y (mv-nth 1 (ineq-4-witness (L)))))))))

(defthm ineq-4-implies-ineq-1
  (implies (and (hypotheses (ineq-1-witness (L)) (DIM))
		(ineq-4 (L)))
	   (ineq-1 (L)))
  :hints (("GOAL" :use ((:instance ineq-4-expanded
				   (x (mv-nth 0 (ineq-1-witness (L))))
				   (y (mv-nth 1 (ineq-1-witness (L)))))
			(:instance ineq-4-implies-ineq-1-expanded
				   (x (mv-nth 0 (ineq-1-witness (L))))
				   (y (mv-nth 1 (ineq-1-witness (L)))))))))

(defthm ineq-1-implies-ineq-2
  (implies (and (hypotheses (ineq-2-witness (L)) (DIM))
		(ineq-1 (L)))
	   (ineq-2 (L)))
  :hints (("GOAL" :use ((:instance ineq-1-expanded-v1
				   (x (mv-nth 0 (ineq-2-witness (L))))
				   (y (mv-nth 1 (ineq-2-witness (L)))))
			(:instance ineq-1-implies-ineq-2-expanded
				   (x (mv-nth 0 (ineq-2-witness (L))))
				   (y (mv-nth 1 (ineq-2-witness (L)))))))))

(defthm ineq-2-implies-ineq-3
  (implies (and (hypotheses (ineq-3-witness (L)) (DIM))
		(ineq-2 (L)))
	   (ineq-3 (L)))
  :hints (("GOAL" :use ((:instance ineq-2-expanded-v1
				   (x (mv-nth 0 (ineq-3-witness (L))))
				   (y (mv-nth 1 (ineq-3-witness (L)))))
			(:instance ineq-2-implies-ineq-3-expanded
				   (x (mv-nth 0 (ineq-3-witness (L))))
				   (y (mv-nth 1 (ineq-3-witness (L)))))))))

(defthm ineq-3-implies-ineq-0
  (implies (and (hypotheses (ineq-0-witness (L)) (DIM))
		(ineq-3 (L)))
	   (ineq-0 (L)))
  :hints (("GOAL" :use ((:instance ineq-3-expanded
				   (x (mv-nth 0 (ineq-0-witness (L))))
				   (y (mv-nth 1 (ineq-0-witness (L)))))
			(:instance ineq-3-implies-ineq-0-expanded
				   (x (mv-nth 0 (ineq-0-witness (L))))
				   (y (mv-nth 1 (ineq-0-witness (L)))))))))

(defthm ineq-2-implies-ineq-5
  (implies (and (alpha-hypotheses (ineq-5-witness (L)) (DIM))
		(ineq-2 (L)))
	   (ineq-5 (L)))
  :hints (("GOAL" :use ((:instance ineq-2-expanded-v2
				   (alpha (mv-nth 2 (ineq-5-witness (L))))
				   (x (mv-nth 0 (ineq-5-witness (L)))) 
				   (y (mv-nth 1 (ineq-5-witness (L)))))
			(:instance ineq-2-implies-ineq-5-expanded
				   (alpha (mv-nth 2 (ineq-5-witness (L))))
				   (x (mv-nth 0 (ineq-5-witness (L))))
				   (y (mv-nth 1 (ineq-5-witness (L)))))))))

(defthm ineq-1-implies-ineq-6
  (implies (and (alpha-hypotheses (ineq-6-witness (L)) (DIM))
		(ineq-1 (L)))
	   (ineq-6 (L)))
  :hints (("GOAL" :use ((:instance ineq-1-expanded-v2
				   (alpha (mv-nth 2 (ineq-6-witness (L))))
				   (x (mv-nth 0 (ineq-6-witness (L))))
				   (y (mv-nth 1 (ineq-6-witness (L)))))
			(:instance ineq-1-implies-ineq-6-expanded
				   (alpha (mv-nth 2 (ineq-6-witness (L))))
				   (x (mv-nth 0 (ineq-6-witness (L))))
				   (y (mv-nth 1 (ineq-6-witness (L)))))))))


(defthm ineq-5-implies-ineq-2
  (implies (and (st-hypotheses (ineq-2-witness (L)))
		(hypotheses (ineq-2-witness (L)) (DIM))
		(alpha->-0-hypotheses (ineq-5 (L)))
		(ineq-5 (L)))
	   (ineq-2 (L)))
  :hints (("GOAL" :use ((:instance ineq-5-expanded
				   (x (mv-nth 0 (ineq-2-witness (L))))
				   (y (mv-nth 1 (ineq-2-witness (L)))))
			(:instance ineq-5-implies-ineq-2-expanded
				   (alpha (mv-nth 2 (ineq-5-witness (L))))
				   (x (mv-nth 0 (ineq-2-witness (L))))
				   (y (mv-nth 1 (ineq-2-witness (L)))))))))
		
(defthm ineq-6-implies-ineq-1
  (implies (and (hypotheses (ineq-1-witness (L)) (DIM))
		(st-hypotheses (ineq-1-witness (L)))
		(alpha->-0-hypotheses (ineq-6 (L)))
		(ineq-6 (L)))
	   (ineq-1 (L)))
  :hints (("GOAL" :use ((:instance ineq-6-expanded
				   (x (mv-nth 0 (ineq-1-witness (L))))
				   (y (mv-nth 1 (ineq-1-witness (L)))))
			(:instance ineq-6-implies-ineq-1-expanded
				   (alpha (mv-nth 2 (ineq-6-witness (L))))
				   (x (mv-nth 0 (ineq-1-witness (L))))
				   (y (mv-nth 1 (ineq-1-witness (L)))))))))
)


;;
;; The final forms of Nesterov's theorem
;;
(defthm nesterov-pt-1
 (implies (and (hypotheses (ineq-0-witness (L)) (DIM))
	       (hypotheses (ineq-4-witness (L)) (DIM))
	       (hypotheses (ineq-1-witness (L)) (DIM))
	       (hypotheses (ineq-2-witness (L)) (DIM))
	       (hypotheses (ineq-3-witness (L)) (DIM))
	       (or (ineq-0 (L))
		   (ineq-4 (L))
		   (ineq-1 (L))
		   (ineq-2 (L))
		   (ineq-3 (L))))
	  (and (ineq-0 (L))
	       (ineq-4 (L))
               (ineq-1 (L))
               (ineq-2 (L))
               (ineq-3 (L))))
 :hints (("GOAL" :use ((:instance ineq-0-implies-ineq-4)
		       (:instance ineq-4-implies-ineq-1)
		       (:instance ineq-1-implies-ineq-2)
		       (:instance ineq-2-implies-ineq-3)
		       (:instance ineq-3-implies-ineq-0)))))

(defthm nesterov
 (implies (and (hypotheses (ineq-0-witness (L)) (DIM))
	       (hypotheses (ineq-4-witness (L)) (DIM))
	       (hypotheses (ineq-1-witness (L)) (DIM))
	       (hypotheses (ineq-2-witness (L)) (DIM))
	       (hypotheses (ineq-3-witness (L)) (DIM))
	       (st-hypotheses (ineq-1-witness (L)))
	       (st-hypotheses (ineq-2-witness (L)))
	       (alpha-hypotheses (ineq-6-witness (L)) (DIM))
	       (alpha-hypotheses (ineq-5-witness (L)) (DIM))
	       (alpha->-0-hypotheses (ineq-6 (L)))
	       (alpha->-0-hypotheses (ineq-5 (L)))
	       (or (ineq-0 (L))
		   (ineq-4 (L))
		   (ineq-1 (L))
		   (ineq-2 (L))
		   (ineq-3 (L))
		   (ineq-5 (L))
		   (ineq-6 (L))))
	  (and (ineq-0 (L))
	       (ineq-4 (L))
               (ineq-1 (L))
               (ineq-2 (L))
               (ineq-3 (L))
               (ineq-5 (L))
               (ineq-6 (L))))
 :hints (("GOAL" :use ((:instance nesterov-pt-1)
		       (:instance ineq-1-implies-ineq-6)
		       (:instance ineq-6-implies-ineq-1)
		       (:instance ineq-2-implies-ineq-5)
		       (:instance ineq-5-implies-ineq-2)))))

