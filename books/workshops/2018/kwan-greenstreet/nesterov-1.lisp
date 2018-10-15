;; 
;; This book contains the basic definitions for Nesterov's theorem
;; and the proofs of:
;;  ineq. 5 implies ineq. 2
;;  ineq. 6 implies ineq. 1
;;

; cert_param: (uses-acl2r)

(in-package "ACL2")

;; A necessary lemma that doesn't pass if nsa books are loaded
(local (defthm i-small-standard-part-zero
 (implies (and (realp alpha) (i-small alpha))
	  (equal (standard-part alpha) 0))))


(include-book "convex")

(encapsulate
 (((mvfn *) => *)
  ((differential-mvfn * *) => * :classicalp nil)
  ((nabla-mvfn *) => * :classicalp nil)
  ((phi * *) => * :classicalp nil)
  ((differential-phi * * *) => * :classicalp nil)
  ((nabla-phi * *) => * :classicalp nil)
  ((L) => *)
  ((DIM) => *)
  ((standard-vecp *) => * :classicalp nil))

 ;; constants
 (defconst *L* 1)
 (defconst *DIM* 2)
 
 ;; The dimension of the space
 (local (defun DIM () (declare (xargs :guard t)) *DIM*))
 (defthm dim-is-natural (natp (DIM)))
 (defthm dim->-0 (< 0 (DIM)))

 ;; Lipschitz constant L
 (local (defun L () *L*))

 ;; a set of silly theorems for use later
 (defthm L>0 (> (L) 0))
 (defthm realp-L (realp (L)))
 (defthm L-nonzero (not (= (L) 0)))
 (defthm L-is-standard (standardp (L)))
 (defthm L->=-0 (<= 0 (L)))
 (defthm random-L-lemma (<= 0 (* 1/2 (/ (L)))))
 (defthm random-L-lemma-2 (standardp (* 1/2 (/ (L)))))
 (defthm random-L-lemma-3 (i-limited (* 1/2 (/ (L)))))
 (defthm random-L-lemma-4 (i-limited (* 1/2 (L))))
 
 (local (in-theory (disable realp-L)))

;; since a vector being standard depends on the dimension, we define it here
(local (defun standard-vecp (vec)
 (and (real-listp vec) 
      (= (len vec) (DIM)) 
      (standardp (car vec)) (standardp (cadr vec)))))
(local (defthm standard-vec-has-standard
 (implies (standard-vecp vec)
	  (and (standardp (car vec)) (standardp (cadr vec))))))

 (local (in-theory (disable L)))

 ;; our witness function
 ;;  mvfn is some function
 (local 
  (defun mvfn (vec) 
   (declare (ignore vec) 
	    (xargs :guard (and (real-listp vec) (= (len vec) (DIM)))))
   42))

 (defthm mvfn-is-real
  (realp (mvfn vec)))

 ;; mvfn is continuous on R^n (metric^2-sq version)
 (defthm mvfn-is-continuous
  (implies (and (real-listp vec1) 
		(real-listp vec2)
		(= (len vec2) (len vec1))
		(= (len vec1) (DIM))
		(i-small (metric^2 vec1 vec2)))
	   (i-small (abs (- (mvfn vec1) (mvfn vec2)))))
  :hints (("GOAL" :in-theory (enable metric^2 norm^2))))

 (defthm mvfn-is-continuous-2
  (implies (and (real-listp vec1) 
		(real-listp vec2)
		(= (len vec2) (len vec1))
		(= (len vec1) (DIM))
		(i-small (metric^2 vec1 vec2)))
	   (i-small (- (mvfn vec1) (mvfn vec2))))
  :hints (("GOAL" :in-theory (enable metric^2 norm^2))))

 (defthm mvfn-is-continuous-3
  (implies (and (real-listp vec1) 
		(real-listp vec2)
		(= (len vec2) (len vec1))
		(= (len vec1) (DIM))
		(i-small (eu-metric vec1 vec2)))
	   (i-small (abs (- (mvfn vec1) (mvfn vec2))))))

 (defthm mvfn-returns-standard-on-standard
  (implies (and (standard-vecp x))
	   (acl2-numberp (mvfn x))))

;; defining the "differential" of mvfn
 (local 
  (defun differential-mvfn (vec eps)
   (list (standard-part 
   	  (/ (- (mvfn (list (+ (nth 1 vec) eps) (nth 2 vec)))
	        (mvfn vec))
	     eps))
 	 (standard-part 
	  (/ (- (mvfn (list (nth 1 vec) (+ (nth 2 vec) eps)))
	        (mvfn vec))
	     eps)))))

 ;; differential-mvfn has dimension (DIM)
  (defthm dimension-of-differential-mvfn
   	    (= (len (differential-mvfn vec eps)) (DIM))
   :hints (("GOAL" :do-not-induct t
		   :in-theory (enable mvfn scalar-* vec-+))))

 ;; the gradient of mvfn
 (local
  (defun nabla-mvfn (vec)
   (differential-mvfn vec (/ (i-large-integer)))))

 ;; nabla-mvfn has dimension 2
  (defthm dimension-of-nabla-mvfn
   (= (len (nabla-mvfn x)) (DIM)))

 ;; nabla-mvfn is real
  (defthm real-listp-nabla-mvfn
   (implies (real-listp x)
	    (real-listp (nabla-mvfn x))))

  (defthm differential-mvfn-is-real
   (implies (and (real-listp x)
 		(realp eps))
            (real-listp (differential-mvfn x eps))))

 ;; mvfn is differentiable
  (defthm mvfn-is-differentiable
   (implies (and (real-listp vec)
		 (real-listp h)
		 (= (len vec) (len h))
		 (= (len vec) (DIM))
		 (i-small (eu-norm h)))
	    (= (standard-part 
		(/ (abs (+ (mvfn (vec-+ vec h)) (- (mvfn vec)) (- (dot (nabla-mvfn vec) h))))
	           (eu-norm h)))
	       0))
   :hints (("GOAL" :do-not-induct t
		   :cases ((real-listp (vec-+ vec h)))
		   :in-theory (enable dot))))

;; Frechet derivative definition of the gradient
(defthm gradient-as-a-derivative
 (implies (and (real-listp vec1) (real-listp vec2) (realp eps) (i-small eps) (< 0 eps))
 	  (equal (standard-part (* (/ eps)
				   (- (mvfn (vec-+ vec1 (scalar-* eps vec2)))
				      (mvfn vec1))))
		 (dot (nabla-mvfn vec1) vec2)))
 :hints (("GOAL" :in-theory (enable dot))))


(local (defthm mvfn-convex-1
 (implies (and (real-listp x) (real-listp y) 
	       (= (len y) (len x)) (= (len x) (DIM))
	       (realp a) (<= 0 a) (<= a 1))
	  (<= (mvfn (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))
	      (+ (* a (mvfn x)) (* (- 1 a) (mvfn y)))))))

(local (defthm mvfn-convex-2
 (implies (and (real-listp x) (real-listp y) 
	       (= (len y) (len x)) (= (len x) (DIM))
	       (realp a) (<= 0 a) (<= a 1))
	  (<= (+ (mvfn x) (dot (nabla-mvfn x) (vec-- y x)))
	      (mvfn y)))
 :hints (("GOAL" :in-theory (enable dot)))))

;;
;; Some theorems about standard-vecp
;;

;; if vec is standard, then so is mvfn vec
(defthm standard-vec-standard-mvfn
 (implies (standard-vecp vec)
	  (standardp (mvfn vec))))

(defthm standard-vec-standard-nabla-mvfn
 (implies (standard-vecp vec)
	  (standard-vecp (nabla-mvfn vec))))

(defthm standard-vec-standard-norm^2
 (implies (and (standard-vecp vec))
	  (standardp (norm^2 vec)))
 :hints (("GOAL" :in-theory (enable norm^2))))

(defthm standard-vec-vec-+
 (implies (and (standard-vecp vec1) (standard-vecp vec2))
	  (standard-vecp (vec-+ vec1 vec2)))
 :hints (("GOAL" :in-theory (enable vec-+))))

(defthm standard-vec-scalar-*
 (implies (and (standard-vecp vec) (realp a) (standardp a))
	  (standard-vecp (scalar-* a vec)))
 :hints (("GOAL" :in-theory (enable scalar-*)
		 :use (:instance scalar-*-closure))))

(defthm standard-vec-metric
 (implies (and (standard-vecp vec1) (standard-vecp vec2))
	  (standardp (metric^2 vec1 vec2)))
 :hints (("GOAL" :in-theory (enable metric^2))))

;; Defining lemma based on integral of mvfn 
(local (include-book "ftc-2"))
(encapsulate
 ()

 (local 
  (defthm lemma-1
   (= (int-rcdfn-prime 0 1) (/ 2))
   :hints (("GOAL" :in-theory (enable svfn-rcdfn-domain-equivalence)
		   :use ((:instance svfn-2-ftc-2 (a 0) (b 1)))))))

 (local (defthm lemma-2
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
		(<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
		    (* (L) (metric^2 x y))))
	   (<= (abs (+ (mvfn y) (- (mvfn x)) (- (dot (nabla-mvfn x) (vec-- y x)))))
	       (* (L) (int-rcdfn-prime 0 1) (metric^2 y x))))))

(local (defthm lemma-3
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
		(<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
		    (* (L) (metric^2 x y))))
	   (<= (abs (+ (mvfn y) (- (mvfn x)) (- (dot (nabla-mvfn x) (vec-- y x)))))
	       (* (L) (/ 2) (metric^2 y x))))
  :hints (("GOAL" :use ((:instance lemma-2))))))

 ;; The LHS is less than ||y-x|| \int_0^1
 (defthm lemma-ineq-4
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
		(<= (dot (vec-- (nabla-mvfn x) (nabla-mvfn y)) (vec-- x y))
		    (* (L) (metric^2 x y))))
	   (<= (abs (+ (mvfn y) (- (mvfn x)) (- (dot (nabla-mvfn x) (vec-- y x)))))
 	       (* (/ (L) 2) (metric^2 y x)))))
)

;; Weird lemma that acl2r refuses to awknowledge
(defthm cdr-of-nabla-mvfn-is-real-listp
  (implies (and (real-listp vec) (= (len vec) (DIM)))
	   (and (real-listp (cdr (nabla-mvfn vec)))
		(= (len (cdr (nabla-mvfn vec))) (- (DIM) 1))))
  :hints (("GOAL" :use ((:instance dimension-of-nabla-mvfn)
			(:instance real-listp-nabla-mvfn)))))

 (defthm dot-i-small-mvfn-is-i-small
  (implies (and (real-listp vec1) 
		(real-listp vec2)
		(real-listp x)
		(= (len vec2) (len vec1))
		(= (len x) (len vec1))
		(= (len vec1) (DIM))
		(i-small (eu-metric vec1 vec2)))
	   (i-small (dot (vec-- vec1 vec2) (nabla-mvfn x))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (enable dot)
		  :use ((:instance eu-metric-i-small-implies-difference-of-entries-i-small (i 0))
			(:instance eu-metric-i-small-implies-difference-of-entries-i-small (i 1))))))

;;
;; This section could be further automated with a set of theorems about multivariate calculus
;;

;; Defining a helper function based on mvfn 
(local
(defun phi (x y) 
     (- (mvfn y) (dot (nabla-mvfn x) y))))

(defthm phi-identity
 (equal (phi x y)
	(- (mvfn y) (dot (nabla-mvfn x) y))))

 ;; defining the "differential" of phi
 (local 
  (defun differential-phi (vec1 vec2 eps)
   (list (standard-part 
   	  (/ (- (phi vec1 (list (+ (nth 1 vec2) eps) (nth 2 vec2)))
	        (phi vec1 vec2))
	     eps))
 	 (standard-part 
	  (/ (- (phi vec1 (list (nth 1 vec2) (+ (nth 2 vec2) eps)))
	        (phi vec1 vec2))
	     eps)))))

 ;; the gradient of phi
 (local
  (defun nabla-phi (vec1 vec2)
   (differential-phi vec1 vec2 (/ (i-large-integer)))))

 ;; phi is differentiable
  (defthm phi-is-differentiable
   (implies (and (real-listp vec) (real-listp x)
		 (real-listp h)
		 (i-small (norm^2 h)))
	    (= (standard-part 
		(/ (abs (+ (phi x (vec-+ vec h)) (- (phi x vec)) (- (dot (nabla-phi x vec) h))))
	           (norm^2 h)))
	       (- (nabla-mvfn vec) (nabla-mvfn x))))
   :hints (("GOAL" :in-theory (enable dot))))

(defthm nabla-phi-identity
	(implies (and (real-listp y) (= (len y) (DIM)) (real-listp x) (= (len x) (len y)))
		 (= (nabla-phi x y) (vec-- (nabla-mvfn y) (nabla-mvfn x))))
 	:hints (("GOAL" :in-theory (enable dot))))


(local (defthm phi-convex-1
 (implies (and (real-listp x) (real-listp y) (real-listp x0)
	       (= (len y) (len x)) (= (len x0) (len x)) 
	       (= (len x) (DIM))
	       (realp a) (<= 0 a) (<= a 1))
	  (<= (phi x0 (vec-+ (scalar-* a x) (scalar-* (- 1 a) y)))
	      (+ (* a (phi x0 x)) (* (- 1 a) (phi x0 y)))))
 :hints (("GOAL" :in-theory (enable dot)))))

(local (defthm phi-convex-2
 (implies (and (real-listp x) (real-listp y) (real-listp x0)
	       (= (len y) (len x)) (= (len x0) (len x)) 
	       (= (len x) (DIM))
	       (realp a) (<= 0 a) (<= a 1))
	  (<= (+ (phi x0 x) (dot (nabla-phi x0 x) (vec-- y x)))
	      (phi x0 y)))
 :hints (("GOAL" :in-theory (enable dot)))))


(defthm minimizer-of-phi
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (<= (phi x x) (phi x y)))
 :hints (("GOAL" :in-theory (enable dot))))

(defthm mvfn-ineq-1-implies-phi-ineq-1
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (real-listp x0) (= (len x0) (len x))
	       (<= (mvfn y) 
       		   (+ (mvfn x) (dot (nabla-mvfn x) (vec-- y x)) (* (/ (L) 2) (metric^2 y x)))))
	  (<= (+ (phi x0 y) (- (phi x0 x)) (- (dot (nabla-phi x0 x) (vec-- y x))))
	      	 (* (/ (L) 2) (metric^2 x y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (enable dot))))


 ;; Disable definitions
 (local (in-theory (disable (:d mvfn) (:e mvfn) (:t mvfn))))
 (local (in-theory (disable (:d nabla-mvfn) (:e nabla-mvfn) (:t nabla-mvfn))))
 (local (in-theory (disable (:d L) (:e L) (:t L))))

;; phi is real
(defthm phi-is-real 
 (implies (and (real-listp x) (real-listp y))
	  (realp (phi x y))))

;; proof that phi is continuous
(encapsulate
 nil
 (local (defthm lemma-1 
  (implies (and (real-listp vec1) 
		(real-listp vec2)
		(real-listp x)
		(= (len vec2) (len vec1))
		(= (len x) (len vec1))
		(= (len vec1) (DIM)))
	   (equal (+ (- (DOT VEC1 (NABLA-MVFN X)))
                     (DOT VEC2 (NABLA-MVFN X)))
		  (+ (dot (scalar-* -1 vec1) (nabla-mvfn x))
                     (DOT VEC2 (NABLA-MVFN X)))))))

;; <-x,z> + <y,z> = <y-x, z>
(local (defthm lemma-2
 (implies (and (real-listp vec1) (real-listp vec2) (real-listp vec3) 
	       (= (len vec2) (len vec1)) (= (len vec3) (len vec1)))
	  (equal (+ (dot (scalar-* -1 vec1) vec3) (dot vec2 vec3))
	     	 (dot (vec-- vec2 vec1) vec3)))
 :hints (("GOAL"
		 :use ((:instance scalar-*-closure (a -1) (vec vec1))
			(:instance dot-linear-first-coordinate-2 
				  (vec1 (scalar-* -1 vec1))))))))

 (local (defthm lemma-3
  (implies (and (real-listp vec1) 
		(real-listp vec2)
		(real-listp x)
		(= (len vec2) (len vec1))
		(= (len x) (len vec1))
		(= (len vec1) (DIM)))
	   (equal (+ (- (DOT VEC1 (NABLA-MVFN X)))
                     (DOT VEC2 (NABLA-MVFN X)))
		  (dot (vec-- vec2 vec1) (nabla-mvfn x))))
			      ;; some of these disabled rules were unexpected
  :hints (("GOAL" :in-theory (disable right-cancellation-for-+
			   	      dot-linear-first-coordinate-1
				      lemma-1)
		  :use ((:instance lemma-1)
			(:instance lemma-2
				   (vec3 (nabla-mvfn x))))))))

 (local (defthm lemma-4
  (implies (and (realp x) (realp y) (i-small x) (i-small y))
	   (i-small (+ x y)))))

 (local (defthm lemma-5
  (implies (and (real-listp x) (real-listp vec1) (real-listp vec2)
		(= (len vec1) (DIM)) (= (len vec2) (len vec1)) (= (len x) (len vec1)))
	   (= (+ (+ (mvfn vec1) (- (mvfn vec2)))
		 (dot (nabla-mvfn x) (vec-- vec2 vec1)))
	      (- (phi x vec1) (phi x vec2))))
  :hints (("GOAL" :use ((:instance lemma-3))
		  :do-not-induct t))))

 (local (defthm lemma-6
  (implies (and (real-listp x) (real-listp vec1) (real-listp vec2)
		(= (len vec1) (DIM)) (= (len vec2) (len vec1)) (= (len x) (len vec1))
		(i-small (+ (mvfn vec1) (- (mvfn vec2))))
		(i-small (dot (nabla-mvfn x) (vec-- vec2 vec1))))
	   (i-small (+ (+ (mvfn vec1) (- (mvfn vec2)))
		       (dot (nabla-mvfn x) (vec-- vec2 vec1)))))
  :hints (("GOAL" :use ((:instance lemma-4 (x (+ (mvfn vec1) (- (mvfn vec2))))
					   (y (dot (nabla-mvfn x) (vec-- vec2 vec1)))))
		  :do-not-induct t))))

 (local (defthm lemma-7-1 
  (implies (and (real-listp x) (real-listp vec1) (real-listp vec2)
		(= (len vec1) (DIM)) (= (len vec2) (len vec1)) (= (len x) (len vec1)))
	   (equal (DOT x (VEC-- VEC1 VEC2))
	   	  (- (dot x (vec-- vec2 vec1)))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable eu-metric scalar-*--1)
		  :use ((:instance vec---anticommutativity (vec1 vec2) (vec2 vec1))
			(:instance dot-linear-second-coordinate-1 (vec1 x) (a -1) (vec2 (vec-- vec2 vec1))))))))

 (local (defthm lemma-7
  (implies (and (real-listp x) (real-listp vec1) (real-listp vec2)
		(= (len vec1) (DIM)) (= (len vec2) (len vec1)) (= (len x) (len vec1))
              	(I-SMALL (DOT x (VEC-- VEC1 VEC2))))
	   (i-small (dot x (vec-- vec2 vec1))))
  :hints (("GOAL" :in-theory (disable lemma-7-1)
		  :use ((:instance lemma-7-1))
		  :do-not-induct t))))

 (local (in-theory (disable lemma-7-1)))

 (local (defthm lemma-8
  (implies (and (real-listp vec1) 
		(real-listp vec2)
		(real-listp x)
		(= (len vec2) (len vec1))
		(= (len x) (len vec1))
		(= (len vec1) (DIM))
		(i-small (eu-metric vec1 vec2)))
	   (i-small (- (phi x vec1) (phi x vec2))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-6)
			(:instance lemma-5)
			(:instance lemma-7 (x (nabla-mvfn x)))
			(:instance dot-i-small-mvfn-is-i-small)
			(:instance mvfn-is-continuous (vec1 vec1) (vec2 vec2))
			(:instance mvfn-is-continuous-2 (vec1 vec1) (vec2 vec2))
			(:instance lemma-4 (x (+ (mvfn vec1) (mvfn vec2)))
					   (y (dot (nabla-mvfn x) (vec-- vec2 vec1)))))))))

 (local (defthm lemma-9
  (implies (and (realp x) (i-small x))
	   (i-small (abs x)))))

 ;; phi is continuous 
 ;; - ACL2 reallllly did not want to prove this for some reason, hence lemmas 1-9
 (defthm phi-is-continuous
  (implies (and (real-listp vec1) 
		(real-listp vec2)
		(real-listp x)
		(= (len vec2) (len vec1))
		(= (len x) (len vec1))
		(= (len vec1) (DIM))
		(i-small (eu-metric vec1 vec2)))
	   (i-small (abs (- (phi x vec1) (phi x vec2)))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-8)
			(:instance lemma-9 (x (- (phi x vec1) (phi x vec2))))))))
)

 ;; differential-phi has dimension 2
 (local 
  (defthm dimension-of-differential-phi
   (= (len (differential-phi x vec2 eps)) (DIM))))

 ;; nabla-phi has dimension 2
  (defthm dimension-of-nabla-phi
   (= (len (nabla-phi x vec2)) (DIM)))

(defthm standard-part-is-real
 (implies (realp x)
 	  (realp (standard-part x))))

 ;; nabla-phi is real
(defthm nabla-phi-is-real
 (implies (and (real-listp x) (real-listp y))
  	  (real-listp (nabla-phi x y))))

  (defthm differential-phi-is-real
   (implies (and (real-listp x)  (real-listp y)
 		(realp eps))
            (real-listp (differential-phi x y eps)))
   :hints (("GOAL" :in-theory (enable dot))))









;; 
;;
;; ineq 6 implies ineq 1
;;
;;   - this needs be in the first encapsulation since standard-vecp is dimension dependent 
;;
;;  2.1.11 implies 2.1.6 in Nesterov's text
;;
;;
(encapsulate
 nil

(local (defthm lemma-1
 (implies (and (realp alpha) (realp x) (realp y) (>= x y) (<= 0 alpha))
	  (>= (* alpha x) (* alpha y)))))

;; 2.1.10 implies 2.1.10 with swapped variables
(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		 (* (* (L) (/ 2))
		    (* alpha (- 1 alpha))
		    (metric^2 y x)))
	      (+ (* alpha (mvfn y))
		 (* (- 1 alpha) (mvfn x)))))))

;; isolating mvfn y
(local (defthm lemma-3
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (+ (* (- alpha 1) (mvfn x))
		 (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		 (* (* (L) (/ 2))
		    (* alpha (- 1 alpha))
		    (metric^2 y x)))
	      (* alpha (mvfn y))))))
		 
;; simple rule to pass inequality
(local (defthm lemma-4
 (implies (and (realp a) (realp b) (realp c) (< 0 c) (>= a (* c b)))
	  (>= (* (/ c) a) b))))

;; must explicitly invoke inequality
(local (defthm lemma-5
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (* (/ alpha) 
		 (+ (* (- alpha 1) (mvfn x))
		    (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		    (* (* (L) (/ 2))
		       (* alpha (- 1 alpha))
		       (metric^2 y x))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable distributivity)
		 :use ((:instance lemma-3)
		       (:instance lemma-4
				  (a (+ (* (- alpha 1) (mvfn x))
		       			(mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		    			(* (* (L) (/ 2))
		       			   (* alpha (- 1 alpha))
		       			   (metric^2 y x))))
				  (b (mvfn y))
				  (c alpha)))))))

;; cleaning up alpha
(local (defthm lemma-6
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (* (/ alpha) 
		 (+ (* (- (* alpha (mvfn x)) (mvfn x)))
		    (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		    (* (* (L) (/ 2))
		       (* alpha (- 1 alpha))
		       (metric^2 y x))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-5))))))

;; cleaning up alpha
(local (defthm lemma-7
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>=  (+ (mvfn x)
		    (* (/ alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		       	  (- (mvfn x))))
		    (* (/ alpha) 
		       (* (L) (/ 2))
		       (* alpha (- 1 alpha))
		       (metric^2 y x)))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-6))))))

;; cleaning up alpha some more
(local (defthm lemma-8
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>=  (+ (mvfn x)
		    (* (/ alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		       	  (- (mvfn x))))
		    (* 
		       (* (L) (/ 2))
		       (- 1 alpha)
		       (metric^2 y x)))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-7))))))

(local (in-theory (disable eu-metric eu-metric-metric-sq-equivalence eu-metric-positive-definite-2)))

;; proving identity for inside of function
(local (defthm lemma-9
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1))
	  (equal (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x))
		 (vec-+ x (scalar-* alpha (vec-- y x)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance scalar-*-closure (a (- 1 alpha)) (vec x))
		       (:instance scalar-*-closure (a alpha) (vec y))
		       (:instance scalar-*-closure (a (- alpha)) (vec x))
		       (:instance scalar-*-closure (a -1) (vec x))
		       (:instance scalar-*-distributivity
				  (a alpha)
				  (vec1 y)
				  (vec2 (scalar-* -1 x)))
		       (:instance vec-+-commutativity
				  (vec2 (scalar-* alpha y))
				  (vec1 (scalar-* (- 1 alpha) x)))
		       (:instance vec-+-distributivity
				  (a 1)
				  (b (- alpha))
				  (vec x))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* 1 x))
				  (vec2 (scalar-* (- alpha) x))
				  (vec3 (scalar-* alpha y)))
		       (:instance vec-+-commutativity
				  (vec2 (scalar-* (- alpha) x))
				  (vec1 (scalar-* alpha y)))
		       (:instance scalar-*-of-scalar-*
				  (a alpha)
				  (b -1)
				  (vec x)))))))

;; cleaning up alpha even more
(local (defthm lemma-10
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>=  (+ (mvfn x)
		    (* (/ alpha) 
		       (+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  (- (mvfn x))))
		    (* 
		       (* (L) (/ 2))
		       (- 1 alpha)
		       (metric^2 y x)))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-8)
		       (:instance lemma-9))))))

(local (defthm lemma-11
 (implies (and (realp a) (realp b) (>= a b))
	  (>= (standard-part a) (standard-part b)))))

(local (in-theory (disable eu-metric eu-metric-metric-sq-equivalence eu-metric-positive-definite-2)))

;; cleaning up alpha again
(local (defthm lemma-12
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (standard-part (+ (mvfn x)
		    		(* (/ alpha) 
		       		   (+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	      (- (mvfn x))))
		    		(* (* (L) (/ 2))
		       		   (- 1 alpha)
		       		   (metric^2 y x))))
	      (standard-part (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-10)
		       (:instance lemma-11
			 	  (a (+ (mvfn x)
		    			(* (/ alpha) 
		       			(+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	   	   (- (mvfn x))))
		    			(* (* (L) (/ 2))
		       		   	   (- 1 alpha)
		       		   	   (metric^2 y x))))
				  (b (mvfn y))))))))

(local (defthm lemma-13
 (implies (and (realp a) (realp b)
	       (i-limited a) (i-limited b))
	  (equal (standard-part (* a b))
		 (* (standard-part a) (standard-part b))))
 :hints (("GOAL" :cases (and (i-limited a) (i-limited b))))))

(local (defthm lemma-14
 (implies (and (realp a) (realp b) (realp c) 
	       (i-limited a) (i-limited b) (i-limited c))
	  (equal (standard-part (* a b c))
		 (* (standard-part a) (standard-part b) (standard-part c))))
 :hints (("GOAL" :use ((:instance lemma-13 (a a) (b (* b c)))
		       (:instance lemma-13 (a b) (b c)))))))

(local (defthm lemma-15
 (implies (and (realp a) (realp b) (realp c))
	  (equal (standard-part (+ a b c))
		 (+ (standard-part a) (standard-part b) (standard-part c))))))

;; cleaning up alpha 
(local (defthm lemma-16
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (+ (standard-part (mvfn x))
		 (standard-part (* (/ alpha) 
		       		   (+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	      (- (mvfn x)))))
		 (standard-part (* (* (L) (/ 2))
		    		   (- 1 alpha)
		    		   (metric^2 y x))))
	      (standard-part (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-12)
		       (:instance lemma-15 
				  (a (mvfn x))
				  (b (* (/ alpha) 
		       		   	(+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	      	   (- (mvfn x)))))
				  (c (* (* (L) (/ 2))
		       		   	(- 1 alpha)
		       		   	(metric^2 y x)))))))))


			
(local (defthm lemma-17
 (implies (and (realp alpha) (<= alpha 1) (<= 0 alpha) (i-small alpha))
	  (and (i-limited (* 1/2 (L))) (i-limited alpha) (i-limited (- 1 alpha))))))


(local (defthm lemma-18
 (implies (and (standard-vecp x) (standard-vecp y))
	  (and (standardp (metric^2 (nabla-mvfn y) (nabla-mvfn x)))
	       (i-limited (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
 :hints (("GOAL" :use ((:instance metric-is-real (vec1 (nabla-mvfn y)) (vec2 (nabla-mvfn x)))
		       (:instance standard-vec-standard-nabla-mvfn (vec x))
		       (:instance standard-vec-standard-nabla-mvfn (vec y))
		       (:instance standards-are-limited-forward 
				  (x (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		       (:instance standard-vec-metric (vec1 (nabla-mvfn x)) (vec2 (nabla-mvfn y))))))))


(local (defthm lemma-18-2
 (implies (and (standard-vecp x) (standard-vecp y))
	  (and (standardp (metric^2 y x ))
	       (i-limited (metric^2 y x))))
 :hints (("GOAL" :use ((:instance metric-is-real (vec1 y) (vec2 x))
		       (:instance standards-are-limited-forward 
				  (x (metric^2 y x)))
		       (:instance standard-vec-metric (vec1 x) (vec2 y)))))))


(local (defthm lemma-18-3
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (i-limited alpha)
	       (standard-vecp x) (standard-vecp y))
  	  (equal (standard-part (* (* 1/2 (L)) (- 1 alpha) (metric^2 x y)))
	 	 (* (standard-part (* 1/2 (L))) 
		    (standard-part (- 1 alpha)) 
		    (standard-part (metric^2 x y)))))
 :hints (("GOAL" :do-not-induct  t
		 :use ((:instance lemma-14
				  (a (* 1/2 (L)))
				  (b (- 1 alpha))
				  (c (metric^2 y x)))
		       (:instance lemma-18)
		       (:instance lemma-18-2)
		       (:instance lemma-17))))))

;; cleaning up alpha finally
;; this one takes reallllllllllly long for some reason
(local (defthm lemma-19
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1) (i-small alpha)
	       (standard-vecp x) (standard-vecp y)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (+ (standard-part (mvfn x))
		 (standard-part (* (/ alpha) 
		       		   (+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	      (- (mvfn x)))))
		 (* (standard-part (* (L) (/ 2)))
		    (standard-part (- 1 alpha))
		    (standard-part (metric^2 y x))))
	      (standard-part (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable standard-vec-standard-mvfn)
		 :use ((:instance lemma-16)
		       (:instance standard-vec-metric (vec1 y) (vec2 x))
		       (:instance lemma-17)
		       (:instance lemma-18)
		       (:instance random-L-lemma-2)
		       (:instance random-L-lemma-3)
		       (:instance standard-vec-standard-nabla-mvfn (vec x))
		       (:instance standard-vec-standard-nabla-mvfn (vec y))
		       (:instance lemma-14
				  (a (* (L) (/ 2)))
				  (b (- 1 alpha))
				  (c (metric^2 y x))))))))

(local (defthm lemma-20
 (implies (and (realp alpha) (i-small alpha))
  	  (equal (standard-part (- 1 alpha)) 1))))

;; penultimate thing
;; this takes wayyy longer than lemma-19
(local (defthm lemma-21
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1) (i-small alpha)
	       (standard-vecp x) (standard-vecp y)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (+ (mvfn x)
		 (dot (nabla-mvfn x) (vec-- y x))
		 (* (* (L) (/ 2))
		    (metric^2 y x)))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-16)
		       (:instance lemma-19)
		       (:instance lemma-20)
		       (:instance standard-vec-metric (vec1 y) (vec2 x))
		       (:instance lemma-17)
		       (:instance lemma-18)
		       (:instance gradient-as-a-derivative
				  (vec1 x)
				  (vec2 (vec-- y x))
				  (eps alpha))
		       (:instance random-L-lemma-2)
		       (:instance random-L-lemma-3)
		       (:instance standard-vec-standard-nabla-mvfn (vec x))
		       (:instance standard-vec-standard-nabla-mvfn (vec y))
		       (:instance lemma-14
				  (a (* (L) (/ 2)))
				  (b (- 1 alpha))
				  (c (metric^2 y x))))))))

(local (defthm lemma-22 
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1) (i-small alpha)
	       (standard-vecp x) (standard-vecp y)
	       (>= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (L) (/ 2))
		    	 (* alpha (- 1 alpha))
			 (metric^2 y x)))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (>= (* (L) (/ 2) (metric^2 y x))
	      (+ (mvfn y)
		 (- (mvfn x))
		 (- (dot (nabla-mvfn x) (vec-- y x))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-21))))))

(defthm ineq-6-implies-ineq-1-expanded 
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1) (i-small alpha)
	       (standard-vecp x) (standard-vecp y)
	       (<= (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))
		   (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (/ (L) 2) alpha (- 1 alpha) (metric^2 y x)))))
	  (<= (mvfn y)
	      (+ (mvfn x)
		 (dot (nabla-mvfn x) (vec-- y x))
		 (* (/ (L) 2) (metric^2 y x)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-22)))))
)












;; 
;;
;; ineq 5 implies ineq 2
;;
;;   - this needs to be inside the first encapsulation, too, since standard-vecp depends on dimension
;;   - a lot of this encapsulation actually resembles ineq. 6 implies ineq. 1
;;     and can probably be streamlined
;;
;; 2.1.10 implies 2.1.7 in Nesterov's text
;;
;;
(encapsulate
 nil

;; 2.1.10 implies 2.1.10
(local (defthm lemma-1
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	      	   (+ (* alpha (mvfn x))
		      (* (- 1 alpha) (mvfn y)))))
	  (<= (+ (mvfn (vec-+ (scalar-* alpha x) (scalar-* (- 1 alpha) y)))
		 (* (* (/ 2) (/ (L))) 
		    (* alpha (- 1 alpha))
		    (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	      (+ (* alpha (mvfn x))
		 (* (- 1 alpha) (mvfn y)))))))

;; 2.1.10 implies 2.1.10 with swapped variables
(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		 (* (* (/ 2) (/ (L))) 
		    (* alpha (- 1 alpha))
		    (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      (+ (* alpha (mvfn y))
		 (* (- 1 alpha) (mvfn x)))))))

;; isolating mvfn y
(local (defthm lemma-3
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<= (+ (* (- alpha 1) (mvfn x))
		 (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		 (* (* (/ 2) (/ (L))) 
		    (* alpha (- 1 alpha))
		    (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      (* alpha (mvfn y))))))
		 
;; simple rule to pass inequality
(local (defthm lemma-4
 (implies (and (realp a) (realp b) (realp c) (< 0 c) (<= a (* c b)))
	  (<= (* (/ c) a) b))))

;; must explicitly invoke inequality
(local (defthm lemma-5
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<= (* (/ alpha) 
		 (+ (* (- alpha 1) (mvfn x))
		    (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		    (* (* (/ 2) (/ (L))) 
		       (* alpha (- 1 alpha))
		       (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-3)
		       (:instance lemma-4
				  (a (+ (* (- alpha 1) (mvfn x))
		       			(mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		    			(* (* (/ 2) (/ (L))) 
		       			   (* alpha (- 1 alpha))
		       			   (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
				  (b (mvfn y))
				  (c alpha)))))))

;; cleaning up alpha
(local (defthm lemma-6
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<= (* (/ alpha) 
		 (+ (* (- (* alpha (mvfn x)) (mvfn x)))
		    (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		    (* (* (/ 2) (/ (L))) 
		       (* alpha (- 1 alpha))
		       (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-5))))))


;; cleaning up alpha
(local (defthm lemma-7
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<=  (+ (mvfn x)
		    (* (/ alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		       	  (- (mvfn x))))
		    (* (/ alpha) 
		       (* (/ 2) (/ (L))) 
		       (* alpha (- 1 alpha))
		       (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-6))))))

;; cleaning up alpha
(local (defthm lemma-8
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<=  (+ (mvfn x)
		    (* (/ alpha) 
		       (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		       	  (- (mvfn x))))
		    (* 
		       (* (/ 2) (/ (L))) 
		       (- 1 alpha)
		       (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-7))))))

(local (in-theory (disable eu-metric eu-metric-metric-sq-equivalence eu-metric-positive-definite-2)))

;; proving identity for inside of function
(local (defthm lemma-9
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1))
	  (equal (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x))
		 (vec-+ x (scalar-* alpha (vec-- y x)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse)
		 :use ((:instance scalar-*-closure (a (- 1 alpha)) (vec x))
		       (:instance scalar-*-closure (a alpha) (vec y))
		       (:instance scalar-*-closure (a (- alpha)) (vec x))
		       (:instance scalar-*-closure (a -1) (vec x))
		       (:instance scalar-*-distributivity
				  (a alpha)
				  (vec1 y)
				  (vec2 (scalar-* -1 x)))
		       (:instance vec-+-commutativity
				  (vec2 (scalar-* alpha y))
				  (vec1 (scalar-* (- 1 alpha) x)))
		       (:instance vec-+-distributivity
				  (a 1)
				  (b (- alpha))
				  (vec x))
		       (:instance vec-+-associativity
				  (vec1 (scalar-* 1 x))
				  (vec2 (scalar-* (- alpha) x))
				  (vec3 (scalar-* alpha y)))
		       (:instance vec-+-commutativity
				  (vec2 (scalar-* (- alpha) x))
				  (vec1 (scalar-* alpha y)))
		       (:instance scalar-*-of-scalar-*
				  (a alpha)
				  (b -1)
				  (vec x)))))))

;; cleaning up alpha
(local (defthm lemma-10
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<=  (+ (mvfn x)
		    (* (/ alpha) 
		       (+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  (- (mvfn x))))
		    (* 
		       (* (/ 2) (/ (L))) 
		       (- 1 alpha)
		       (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-8)
		       (:instance lemma-9))))))

(local (defthm lemma-11
 (implies (and (realp a) (realp b) (<= a b))
	  (<= (standard-part a) (standard-part b)))))

(local (in-theory (disable eu-metric eu-metric-metric-sq-equivalence eu-metric-positive-definite-2)))

;; cleaning up alpha
(local (defthm lemma-12
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<= (standard-part (+ (mvfn x)
		    		(* (/ alpha) 
		       		   (+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	      (- (mvfn x))))
		    		(* (* (/ 2) (/ (L))) 
		       		   (- 1 alpha)
		       		   (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
	      (standard-part (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-10)
		       (:instance lemma-11
			 	  (a (+ (mvfn x)
		    			(* (/ alpha) 
		       			(+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	   	   (- (mvfn x))))
		    			(* (* (/ 2) (/ (L))) 
		       		   	   (- 1 alpha)
		       		   	   (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
				  (b (mvfn y))))))))

(local (defthm lemma-13
 (implies (and (realp a) (realp b) 
	       (i-limited a) (i-limited b))
	  (equal (standard-part (* a b))
		 (* (standard-part a) (standard-part b))))
 :hints (("GOAL" :cases (and (i-limited a) (i-limited b))))))

(local (defthm lemma-14
 (implies (and (realp a) (realp b) (realp c) 
	       (i-limited a) (i-limited b) (i-limited c))
	  (equal (standard-part (* a b c))
		 (* (standard-part a) (standard-part b) (standard-part c))))
 :hints (("GOAL" :use ((:instance lemma-13 (a a) (b (* b c)))
		       (:instance lemma-13 (a b) (b c)))))))

(local (defthm lemma-15
 (implies (and (realp a) (realp b) (realp c))
	  (equal (standard-part (+ a b c))
		 (+ (standard-part a) (standard-part b) (standard-part c))))))

;; cleaning up alpha
(local (defthm lemma-16
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1)
	       
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<= (+ (standard-part (mvfn x))
		 (standard-part (* (/ alpha) 
		       		   (+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	      (- (mvfn x)))))
		 (standard-part (* (* (/ 2) (/ (L)))
		    		   (- 1 alpha)
		    		   (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
	      (standard-part (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-12)
		       (:instance lemma-15 
				  (a (mvfn x))
				  (b (* (/ alpha) 
		       		   	(+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	      	   (- (mvfn x)))))
				  (c (* (* (/ 2) (/ (L))) 
		       		   	   (- 1 alpha)
		       		   	   (metric^2 (nabla-mvfn y) (nabla-mvfn x))))))))))
			
(local (defthm lemma-17
 (implies (and (realp alpha) (<= alpha 1) (<= 0 alpha) (i-small alpha))
	  (and (i-limited alpha) (i-limited (- 1 alpha))))))
(local (defthm lemma-18
 (implies (and (standard-vecp x) (standard-vecp y))
	  (and (standardp (metric^2 (nabla-mvfn y) (nabla-mvfn x)))
	       (i-limited (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
 :hints (("GOAL" :use ((:instance metric-is-real (vec1 (nabla-mvfn y)) (vec2 (nabla-mvfn x)))
		       (:instance standard-vec-standard-nabla-mvfn (vec x))
		       (:instance standard-vec-standard-nabla-mvfn (vec y))
		       (:instance standards-are-limited-forward 
				  (x (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
		       (:instance standard-vec-metric (vec1 (nabla-mvfn x)) (vec2 (nabla-mvfn y))))))))

;; cleaning up alpha
;; this one takes reallllllllllly long for some reason
(local (defthm lemma-19
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1) (i-small alpha)
	       (standard-vecp x) (standard-vecp y)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (* (/ 2) (/ (L))) 
		    	 (* alpha (- 1 alpha))
			 (metric^2 (nabla-mvfn y) (nabla-mvfn x))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<= (+ (standard-part (mvfn x))
		 (standard-part (* (/ alpha) 
		       		   (+ (mvfn (vec-+ x (scalar-* alpha (vec-- y x))))
		       	  	      (- (mvfn x)))))
		 (* (standard-part (* (/ 2) (/ (L))))
		    (standard-part (- 1 alpha))
		    (standard-part (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
	      (standard-part (mvfn y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-16)
		       (:instance standard-vec-metric (vec1 (nabla-mvfn x)) (vec2 (nabla-mvfn y)))
		       (:instance lemma-17)
		       (:instance lemma-18)
		       (:instance random-L-lemma-2)
		       (:instance random-L-lemma-3)
		       (:instance standard-vec-standard-nabla-mvfn (vec x))
		       (:instance standard-vec-standard-nabla-mvfn (vec y))
		       (:instance lemma-14
				  (a (* (/ 2) (/ (L))))
				  (b (- 1 alpha))
				  (c (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))))))

(local (defthm lemma-20
 (implies (and (realp alpha) (i-small alpha))
  	  (equal (standard-part (- 1 alpha)) 1))))

;; final lemma: this also takes reallllly long
(defthm ineq-5-implies-ineq-2-expanded 
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (= (len x) (DIM))
	       (realp alpha) (< 0 alpha) (<= alpha 1) (i-small alpha)
	       (standard-vecp x) (standard-vecp y)
	       (<= (+ (mvfn (vec-+ (scalar-* alpha y) (scalar-* (- 1 alpha) x)))
		      (* (/ (* 2 (L)))
		    	 (* alpha (- 1 alpha) (metric^2 (nabla-mvfn y) (nabla-mvfn x)))))
	      	   (+ (* alpha (mvfn y))
		      (* (- 1 alpha) (mvfn x)))))
	  (<= (+ (mvfn x)
		 (dot (nabla-mvfn x) (vec-- y x))
		 (* (/ (* 2 (L)))
		    (metric^2 (nabla-mvfn x) (nabla-mvfn y))))
	      (mvfn y)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance metric-commutativity
				  (vec1 (nabla-mvfn x))
				  (vec2 (nabla-mvfn y)))
		       (:instance lemma-16)
		       (:instance lemma-19)
		       (:instance lemma-20)
		       (:instance standard-vec-metric (vec1 (nabla-mvfn x)) (vec2 (nabla-mvfn y)))
		       (:instance lemma-17)
		       (:instance lemma-18)
		       (:instance gradient-as-a-derivative
				  (vec1 x)
				  (vec2 (vec-- y x))
				  (eps alpha))
		       (:instance random-L-lemma-2)
		       (:instance random-L-lemma-3)
		       (:instance standard-vec-standard-nabla-mvfn (vec x))
		       (:instance standard-vec-standard-nabla-mvfn (vec y))
		       (:instance lemma-14
				  (a (* (/ 2) (/ (L))))
				  (b (- 1 alpha))
				  (c (metric^2 (nabla-mvfn y) (nabla-mvfn x))))))))
)
)

