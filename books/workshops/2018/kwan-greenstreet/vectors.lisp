; cert_param: (uses-acl2r)

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist-base" :dir :system)
(include-book "arithmetic/top" :dir :system)

;; recognizer of the zero vector
(define zvecp ((vec real-listp))
 :returns (ret booleanp)
 (cond ((null vec) t)
       ((not (real-listp vec)) nil)
       (t (and (= (car vec) 0)
               (zvecp (cdr vec)))))
 ///
 (more-returns
  (ret (implies ret (zvecp (cdr vec)))
       :hints(("GOAL" :in-theory (enable zvecp)))
       :name zvecp-monotonicity-1)
  (ret (implies ret (equal (zvecp (cons hd vec)) (= hd 0)))
       :hints(("GOAL" :in-theory (enable zvecp)))
       :name zvecp-monotonicity-2)
  ))
  
;; define vector addition for vectors from the same vector space
(define vec-+ ((vec1 real-listp) (vec2 real-listp))
 :guard (and (real-listp vec1)
             (real-listp vec2)
             (= (len vec1) (len vec2)))
 :returns (vec real-listp)
  (b* (((unless (and (consp vec1) (consp vec2))) nil)
       ((cons hd1 tl1) vec1)
       ((cons hd2 tl2) vec2)
       ((unless (and (realp hd1) (realp hd2))) nil))
      (cons (+ hd1 hd2) (vec-+ tl1 tl2)))
 /// 
 (more-returns 
  (vec (real-listp vec)
       :name vec-+-closure-1)
  (vec (implies (and (real-listp vec1)
                     (real-listp vec2)
		     (= (len vec1) (len vec2)))
		(= (len vec) (len vec1)))
       :name vec-+-closure-2)

  (vec (implies (and (real-listp vec1)
		     (real-listp vec2)
		     (= (len vec1) (len vec2))
		     (realp a)
		     (realp b))
		(equal (vec-+ (cons a vec1) (cons b vec2))
		       (cons (+ a b) vec)))
       :name vec-+-of-cons
       :hints (("GOAL" :in-theory (enable vec-+))))

  (vec (implies (and (real-listp vec1)
		     (real-listp vec2)
		     (= (len vec1) (len vec2))
		     (natp i)
		     (< i (len vec)))
		(= (nth i vec)
		   (+ (nth i vec1) (nth i vec2))))
       :name nth-element-of-vec-+
       :hints (("GOAL" :expand (vec-+ vec1 vec2)
		       ;; ACL2 doesn't want to do nice induction
		       :induct (and (nth i vec)
				    (nth i vec1)
			       	    (nth i vec2)))))))

(defthm vec-+-commutativity
 (implies (and (real-listp vec1)
               (real-listp vec2)
               (= (len vec1) (len vec2)))
	  (equal (vec-+ vec2 vec1) (vec-+ vec1 vec2)))
 :hints (("GOAL" :in-theory (enable vec-+))))

(defthm vec-+-associativity
 (implies (and (real-listp vec1)
               (real-listp vec2)
               (real-listp vec3)
               (= (len vec1) (len vec2))
               (= (len vec3) (len vec2)))
	  (equal (vec-+ (vec-+ vec1 vec2) vec3)
		 (vec-+ vec1 (vec-+ vec2 vec3))))
 :hints (("GOAL" :in-theory (enable vec-+))))
				   			   
;; define scalar multiplication for vectors
(define scalar-* ((a realp) (vec real-listp))
 :returns (retvec real-listp)
 (b* (((unless (consp vec)) nil)
      ((cons hd tl) vec)
      ((unless (and (realp a) (realp hd))) nil))
     (cons (* a hd) (scalar-* a tl)))
 ///
 (more-returns 
  (retvec (implies (and (real-listp vec) (realp a) )
		   (equal (len retvec) (len vec)))
	  :name scalar-*-closure
	  :rule-classes nil)
  (retvec (implies (and (real-listp vec)
			(realp a)
			(natp i)
			(< i vec))
		   (= (nth i retvec)
		      (* a (nth i vec))))
	  :name nth-element-of-scalar-*
 	  :hints (("GOAL" :in-theory (enable scalar-*))))
  (retvec (implies (and (realp a) (real-listp vec))
                   (iff (or (= a 0) (zvecp vec))
			(zvecp retvec)))
 	  :hints (("GOAL" :in-theory (enable scalar-* zvecp)))
	  :name  scalar-vec-0)
  (retvec (implies (and (= a 1) (real-listp vec))
	           (equal retvec vec))
 	  :hints (("GOAL" :in-theory (enable scalar-*)))
	  :name  scalar-vec-identity)))

;; scalar multiplication is something
(defthm scalar-*-of-scalar-*
 (implies (and (realp a) (realp b) (real-listp vec))
	  (equal (scalar-* a (scalar-* b vec))
		 (scalar-* (* a b) vec)))
 :hints (("GOAL" :in-theory (enable scalar-*))))

(defthm scalar-*-unclosure
 (implies (not (realp a))
	  (zvecp (scalar-* a v)))
 :hints (("GOAL" :in-theory (enable scalar-*)))
 :rule-classes nil)

;; scalar-* is distributive over vec-+
(defthm scalar-*-distributivity
 (implies (and (realp a) (real-listp vec1) (real-listp vec2)
	       (= (len vec2) (len vec1)))
	  (equal (scalar-* a (vec-+ vec1 vec2))
		 (vec-+ (scalar-* a vec1) (scalar-* a vec2))))
 :hints (("GOAL" :in-theory (enable vec-+ scalar-*))))

;; 1 is a scalar-* identity
(defthm scalar-*-identity
 (implies (real-listp vec)
	  (equal (scalar-* 1 vec) vec))
 :hints (("GOAL" :in-theory (enable scalar-*))))

;; vec-+ is distributive over scalar-*
(defthm vec-+-distributivity
 (implies (and (realp a) (realp b) (real-listp vec))
	  (equal (vec-+ (scalar-* a vec) (scalar-* b vec))
		 (scalar-* (+ a b) vec)))
 :hints (("GOAL" :in-theory (enable vec-+ scalar-*))))

;; vector difference
(defmacro vec-- (vec1 vec2)
 (list 'vec-+ vec1 (list 'scalar-* -1 vec2)))


;; ACL2(r) does not like the macro definition of vec-- for proving properites.
;; Instead, we define a new function vec--x equivalent to vec-- and prove the 
;; properties we desire for vec-- on vec--x. 
(define vec--x (vec1 vec2)
 :guard (and (real-listp vec1)
             (real-listp vec2)
             (= (len vec1) (len vec2)))
 :returns (vec real-listp)
 (cond ((or (null vec1) (null vec2)) nil)
       ((not (= (len vec1) (len vec2))) nil)
       ((or (not (real-listp vec1)) (not (real-listp vec2))) nil)
       (t (cons (- (car vec1) (car vec2)) (vec--x (cdr vec1) (cdr vec2)))))
 ///
 (more-returns
  (vec real-listp) ;:rule-classes :type-prescription)))

  (vec (implies (and (real-listp vec1)
		     (real-listp vec2)
		     (= (len vec1) (len vec2))
		     (realp a)
		     (realp b))
		(equal (vec--x (cons a vec1) (cons b vec2))
		       (cons (- a b) vec)))
       :name vec--x-of-cons
       :hints (("GOAL" :in-theory (enable vec-+))))

  (vec (implies (and (real-listp vec1)
		     (real-listp vec2)
		     (= (len vec1) (len vec2))
		     (natp i)
		     (< i (len vec)))
		(= (nth i vec)
		   (- (nth i vec1) (nth i vec2))))
       :name nth-element-of-vec--x
       :hints (("GOAL" :expand (vec-+ vec1 vec2)
		       ;; ACL2 doesn't want to do nice induction
		       :induct (and (nth i vec)
				    (nth i vec1)
			       	    (nth i vec2)))))))

(defthm scalar-*--1
 (implies (and (real-listp vec)) 
  	    (equal (len (scalar-* -1 vec)) (len vec)))
 :hints (("GOAL" :use (:instance scalar-*-closure (a -1)))))


;; vec-- is equivalent to vec--x 
(encapsulate
 nil
 (local 
  (defthm lemma-1
   (implies (and (real-listp vec)) 
  	    (equal (len (scalar-* -1 vec)) (len vec)))
   :hints (("GOAL" :in-theory (enable scalar-*)))))


 (defthm vec---closure
  (implies (and (real-listp vec1) (real-listp vec2) (= (len vec2) (len vec1)))
	   (and (real-listp (vec-- vec1 vec2))
		(= (len (vec-- vec1 vec2)) (len vec1))
		(= (len (vec-- vec1 vec2)) (len vec2))))
  :hints (("GOAL" :do-not-induct t
		  :use ((:instance lemma-1 (vec vec2))))))

 (defthm vec---equivalence
  (implies (and (real-listp vec1) 
 	        (real-listp vec2)
 	        (= (len vec1) (len vec2)))
 	   (equal (vec-- vec1 vec2) (vec--x vec1 vec2)))
  :hints (("GOAL" :in-theory (enable vec--x vec-+ scalar-*)
 		  :induct (and (nth i vec1) (nth i vec2)))))

)

;; vec--x has an additive inverse
(defthm vec--x-zero-inverse
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (equal (len vec1) (len vec2)))
	  (equal (equal vec1 vec2)
		 (zvecp (vec--x vec1 vec2))))
 :hints (("GOAL" :induct (and (nth i vec1) (nth i vec2))
		 :in-theory (enable zvecp vec--x)))
 :rule-classes nil)

 ;; vec-- has an additive inverse 
(defthm vec---zero-inverse
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (equal (len vec1) (len vec2)))
	  (equal (equal vec1 vec2)
		 (zvecp (vec-- vec1 vec2))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance vec---equivalence)
		       (:instance vec--x-zero-inverse)))))

;; x + 0 = x 
(defthm zvecp-is-additive-identity-1
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (equal (len vec1) (len vec2))
	       (zvecp vec2))
	  (equal (vec-+ vec1 vec2)
		 vec1))
 :hints (("GOAL" :in-theory (enable zvecp vec-+))))

;; 0 + x = x
(defthm zvecp-is-additive-identity-2
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (equal (len vec1) (len vec2))
	       (zvecp vec1))
	  (equal (vec-+ vec1 vec2)
		 vec2))
 :hints (("GOAL" :in-theory (enable zvecp vec-+))))

 ;; x - 0 = x 
(defthm zvecp-is-subtractive-identity-1
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (equal (len vec1) (len vec2))
	       (zvecp vec2))
	  (equal (vec-- vec1 vec2)
		 vec1))
 :hints (("GOAL" :in-theory (enable zvecp vec-+ vec--x))))

 ;; 0 - x = -x 
(defthm zvecp-is-subtractive-identity-2
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (equal (len vec1) (len vec2))
	       (zvecp vec1))
	  (equal (vec-- vec1 vec2)
		 (scalar-* -1 vec2)))
 :hints (("GOAL" :use ((:instance scalar-*-closure (vec vec2) (a -1))
		       (:instance zvecp-is-additive-identity-2
				  (vec2 (scalar-* -1 vec2))))
		 :in-theory (disable vec---equivalence))))

;; elements of vec-- are difference of elements of veci
(defthm vec---elements-difference
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (= (len vec1) (len vec2))
	       (natp i)
	       (< i (len (vec-- vec1 vec2))))
 	  (= (nth i (vec-- vec1 vec2)) 
	     (- (nth i vec1) (nth i vec2))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance nth-element-of-scalar-* (a -1) (vec vec2))
		       (:instance nth-element-of-vec-+)))))

(in-theory (disable vec---equivalence))

;; dot/inner product
;;  - need to check lengths of vectors anyways so non-linear
(define dot ((vec1 real-listp) (vec2 real-listp))
 :guard (and (real-listp vec1) (real-listp vec2)
	     (= (len vec2) (len vec1)))
 :returns (r realp)
 (cond ((or (not (real-listp vec1)) (not (real-listp vec2))) 0)
       ((not (= (len vec2) (len vec1))) 0)
       ((or (null vec1) (null vec2)) 0)
       (t (+ (* (car vec1) (car vec2))
	     (dot (cdr vec1) (cdr vec2)))))
 ///
 (more-returns
  (r realp
   :name dot-is-real)))

;; the inner product is commutative
(defthm dot-commutativity
 (implies (and (real-listp vec1) (real-listp vec2) (= (len vec2) (len vec1)))
	  (= (dot vec1 vec2) (dot vec2 vec1)))
 :hints (("GOAL" :in-theory (enable dot))))

;; We now aim to prove the inner product is bilinear

;; <ax,y> = a<x,y>
(defthm dot-linear-first-coordinate-1
 (implies (and (real-listp vec1) (real-listp vec2) (= (len vec2) (len vec1))
	       (realp a))
	  (= (dot (scalar-* a vec1) vec2)
	     (* a (dot vec1 vec2))))
 :hints (("GOAL" :in-theory (enable dot scalar-*))))
	        
;; <x,z> + <y,z> = <x + y, z>
(defthm dot-linear-first-coordinate-2
 (implies (and (real-listp vec1) (real-listp vec2) (real-listp vec3) 
	       (= (len vec2) (len vec1)) (= (len vec3) (len vec1)))
	  (= (+ (dot vec1 vec3) (dot vec2 vec3))
	     (dot (vec-+ vec1 vec2) vec3)))
 :hints (("GOAL" :in-theory (enable dot vec-+))))


;; For some reason, the proof of linearity of coefficients in the second 
;; coordinate does not pass with the same hints as in the case of the 
;; first coordinate. Instead, we use commutativity.

;; <x,ay> = a<x,y>
(defthm dot-linear-second-coordinate-1
 (implies (and (real-listp vec1) (real-listp vec2) (= (len vec2) (len vec1))
	       (realp a))
	  (= (dot vec1 (scalar-* a vec2))
	     (* a (dot vec1 vec2))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure (vec vec2))
		       (:instance dot-commutativity (vec2 (scalar-* a vec2)))))))

;; <x,y> + <x,z> = <x, y + z>
(defthm dot-linear-second-coordinate-2
 (implies (and (real-listp vec1) (real-listp vec2) (real-listp vec3) 
	       (= (len vec2) (len vec1)) (= (len vec3) (len vec1)))
	  (= (+ (dot vec1 vec2) (dot vec1 vec3))
	     (dot vec1 (vec-+ vec2 vec3))))
 :hints (("GOAL" :in-theory (enable dot vec-+))))

;; dot with first coordinate zvecp is zero 
(defthm dot-with-zvec-is-zero
 (implies (and (real-listp x) (zvecp x) (real-listp y) (= (len x) (len y)))
	  (= (dot x y) 0))
 :hints (("GOAL" :in-theory (enable dot zvecp))))

;; dot with second coordinate zvecp is zero 
(defthm dot-with-zvec-is-zero-2
 (implies (and (real-listp x) (zvecp y) (real-listp y) (= (len x) (len y)))
	  (= (dot x y) 0))
 :hints (("GOAL" :in-theory (enable dot zvecp))))

(defthm self-dot-is-positive-definite
 (implies (real-listp u)
	  (<= 0 (dot u u)))
 :hints (("GOAL" :in-theory (enable dot))))
          
(encapsulate
 nil
 (local (defthm lemma-1
  (implies (and (realp x) (not (equal x 0)))
	   (< 0 (* x x)))
  :rule-classes nil))

(local (defthm lemma-2
 (implies (and (realp x) (realp y) (<= 0 y) (< 0 x))
	  (not (equal (+ x y) 0)))))

(defthm zero-dot-implies-zvecp
 (implies (and (real-listp u) (equal (dot u u) 0))
	  (zvecp u))
 :hints (("GOAL" :in-theory (enable zvecp dot))))
)

;; We need the following to prove 2.1.7=>2.1.8
;;
;; Oddly, this doesn't require the hypotheses that vec1 vec2 are real vectors.
(defthm vec--x-anticommutativity
 (= (vec--x vec1 vec2) (scalar-* -1 (vec--x vec2 vec1)))
 :hints (("GOAL" :in-theory (enable vec--x scalar-*))))

;; disable the above theorem since the rewriter really likes to use it
(in-theory (disable vec--x-anticommutativity))

(defthm vec---anticommutativity
 (implies (and (real-listp vec1) (real-listp vec2) (= (len vec2) (len vec1)))
	  (= (vec-- vec1 vec2) (scalar-* -1 (vec-- vec2 vec1))))
 :hints (("GOAL" :use ((:instance vec---equivalence) 
		       (:instance vec---equivalence (vec1 vec2) (vec2 vec1))
		       (:instance vec--x-anticommutativity (vec1 vec1) (vec2 vec2))))))

;; disable the above theorem since the rewriter really likes to use it
(in-theory (disable vec---anticommutativity))



