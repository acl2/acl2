; cert_param: (uses-acl2r)

(in-package "ACL2")

(include-book "norm")
(include-book "std/util/define-sk" :dir :system)

(encapsulate
 nil
 
(defthm unit-vector-is-unit
 (implies (and (not (zvecp vec)) (real-listp vec))
	  (equal (eu-norm (scalar-* (/ (eu-norm vec)) vec)) 1))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable sqrt-* sqrt-/)
		 :use ((:instance sqrt-/ (x (norm^2 vec)))
		       (:instance norm-is-real)
		       (:instance zvecp-iff-zp-vec)))))


;; || u - v ||^2 = <u - v, u - v>
(local (defthm lemma-1
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (norm^2 (vec-- u v))
		 (dot (vec-- u v) (vec-- u v))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance norm-inner-product-equivalence (vec (vec-- u v))))))))


;; || u - v ||^2 = <u, u-v> - <v, u-v>
(local (defthm lemma-2
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (norm^2 (vec-- u v)) 
		 (+ (dot u (vec-- u v)) (- (dot v (vec-- u v))))))
 :hints (("GOAL" :use ((:instance scalar-*-closure (a -1) (vec v))
		       (:instance dot-linear-first-coordinate-2 
				  (vec1 u)
				  (vec2 (scalar-* -1 v))
				  (vec3 (vec-- u v))))))))

;; || u - v ||^2 = <u, u> - <u, v> - <v, u> + <v, v>
(local (defthm lemma-3
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (norm^2 (vec-- u v)) 
		 (+ (dot u u) (- (dot u v)) (- (dot v u)) (dot v v))))
 :hints (("GOAL" :use ((:instance scalar-*-closure (a -1) (vec v))
		       (:instance dot-linear-second-coordinate-2 
				  (vec1 v)
				  (vec2 u)
				  (vec3 (scalar-* -1 v)))
		       (:instance dot-linear-second-coordinate-2 
				  (vec1 u)
				  (vec2 u)
				  (vec3 (scalar-* -1 v))))))))

;; < u - v, u - v > = < u, u > - 2 < u , v > + < v, v >
(local (defthm lemma-4
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (norm^2 (vec-- u v)) 
		 (+ (dot u u) (- (* 2 (dot u v))) (dot v v))))
 :hints (("GOAL" :use ((:instance dot-commutativity (vec1 u) (vec2 v)))))))

;; 0 <= < u, u > - 2 < u , v > + < v, v >
(local (defthm lemma-6
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (<= 0 (norm^2 (vec-- u v)))
		 (<= 0 (+ (dot u u) (- (* 2 (dot u v))) (dot v v)))))))

;; let v = (scalar-* (* (/ (dot v v)) (dot u v)) v)
(local (defthm lemma-7
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))) 
	  (equal (<= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (<= 0 
	      	     (+ (dot u u) 
		 	(- (* 2 (dot u (scalar-* (* (/ (dot v v)) (dot u v)) v))))
		 	(dot (scalar-* (* (/ (dot v v)) (dot u v)) v)
		      	     (scalar-* (* (/ (dot v v)) (dot u v)) v))))))
 :hints (("GOAL" :use ((:instance scalar-*-closure (a (* (/ (dot v v)) (dot u v))) (vec v))
		       (:instance lemma-6 (v (scalar-* (* (/ (dot v v)) (dot u v)) v))))))))

;;  0 <= ||u||^2 - 2 <u, W> + (||v||^{-2})^2<u, v>^2||v||^2 
(local (defthm lemma-8
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))) 
	  (equal (<= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (<= 0 
	      	     (+ (dot u u) 
		 	(- (* (* 2 (* (/ (dot v v)) (dot u v))) 
		       	   (dot u v)))
		 	(* (/ (dot v v)) 
		    	   (dot u v)
		    	   (/ (dot v v)) 
		    	   (dot u v)
		    	   (dot v v))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure (a (* (/ (dot v v)) (dot u v))) (vec v))
		       (:instance lemma-7))))))


;;
;; case when v is not zero
;;

(local (defthm lemma-9
 (implies (and (realp x) (not (= x 0)) 
	       (realp y))
	  (equal (* (/ x) y (/ x) y x)
		 (* (/ x) y y)))))


(local (defthm lemma-10
 (implies (and (real-listp v) (not (zvecp v)))
	  (and (not (equal (dot v v) 0))
	       (< 0 (dot v v))))
 :hints (("GOAL" :use ((:instance norm-inner-product-equivalence (vec v))
		       (:instance zvecp-iff-zp-vec (vec v)))))))

;; 0 <= ||u||^2 - 2/||v||^2 <u, v>^2 + ||v||^{-2} <u, v>^2
(local (defthm lemma-11
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (equal (<= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (<= 0 
	      	     (+ (dot u u) 
		 	(* -2 (* (/ (dot v v)) (dot u v) (dot u v)))
		 	(* (/ (dot v v)) (dot u v) (dot u v))))))
 :hints (("GOAL" :use ((:instance scalar-*-closure (a (* (/ (dot v v)) (dot u v))) (vec v))
		       (:instance lemma-9 (x (dot v v)) (y (dot u v)))
		       (:instance lemma-8))))))

;; ||v||^{-2}<u, v>^2 <= ||u||^2 
(local (defthm lemma-13
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (equal (<= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (<= (* (/ (dot v v)) (dot u v) (dot u v))
	      	     (dot u u))))
 :hints (("GOAL" :use ((:instance lemma-11))))))

(local (defthm lemma-14
 (implies (and (realp x) (realp y) (realp z) (not (= x 0)) (< 0 x) (<= (* (/ x) y y) z))
	  (<= (* y y) (* z x)))))

(local (defthm lemma-15
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (equal (<= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (<= (* (dot u v) (dot u v))
	      	     (* (dot u u) (dot v v)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-11)
		       (:instance lemma-13)
		       (:instance lemma-14 (x (dot v v)) (y (dot u v)) (z (dot u u))))))))


(defthm cauchy-schwarz-1
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  	 (<= (* (dot u v) (dot u v))
	      	     (* (dot u u) (dot v v))))
 :hints (("GOAL" :use ((:instance lemma-15))
		 :cases ((zvecp v)(not (zvecp v))))))

;;
;; Proving norm version of cauchy-schwarz by taking square roots
;;
(local (defthm lemma-16
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (and (equal (acl2-sqrt (* (dot u v) (dot u v)))
		      (abs (dot u v)))
	       (equal (acl2-sqrt (dot u u)) (eu-norm u))
	       (equal (acl2-sqrt (dot v v)) (eu-norm v))
	       (equal (acl2-sqrt (* (dot u u) (dot v v)))
		      (* (eu-norm u) (eu-norm v)))))
 :hints (("GOAL" :use ((:instance norm-inner-product-equivalence (vec u))
		       (:instance norm-inner-product-equivalence (vec v)))))))

(local (defthm lemma-18
 (implies (and (realp a) (realp b) (<= 0 a) (<= 0 b) (<= a b))
	  (<= (acl2-sqrt a) (acl2-sqrt b)))))

(defthm cauchy-schwarz-2
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (<= (abs (dot u v))
	      (* (eu-norm u) (eu-norm v))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable eu-norm-*-eu-norm eu-norm abs)
		 :use ((:instance cauchy-schwarz-1)
		       (:instance norm-inner-product-equivalence (vec v))
		       (:instance norm-inner-product-equivalence (vec u))
		       (:instance lemma-18 
				  (a (* (dot u v) (dot u v)))
				  (b (* (dot u u) (dot v v))))))))

;;
;; cs-2-implies-cs-1
;; 

(local (defthm lemma-19
 (implies (and (realp a) (realp b) (realp c) (= (abs a) (* b c)))
 	  (= (* (abs a) (abs a)) (* (* b c) (* b c))))))

(local (defthm lemma-20
 (implies (and (realp b) (realp c))
	  (= (* (* b c) (* b c)) (* (* b b) (* c c))))))

(local (defthm lemma-21
 (implies (and (realp a) (realp b) (realp c) (= (abs a) (* b c)))
 	  (= (* (abs a) (abs a)) (* (* b b) (* c c))))
 :hints (("GOAL" :use ((:instance lemma-20))))))

;; |< u , v >| = || u || || v || implies 
;; |< u , v >| |< u , v >| = < u , u > < v , v >
(local (defthm lemma-22
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))
	       (=  (abs (dot u v)) (* (eu-norm u) (eu-norm v))))
	  (=  (* (abs (dot u v)) (abs (dot u v)))
	      (* (dot u u) (dot v v))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable eu-norm eu-norm-*-eu-norm lemma-20 abs)
		 :use ((:instance lemma-21 
				  (a (dot u v)) 
				  (b (eu-norm u))
				  (c (eu-norm v)))
		       (:instance dot-eu-norm (vec u))
		       (:instance dot-eu-norm (vec v)))))))

(local (defthm lemma-23
 (implies (realp a)
	  (= (* (abs a) (abs a)) (* a a)))))

;; |< u , v >| = || u || || v || implies 
;; |< u , v > < u , v >| = < u , u > < v , v >
(defthm cs-2-implies-cs-1
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))
	       (=  (abs (dot u v)) (* (eu-norm u) (eu-norm v))))
	  (=  (* (dot u v) (dot u v))
	      (* (dot u u) (dot v v))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable eu-norm eu-norm-*-eu-norm lemma-20 abs)
		 :use ((:instance lemma-22))))
 :rule-classes nil)
)



;;
;; Now to show the conditions for equality
;;
(encapsulate
 nil

;; \| u - v \|^2 = <u - v, u - v>
(local (defthm lemma-1
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (norm^2 (vec-- u v))
		 (dot (vec-- u v) (vec-- u v))))
 :hints (("GOAL" :use ((:instance norm-inner-product-equivalence (vec (vec-- u v))))))))

(local (defthm lemma-2
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (norm^2 (vec-- u v)) 
		 (+ (dot u (vec-- u v)) (- (dot v (vec-- u v))))))
 :hints (("GOAL" :use ((:instance scalar-*-closure (a -1) (vec v))
		       (:instance dot-linear-first-coordinate-2 
				  (vec1 u)
				  (vec2 (scalar-* -1 v))
				  (vec3 (vec-- u v))))))))

(local (defthm lemma-3
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (norm^2 (vec-- u v)) 
		 (+ (dot u u) (- (dot u v)) (- (dot v u)) (dot v v))))
 :hints (("GOAL" :use ((:instance lemma-2)
		       (:instance scalar-*-closure (a -1) (vec v))
		       (:instance dot-linear-second-coordinate-2 
				  (vec1 v)
				  (vec2 u)
				  (vec3 (scalar-* -1 v)))
		       (:instance dot-linear-second-coordinate-2 
				  (vec1 u)
				  (vec2 u)
				  (vec3 (scalar-* -1 v))))))))

;; < u - v, u - v > = < u, u > - 2 < u , v > + < v, v >
(local (defthm lemma-4
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (norm^2 (vec-- u v)) 
		 (+ (dot u u) (- (* 2 (dot u v))) (dot v v))))
 :hints (("GOAL" :do-not-induct t
		 ;:in-theory (disable <-+-negative-0-2)
		 :use ((:instance lemma-3)
		       (:instance dot-commutativity (vec1 u) (vec2 v)))))))

;; 0 <= \| u - v \|^2
(local (defthm lemma-5
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))) 
	  (<= 0 (norm^2 (vec-- u v))))))

;; 0 <= < u, u > - 2 < u , v > + < v, v >
(local (defthm lemma-6
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (= 0 (norm^2 (vec-- u v)))
		 (= 0 (+ (dot u u) (- (* 2 (dot u v))) (dot v v)))))
 :hints (("GOAL" :use ((:instance lemma-5)
		       (:instance lemma-4))))))

;; replacing v with (scalar-* (* (/ (dot v v)) (dot u v)) v)
(local (defthm lemma-7
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))) 
	  (equal (= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
		 
	  	 (= 0 
	      	     (+ (dot u u) 
		 	(- (* 2 (dot u (scalar-* (* (/ (dot v v)) (dot u v)) v))))
		 	(dot (scalar-* (* (/ (dot v v)) (dot u v)) v)
		      	     (scalar-* (* (/ (dot v v)) (dot u v)) v))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure (a (* (/ (dot v v)) (dot u v))) (vec v))
		       (:instance lemma-6 (v (scalar-* (* (/ (dot v v)) (dot u v)) v))))))))

(local (defthm lemma-8
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))) 
	  (equal (= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (= 0 
	      	     (+ (dot u u) 
		 	(- (* (* 2 (* (/ (dot v v)) (dot u v))) 
		       	   (dot u v)))
		 	(* (/ (dot v v)) 
		    	   (dot u v)
		    	   (/ (dot v v)) 
		    	   (dot u v)
		    	   (dot v v))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure (a (* (/ (dot v v)) (dot u v))) (vec v))
		       (:instance lemma-7))))))

;;
;; case when v is not zero
;;
(local (defthm lemma-9
 (implies (and (realp x) (not (= x 0)) 
	       (realp y))
	  (equal (* (/ x) y (/ x) y x)
		 (* (/ x) y y)))))

(local (defthm lemma-10
 (implies (and (real-listp v) (not (zvecp v)))
	  (and (not (equal (dot v v) 0))
	       (< 0 (dot v v))))
 :hints (("GOAL" :use ((:instance norm-inner-product-equivalence (vec v))
		       (:instance zvecp-iff-zp-vec (vec v)))))))

(local (defthm lemma-11
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (equal (= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (= 0 
	      	     (+ (dot u u) 
		 	(* -2 (* (/ (dot v v)) (dot u v) (dot u v)))
		 	(* (/ (dot v v)) (dot u v) (dot u v))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure (a (* (/ (dot v v)) (dot u v))) (vec v))
		       (:instance lemma-9 (x (dot v v)) (y (dot u v)))
		       (:instance lemma-8))))))


(local (defthm lemma-12
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (equal (= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (= 0 
	      	     (+ (dot u u) 
		 	(- (* (/ (dot v v)) (dot u v) (dot u v)))))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-11))
		 :in-theory (disable <-+-negative-0-2)))))

(local (defthm lemma-13
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (equal (= 0 (norm^2 (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (= (* (/ (dot v v)) (dot u v) (dot u v))
	      	     (dot u u))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-11))))))

(local (defthm lemma-14
 (implies (and (realp x) (realp y) (realp z) (not (= x 0)))
	  (equal (= (* (/ x) y y) z)
	  	 (= (* y y) (* z x))))))

(local (defthm lemma-15
 (implies (and (realp a) (realp b)) 
	  (= (* a b) (* b a)))
 :rule-classes nil))

(local (defthm lemma-16
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (equal (= 0 (norm^2 (vec-- u 
				   (scalar-* (* (/ (dot v v)) (dot u v)) v))))
	  	 (= (* (dot u v) (dot u v))
	      	    (* (dot u u) (dot v v)))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable not commutativity-2-of-* commutativity-of-*)
		 :use ((:instance lemma-11)
		       (:instance lemma-13)
		       (:instance lemma-14 (x (dot v v)) (y (dot u v)) (z (dot u u))))))))

;; equality implies norm thing is zero
(local (defthm lemma-17
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (implies (= (* (dot u v) (dot u v))
	      	      (* (dot u u) (dot v v)))
		      (= 0 (norm^2 (vec-- u 
				   	(scalar-* (* (/ (dot v v)) (dot u v)) v))))))
 :hints (("GOAL" :use ((:instance lemma-11)
		       (:instance lemma-13)
		       (:instance lemma-14 (x (dot v v)) (y (dot u v)) (z (dot u u))))))
 :rule-classes nil))


;; equality implies the difference is zero
(local (defthm lemma-18
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v)))
	  (implies (= (* (dot u v) (dot u v))
	      	      (* (dot u u) (dot v v)))
		      (zvecp (vec-- u 
				    (scalar-* (* (/ (dot v v)) (dot u v)) v)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-17)
		       (:instance zvecp-iff-zp-vec
				  (vec (vec-- u (scalar-* (* (/ (dot v v)) (dot u v)) v)))))))))

;; equality means the two vectors are linear
(local (defthm lemma-19
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v))
	       (= (* (dot u v) (dot u v))
	      	     (* (dot u u) (dot v v))))
	  (equal u 
		 (scalar-* (* (/ (dot v v)) (dot u v)) v)))
 :rule-classes nil
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure (a (* (/ (dot v v)) (dot u v))) (vec v))
		       (:instance lemma-18)
		       (:instance vec---zero-inverse
				  (vec1 u)
				  (vec2 (scalar-* (* (/ (dot v v)) (dot u v)) v))))))))

(defun-sk linear-dependence-nz (u v)
 (exists a
	 (equal u (scalar-* a v))))

(defun linear-dependence (u v)
 (or (zvecp u) (zvecp v) (linear-dependence-nz u v)))

(local (defthm lemma-20
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (not (zvecp v))
	       (= (* (dot u v) (dot u v))
	      	     (* (dot u u) (dot v v))))
	  (linear-dependence-nz u v))
 :hints (("GOAL" :do-not-induct t
		 :cases (zvecp v)
		 :use ((:instance lemma-19))))))

;; CS1 equality implies v = 0 or u = av
(local (defthm lemma-21
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))
	       (= (* (dot u v) (dot u v))
	      	  (* (dot u u) (dot v v))))
	  (or (zvecp v) (linear-dependence-nz u v)))
 :rule-classes nil))

;; CS2 equality implies v = 0 or u = av
(local (defthm lemma-22
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))
	       (=  (abs (dot u v)) (* (eu-norm u) (eu-norm v))))
	  (or (zvecp v) (linear-dependence-nz u v)))
 :hints (("GOAL" :use ((:instance cs-2-implies-cs-1))))
 :rule-classes nil))

;; v = 0 implies CS1 equality
(local (defthm lemma-23
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (zvecp v))
 	  (= (* (dot u v) (dot u v))
	     (* (dot u u) (dot v v))))))

;; u = 0 implies CS1 equality
(local (defthm lemma-24
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (zvecp u))
 	  (= (* (dot u v) (dot u v))
	     (* (dot u u) (dot v v))))))


;; v = 0 implies CS2 equality
(local (defthm lemma-25
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (zvecp v))
	  (=  (abs (dot u v)) (* (eu-norm u) (eu-norm v))))
 :hints (("GOAL" :use ((:instance eu-norm-zero-iff-zvecp (vec v)))))))

;; u = 0 implies CS2 equality
(local (defthm lemma-26
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (zvecp u))
	  (=  (abs (dot u v)) (* (eu-norm u) (eu-norm v))))
 :hints (("GOAL" :use ((:instance eu-norm-zero-iff-zvecp (vec u)))))))

;; u = av implies CS1 equality
(local (defthm lemma-27
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))
	       (linear-dependence-nz u v))
 	  (= (* (dot u v) (dot u v))
	     (* (dot u u) (dot v v))))
 :hints (("GOAL" ;:do-not-induct t
		 :use ((:instance scalar-*-unclosure (a (linear-dependence-nz-witness u v)))
		       (:instance dot-linear-first-coordinate-1 
				  (a (linear-dependence-nz-witness u v))
				  (vec1 v)
				  (vec2 v)))
		 :cases ((realp (linear-dependence-nz-witness u v))))
	  ("Subgoal 1''" :use ((:instance dot-linear-first-coordinate-1 
				  	  (a (linear-dependence-nz-witness u v))
				  	  (vec1 v)
				  	  (vec2 v))
		       	       (:instance dot-linear-second-coordinate-1 
				 	  (a (linear-dependence-nz-witness u v))
				  	  (vec2 v)
				    	  (vec1 (scalar-* (linear-dependence-nz-witness u v) v))))))))

(local (Defthm lemma-28 
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (realp a) 
	       (equal u (scalar-* a v)))
	  (equal (eu-norm u)
		 (* (abs a) (eu-norm v))))
 :hints (("GOAL" :use ((:instance eu-norm-scalar-* (vec v)))))))

(local (defthm lemma-29
 (implies (and (realp a) (realp b) (<= 0 b))
	  (equal (abs (* a b))
		 (* (abs a) b)))))

(local (defthm lemma-30
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)) (realp a) 
	       (equal u (scalar-* a v)))
	  (equal (abs (dot u v))
		 (* (* (eu-norm v) (eu-norm v))
		    (abs a))))
 :hints (("GOAL" :in-theory (disable abs eu-norm eu-norm-*-eu-norm)
		 :do-not-induct t
		 :use ((:instance dot-eu-norm (vec v))
		       (:instance dot-linear-first-coordinate-1 
				  (a a)
				  (vec1 v)
				  (vec2 v)))))))
(local (defthm lemma-31
 (implies (real-listp v)
	  (equal (norm^2 v)
		 (* (eu-norm v) (eu-norm v))))
 :hints (("GOAL" :in-theory (disable abs eu-norm eu-norm-*-eu-norm)
		 :use ((:instance eu-norm-*-eu-norm (vec v)))
		 :do-not-induct t))))


(local (defthm lemma-32 
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v))
	       (linear-dependence-nz u v))
	  (=  (abs (dot u v)) (* (eu-norm u) (eu-norm v))))
 :hints (("GOAL" :cases ((realp (linear-dependence-nz-witness u v)))
		 :in-theory (disable abs eu-norm eu-norm-*-eu-norm) 
		 :use ((:instance scalar-*-unclosure (a (linear-dependence-nz-witness u v)))
		       (:instance eu-norm-zero-iff-zvecp (vec u)))))))

;; conditions for CS1 equality
(defthm cauchy-schwarz-3 
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (= (* (dot u v) (dot u v))
	      	    (* (dot u u) (dot v v)))
		 (or (zvecp u) (zvecp v) (linear-dependence-nz u v))))
 :hints (("GOAL" :use ((:instance lemma-21)))))

; CS2 equality implies v = 0 or u = av
(defthm cauchy-schwarz-4
 (implies (and (real-listp u) (real-listp v) (= (len u) (len v)))
	  (equal (=  (abs (dot u v)) (* (eu-norm u) (eu-norm v)))
	  	 (or (zvecp u) (zvecp v) (linear-dependence-nz u v))))
 :hints (("GOAL" :in-theory (disable abs lemma-31 eu-norm eu-norm-*-eu-norm lemma-27)
		 :do-not-induct t
		 :use ((:instance eu-norm-zero-iff-zvecp (vec u))
		       (:instance eu-norm-zero-iff-zvecp (vec v))
		       (:instance lemma-22)))))
)


