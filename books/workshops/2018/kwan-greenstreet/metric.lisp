; cert_param: (uses-acl2r)

(in-package "ACL2")

;; theorem used later on that fails if nsa books are loaded
(local (defthm i-small-=>-i-close
 (implies (and (realp x) (realp y) (i-small (- x y)))
	  (i-close x y))))

;; we need Cauchy-Schwarz for the triangle inequality
(include-book "cauchy-schwarz")
(include-book "nonstd/nsa/continuity" :dir :system)

;; this is metric squared 
(define metric^2 (vec1 vec2)
 :returns (d realp)
 :guard (and (real-listp vec1)
             (real-listp vec2)
             (= (len vec1) (len vec2)))
 (norm^2 (vec-- vec1 vec2))
 /// 
 (more-returns 
  (d realp :name metric-is-real) ;; keeping these names temporarily b/c its used
  (d (<= 0 d) :name metric-positive-definite-1)))

;; showing the "definite" part of "positive-definite"
(encapsulate 
 nil

 (local 
  (defthm lemma-1 (implies (real-listp vec)
		  	   (= (len (scalar-* -1 vec))
		     	      (len vec)))
		  :hints (("GOAL" :use ((:instance scalar-*-closure (a -1)))))))

 (local 
  (defthm lemma-2
   (implies (and (real-listp vec1)
	    	 (real-listp vec2)
		 (= (len vec1) (len vec2))
		 (equal vec1 vec2))
	    (= (metric^2 vec1 vec2) 0))
   :hints (("GOAL" :do-not-induct t
		   :in-theory (enable metric^2)
		   :use ((:instance vec---zero-inverse (vec1 vec1) (vec2 vec1))
			 (:instance zvecp-iff-zp-vec (vec (vec-- vec1 vec1))))))))
	 
 (local
  (defthm lemma-3
   (implies (and (real-listp vec1)
	         (real-listp vec2)
	         (equal (len vec1) (len vec2))
		 (= (norm^2 (vec-- vec1 vec2)) 0))
	  (equal vec1 vec2))
   :rule-classes nil
   :hints (("GOAL" :do-not-induct t
		   :use ((:instance zvecp-iff-zp-vec (vec (vec-- vec1 vec2))))))))

 (defthm metric-positive-definite-2
  (implies (and (real-listp vec1)
                (real-listp vec2)
                (= (len vec1) (len vec2)))
           (equal (= (metric^2 vec1 vec2) 0)
                  (equal vec1 vec2)))
  :hints (("GOAL" :in-theory (enable metric^2)
	          :use ((:instance lemma-3)
			(:instance lemma-2)))))

 (defthm metric-commutativity
  (implies (and (real-listp vec1)
                (real-listp vec2)
                (= (len vec1) (len vec2)))
	   (= (metric^2 vec1 vec2)
	      (metric^2 vec2 vec1)))
  :hints (("GOAL" :expand ((metric^2 vec2 vec1)
			   (metric^2 vec1 vec2)))))

)

;;
;; The following are lemmas for showing i-small metric implies i-small entries
;; 

;; max member in a list of reals
(define max-reals ((vec real-listp))
 :guard (real-listp vec)
 :returns (m realp)
 (cond ((not (real-listp vec)) 0)
       ((atom vec) 0)
       (t (max (car vec) (max-reals (cdr vec)))))
 ///
 (more-returns 
  (m (realp m))
  (m (implies (and (natp i) (< i (len vec)) (real-listp vec))
	      (<= (nth i vec) m))
     :name max-reals-is-max
     :hints (("GOAL" :in-theory (enable max-reals)))))) 

;; max abs member in a list of reals
(define max-abs-reals ((vec real-listp))
 :guard (real-listp vec)
 :returns (m realp)
 (b* (((unless (consp vec)) 0)
       ((cons hd tl) vec)
       ((unless (realp hd)) 0))
      (max (abs hd) (max-abs-reals tl)))
 ///
 (more-returns
  (m (realp m)
   :name max-abs-reals-is-real)

  (m (<= 0 m)
     :name max-abs-reals-positive-definite-1)

  (m (implies (and (realp x) (real-listp vec))
              (equal (max-abs-reals (cons x vec))
            	     (max (abs x) m)))
     :name max-abs-reals-of-cons
     :hints (("GOAL" :expand (max-abs-reals vec))))

  (m (<= (max-reals vec) m)
     :name max-reals-<=-max-abs-reals
     :hints (("GOAL" :expand ((max-reals vec) (max-abs-reals vec)))))

  ;; This is super necessary for some reason
  (m (implies (and (natp i) (< i (len vec)) (real-listp vec))
	      (<= (- (nth i vec)) m))
     :name max-abs-reals-is-max--
     :hints (("GOAL" :in-theory (enable max-abs-reals))))

  ;; finally, we show each entry in a list is <= max-abs-reals
  (m (implies (and (natp i) (< i (len vec)) (real-listp vec))
	      (<= (abs (nth i vec)) m))
     :name max-abs-reals-is-max
     :hints (("GOAL" :in-theory (enable max-abs-reals))))))

;; some bits in this encapsulation may be unnecessary
(encapsulate 
 () 

 (local
  (defthm lemma-1
   (implies (and (realp eps) (realp m)
		 (i-small eps)
		 (<= 0 eps)
		 (<= 0 m)
		 (<= m eps))
	    (i-small m))))

 (local
  (defthm lemma-2
   (implies (and (<= a b) (<= b c))
 	    (<= a c))))

 (local
  (defthm lemma-3 
   (implies (and (realp eps)
 	        (natp i)
 	        (< i (len vec))
 	        (real-listp vec)
 	        (<= (max-abs-reals vec) eps))
  	    (<= (abs (nth i vec)) eps))
   :hints (("GOAL" :do-not-induct t
 		   :use ((:instance max-abs-reals-is-max (i i) (vec vec))
 		       	 (:instance lemma-2 (a (nth i vec)) (b (max-abs-reals vec)) (c eps)))))))

 (local
  (defthm lemma-4
   (implies (and (realp eps)
 	        (natp i)
 	        (<= 0 eps)
 	        (< i (len vec))
 	        (i-small eps)
 	        (real-listp vec)
 	        (<= (max-abs-reals vec) eps))
  	    (<= (abs (nth i vec)) eps))
  :hints (("GOAL" :do-not-induct t
 		  :use ((:instance max-abs-reals-is-max (i i) (vec vec))
 		        (:instance lemma-2 (a (nth i vec)) (b (max-abs-reals vec)) (c eps)))))))

(defthm real-vec-is-real
 (implies (and (real-listp vec) (< i (len vec)) (natp i))
	  (realp (nth i vec))))

;; if the norm of the vector is i-small, 
;;  then so are the abs of the entries
(defthm i-small-vec-=>-abs-elements-i-small
 (implies (and (realp eps)
	       (natp i)
	       (<= 0 eps)
	       (< i (len vec))
	       (i-small eps)
	       (real-listp vec)
	       (<= (max-abs-reals vec) eps))
 	  (i-small (abs (nth i vec))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-4)
		       (:instance lemma-1 (m (nth i vec)))))))
		       
;; if the norm of the vector is i-small, 
;;  then so are the entries
(defthm i-small-vec-=>-elements-i-small
 (implies (and (realp eps)
	       (natp i)
	       (<= 0 eps)
	       (< i (len vec))
	       (i-small eps)
	       (real-listp vec)
	       (<= (max-abs-reals vec) eps))
 	  (i-small (nth i vec)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-4)
		       (:instance lemma-1 (m (nth i vec)))))))
)


;; Now if the norm of the difference of vectors is i-small
;;  then so are the differences of entries
(defthm vec---i-small-=>-abs-elements-i-small
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (= (len vec1) (len vec2))
	       (realp eps)
	       (i-small eps)
	       (<= 0 eps)
	       (natp i)
	       (< i (len (vec-- vec1 vec2)))
	       (<= (max-abs-reals (vec-- vec1 vec2)) eps))
	  (i-small (abs (- (nth i vec1) (nth i vec2)))))
 :hints (("GOAL" :use ((:instance vec---elements-difference)
		       (:instance i-small-vec-=>-abs-elements-i-small (vec (vec-- vec1 vec2)))))))

;;
;; So now i want to say (nth i vec1) and (nth i vec2) are i-close 
;;
(encapsulate
 ()
 (local 
  (defthm lemma-1
   (implies (and (realp a) (realp b) (i-small (abs (- a b))))
  	    (i-small (- a b)))))
 
;; i'll just have to settle for i-small (nth i vec1) - (nth i vec2)
(defthm vec---i-small-=>-elements-i-small
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (= (len vec1) (len vec2))
	       (realp eps)
	       (i-small eps)
	       (<= 0 eps)
	       (natp i)
	       (< i (len (vec-- vec1 vec2)))
	       (<= (max-abs-reals (vec-- vec1 vec2)) eps))
	  (i-small (- (nth i vec1) (nth i vec2))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure (a -1) (vec vec2))
		       (:instance vec---i-small-=>-abs-elements-i-small)))))

;; (nth i vec1) and (nth i vec2) are i-close 
(defthm vec---i-small-=>-elements-i-close
 (implies (and (real-listp vec1)
	       (real-listp vec2)
	       (= (len vec1) (len vec2))
	       (realp eps)
	       (i-small eps)
	       (<= 0 eps)
	       (natp i)
	       (< i (len (vec-- vec1 vec2)))
	       (<= (max-abs-reals (vec-- vec1 vec2)) eps))
	  (i-close (nth i vec1) (nth i vec2)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance vec---i-small-=>-elements-i-small)
		       (:instance i-small-=>-i-close (x (nth i vec1)) (y (nth i vec2)))))))
)

;; if the max-abs-reals is i-limited, then so are the entries
(encapsulate
 nil

(local (defthm lemma-1
 (implies (and (realp x) (realp y) (< (abs x) y) (i-limited y))
	  (i-limited (abs x)))))

(local (defthm lemma-2
 (implies (and (realp x) (i-limited (abs x)))
	  (i-limited x))))

(local (defthm lemma-3
 (implies (and (real-listp vec) (= (max-abs-reals vec) 0)
	       (natp i) (< i (len vec)))
	  (or (null vec) (= (nth i vec) 0 )))
 :hints (("GOAL" :in-theory (enable max-abs-reals)))
 :rule-classes nil))

(defthm max-abs-i-limited-implies-elements-i-limited
 (implies (and (real-listp vec) (i-limited (max-abs-reals vec)) 
	       (natp i) (< i (len vec)))
	  (i-limited (nth i vec)))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance max-abs-reals-is-max)
		       (:instance lemma-3)
		       (:instance lemma-1 (x (nth i vec)) (y (max-abs-reals vec)))
		       (:instance lemma-2 (x (nth i vec)))))))
)


;; 
;; similar to before, but now I want to say the entries are i-small
;;
(encapsulate
 nil

(local (defthm lemma-1
 (implies (and (realp x) (realp y) (< (abs x) y) (i-small y))
	  (i-small (abs x)))))

(local (defthm lemma-2
 (implies (and (real-listp vec) (i-small (max-abs-reals vec)) 
	       (natp i) (< i (len vec)))
	  (i-small (abs (nth i vec))))
 :hints (("GOAL" :use ((:instance max-abs-reals-is-max (vec vec))
		       (:instance lemma-1 (x (nth i vec)) (y (max-abs-reals vec))))))))

(local (defthm lemma-3
 (implies (and (realp x) (i-small (abs x)))
	  (i-small x))))

(defthm max-abs-i-small-implies-elements-i-small
 (implies (and (real-listp vec) (i-small (max-abs-reals vec)) 
	       (natp i) (< i (len vec)))
	  (i-small (nth i vec)))
 :hints (("GOAL" :use ((:instance lemma-2)
		       (:instance lemma-3 (x (nth i vec)))))))
)



;;
;; max-abs-reals <= norm^2
;;
(encapsulate
 ()

(local (defthm lemma-2
 (implies (and (realp x) (<= 0 x) (real-listp vec))
	  (<= (* (car vec) (car vec)) (+ x (* (car vec) (car vec)))))))

;; norm-sq is larger than max-abs-reals
(defthm max-abs-reals-<=-norm^2
 (implies (real-listp vec)
	  (<= (* (max-abs-reals vec) (max-abs-reals vec)) 
	      (norm^2 vec)))
 :hints (("GOAL" :in-theory (enable max-abs-reals norm^2))))
)

(defthm i-small-dot-=>-i-small-dot
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y))
	       (i-small (dot x y)))
	  (i-small (dot y x))))

;;
;; defining the euclidean metric
;; 
(defun eu-metric (x y)
 (eu-norm (vec-- x y)))

(defthm eu-metric-metric-sq-equivalence
 (equal (eu-metric x y) (acl2-sqrt (metric^2 x y)))
 :hints (("GOAL" :in-theory (enable metric^2))))

(defthm eu-metric-commutativity
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y)))
	  (equal (eu-metric x y) (eu-metric y x))))

(defthm eu-metric-positive-definite-1
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y)))
	  (<= 0 (eu-metric x y))))

(defthm eu-metric-positive-definite-2
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y)))
	  (equal (equal x y)
	         (= (eu-metric x y) 0)))
 :hints (("GOAL" :use ((:instance metric-positive-definite-2 (vec1 x) (vec2 y))))))

;; triangle inequality for vectors (non-metric)
(encapsulate
 nil

;; starting off with two vectors
(local (defthm lemma-1
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (equal (norm^2 (vec-+ x y))
		 (dot (vec-+ x y) (vec-+ x y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance norm-inner-product-equivalence (vec (vec-+ x y))))))))

;; seperating into dot products
(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (equal (norm^2 (vec-+ x y))
		 (+ (dot x (vec-+ x y)) (dot y (vec-+ x y)))))
 :hints (("GOAL" :do-not-induct t))))

;; acl2 didnt like using linearity of the second coordinate (again)
(local (defthm lemma-3
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (equal (norm^2 (vec-+ x y))
		 (+ (dot x x) (dot x y) (dot y x) (dot y y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable dot-linear-first-coordinate-2 dot-linear-second-coordinate-2)
		 :use ((:instance lemma-2)
		       (:instance dot-linear-second-coordinate-2 (vec1 x) (vec2 x) (vec3 y))
		       (:instance dot-linear-second-coordinate-2 (vec1 y) (vec2 x) (vec3 y)))))))

;; simplifying RHS
(local (defthm lemma-4
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (equal (norm^2 (vec-+ x y))
		 (+ (norm^2 x) (* 2 (dot x y)) (norm^2 y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable dot-linear-first-coordinate-2 dot-linear-second-coordinate-2)
		 :use ((:instance lemma-3)
		       (:instance norm-inner-product-equivalence (vec x))
		       (:instance norm-inner-product-equivalence (vec y))
		       (:instance dot-commutativity (vec2 y) (vec1 x)))))))

(local (defthm lemma-5
 (implies (and (realp a) (realp b) (realp c))
	  (<= (+ a b c)
	      (+ a (abs b) c)))))

;; taking abs
(local (defthm lemma-6
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (<= (norm^2 (vec-+ x y))
	      (+ (norm^2 x) (abs (* 2 (dot x y))) (norm^2 y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-4)
		       (:instance lemma-5 (a (norm^2 x)) (b (* 2 (dot x y))) (c (norm^2 y))))))))
	
;; lemma involving abs b/c ACL2 can't figure this out by itself
(local (defthm lemma-7
 (implies (and (realp a))
	  (equal (abs (* 2 a)) (* 2 (abs a))))))

;; moving abs inwards more
(local (defthm lemma-8
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (<= (norm^2 (vec-+ x y))
	      (+ (norm^2 x) (* 2 (abs (dot x y))) (norm^2 y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-6))))))
		
;; applying Cauchy-Schwarz
(local (defthm lemma-9
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (<= (norm^2 (vec-+ x y))
	      (+ (norm^2 x) (* 2 (eu-norm x) (eu-norm y)) (norm^2 y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-8)
		       (:instance cauchy-schwarz-2 (u x) (v y)))))))

;; applying square of sum
(local (defthm lemma-10
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (<= (norm^2 (vec-+ x y))
	      (* (+ (eu-norm x) (eu-norm y)) (+ (eu-norm x) (eu-norm y)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-9))))))

;; applying square of sum
(defthm triangle-inequality
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (<= (eu-norm (vec-+ x y))
	      (+ (eu-norm x) (eu-norm y))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance lemma-10)
		       (:instance eu-norm-*-eu-norm (vec (vec-+ x y)))))))
)

;; metric triangle inequality
(encapsulate
 nil

;; x - y = x - z + z - y
(local (defthm lemma-1
 (implies (and (real-listp x) (real-listp y) (real-listp z) (= (len y) (len x)) (= (len z) (len x)))
	  (equal (vec-- x y)
		 (vec-+ (vec-- x z) (vec-- z y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable eu-metric-positive-definite-2 vec---zero-inverse) 
		 :use ((:instance scalar-*-closure (a -1) (vec z))
		       (:instance scalar-*-closure (a -1) (vec y))
		       (:instance vec---zero-inverse (vec1 z) (vec2 z))
		       (:instance vec-+-associativity 
				  (vec1 (scalar-* -1 z))
				  (vec2 z)
				  (vec3 (scalar-* -1 y)))
		       (:instance vec-+-associativity 
				  (vec1 x)
				  (vec2 (scalar-* -1 z))
				  (vec3 (vec-- z y))))))))

;; applying triangle inequality for vectors
(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (real-listp z) (= (len y) (len x)) (= (len z) (len x)))
	  (<= (eu-metric x y)
	      (+ (eu-metric x z) (eu-metric z y))))
 :hints (("GOAL" :do-not-induct t
		 :expand ((eu-metric x y) (eu-metric x z) (eu-metric z y))
		 :in-theory (disable lemma-1 eu-metric-metric-sq-equivalence eu-metric-positive-definite-2 vec---zero-inverse)
		 :use ((:instance lemma-1)
		       (:instance triangle-inequality (x (vec-- x z)) (y (vec-- z y))))))))

;; main theorem
(defthm metric-triangle-inequality
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len y) (len x)) (= (len z) (len x)))
	  (<= (eu-metric x y)
	      (+ (eu-metric x z) (eu-metric y z))))
 :hints (("GOAL" :use ((:instance lemma-2)))))

)

;; 
;; reverse triangle inequality
;;
(encapsulate
 nil

;; x = x - y + y
(local (defthm lemma-1
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (equal x (vec-+ (vec-- x y) y)))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse eu-metric-positive-definite-2)
		 :use ((:instance scalar-*-closure (a -1) (vec y))
		       (:instance vec---zero-inverse (vec1 y) (vec2 y))
		       (:instance zvecp-is-additive-identity-2 (vec1 x) (vec2 (vec-+ (scalar-* -1 y) y)))
		       (:instance vec-+-associativity (vec1 x) (vec2 (scalar-* -1 y)) (vec3 y)))))
 :rule-classes nil))

;; || x || <= || x - y || + || y ||
(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (<= (eu-norm x)
	      (+ (eu-norm (vec-- x y)) (eu-norm y)))) 
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable vec---zero-inverse eu-metric-positive-definite-2)
		 :use ((:instance lemma-1)
		       (:instance triangle-inequality (x (vec-- x y))))))))
	
;; || x || - || y || <= || x - y ||
(local (defthm lemma-3
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)))
	  (<= (- (eu-norm x) (eu-norm y))
	      (eu-norm (vec-- x y))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable eu-norm)
		 :use ((:instance lemma-2))))))

;; case || y || <= || x || 
(local (defthm lemma-4
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (<= (eu-norm y) (eu-norm x)))
	  (<= (abs (- (eu-norm x) (eu-norm y)))
	      (eu-norm (vec-- x y))))
 :hints (("GOAL" :in-theory (disable eu-norm)))))

;; - || x - y || <= || x || - || y || 
(local (defthm lemma-5
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y)))
	  (<= (- (eu-norm y) (eu-norm x))
	      (eu-norm (vec-- x y))))
 :hints (("GOAL" :in-theory (disable eu-norm eu-metric-metric-sq-equivalence)
		 :use ((:instance eu-metric-commutativity)
		       (:instance lemma-3 (x y) (y x)))))))

;; case || x || <= || y || 
(local (defthm lemma-6
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (<= (eu-norm x) (eu-norm y)))
	  (<= (abs (- (eu-norm x) (eu-norm y)))
	      (eu-norm (vec-- x y))))
 :hints (("GOAL" ;:do-not-induct t
		 :in-theory (disable eu-norm)
		 :use ((:instance lemma-5))))))

;; combine both cases
(defthm reverse-triangle-inequality
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y)))
	  (<= (abs (- (eu-norm x) (eu-norm y))) (eu-norm (vec-- x y))))
 :hints (("GOAL" :cases ((<= (eu-norm x) (eu-norm y)))
		 :in-theory (disable eu-norm abs))))
)


;; norms are continuous
(defthm eu-norm-is-continuous
 (implies (and (real-listp x) (real-listp y) (= (len x) (len y)) (i-small (eu-metric x y)))
	  (i-small (abs (- (eu-norm x) (eu-norm y)))))
 :hints (("GOAL" :in-theory (disable eu-norm eu-metric eu-metric-metric-sq-equivalence)
		 :use((:instance reverse-triangle-inequality))
		 :expand (eu-metric x y))))


;; norm-sq are continuous
(encapsulate
 nil

 ;; difference of squares
 (local (defthm lemma-1
  (implies (and (real-listp x) (real-listp y)) 
	   (equal (- (norm^2 x) (norm^2 y))
		  (* (- (eu-norm x) (eu-norm y)) 
		     (+ (eu-norm x) (eu-norm y)))))))

 ;; applying abs
 (local (defthm lemma-2
  (implies (and (real-listp x) (real-listp y)) 
	   (equal (abs (- (norm^2 x) (norm^2 y)))
		  (abs (* (- (eu-norm x) (eu-norm y)) 
		       	  (+ (eu-norm x) (eu-norm y))))))
  :hints (("GOAL" :in-theory (disable distributivity)))))

 ;; ACL2 wants this for some reason to prove lemma-4
 (local (defthm lemma-3
  (implies (and (realp a) (realp b))
	   (equal (abs (* a b)) (* (abs a) (abs b))))))

 ;; moving abs
 (local (defthm lemma-4
  (implies (and (real-listp x) (real-listp y))
	   (equal (abs (- (norm^2 x) (norm^2 y)))
		  (* (abs (- (eu-norm x) (eu-norm y)))
		     (abs (+ (eu-norm x) (eu-norm y))))))
  :hints (("GOAL" :do-not-induct t 
		  :in-theory (disable distributivity)
		  :use ((:instance lemma-2))))))

;; ACL2 wants this too for some reason
(local (defthm lemma-5
 (implies (and (realp a) (i-limited a))
	  (i-limited (abs a)))))

;; ACL2 wants this too too for some reason
(local (defthm lemma-6
 (implies (and (realp a) (realp b) (i-limited a) (i-small (abs (- a b))))
	  (i-limited (+ a b)))
 :hints (("GOAL" :cases ((i-limited b))))))

;; norm^2 is continuous
(defthm norm^2-is-continuous
  (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (i-small (eu-metric x y)) (i-limited (eu-norm x)))
	   (i-small (abs (- (norm^2 x) (norm^2 y)))))
  :hints (("GOAL" :do-not-induct t
		  :in-theory (disable abs distributivity eu-norm)
		  :use ((:instance eu-norm-is-continuous)
			(:instance lemma-6 (a (eu-norm x)) (b (eu-norm y)))
			(:instance lemma-5 (a (+ (eu-norm x) (eu-norm y))))
			(:instance small*limited->small 
				   (x (abs (- (eu-norm x) (eu-norm y))))
				   (y (abs (+ (eu-norm x) (eu-norm y)))))
			(:instance lemma-4)))))

;; (dot x x) is continuous
(defthm dot-x-x-is-continuous
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x)) (i-small (eu-metric x y)) (i-limited (eu-norm x)))
	   (i-small (abs (- (dot x x) (dot y y)))))
 :hints (("GOAL" :in-theory (disable distributivity)
		 :use ((:instance norm^2-is-continuous)
		       (:instance norm-inner-product-equivalence (vec x))
		       (:instance norm-inner-product-equivalence (vec y))))))
)

(defthm i-small-eu-metric-implies-i-small-metric
 (implies (and (real-listp x) (real-listp y) (i-small (eu-metric x y)))
	  (i-small (metric^2 x y)))
 :hints (("GOAL" :in-theory (disable eu-metric-metric-sq-equivalence eu-metric)
 		 :use ((:instance eu-metric-metric-sq-equivalence)))))

;; dot product is continuous
(encapsulate
 nil

(local (defthm lemma-1
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len y) (len x)) (= (len z) (len x)))
	  (equal (abs (- (dot x z) (dot y z)))
		 (abs (dot (vec-- x y) z))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance scalar-*-closure (a -1) (vec y))
		       (:instance dot-linear-first-coordinate-2
				  (vec1 x)	
				  (vec2 (scalar-* -1 y))
				  (vec3 z))
		       (:instance dot-linear-first-coordinate-1 (a -1) (vec1 y) (vec2 z)))))))

(local (defthm lemma-2
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len y) (len x)) (= (len z) (len x)))
	  (<=  (abs (- (dot x z) (dot y z)))
	       (abs (dot (vec-- x y) z))))
 :hints (("GOAL" :do-not-induct t))))

(local (defthm lemma-3
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (= (len y) (len x)) (= (len z) (len x)))
	  (<=  (abs (- (dot x z) (dot y z)))
	       (abs (* (eu-norm (vec-- x y)) (eu-norm z)))))
 :hints (("GOAL" :do-not-induct t
		 :use ((:instance cauchy-schwarz-2 (u (vec-- x y)) (v z)))))))

(local (defthm lemma-4
 (implies (and (realp a) (realp b) (i-small a) (i-limited b))
	  (i-small (* a b)))))

(local (defthm lemma-5
 (implies (and (real-listp x) (real-listp y) (real-listp z) (i-limited (eu-norm z))
	       (= (len y) (len x)) (= (len z) (len x))
	       (i-small (eu-metric x y)))
	  (i-small (abs (* (eu-norm (vec-- x y)) (eu-norm z)))))
 :hints (("GOAL" :do-not-induct t
		 :expand (eu-metric x y)
		 :use ((:instance lemma-4 (a (eu-metric x y)) (b (eu-norm z))))
		 :in-theory (disable eu-norm eu-metric-metric-sq-equivalence)))))

(local (defthm lemma-6
 (implies (and (realp a) (realp b) (<= (abs a) (abs b)) (i-small (abs b)))
	  (i-small a))
 :hints (("GOAL" :use ((:instance small-if-<-small))))))

(defthm dot-is-continuous-1
 (implies (and (real-listp x) (real-listp y) (real-listp z) 
	       (i-limited (eu-norm z))
	       (= (len y) (len x)) (= (len z) (len x))
	       (i-small (eu-metric x y)))
	  (i-small (- (dot x z) (dot y z))))
 :hints (("GOAL" :do-not-induct t
		 :in-theory (disable abs lemma-1)
		 :use ((:instance lemma-5)
		       (:instance lemma-6 
				  (a (- (dot x z) (dot y z)))
				  (b (* (eu-norm (vec-- x y)) (eu-norm z))))
		       (:instance lemma-3)))))
)

;;
;; The following is how we show i-small metrics implies i-small entries
;;  in general for the sake of continuity 
;;
(defthm max-abs-reals-<=-sqrt-norm
 (implies (real-listp vec)
	  (<= (max-abs-reals vec)
	      (acl2-sqrt (norm^2 vec))))
 :hints (("GOAL" :do-not-induct t)))

(defthm max-abs-reals-<=-eu-norm
 (implies (real-listp vec)
	  (<= (max-abs-reals vec)
	      (eu-norm vec)))
 :hints (("GOAL" :do-not-induct t)))

(defthm eu-norm-i-small-implies-max-abs-reals-i-small
 (implies (and (real-listp vec) (i-small (eu-norm vec)))
	  (i-small (max-abs-reals vec))))

(defthm eu-norm-i-small-implies-elements-i-small
 (implies (and (real-listp vec) (i-small (eu-norm vec))
	       (natp i) (< i (len vec)))
	  (i-small (nth i vec))))

(defthm eu-metric-i-small-implies-entries-of-difference-i-small
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x))
	       (i-small (eu-metric x y)) (natp i) (< i (len x)))
	  (i-small (nth i (vec-- x y))))
 :hints (("GOAL" :in-theory (disable eu-metric-metric-sq-equivalence)
		 :use ((:instance eu-norm-i-small-implies-elements-i-small
				  (vec (vec-- x y)))))))

(defthm eu-metric-i-small-implies-difference-of-entries-i-small
 (implies (and (real-listp x) (real-listp y) (= (len y) (len x))
	       (i-small (eu-metric x y)) (natp i) (< i (len x)))
	  (i-small (- (nth i x) (nth i y))))
 :hints (("GOAL" :use ((:instance vec---elements-difference (vec1 x) (vec2 y))
		       (:instance eu-metric-i-small-implies-entries-of-difference-i-small)))))


(in-theory (disable eu-metric-metric-sq-equivalence))

(encapsulate
 nil

 (local (defthm lemma-1
  (implies (and (realp x) (realp y) (i-limited y) (<= 0 x) (<= x y))
	   (i-limited x))))

(defthm eu-norm-i-limited-implies-max-abs-reals-i-limited
 (implies (and (real-listp vec) (i-limited (eu-norm vec)))
	  (i-limited (max-abs-reals vec)))
 :hints (("GOAL" :use ((:instance lemma-1 
				  (x (max-abs-reals vec))
				  (y (eu-norm vec)))))))
)

(defthm eu-norm-i-limited-implies-entries-i-limited
 (implies (and (real-listp vec) (i-limited (eu-norm vec)) (natp i) (< i (len vec)))
	  (i-limited (nth i vec))))






