; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "vectors")

;; this is actually norm squared 
(define norm^2 ((vec real-listp))
 :returns (ret realp)
 (cond ((null vec) 0)
       ((not (real-listp vec)) 0)
       (t (+ (* (car vec) (car vec))
             (norm^2 (cdr vec)))))
 ///
 (more-returns
  (ret realp :name norm-is-real) ;; keeping this name temporarily b/c its used
  (ret (implies (real-listp vec) (<= 0 ret))
       :hints (("GOAL" :in-theory (enable norm^2)))
       :name norm-positive-definite-1)
  (ret (implies (real-listp vec)
        	(<= (norm^2 (cdr vec)) ret))
; Commented out by Matt K.; see GitHub Issue #1320
;      :hints (("GOAL" :expand (ret)))
       :rule-classes ((:linear))
       :name norm-monotonicity-1)))

;; the definite part of "norm is positive-definite"
(encapsulate 
 nil

 (local 
  (defthm lemma-1
   (implies (and (real-listp vec) (zvecp vec))
            (= (norm^2 vec) 0))
   :hints (("GOAL" :in-theory (enable zvecp norm^2)))))

 (local 
  (defthm lemma-2
   (implies (and (real-listp vec) 
                 (not (equal (norm^2 (cdr vec)) 0)))
            (not (equal (norm^2 vec) 0)))
   :hints (("GOAL" :expand ((norm^2 vec))
                   :use ((:instance norm-positive-definite-1
                                    (vec (cdr vec))))))))
 (local
  (defthm lemma-3
   (implies (and (real-listp vec)
                 (realp (car vec))
                 (zvecp (cdr vec))
                 (equal (norm^2 vec) 0))
            (equal (car vec) 0))
   :hints (("GOAL" :expand ((norm^2 vec))))))

 (defthm zvecp-monotonicity-2-2
  (implies (and (zvecp (cdr vec)) (consp vec))
           (equal (zvecp vec) (= (car vec) 0)))
  :hints (("GOAL" :in-theory (enable zvecp))))

 ;; norm-positive-definite-2
 (defthm zvecp-iff-zp-vec
  (implies (real-listp vec) 
           (equal  (= (norm^2 vec) 0) (zvecp vec))))
 )

;; the norm of -x is the same as x
(defthm norms-under-negative-vec
 (implies (real-listp vec)
	  (equal (norm^2 (scalar-* -1 vec)) (norm^2 vec)))
 :hints (("GOAL" :in-theory (enable scalar-* norm^2))))

 ;; norms are commutative wrt to differences
 (defthm norm-vec--x-commutative 
  (implies (and (real-listp vec1)
                (real-listp vec2)
                (= (len vec1) (len vec2)))
  	   (= (norm^2 (vec--x vec1 vec2)) (norm^2 (vec--x vec2 vec1))))
  :hints (("GOAL" :in-theory (enable norm^2 vec--x)
		  :induct (and (nth i vec1) (nth i vec2)))))

 (defthm norm-vec---commutative 
  (implies (and (real-listp vec1)
                (real-listp vec2)
                (= (len vec1) (len vec2)))
  	   (= (norm^2 (vec-- vec1 vec2)) (norm^2 (vec-- vec2 vec1))))
  :hints (("GOAL" :in-theory (enable vec---equivalence))))

(defthm norm-scalar-*
 (implies (and (realp a) (real-listp vec))
	  (equal (norm^2 (scalar-* a vec))
		 (* (* a a) (norm^2 vec))))
 :hints (("GOAL" :in-theory (enable scalar-* norm^2))))


(defthm norm-inner-product-equivalence
 (equal (norm^2 vec) (dot vec vec))
 :hints (("GOAL" :in-theory (enable norm^2 dot)))
 :rule-classes nil)

(include-book "nonstd/nsa/sqrt" :dir :system)

(defun eu-norm (vec)
 (acl2-sqrt (norm^2 vec)))

(defthm eu-norm->=-0
 (<= 0 (eu-norm vec)))

;; definite part of "norm is positive definite" but with a different name
(encapsulate
 nil

(local (defthm lemma-1
 (implies (zvecp vec)
	  (= (eu-norm vec) 0))
 :hints (("GOAL" :use (:instance zvecp-iff-zp-vec)
		 :in-theory (enable zvecp)))))

(local (defthm lemma-2
 (implies (and (real-listp vec) (= (eu-norm vec) 0))
	  (= (norm^2 vec) 0))
 :hints (("GOAL" :use ((:instance norm-positive-definite-1)
		       (:instance sqrt->-0 (x (norm^2 vec))))))))

(defthm eu-norm-zero-iff-zvecp
 (implies (real-listp vec)
 	  (iff (= (eu-norm vec) 0)
      	       (zvecp vec)))
 :hints (("GOAL" :use ((:instance lemma-1)
		       (:instance zvecp-iff-zp-vec)
		       (:instance lemma-2)))))
)

(defthm eu-norm-scalar-*
 (implies (and (real-listp vec) (realp a))
	  (equal (eu-norm (scalar-* a vec))
		 (* (abs a) (eu-norm vec))))
 :hints (("GOAL" :in-theory (disable abs) 
		 :do-not-induct t
		 :use ((:instance norm-scalar-*)
		       (:instance sqrt-* (x (* a a)) (y (norm^2 vec)))))))

(defthm eu-norm-*-eu-norm
 (implies (real-listp vec)
	  (equal (* (eu-norm vec) (eu-norm vec))
		 (norm^2 vec))))

(defthm abs-eu-norm
 (implies (real-listp vec)
	  (equal (abs (eu-norm vec)) (eu-norm vec))))


(defthm dot-eu-norm 
 (implies (real-listp vec)
	  (equal (dot vec vec) (* (eu-norm vec) (eu-norm vec))))
 :hints (("GOAL" :use ((:instance norm-inner-product-equivalence)
		       (:instance eu-norm-*-eu-norm)))))

(defthm eu-norm-negative-vec
 (implies (real-listp vec)
	  (equal (eu-norm (scalar-* -1 vec)) (eu-norm vec))))

(in-theory (disable dot-eu-norm))



