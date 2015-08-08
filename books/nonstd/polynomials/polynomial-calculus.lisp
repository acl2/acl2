(in-package "ACL2")

(include-book "polynomial-defuns")
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)

(local (include-book "polynomial-lemmas"))
(local (include-book "nonstd/nsa/derivative-raise" :dir :system))
(local (include-book "nonstd/nsa/equivalence-continuity" :dir :system))
(local (include-book "nonstd/nsa/equivalence-derivatives" :dir :system))
(local (include-book "nonstd/integrals/equivalence-ftc" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

#|
(defun revpoly (poly)
  (if (endp poly)
      nil
    (append (revpoly (cdr poly)) (list (car poly)))))

(defun eval-polynomial-len (poly x)
  (if (consp poly)
      (+ (* (car poly)
	    (expt x (1- (len poly))))
	 (eval-polynomial-len (cdr poly) x))
    0))

(defthm eval-polynomial-len-correct
  (implies (and (real-polynomial-p poly)
		(realp x))
	   (equal (eval-polynomial-len (revpoly poly) x)
		  (eval-polynomial-expt-aux poly x
))))
  |#



(defun derivative-polynomial-aux (poly n)
  (if (and (real-polynomial-p poly)
	   (natp n)
	   (consp poly))
      (if (< 0 n)
	  (cons (* n (car poly))
		(derivative-polynomial-aux (cdr poly) (1+ n)))
	(derivative-polynomial-aux (cdr poly) (1+ n)))
    nil))

(defun derivative-polynomial (poly)
  (derivative-polynomial-aux poly 0))

(defun integral-polynomial-aux (poly n)
  (if (and (real-polynomial-p poly)
	   (natp n)
	   (consp poly))
      (append (if (= n 0)
                  (list 0 (/ (car poly) (1+ n)))
                (list (/ (car poly) (1+ n))))
              (integral-polynomial-aux (cdr poly) (1+ n)))
    nil))

(defun integral-polynomial (poly)
  (integral-polynomial-aux poly 0))

(defthm real-derivative-aux-poly
  (implies (and (real-polynomial-p poly)
		(realp n))
	   (real-polynomial-p (derivative-polynomial-aux poly n))))

(defthm real-derivative-poly
  (implies (real-polynomial-p poly)
	   (real-polynomial-p (derivative-polynomial poly))))

(defthm real-integral-aux-poly
  (implies (and (real-polynomial-p poly)
		(realp n))
	   (real-polynomial-p (integral-polynomial-aux poly n))))

(defthm real-integral-poly
  (implies (real-polynomial-p poly)
	   (real-polynomial-p (integral-polynomial poly))))



(defthm derivative-of-integral-polynomial-aux
  (implies (and (real-polynomial-p poly)
		(natp n))
	   (equal (derivative-polynomial-aux (integral-polynomial-aux poly n)
                                             (if (zp n) n (1+ n)))
		  poly)))

(defthm derivative-of-integral-polynomial
  (implies (real-polynomial-p poly)
	   (equal (derivative-polynomial (integral-polynomial poly))
		  poly))
  :hints (("Goal"
           :use ((:instance derivative-of-integral-polynomial-aux
                            (poly poly)
                            (n 0))))))

(encapsulate
 nil

 (local
  (defun induction-hint (poly n)
    (if (consp poly)
	(1+ (induction-hint (cdr poly) (if (zp n) n (1+ n))))
      n)))

 (local
  (defthmd lemma-1
   (implies (and (real-polynomial-p poly)
                 (natp n)
		 (not (consp poly)))
	    (equal (integral-polynomial-aux
                    (derivative-polynomial-aux poly (if (zp n) n (1+ n)))
                    n)
		   (if (consp poly)
                       (if (zp n)
                           (if (consp (cdr poly))
                               (cons 0 (cdr poly))
                             nil)
                         poly)
                     nil)))))

 (local
  (defthmd lemma-2
    (implies (and (real-polynomial-p poly)
                  (natp n)
                  (< 0 n))
             (equal (integral-polynomial-aux
                     (derivative-polynomial-aux poly (if (zp n) n (1+ n)))
                     n)
                    (if (consp poly)
                        (if (zp n)
                            (if (consp (cdr poly))
                                (cons 0 (cdr poly))
                              nil)
                          poly)
                      nil)))
    :hints (("Goal"
             :induct (induction-hint poly n)))))

 (local
  (defthmd lemma-3
    (implies (and (real-polynomial-p poly)
                  (consp (cdr poly)))
             (equal (CDR (DERIVATIVE-POLYNOMIAL-AUX (CDR POLY) 1))
                    (derivative-polynomial-aux (cdr (cdr poly)) 2)))))

 (local
  (defthmd lemma-4
    (implies (and (real-polynomial-p poly)
                  (natp n)
                  (= 0 n)
                  ;(consp poly)
                  )
             (equal (integral-polynomial-aux
                     (derivative-polynomial-aux poly (if (zp n) n (1+ n)))
                     n)
                    (if (consp poly)
                        (if (zp n)
                            (if (consp (cdr poly))
                                (cons 0 (cdr poly))
                              nil)
                          poly)
                      nil)))
    :hints (("Goal"
             :use ((:instance lemma-3)
                   (:instance lemma-2
                              (poly (cddr poly))
                              (n 1)))
             :do-not-induct t)
            )
    ))

  (defthm integral-of-derivative-polynomial-aux
    (implies (and (real-polynomial-p poly)
                  (natp n))
             (equal (integral-polynomial-aux
                     (derivative-polynomial-aux poly (if (zp n) n (1+ n)))
                     n)
                    (if (consp poly)
                        (if (zp n)
                            (if (consp (cdr poly))
                                (cons 0 (cdr poly))
                              nil)
                          poly)
                      nil)))
    :hints (("Goal"
             :use ((:instance lemma-1)
                   (:instance lemma-2)
                   (:instance lemma-4)))))
 )

(defthm integral-of-derivative-polynomial
  (implies (real-polynomial-p poly)
	   (equal (integral-polynomial (derivative-polynomial poly))
                  (if (and (consp poly)
                           (consp (cdr poly)))
                      (cons 0 (cdr poly))
                    nil)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance integral-of-derivative-polynomial-aux
                            (n 0)))
           :in-theory (disable integral-of-derivative-polynomial-aux)))
  )

(defthm realp-eval-polynomial-expt-aux
  (implies (and (real-polynomial-p poly)
		(realp x)
		(realp n))
	   (realp (eval-polynomial-expt-aux poly x n))))

(defthm realp-eval-cdr-polynomial-expt-aux
  (implies (and (real-polynomial-p poly)
		(consp poly)
		(realp x)
		(realp n))
	   (realp (eval-polynomial-expt-aux (cdr poly) x n))))


(defun-sk forall-x-eps-delta-in-range-deriv-poly-expt-aux-works (poly x n eps delta)
  (forall (x1)
	  (implies (and (realp x1)
			(realp x)
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
				    (eval-polynomial-expt-aux poly x1 n))
				 (- x x1))
			      (eval-polynomial-expt-aux
			       (derivative-polynomial-aux poly n)
			       x
			       (if (zp n) n (1- n))
			       )))
		      eps)))
  :rewrite :direct)

(defun-sk exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works (poly x n eps)
  (exists delta
	  (implies (and (realp x)
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-poly-expt-aux-works poly x n eps delta)))))

(encapsulate
 nil

 (local
  (defthmd lemma-1
    (implies (and (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (natp n)
		  (consp poly))
	     (equal (- (eval-polynomial-expt-aux poly x n)
		       (eval-polynomial-expt-aux poly x1 n))
		    (+ (* (car poly)
			  (- (expt x n)
			     (expt x1 n)))
		       (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
			  (eval-polynomial-expt-aux (cdr poly) x1 (1+ n))))))
    ))

 (local
  (defthmd lemma-2
    (implies (and (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (natp n)
		  (consp poly))
	     (equal (/ (- (eval-polynomial-expt-aux poly x n)
			  (eval-polynomial-expt-aux poly x1 n))
		       (- x x1))
		    (+ (/ (* (car poly)
			     (- (expt x n)
				(expt x1 n)))
			  (- x x1))
		       (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
			     (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
			  (- x x1)))))
    :hints (("Goal"
	     :in-theory (enable lemma-1)))
    ))

 (local
  (defun induction-hint (poly n eps)
    (if (consp poly)
	(1+ (induction-hint (cdr poly)
			    (1+ n)
			    (/ eps 2)))
      (* n eps))))

 (local
  (defthmd lemma-3
    (implies (and (not (consp poly))
		  (realp x)
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works poly x n eps))
    :hints (("Goal"
	     :use ((:instance exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-suff
			      (delta 1)))))))

 (local
  (defthmd lemma-4
    (implies (and (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works poly x n eps delta)
		  (realp delta)
		  (< 0 delta)
		  (realp gamma)
		  (< 0 gamma)
		  (< gamma delta))
	     (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works poly x n eps gamma))
    :hints (("Goal"
	     :use ((:instance forall-x-eps-delta-in-range-deriv-poly-expt-aux-works-necc
			      (x1 (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works-witness poly x n eps gamma))))
	     :in-theory (disable abs)))))

 (local
  (defthmd lemma-5
    (implies (and (forall-x-eps-delta-in-range-deriv-expt-works x n eps delta)
		  (realp delta)
		  (< 0 delta)
		  (realp gamma)
		  (< 0 gamma)
		  (< gamma delta))
	     (forall-x-eps-delta-in-range-deriv-expt-works x n eps gamma))
    :hints (("Goal"
	     :use ((:instance forall-x-eps-delta-in-range-deriv-expt-works-necc
			      (x1 (forall-x-eps-delta-in-range-deriv-expt-works-witness x n eps gamma))))
	     :in-theory (disable abs)))
    ))

 (local
  (defthmd lemma-6
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (integerp n)
		  (= 0 n)
		  )
	     (equal (/ (- (eval-polynomial-expt-aux poly x n)
			  (eval-polynomial-expt-aux poly x1 n))
		       (- x x1))
		    (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
			  (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
		       (- x x1))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-2))
	     :in-theory (disable abs eval-polynomial-expt-aux real-polynomial-p)))))

 (local
  (defthmd lemma-7
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (integerp n)
		  (= 0 n)
		  )
	     (equal (eval-polynomial-expt-aux
		     (derivative-polynomial-aux poly n) x n)
		    (eval-polynomial-expt-aux
		     (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))
    :hints (("Goal" :do-not-induct t
	     :in-theory (disable abs
				 eval-polynomial-expt-aux
				 real-polynomial-p)))))

 (local
  (defthmd lemma-8
    (implies (and (realp x)
		  (realp eps)
		  (< 0 eps)
		  (< (abs x) (/ eps 2)))
	     (< (abs x) eps))))

 (local
  (defthm lemma-9
    (acl2-numberp (abs (+ x y)))))

 (local
  (defthmd lemma-10
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (integerp n)
		  (= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (< (abs (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
				   (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
				(- x x1))
			     (eval-polynomial-expt-aux
			      (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))
		     (/ eps 2))
		  )
	     (< (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
			      (eval-polynomial-expt-aux poly x1 n))
			   (- x x1))
			(eval-polynomial-expt-aux
			 (derivative-polynomial-aux poly n) x n)))
		eps))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-6 (n 0))
		   (:instance lemma-7)
		   (:instance (:theorem (implies (and (equal (/ (+ b1 b2) d)
							     (/ (+ c1 c2) d))
						      (not (equal d 0))
						      (acl2-numberp d)
						      (acl2-numberp b1)
						      (acl2-numberp b2)
						      (acl2-numberp c1)
						      (acl2-numberp c2)
						      )
						 (hide (equal (+ a (/ b1 d) (/ b2 d))
							      (+ a (/ c1 d) (/ c2 d))))))
			      (a (- (EVAL-POLYNOMIAL-EXPT-AUX (DERIVATIVE-POLYNOMIAL-AUX POLY 0)
							      X 0)))
			      (b1 (EVAL-POLYNOMIAL-EXPT-AUX POLY X 0))
			      (b2 (- (EVAL-POLYNOMIAL-EXPT-AUX POLY X1 0)))
			      (c1 (EVAL-POLYNOMIAL-EXPT-AUX (CDR POLY)
							    X 1))
			      (c2 (- (EVAL-POLYNOMIAL-EXPT-AUX (CDR POLY)
							       X1 1)))
			      (d (+ X (- X1)))))
	     :in-theory (disable abs
				 eval-polynomial-expt-aux
				 real-polynomial-p
				 derivative-polynomial-aux))
	    ("Subgoal 2.1"
	     :in-theory (enable hide))
	    ("Subgoal 1"
	     :expand ((HIDE (EQUAL (+ A (* B1 (/ D)) (* B2 (/ D)))
				   (+ A (* C1 (/ D)) (* C2 (/ D))))))
	     :in-theory (enable hide))
	    )))

 (local
  (defthmd lemma-11
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (integerp n)
		  (< 0 n)
		  (equal (car poly) 0)
		  )
	     (equal (/ (- (eval-polynomial-expt-aux poly x n)
			  (eval-polynomial-expt-aux poly x1 n))
		       (- x x1))
		    (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
			  (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
		       (- x x1))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-2))
	     :in-theory (disable abs eval-polynomial-expt-aux real-polynomial-p)))))

 (local
  (defthmd lemma-12
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (integerp n)
		  (< 0 n)
		  (equal (car poly) 0)
		  )
	     (equal (eval-polynomial-expt-aux
		     (derivative-polynomial-aux poly n) x (1- n))
		    (eval-polynomial-expt-aux
		     (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))
    :hints (("Goal" :do-not-induct t
	     :in-theory (disable abs)))))

 (local
  (defthmd lemma-13
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (integerp n)
		  (< 0 n)
		  (realp eps)
		  (< 0 eps)
		  (equal (car poly) 0)
		  (< (abs (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
				   (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
				(- x x1))
			     (eval-polynomial-expt-aux
			      (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))
		     (/ eps 2))
		  )
	     (< (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
			      (eval-polynomial-expt-aux poly x1 n))
			   (- x x1))
			(eval-polynomial-expt-aux
			 (derivative-polynomial-aux poly n) x (1- n))))
		eps))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-2)
		   (:instance lemma-12)
		   (:instance (:theorem (implies (and (equal (/ (+ b1 b2) d)
							     (/ (+ c1 c2) d))
						      (not (equal d 0))
						      (acl2-numberp d)
						      (acl2-numberp b1)
						      (acl2-numberp b2)
						      (acl2-numberp c1)
						      (acl2-numberp c2)
						      )
						 (hide (equal (+ a (/ b1 d) (/ b2 d))
							      (+ a (/ c1 d) (/ c2 d))))))
			      (a (- (EVAL-POLYNOMIAL-EXPT-AUX (DERIVATIVE-POLYNOMIAL-AUX POLY N)
							      X (+ -1 N))))
			      (b1 (EVAL-POLYNOMIAL-EXPT-AUX POLY X N))
			      (b2 (- (EVAL-POLYNOMIAL-EXPT-AUX POLY X1 N)))
			      (c1 (EVAL-POLYNOMIAL-EXPT-AUX (CDR POLY)
							    X (+ 1 N)))
			      (c2 (- (EVAL-POLYNOMIAL-EXPT-AUX (CDR POLY)
							       X1 (+ 1 N))))
			      (d (+ X (- X1)))))
	     :in-theory (disable abs
				 eval-polynomial-expt-aux
				 real-polynomial-p
				 derivative-polynomial-aux))
	    ("Subgoal 2.1"
	     :in-theory (enable hide))
	    ("Subgoal 1"
	     :expand ((HIDE (EQUAL (+ A (* B1 (/ D)) (* B2 (/ D)))
				   (+ A (* C1 (/ D)) (* C2 (/ D))))))
	     :in-theory (enable hide))
	    )))

 (local
  (defthmd lemma-14
    (implies (and (realp x)
		  (realp y)
		  (realp eps)
		  (< 0 eps)
		  (< (abs x) (/ eps 2))
		  (< (abs y) (/ eps 2)))
	     (< (abs (+ x y)) eps))))

 (local
  (defthm lemma-15
    (implies (realp x)
	     (realp (expt x n)))))

 (local
  (defthm lemma-16
    (implies (and (real-polynomial-p poly)
		  (consp poly))
	     (realp (car poly)))))

 (local
  (defthmd lemma-17
    (implies (and (realp x)
		  (realp y))
	     (<= (abs (+ x y))
		 (+ (abs x) (abs y))))))

 (local
  (defthmd lemma-18
    (implies (and (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (natp n)
		  (< 0 n)
		  (consp poly))
	     (equal (- (/ (- (eval-polynomial-expt-aux poly x n)
			     (eval-polynomial-expt-aux poly x1 n))
			  (- x x1))
		       (eval-polynomial-expt-aux
			(derivative-polynomial-aux poly n) x (1- n)))
		    (+ (- (/ (* (car poly)
				(- (expt x n)
				   (expt x1 n)))
			     (- x x1))
			  (* n (car poly) (expt x (1- n))))
		       (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
				(eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
			     (- x x1))
			  (eval-polynomial-expt-aux
			   (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))))
    :hints (("Goal"
	     :do-not-induct t
	     :in-theory (enable lemma-2)))
    ))

 (local
  (defthmd lemma-19
    (implies (and (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (natp n)
		  (< 0 n)
		  (consp poly))
	     (equal (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
				  (eval-polynomial-expt-aux poly x1 n))
			       (- x x1))
			    (eval-polynomial-expt-aux
			     (derivative-polynomial-aux poly n) x (1- n))))
		    (abs (+ (- (/ (* (car poly)
				     (- (expt x n)
					(expt x1 n)))
				  (- x x1))
			       (* n (car poly) (expt x (1- n))))
			    (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
				     (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
				  (- x x1))
			       (eval-polynomial-expt-aux
				(derivative-polynomial-aux (cdr poly) (1+ n)) x n))))))
    :hints (("Goal"
	     :do-not-induct t
	     :use ((:instance lemma-18))
	     :in-theory nil))))

 (local
  (defthmd lemma-20
    (implies (and (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  ;(not (equal x x1))
		  (natp n)
		  (< 0 n)
		  (consp poly))
	     (<= (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
			       (eval-polynomial-expt-aux poly x1 n))
			    (- x x1))
			 (eval-polynomial-expt-aux
			  (derivative-polynomial-aux poly n) x (1- n))))
		 (+ (abs (- (/ (* (car poly)
				  (- (expt x n)
				     (expt x1 n)))
			       (- x x1))
			    (* n (car poly) (expt x (1- n)))))
		    (abs (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
				  (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
			       (- x x1))
			    (eval-polynomial-expt-aux
			     (derivative-polynomial-aux (cdr poly) (1+ n)) x n))))))
    :hints (("Goal"
	     :do-not-induct t
	     :use ((:instance lemma-19)
		   (:instance lemma-17
			      (x (- (/ (* (car poly)
					  (- (expt x n)
					     (expt x1 n)))
				       (- x x1))
				    (* n (car poly) (expt x (1- n)))))
			      (y (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
					  (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
				       (- x x1))
				    (eval-polynomial-expt-aux
				     (derivative-polynomial-aux (cdr poly) (1+ n)) x n))))
		   )
	     :in-theory (disable abs eval-polynomial-expt-aux derivative-polynomial-aux)))))


 (local
  (defthmd lemma-21
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (integerp n)
		  (< 0 n)
		  (realp eps)
		  (< 0 eps)
		  (< (abs (- (/ (* (car poly)
				   (- (expt x n)
				      (expt x1 n)))
				(- x x1))
			     (* n (car poly) (expt x (1- n)))))
		     (/ eps 2))
		  (< (abs (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
				   (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
				(- x x1))
			     (eval-polynomial-expt-aux
			      (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))
		     (/ eps 2))
		  )
	     (< (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
			      (eval-polynomial-expt-aux poly x1 n))
			   (- x x1))
			(eval-polynomial-expt-aux
			 (derivative-polynomial-aux poly n) x (1- n))))
		eps))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-20))
	     :in-theory (disable abs
				 derivative-polynomial-aux
				 eval-polynomial-expt-aux)))
    ))

 (local
  (defthmd lemma-22
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (< (abs (- (/ (* (car poly)
				   (- (expt x n)
				      (expt x1 n)))
				(- x x1))
			     (* n (car poly) (expt x (1- n)))))
		     (/ eps 2))
		  (< (abs (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
				   (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
				(- x x1))
			     (eval-polynomial-expt-aux
			      (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))
		     (/ eps 2))
		  )
	     (< (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
			      (eval-polynomial-expt-aux poly x1 n))
			   (- x x1))
			(eval-polynomial-expt-aux
			 (derivative-polynomial-aux poly n)
			 x
			 (if (zp n) n (1- n))
			 )))
		eps))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-10)
		   (:instance lemma-21))
	     :in-theory (disable abs
				 derivative-polynomial-aux
				 eval-polynomial-expt-aux))
	    )
    ))

 (local
  (defthmd lemma-23
    (implies (and (realp x)
		  (realp y)
		  (realp z)
		  (< (abs x) y)
		  (not (equal z 0)))
	     (< (abs (* z x)) (* (abs z) y)))))


 (local
  (defthm lemma-24
    (implies (and (realp x)
		  (not (equal x 0)))
	     (realp (/ (abs x))))))

 (local
  (defthm lemma-25
    (implies (and (realp x)
		  (not (equal x 0))
		  (realp eps)
		  (< 0 eps))
	     (< 0 (* eps 1/2 (/ (abs x)))))))

 (local
  (defthm lemma-26
    (implies (and (real-polynomial-p poly)
		  (consp poly)
		  (not (equal (car poly) 0))
		  (realp eps)
		  (< 0 eps))
	     (< 0 (* EPS 1/2 (/ (ABS (CAR POLY))))))
    :rule-classes (:rewrite :linear)))

 (local
  (defthm lemma-27
    (equal (INSIDE-INTERVAL-P X '(NIL))
	   (realp x))
    :hints (("Goal"
	     :expand ((INSIDE-INTERVAL-P X '(NIL)))))))

 (local
  (defthmd lemma-28
    (implies (and (realp x)
		  (realp y)
		  (realp z)
		  (not (equal z 0)))
	     (equal (< (abs x) y)
		    (< (abs (* z x)) (* (abs z) y))))))


 (local
  (defthmd lemma-29
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (not (equal x x1))
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (realp delta)
		  (< 0 delta)
		  (or (equal (car poly) 0)
		      (< delta (exists-delta-for-x-and-eps-so-deriv-expt-works-witness
				x n (/ eps (* 2 (abs (car poly)))))))
		  (< (abs (- x x1)) delta)
		  )
	     (< (abs (- (/ (* (car poly)
			      (- (expt x n)
				 (expt x1 n)))
			   (- x x1))
			(* n (car poly) (expt x (1- n)))))
		(/ eps 2)))
    :hints (("Goal"
	     :do-not-induct t
	     :cases ((equal (car poly) 0))
	     :use ((:instance expt-differentiable-using-hyperreal-criterion
			      (x x)
			      (n n)
			      (eps (/ eps (* 2 (abs (car poly)))))))
	     :in-theory (disable abs)
	     )
	    ("Subgoal 2"
	     :use ((:instance lemma-26)
		   (:instance lemma-28
			      (x (+ (- (* N (EXPT X (+ -1 N))))
				    (* (EXPT X N) (/ (+ X (- X1))))
				    (- (* (EXPT X1 N) (/ (+ X (- X1)))))))
			      (y (* 1/2 eps (/ (abs (car poly)))))
			      (z (CAR POLY)))
		   (:instance forall-x-eps-delta-in-range-deriv-expt-works-necc
			      (x x)
			      (n n)
			      (eps (* 1/2 EPS (/ (ABS (CAR POLY)))))
			      (delta (EXISTS-DELTA-FOR-X-AND-EPS-SO-DERIV-EXPT-WORKS-WITNESS
				      X N (* 1/2 EPS (/ (ABS (CAR POLY)))))))
		   )
	     :expand ((EXISTS-DELTA-FOR-X-AND-EPS-SO-DERIV-EXPT-WORKS
		       X N (* 1/2 EPS (/ (CAR POLY)))))
	     :in-theory (e/d (EXISTS-DELTA-FOR-X-AND-EPS-SO-DERIV-EXPT-WORKS)
			     (abs
			      FORALL-X-EPS-DELTA-IN-RANGE-DERIV-EXPT-WORKS
			      forall-x-eps-delta-in-range-deriv-expt-works-necc
			      lemma-25
			      lemma-26))
	     )
	    )))

 (local
  (defthmd lemma-30
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (not (equal x x1))
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (realp delta)
		  (< 0 delta)
		  (or (equal (car poly) 0)
		      (< delta (exists-delta-for-x-and-eps-so-deriv-expt-works-witness
				x n (/ eps (* 2 (abs (car poly)))))))
		  (< (abs (- x x1)) delta)
		  (< (abs (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
				   (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
				(- x x1))
			     (eval-polynomial-expt-aux
			      (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))
		     (/ eps 2))
		  )
	     (< (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
			      (eval-polynomial-expt-aux poly x1 n))
			   (- x x1))
			(eval-polynomial-expt-aux
			 (derivative-polynomial-aux poly n)
			 x
			 (if (zp n) n (1- n))
			 )))
		eps))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-22)
		   (:instance lemma-29))
	     :in-theory (disable abs
				 derivative-polynomial-aux
				 eval-polynomial-expt-aux))
	    )
    ))


 (local
  (defthmd lemma-31
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (not (equal x x1))
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (realp delta)
		  (< 0 delta)
		  (< (abs (- x x1)) delta)
		  (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works (cdr poly) x (1+ n) (/ eps 2) delta)
		  )
	     (< (abs (- (/ (- (eval-polynomial-expt-aux (cdr poly) x (1+ n))
			      (eval-polynomial-expt-aux (cdr poly) x1 (1+ n)))
			   (- x x1))
			(eval-polynomial-expt-aux
			 (derivative-polynomial-aux (cdr poly) (1+ n)) x n)))
		(/ eps 2)))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance forall-x-eps-delta-in-range-deriv-poly-expt-aux-works-necc
			      (poly (cdr poly))
			      (x x)
			      (n (1+ n))
			      (eps (/ eps 2))
			      (delta delta)))
	     :in-theory (disable abs
				 derivative-polynomial-aux
				 eval-polynomial-expt-aux
				 forall-x-eps-delta-in-range-deriv-poly-expt-aux-works-necc))
	    )
    ))

 (local
  (defthmd lemma-32
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (realp x1)
		  (not (equal x x1))
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (realp delta)
		  (< 0 delta)
		  (or (equal (car poly) 0)
		      (< delta (exists-delta-for-x-and-eps-so-deriv-expt-works-witness
				x n (/ eps (* 2 (abs (car poly)))))))
		  (< (abs (- x x1)) delta)
		  (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works (cdr poly) x (1+ n) (/ eps 2) delta)
		  )
	     (< (abs (- (/ (- (eval-polynomial-expt-aux poly x n)
			      (eval-polynomial-expt-aux poly x1 n))
			   (- x x1))
			(eval-polynomial-expt-aux
			 (derivative-polynomial-aux poly n)
			 x
			 (if (zp n) n (1- n))
			 )))
		eps))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-30)
		   (:instance lemma-31))
	     :in-theory (disable abs
				 derivative-polynomial-aux
				 eval-polynomial-expt-aux))
	    )
    ))

 (local
  (defthmd lemma-33
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (realp delta)
		  (< 0 delta)
		  (or (equal (car poly) 0)
		      (< delta (exists-delta-for-x-and-eps-so-deriv-expt-works-witness
				x n (/ eps (* 2 (abs (car poly)))))))
		  (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works (cdr poly) x (1+ n) (/ eps 2) delta)
		  )
	     (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works poly x n eps delta))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-32
			      (x1 (FORALL-X-EPS-DELTA-IN-RANGE-DERIV-POLY-EXPT-AUX-WORKS-WITNESS
				   POLY X N EPS DELTA))
			      ))
	     :in-theory (disable abs
				 derivative-polynomial-aux
				 eval-polynomial-expt-aux))
	    )
    ))

 (local
  (defthmd lemma-34
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (realp delta)
		  (< 0 delta)
		  (or (equal (car poly) 0)
		      (< delta (exists-delta-for-x-and-eps-so-deriv-expt-works-witness
				x n (/ eps (* 2 (abs (car poly)))))))
		  (< delta (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-witness
			    (cdr poly) x (1+ n) (/ eps 2)))
		  (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works (cdr poly) x (1+ n) (/ eps 2))
		  )
	     (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works poly x n eps delta))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-33)
		   (:instance lemma-4
			      (poly (cdr poly))
			      (x x)
			      (n (1+ n))
			      (eps (/ eps 2))
			      (delta (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-witness
				      (cdr poly) x (1+ n) (/ eps 2)))
			      (gamma delta))
		   )
	     :in-theory (disable abs
				 derivative-polynomial-aux
				 eval-polynomial-expt-aux
				 forall-x-eps-delta-in-range-deriv-poly-expt-aux-works))
	    )
    ))



 (local
  (defthm lemma-35
    (implies (and (real-polynomial-p poly)
		  (consp poly))
	     (realp (abs (car poly))))))

 (local
  (defun fix-delta (poly x n eps)
    (/ (min (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-witness
	     (cdr poly) x (1+ n) (/ eps 2))
	    (if (equal (realfix (abs (car poly))) 0)
		1
	      (exists-delta-for-x-and-eps-so-deriv-expt-works-witness
	       x n (/ eps (* 2 (abs (car poly)))))))
       2)))

 (local
  (defthmd fix-delta-works
    (implies (and (realp x)
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works (cdr poly) x (1+ n) (/ eps 2)))
	     (and (realp (fix-delta poly x n eps))
		  (< 0 (fix-delta poly x n eps))
		  (< (fix-delta poly x n eps)
		     (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-witness
		      (cdr poly) x (1+ n) (/ eps 2)))
		  (< (fix-delta poly x n eps)
		     (if (equal (realfix (abs (car poly))) 0)
			 1
		       (exists-delta-for-x-and-eps-so-deriv-expt-works-witness x n (/ eps (* 2 (abs (car poly)))))))))
    :hints (("Goal"
	     :use ((:instance expt-differentiable-using-hyperreal-criterion
			      (x x)
			      (n n)
			      (eps (/ eps (* 2 (abs (car poly)))))))))
    ))

 (local
  (defthm lemma-36
    (implies (realp x)
	     (equal (equal (abs x) 0)
		    (equal x 0)))))

 (local
  (defthmd lemma-37
    (implies (and (consp poly)
		  (real-polynomial-p poly)
		  (realp x)
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps)
		  (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works (cdr poly) x (1+ n) (/ eps 2)))
	     (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works poly x n eps))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-34
			      (delta (fix-delta poly x n eps)))
		   (:instance fix-delta-works)
		   (:instance exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-suff
			      (delta (fix-delta poly x n eps))))
	     :in-theory (disable abs
				 derivative-polynomial-aux
				 eval-polynomial-expt-aux
				 fix-delta
				 exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works
				 forall-x-eps-delta-in-range-deriv-poly-expt-aux-works)))))

 (local
  (defthm poly-expt-differentiable-using-hyperreal-criterion-lemma
    (implies (and (real-polynomial-p poly)
		  (realp x)
		  (integerp n)
		  (<= 0 n)
		  (realp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works poly x n eps))
    :hints (("Goal"
	     :induct (induction-hint poly n eps)
	     :in-theory (disable exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works))
	    ("Subgoal *1/2"
	     :use ((:instance lemma-3)))
	    ("Subgoal *1/1"
	     :use ((:instance lemma-37))))))

 (local
  (defthm lemma-38
    (implies (not (and (real-polynomial-p poly)
			(realp x)
			(integerp n)
			(<= 0 n)))
	     (equal (eval-polynomial-expt-aux poly x n) 0))
    ))

 (local
  (defthm lemma-39
    (implies (not (and (real-polynomial-p poly)
			(integerp n)
			(<= 0 n)))
	     (equal (derivative-polynomial-aux poly n) nil))
    ))

 (local
  (defthm lemma-40
    (implies (and (not (and (real-polynomial-p poly)
			    (realp x)
			    (integerp n)
			    (<= 0 n)))
		  (realp eps)
		  (< 0 eps))
	     (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works poly x n eps delta))
    ))

 (local
  (defthm lemma-41
    (implies (and (not (and (real-polynomial-p poly)
			    (realp x)
			    (integerp n)
			    (<= 0 n)))
		  (realp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works poly x n eps))
    :hints (("Goal"
	     :use ((:instance exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-suff
			      (delta 1)))))))

 (defthm poly-expt-differentiable-using-hyperreal-criterion
   (implies (and (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works poly x n eps))
   :hints (("Goal"
	    :use ((:instance lemma-41)
		  (:instance poly-expt-differentiable-using-hyperreal-criterion-lemma)))))

   )

(defun-sk forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux (poly x0 n eps delta)
     (forall (x)
	     (implies (and (realp x0)
			   (realp x)
			   (realp delta)
			   (< 0 delta)
			   (realp eps)
			   (< 0 eps)
			   (< (abs (- x x0)) delta)
			   (not (equal x x0)))
		      (< (abs (- (eval-polynomial-expt-aux poly x n)
				 (eval-polynomial-expt-aux poly x0 n)))
			 eps)))
     :rewrite :direct)

(defun-sk exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux (poly x0 n eps)
     (exists (delta)
	     (implies (and (realp x0)
			   (realp eps)
			   (< 0 eps))
		      (and (realp delta)
			   (< 0 delta)
			   (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux poly x0 n eps delta)))))

(local
 (defthm inside-interval-nil-nil
   (equal (inside-interval-p x (interval nil nil))
	  (realp x))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthm real-eval-polynomial-expt
   (realp (eval-polynomial-expt-aux poly x n))))

(defthmd poly-expt-and-prime-are-continuous
   (implies (and ;(real-polynomial-p poly)
		 (realp x0)
		 ;(integerp n)
		 ;(<= 0 n)
		 (realp epsilon)
		 (< 0 epsilon))
	    (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux poly x0 n epsilon))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance
		  (:functional-instance rdfn-classic-is-continuous-hyperreals
					(rdfn-classical
					 (lambda (x)
					   (eval-polynomial-expt-aux poly x n)))
					(derivative-rdfn-classical
					 (lambda (x)
					   (eval-polynomial-expt-aux (derivative-polynomial-aux poly n) x (if (zp n) n (1- n)))))
					(rdfn-classical-domain
					 (lambda () (interval nil nil)))
					(exists-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn
					 (lambda (x eps)
					   (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux poly x n eps)))
					(exists-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn-witness
					 (lambda (x eps)
					   (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux-witness poly x n eps)))
					(forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn
					 (lambda (x eps delta)
					   (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux poly x n eps delta)))
					(forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn-witness
					 (lambda (x eps delta)
					   (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux-witness poly x n eps delta)))
					(forall-x-eps-delta-in-range-deriv-classical-works
					 (lambda (x eps delta)
					   (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works poly x n eps delta)))
					(forall-x-eps-delta-in-range-deriv-classical-works-witness
					 (lambda (x eps delta)
					   (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works-witness poly x n eps delta)))
					(exists-delta-for-x-and-eps-so-deriv-classical-works
					 (lambda (x eps)
					   (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works poly x n eps)))
					(exists-delta-for-x-and-eps-so-deriv-classical-works-witness
					 (lambda (x eps)
					   (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-witness poly x n eps)))
					)
		  (eps epsilon))))
	  ("Subgoal 10"
	   :use ((:instance exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux-suff))
	   :in-theory (disable FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-POLY-EXPT-AUX))
	  ("Subgoal 8"
	   :use ((:instance FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-POLY-EXPT-AUX-necc))
	   :in-theory (disable FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-POLY-EXPT-AUX-necc
			       FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-POLY-EXPT-AUX))
	  ("Subgoal 4"
	   :use ((:instance EXISTS-DELTA-FOR-X-AND-EPS-SO-DERIV-POLY-EXPT-AUX-WORKS-suff))
	   :in-theory (disable FORALL-X-EPS-DELTA-IN-RANGE-DERIV-POLY-EXPT-AUX-WORKS))
	  ("Subgoal 2"
	   :use ((:instance FORALL-X-EPS-DELTA-IN-RANGE-DERIV-POLY-EXPT-AUX-WORKS-necc)))
	  )
  )

(defun map-poly-expt-classical (poly p n)
  (if (consp p)
      (cons (eval-polynomial-expt-aux poly (car p) n)
	    (map-poly-expt-classical poly (cdr p) n))
    nil))

(defun riemann-poly-expt-classical (poly p n)
  (dotprod (deltas p)
	   (map-poly-expt-classical poly (cdr p) n)))

(defthmd riemann-poly-expt-classical-alternative
  (equal (riemann-poly-expt-classical poly p n)
	 (if (and (consp p) (consp (cdr p)))
	     (+ (riemann-poly-expt-classical poly (cdr p) n)
		(* (- (cadr p) (car p))
		   (eval-polynomial-expt-aux poly (cadr p) n)))
	   0))
  :rule-classes :definition)

(defthm realp-riemann-poly-expt-classical
  (implies (partitionp p)
	   (realp (riemann-poly-expt-classical poly p n))))

(defun-sk is-maximum-point-of-poly-expt-classical (poly a b n max)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (eval-polynomial-expt-aux poly x n)
		       (eval-polynomial-expt-aux poly max n)))))

(defun-sk poly-expt-classical-achieves-maximum-point (poly a b n)
  (exists (max)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp max)
			(<= a max)
			(<= max b)
			(is-maximum-point-of-poly-expt-classical poly a b n max)))))

(defthm maximum-point-theorem-poly-expt-classical-sk
  (implies (and (realp a)
		(realp b)
		(< a b)
					;(real-polynomial-p poly)
					;(natp n)
		)
	   (poly-expt-classical-achieves-maximum-point poly a b n))
  :hints (("Goal" :do-not-induct t
	   :use ((:functional-instance maximum-point-theorem-hyper-sk
				       (rcfn-hyper
					(lambda (x)
					  (eval-polynomial-expt-aux poly x n)))
				       (rcfn-hyper-domain
					(lambda () (interval nil nil)))
				       (is-maximum-point-of-rcfn-hyper
					(lambda (a b max)
					  (is-maximum-point-of-poly-expt-classical poly a b n max)))
				       (is-maximum-point-of-rcfn-hyper-witness
					(lambda (a b max)
					  (is-maximum-point-of-poly-expt-classical-witness poly a b n max)))
				       (rcfn-hyper-achieves-maximum-point
					(lambda (a b)
					  (poly-expt-classical-achieves-maximum-point poly a b n)))
				       (rcfn-hyper-achieves-maximum-point-witness
					(lambda (a b)
					  (poly-expt-classical-achieves-maximum-point-witness poly a b n)))
				       (exists-delta-for-x0-to-make-x-within-epsilon-of-hyper-f
					(lambda (x eps)
					  (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux poly x n eps)))
				       (exists-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-witness
					(lambda (x eps)
					  (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux-witness poly x n eps)))
				       (forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f
					(lambda (x eps delta)
					  (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux poly x n eps delta)))
				       (forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f-witness
					(lambda (x eps delta)
					  (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux-witness poly x n eps delta)))
				       ))
	   )
	  ("Subgoal 10"
	   :use ((:instance poly-expt-classical-achieves-maximum-point-suff))
	   )
	  ("Subgoal 8"
	   :use ((:instance is-maximum-point-of-poly-expt-classical-necc)))
	  ("Subgoal 6"
	   :use ((:instance poly-expt-and-prime-are-continuous
			    (epsilon eps))))
	  ("Subgoal 4"
	   :use ((:instance exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux-suff)))
	  ("Subgoal 2"
	   :use ((:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux-necc)))
	  ("Subgoal 1"
	   :use ((:instance FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-POLY-EXPT-AUX-necc)))
	  ))

(defun-sk is-minimum-point-of-poly-expt-classical (poly a b n min)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (eval-polynomial-expt-aux poly min n)
		       (eval-polynomial-expt-aux poly x n)))))

(defun-sk poly-expt-classical-achieves-minimum-point (poly a b n)
  (exists (min)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp min)
			(<= a min)
			(<= min b)
			(is-minimum-point-of-poly-expt-classical poly a b n min)))))

(defthm minimum-point-theorem-poly-expt-classical-sk
  (implies (and (realp a)
		(realp b)
		(< a b)
					;(real-polynomial-p poly)
					;(natp n)
		)
	   (poly-expt-classical-achieves-minimum-point poly a b n))
  :hints (("Goal" :do-not-induct t
	   :use ((:functional-instance minimum-point-theorem-hyper-sk
				       (rcfn-hyper
					(lambda (x)
					  (eval-polynomial-expt-aux poly x n)))
				       (rcfn-hyper-domain
					(lambda () (interval nil nil)))
				       (is-minimum-point-of-rcfn-hyper
					(lambda (a b min)
					  (is-minimum-point-of-poly-expt-classical poly a b n min)))
				       (is-minimum-point-of-rcfn-hyper-witness
					(lambda (a b min)
					  (is-minimum-point-of-poly-expt-classical-witness poly a b n min)))
				       (rcfn-hyper-achieves-minimum-point
					(lambda (a b)
					  (poly-expt-classical-achieves-minimum-point poly a b n)))
				       (rcfn-hyper-achieves-minimum-point-witness
					(lambda (a b)
					  (poly-expt-classical-achieves-minimum-point-witness poly a b n)))
				       (exists-delta-for-x0-to-make-x-within-epsilon-of-hyper-f
					(lambda (x eps)
					  (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux poly x n eps)))
				       (exists-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-witness
					(lambda (x eps)
					  (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux-witness poly x n eps)))
				       (forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f
					(lambda (x eps delta)
					  (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux poly x n eps delta)))
				       (forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f-witness
					(lambda (x eps delta)
					  (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux-witness poly x n eps delta)))
				       ))
	   )
	  ("Subgoal 4"
	   :use ((:instance poly-expt-classical-achieves-minimum-point-suff))
	   )
	  ("Subgoal 2"
	   :use ((:instance is-minimum-point-of-poly-expt-classical-necc)))
	  ))



(defun map-m-poly-expt-classical (m p)
  (if (consp p)
      (cons m
	    (map-m-poly-expt-classical m (cdr p)))
    nil))

(defun riemann-m-poly-expt-classical (m p)
  (dotprod (deltas p)
	   (map-m-poly-expt-classical m (cdr p))))

(defthmd riemann-m-poly-expt-classical-alternative
  (equal (riemann-m-poly-expt-classical m p)
	 (if (and (consp p) (consp (cdr p)))
	     (+ (riemann-m-poly-expt-classical m (cdr p))
		(* (- (cadr p) (car p))
		   m))
	   0))
  :rule-classes :definition)

(defthmd riemann-m-poly-expt-classical-better-alternative
  (implies (and (partitionp p)
		(realp m))
	   (equal (riemann-m-poly-expt-classical m p)
		  (* m (- (car (last p))
			  (car p)))
		  ))
  :rule-classes :definition)

(local
 (defthm-std standard-riemann-m-poly-expt-classical-better-alternative-lemma
   (implies (and (standardp m)
		 (standardp a)
		 (standardp b))
	    (standardp (* m (- b a))))))

(defthmd standard-riemann-m-poly-expt-classical-better-alternative
   (implies (and (standardp m)
		 (standardp a)
		 (standardp b)
		 (realp m)
		 (realp a)
		 (realp b)
		 (< A B))
	    (standardp (riemann-m-poly-expt-classical m (make-small-partition a b))))
   :hints (("Goal"
	    :use ((:instance riemann-m-poly-expt-classical-better-alternative
			     (p (make-small-partition a b)))
		  (:instance standard-riemann-m-poly-expt-classical-better-alternative-lemma)
		  )
	    :in-theory (disable RIEMANN-M-POLY-EXPT-CLASSICAL
				standardp-times))))

(local
 (defthmd max-is-maximum-open
   (implies (and (realp a)
		 (realp b)
		 (realp x)
		 (< a x)
		 (<= x b)
		 )
	    (<= (eval-polynomial-expt-aux poly x n)
		(eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance is-maximum-point-of-poly-expt-classical-necc
			     (max (poly-expt-classical-achieves-maximum-point-witness poly a b n))
			     )
		  (:instance maximum-point-theorem-poly-expt-classical-sk))
	    :in-theory (disable eval-polynomial-expt-aux
				IS-MAXIMUM-POINT-OF-POLY-EXPT-CLASSICAL
				MAXIMUM-POINT-THEOREM-POLY-EXPT-CLASSICAL-SK)))))

(local
 (defthmd min-is-minimum-open
   (implies (and (realp a)
		 (realp b)
		 (realp x)
		 (< a x)
		 (<= x b)
                 ;(natp n)
		 )
	    (<= (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
		(eval-polynomial-expt-aux poly x n)))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance is-minimum-point-of-poly-expt-classical-necc
			     (min (poly-expt-classical-achieves-minimum-point-witness poly a b n))
			     )
		  (:instance minimum-point-theorem-poly-expt-classical-sk))
	    :in-theory (disable eval-polynomial-expt-aux
				is-minimum-point-of-poly-expt-classical
				minimum-point-theorem-poly-expt-classical-sk)))))


(local
 (defthm realp-riemann-eval-poly-min-witness
   (implies (and (partitionp p)
		 (realp m))
	    (REALP (RIEMANN-M-POLY-EXPT-CLASSICAL
		    m
		    p)))))

(local
 (defthm car-<-last-partition
   (implies (partitionp p)
	    (<= (car p) (car (last p))))))

(encapsulate
 nil

 (local
  (defthm lemma-1
    (implies (and (partitionp p)
		  (consp (cdr p)))
	     (REALP (+ (CADR P) (- (CAR P)))))))

 (local
  (defthm lemma-2
    (implies (and (partitionp p)
		  (consp (cdr p)))
	     (< 0 (+ (CADR P) (- (CAR P)))))))

 (local
  (defthm lemma-3
    (implies (and (partitionp p)
		  (consp (cdr p)))
	     (equal (last p)
		    (last (cdr p))))))

 (local
  (defthm lemma-4
    (implies (and (partitionp p)
		  (consp (cdr p)))
	     (realp (cadr p)))))

 (local
  (defthm lemma-5
    (implies (and (partitionp p)
		  (consp (cdr p)))
	     (<= (cadr p) (car (last (cdr p)))))))

 (local
  (defthm lemma-6
    (implies (and (partitionp p)
		  (consp (cdr p))
		  (<= a (car p)))
	     (< a (cadr p)))))

 (local
  (defthm lemma-7
    (implies (and (realp a)
		  (realp b)
		  (< a b)
		  (partitionp p)
		  (consp (cdr p))
		  (<= a (car p))
		  (= b (car (last p))))
	     (<=
	      (* (+ (CADR P) (- (CAR P)))
		 (EVAL-POLYNOMIAL-EXPT-AUX
		  POLY
		  (POLY-EXPT-CLASSICAL-ACHIEVES-MINIMUM-POINT-WITNESS POLY A B N)
		  N))
	      (* (+ (CADR P) (- (CAR P)))
		 (EVAL-POLYNOMIAL-EXPT-AUX POLY (CADR P)
					   N))))
    :hints (("Goal"
	     :do-not-induct t
	     :use ((:instance min-is-minimum-open
			      (x (cadr p)))
		   (:instance (:theorem (implies (and (realp x)
						      (realp y)
						      (realp z)
						      (< 0 z)
						      (<= x y))
						 (<= (* z x) (* z y))))
			      (x (EVAL-POLYNOMIAL-EXPT-AUX POLY
							   (POLY-EXPT-CLASSICAL-ACHIEVES-MINIMUM-POINT-WITNESS
							    POLY A (CAR (LAST (CDR P)))
							    N)
							   N))
			      (y (EVAL-POLYNOMIAL-EXPT-AUX POLY (CADR P) N))
			      (z (- (cadr p) (car p)))))
	     )
	    ("Subgoal 2"
	     :use ((:instance CAR-<-LAST-PARTITION))
	     :in-theory '((:FORWARD-CHAINING PARTITIONP-FORWARD-TO-REALP-CAR)
			  (:REWRITE REAL-EVAL-POLYNOMIAL-EXPT)
			  =
			  lemma-1
			  lemma-2
			  lemma-3
			  lemma-4
			  lemma-5
			  lemma-6))
	    )
    ))

 (local
  (defthm lemma-8
    (implies (and (realp a)
		  (realp b)
		  (< a b)
		  (partitionp p)
		  (consp (cdr p))
		  (<= a (car p))
		  (= b (car (last p))))
	     (<=
	      (* (+ (CADR P) (- (CAR P)))
		 (EVAL-POLYNOMIAL-EXPT-AUX POLY (CADR P)
					   N))
	      (* (+ (CADR P) (- (CAR P)))
		 (EVAL-POLYNOMIAL-EXPT-AUX
		  POLY
		  (POLY-EXPT-CLASSICAL-ACHIEVES-MAXIMUM-POINT-WITNESS POLY A B N)
		  N))))
    :hints (("Goal"
	     :do-not-induct t
	     :use ((:instance max-is-maximum-open
			      (x (cadr p)))
		   (:instance (:theorem (implies (and (realp x)
						      (realp y)
						      (realp z)
						      (< 0 z)
						      (<= x y))
						 (<= (* z x) (* z y))))
			      (x (EVAL-POLYNOMIAL-EXPT-AUX POLY (CADR P) N))
			      (y (EVAL-POLYNOMIAL-EXPT-AUX POLY
							   (POLY-EXPT-CLASSICAL-ACHIEVES-MAXIMUM-POINT-WITNESS
							    POLY A (CAR (LAST (CDR P)))
							    N)
							   N))
			      (z (- (cadr p) (car p)))))
	     )
	    ("Subgoal 2"
	     :use ((:instance CAR-<-LAST-PARTITION))
	     :in-theory '((:FORWARD-CHAINING PARTITIONP-FORWARD-TO-REALP-CAR)
			  (:REWRITE REAL-EVAL-POLYNOMIAL-EXPT)
			  =
			  lemma-1
			  lemma-2
			  lemma-3
			  lemma-4
			  lemma-5
			  lemma-6))
	    )
    ))

 (defthm riemann-poly-expt-classical-bounded-from-above
   (implies (and (realp a)
		 (realp b)
		 (< a b)
		 (partitionp p)
		 (<= a (car p))
		 (= b (car (last p))))
	    (<= (riemann-poly-expt-classical poly p n)
		(riemann-m-poly-expt-classical
		 (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)
		 p)))
   :INSTRUCTIONS
   ((:IN-THEORY
     (E/D
      (RIEMANN-POLY-EXPT-CLASSICAL-ALTERNATIVE
       RIEMANN-M-POLY-EXPT-CLASSICAL-ALTERNATIVE)
      (RIEMANN-POLY-EXPT-CLASSICAL RIEMANN-M-POLY-EXPT-CLASSICAL
                                   MAP-POLY-EXPT-CLASSICAL
                                   MAP-M-POLY-EXPT-CLASSICAL
                                   EVAL-POLYNOMIAL-EXPT-AUX)))
    (:INDUCT (PARTITIONP P))
    :BASH
    :BASH :BASH :BASH (:CHANGE-GOAL NIL T)
    :BASH :PROMOTE (:FORWARDCHAIN 6)
    (:DV 2)
    (:REWRITE RIEMANN-M-POLY-EXPT-CLASSICAL-ALTERNATIVE)
    (:=
     (+
      (RIEMANN-M-POLY-EXPT-CLASSICAL
       (EVAL-POLYNOMIAL-EXPT-AUX
	POLY
	(POLY-EXPT-CLASSICAL-ACHIEVES-MAXIMUM-POINT-WITNESS POLY A B N)
	N)
       (CDR P))
      (* (+ (CADR P) (- (CAR P)))
	 (EVAL-POLYNOMIAL-EXPT-AUX
	  POLY
	  (POLY-EXPT-CLASSICAL-ACHIEVES-MAXIMUM-POINT-WITNESS POLY A B N)
	  N))))
    :UP (:DV 2)
    (:REWRITE RIEMANN-POLY-EXPT-CLASSICAL-ALTERNATIVE)
    (:= (+ (RIEMANN-POLY-EXPT-CLASSICAL POLY (CDR P)
                                        N)
	   (* (+ (CADR P) (- (CAR P)))
	      (EVAL-POLYNOMIAL-EXPT-AUX POLY (CADR P)
					N))))
    :UP :TOP (:USE (:INSTANCE LEMMA-8))
    :BASH)
   )

 (defthm riemann-poly-expt-classical-bounded-from-below
   (implies (and (realp a)
		 (realp b)
		 (< a b)
		 (partitionp p)
		 (<= a (car p))
		 (= b (car (last p))))
	    (<= (riemann-m-poly-expt-classical
		 (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
		 p)
		(riemann-poly-expt-classical poly p n)))
   :INSTRUCTIONS
   ((:IN-THEORY
     (E/D
      (RIEMANN-POLY-EXPT-CLASSICAL-ALTERNATIVE
       RIEMANN-M-POLY-EXPT-CLASSICAL-ALTERNATIVE)
      (RIEMANN-POLY-EXPT-CLASSICAL RIEMANN-M-POLY-EXPT-CLASSICAL
                                   MAP-POLY-EXPT-CLASSICAL
                                   MAP-M-POLY-EXPT-CLASSICAL
                                   EVAL-POLYNOMIAL-EXPT-AUX)))
    (:INDUCT (PARTITIONP P))
    :BASH
    :BASH :BASH :BASH (:CHANGE-GOAL NIL T)
    :BASH :PROMOTE (:FORWARDCHAIN 6)
    (:DV 1)
    (:REWRITE RIEMANN-M-POLY-EXPT-CLASSICAL-ALTERNATIVE)
    (:=
     (+
      (RIEMANN-M-POLY-EXPT-CLASSICAL
       (EVAL-POLYNOMIAL-EXPT-AUX
	POLY
	(POLY-EXPT-CLASSICAL-ACHIEVES-MINIMUM-POINT-WITNESS POLY A B N)
	N)
       (CDR P))
      (* (+ (CADR P) (- (CAR P)))
	 (EVAL-POLYNOMIAL-EXPT-AUX
	  POLY
	  (POLY-EXPT-CLASSICAL-ACHIEVES-MINIMUM-POINT-WITNESS POLY A B N)
	  N))))
    :UP (:DV 1)
    (:REWRITE RIEMANN-POLY-EXPT-CLASSICAL-ALTERNATIVE)
    (:= (+ (RIEMANN-POLY-EXPT-CLASSICAL POLY (CDR P)
                                        N)
	   (* (+ (CADR P) (- (CAR P)))
	      (EVAL-POLYNOMIAL-EXPT-AUX POLY (CADR P)
					N))))
    :TOP (:USE (:INSTANCE LEMMA-7))
    :BASH)
   )
 )

(encapsulate
 nil


 (local
  (defthm-std lemma-1
   (implies (and (standardp a)
		 (standardp b)
		 (standardp poly)
		 (standardp n))
	    (standardp (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)))))

 (defthm standard-upper-bound
   (implies (and (realp a)
		 (realp b)
		 (< a b)
		 (standardp a)
		 (standardp b)
		 (standardp poly)
		 (standardp n))
	    (standardp (riemann-m-poly-expt-classical
			(eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)
			(make-small-partition a b))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance lemma-1)
		  (:instance standard-riemann-m-poly-expt-classical-better-alternative
			     (m (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n))))
	    :in-theory (disable lemma-1 standard-riemann-m-poly-expt-classical-better-alternative)
	    )))

 (local
  (defthm-std lemma-2
   (implies (and (standardp a)
		 (standardp b)
		 (standardp poly)
		 (standardp n))
	    (standardp (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)))))

 (defthm standard-lower-bound
   (implies (and (realp a)
		 (realp b)
		 (< a b)
		 (standardp a)
		 (standardp b)
		 (standardp poly)
		 (standardp n))
	    (standardp (riemann-m-poly-expt-classical
			(eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
			(make-small-partition a b))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance lemma-2)
		  (:instance standard-riemann-m-poly-expt-classical-better-alternative
			     (m (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n))))
	    :in-theory (disable lemma-2 standard-riemann-m-poly-expt-classical-better-alternative)
	    )))

)

(encapsulate
 nil

 (local
  (defthm lemma-1
    (implies (and (realp L)
		  (realp x)
		  (realp U)
		  (<= L x)
		  (<= x U))
	     (<= (abs x) (abs (max (abs L) (abs U)))))))

 (local
  (defthm lemma-2
   (implies (and (realp a)
		 (realp b)
		 (< a b)
		 (partitionp p)
		 (<= a (car p))
		 (= b (car (last p))))
	    (<= (abs (riemann-poly-expt-classical poly p n))
		(abs (max (abs (riemann-m-poly-expt-classical
				(eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)
				p))
			  (abs (riemann-m-poly-expt-classical
				(eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
				p))))))
   :hints (("Goal"
	    :use ((:instance riemann-poly-expt-classical-bounded-from-below)
		  (:instance riemann-poly-expt-classical-bounded-from-above))
	    :in-theory (disable riemann-poly-expt-classical-bounded-from-below
				riemann-poly-expt-classical-bounded-from-above)))
   ))

 (local
  (defthm lemma-3
    (implies (and (realp a)
		  (realp b)
		  (< a b)
		  (standardp a)
		  (standardp b)
		  (standardp poly)
		  (standardp n))
	     (standardp (max (abs (riemann-m-poly-expt-classical
				   (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)
				   (make-small-partition a b)))
			     (abs (riemann-m-poly-expt-classical
				   (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
				   (make-small-partition a b))))))
    :hints (("Goal"
	     :use ((:instance standard-lower-bound)
		   (:instance standard-upper-bound))
	     :in-theory (disable riemann-m-poly-expt-classical
				 eval-polynomial-expt-aux
				 standard-lower-bound
				 standard-upper-bound)
	     ))))

 (local
  (defthm lemma-4
    (implies (and (realp a)
		  (realp b)
		  (< a b)
		  (standardp a)
		  (standardp b)
		  (standardp poly)
		  (standardp n))
	     (realp (max (abs (riemann-m-poly-expt-classical
			       (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)
			       (make-small-partition a b)))
			 (abs (riemann-m-poly-expt-classical
			       (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
			       (make-small-partition a b))))))
    :hints (("Goal"
	     :in-theory (disable riemann-m-poly-expt-classical
				 eval-polynomial-expt-aux)))
    ))

 (local
  (defthm lemma-5
    (implies (and (realp a)
		  (realp b)
		  (< a b)
		  (standardp a)
		  (standardp b)
		  (standardp poly)
		  (standardp n))
	     (i-limited (max (abs (riemann-m-poly-expt-classical
				   (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)
				   (make-small-partition a b)))
			     (abs (riemann-m-poly-expt-classical
				   (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
				   (make-small-partition a b))))))
    :hints (("Goal"
	     :use ((:instance lemma-3)
		   (:instance standards-are-limited
			      (x (max (abs (riemann-m-poly-expt-classical
					    (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)
					    (make-small-partition a b)))
				      (abs (riemann-m-poly-expt-classical
					    (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
					    (make-small-partition a b)))))))
	     :in-theory (disable riemann-m-poly-expt-classical
				 eval-polynomial-expt-aux
				 standard-lower-bound
				 standard-upper-bound)
	     ))))

 (defthm limited-rieman-poly-expt-classical
   (implies (and (realp a)
		 (realp b)
		 (< a b)
		 (standardp a)
		 (standardp b)
		 (standardp poly)
		 (standardp n))
	    (i-limited (riemann-poly-expt-classical poly (make-small-partition a b) n)))
   :hints (("Goal"
	    :use ((:instance large-if->-large
			     (x (riemann-poly-expt-classical poly (make-small-partition a b) n))
			     (y (max (abs (riemann-m-poly-expt-classical
					   (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-maximum-point-witness poly a b n) n)
					   (make-small-partition a b)))
				     (abs (riemann-m-poly-expt-classical
					   (eval-polynomial-expt-aux poly (poly-expt-classical-achieves-minimum-point-witness poly a b n) n)
					   (make-small-partition a b))))))
		  (:instance lemma-2
			     (p (make-small-partition a b)))
		  (:instance lemma-5))
	    :in-theory (disable max
				abs
				riemann-m-poly-expt-classical
				riemann-poly-expt-classical
				eval-polynomial-expt-aux
				lemma-2
				lemma-3
				large-if->-large
				LARGE->-NON-LARGE
				standards-are-limited))))

 (local (in-theory (disable riemann-poly-expt-classical)))

 (defun-std strict-int-poly-expt-classical (poly a b n)
   (if (and (realp a)
	    (realp b)
	    (< a b))
       (standard-part (riemann-poly-expt-classical poly (make-small-partition a b) n))
     0))
 )

(defun int-poly-expt-classical-aux (poly a b n)
  (if (<= a b)
      (strict-int-poly-expt-classical poly a b n)
    (- (strict-int-poly-expt-classical poly b a n))))

(defun real-polynomial-fix (poly)
  (if (consp poly)
      (cons (realfix (car poly))
            (real-polynomial-fix (cdr poly)))
    nil))

(defthm real-polynomial-real-polynomial-fix
  (real-polynomial-p (real-polynomial-fix poly))
  :rule-classes (:type-prescription :rewrite)
  )

(defthm real-polynomial-identity
  (implies (real-polynomial-p poly)
           (equal (real-polynomial-fix poly)
                  poly)))

(defun int-poly-expt-classical (poly a b)
  (int-poly-expt-classical-aux poly a b 0))

#|
TODO: This theorem no longer works.  The substitution

	strict-int-rcdfn-classical-prime ->
			(lambda (a b)
			  (strict-int-poly-expt-classical (real-polynomial-fix poly) a b 0))

is causing problems with the new algorithm for finding constraints (which
fixed the soundness bug related to missing constraints on defun-std functions).
The specific problem here has to do with the fact that
strict-int-poly-expt-classical is defined using defun-std, so its definition
does not open up when poly is not known to be standard.  That keeps ACL2(r)
from proving that it satisfies the definitional constraint for
strict-int-rcdfn-classical-prime.

(defthm ftc-2-for-poly-expt-classical-lemma
  (implies (and (realp a)
		(realp b)
                (real-polynomial-p poly))
	   (equal (int-poly-expt-classical poly a b)
		  (- (eval-polynomial-expt (integral-polynomial poly) b)
		     (eval-polynomial-expt (integral-polynomial poly) a))))
  :hints (("Goal" :do-not-induct t
	   :use ((:functional-instance ftc-2-for-rcdfn-classical
				       (rcdfn-classical
					(lambda (x)
					  (eval-polynomial-expt
                                           (integral-polynomial (real-polynomial-fix poly)) x)))
				       (rcdfn-classical-prime
					(lambda (x)
					  (eval-polynomial-expt
					   (real-polynomial-fix poly)
					   x)))
				       (rcdfn-classical-domain
					(lambda () (interval nil nil)))
				       (int-rcdfn-classical-prime
					(lambda (a b)
					  (int-poly-expt-classical (real-polynomial-fix poly) a b)))
				       (strict-int-rcdfn-classical-prime
					(lambda (a b)
					  (strict-int-poly-expt-classical (real-polynomial-fix poly) a b 0)))
				       (riemann-rcdfn-classical-prime
					(lambda (p)
					  (riemann-poly-expt-classical (real-polynomial-fix poly) p 0)))
				       (map-rcdfn-classical-prime
					(lambda (p)
					  (map-poly-expt-classical (real-polynomial-fix poly) p 0)))
				       (exists-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime
					(lambda (x0 eps)
					  (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux (real-polynomial-fix poly) x0 0 eps)))
				       (exists-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime-witness
					(lambda (x0 eps)
					  (exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux-witness (real-polynomial-fix poly) x0 0 eps)))
				       (forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime
					(lambda (x0 eps delta)
					  (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux
                                           (real-polynomial-fix poly)
                                           x0
                                           0
                                           eps
                                           delta)))
				       (forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime-witness
					(lambda (x0 eps delta)
					  (forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux-witness
                                           (real-polynomial-fix poly)
                                           x0
                                           0
                                           eps
                                           delta)))
				       (exists-delta-for-x-and-eps-so-deriv-rcdfn-classical-works
					(lambda (x eps)
					  (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works
                                           (integral-polynomial (real-polynomial-fix poly))
                                           x
                                           0
                                           eps)))
				       (exists-delta-for-x-and-eps-so-deriv-rcdfn-classical-works-witness
					(lambda (x eps)
					  (exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-witness
                                           (integral-polynomial (real-polynomial-fix poly))
                                           x
                                           0
                                           eps)))
				       (forall-x-eps-delta-in-range-deriv-rcdfn-classical-works
					(lambda (x eps delta)
					  (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works
                                           (integral-polynomial (real-polynomial-fix poly))
                                           x
                                           0
                                           eps
                                           delta)))
				       (forall-x-eps-delta-in-range-deriv-rcdfn-classical-works-witness
					(lambda (x eps delta)
					  (forall-x-eps-delta-in-range-deriv-poly-expt-aux-works-witness
                                           (integral-polynomial (real-polynomial-fix poly))
                                           x
                                           0
                                           eps
                                           delta)))
				       )
		 )
           :in-theory (disable integral-polynomial)
	   )
	  ("Subgoal 15"
	   :use ((:instance poly-expt-and-prime-are-continuous
			    (poly (real-polynomial-fix poly))
			    (x0 x0)
			    (n 0)
			    (epsilon eps))))
	  ("Subgoal 13"
	   :use ((:instance exists-delta-for-x0-to-make-x-within-epsilon-of-poly-expt-aux-suff
			    (poly (real-polynomial-fix poly))
			    (x0 x0)
			    (n 0))))
	  ("Subgoal 11"
	   :use ((:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-poly-expt-aux-necc
			    (poly (real-polynomial-fix poly))
			    (x0 x0)
			    (n 0))))
          ("Subgoal 8"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-suff
			    (poly (integral-polynomial (real-polynomial-fix poly)))
			    (x x)
			    (n 0)
                            (eps eps))))
          ("Subgoal 7"
	   :use ((:instance derivative-of-integral-polynomial
			    (poly (real-polynomial-fix poly)))))
	  ("Subgoal 6"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-poly-expt-aux-works-necc
			    (poly (integral-polynomial (real-polynomial-fix poly)))
			    (n 0))
                 (:instance derivative-of-integral-polynomial
			    (poly (real-polynomial-fix poly)))))
	  ("Subgoal 500"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-poly-expt-aux-works-suff)))
	  ("Subgoal 300"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-poly-expt-aux-works-necc)))
	  ))

|#
