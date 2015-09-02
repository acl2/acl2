; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(include-book "add")

(local (include-book "mult-new"))


(local
 (defthm bits-is-bits_alt
   (equal (bits x i j)
          (bits_alt x i j))
   :hints (("Goal" :in-theory (e/d (bits_alt bits) ())))))

(local
 (defthm bitn-is-bitn_alt
   (equal (bitn x n)
          (bitn_alt x n))
   :hints (("Goal" :in-theory (e/d (bitn_alt bitn) ())))))

(local
 (defthm binary-cat_alt-is-binary-cat
   (equal (binary-cat x m y n)
          (binary-cat_alt x m y n))
   :hints (("Goal" :in-theory (e/d (binary-cat_alt binary-cat) ())))))

(local
 (defthm mulcat_alt-is-mulcat
   (equal (mulcat l n x)
          (mulcat_alt l n x))
   :hints (("Goal" :in-theory (e/d (mulcat_alt mulcat) ())))))




;;;**********************************************************************
;;;			Radix-4 Booth Encoding
;;;**********************************************************************


(defun theta (i y)
  (+ (bitn y (1- (* 2 i)))
     (bitn y (* 2 i))
     (* -2 (bitn y (1+ (* 2 i))))))

(local
 (defthm theta-is-theta_alt
   (equal (theta i y)
          (theta_alt i y))))



(defun sum-theta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (theta (1- m) y))
	(sum-theta (1- m) y))))


(local
 (defthm sum-theta-is-sum-theta_alt
   (equal (sum-theta m y)
          (sum-theta_alt m y))))


(defthm sum-theta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 2 m))))
	     (equal y (sum-theta m y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sum-theta_alt-lemma)))))


(defun bmux4 (zeta x n)
  (case zeta
    (1  x)
    (-1 (bits (lognot x) (1- n) 0))
    (2  (* 2 x))
    (-2 (bits (lognot (* 2 x)) (1- n) 0))
    (0  0)))




(local
 (defthm bmux4-is-bmux4_alt
   (implies (and (natp n)
                 (integerp x)
                 (> n 0))
            (equal (bmux4 zeta x n)
                   (bmux4_alt zeta x n)))
   :hints (("Goal" :in-theory (e/d (bmux4_alt
                                    bmux4) ())))))


(defun neg (x) (if (< x 0) 1 0))

(encapsulate ((zeta (i) t))
 (local (defun zeta (i) (declare (ignore i)) 0))
 (defthm zeta-bnd
     (and (integerp (zeta i))
	  (<= (zeta i) 2)
	  (>= (zeta i) -2))))


(defun pp4 (i x n)
  (if (zerop i)
      (cat 1 1
	   (bitn (lognot (neg (zeta i))) 0) 1
	   (bmux4 (zeta i) x n) n)
    (cat 1 1
	 (bitn (lognot (neg (zeta i))) 0) 1
	 (bmux4 (zeta i) x n) n
	 0 1
	 (neg (zeta (1- i))) 1
	 0 (* 2 (1- i)))))


(local
 (defthm pp4-is-pp4_alt
   (implies (and (natp n)
                 (natp i)
                 (bvecp x (+ -1 n))
                 (integerp x)
                 (> n 0))
            (equal (pp4 i x n)
                   (pp4_alt i x n)))
   :hints (("Goal" :in-theory (e/d (pp4 pp4_alt) ())))))




(defun sum-zeta (m)
  (if (zp m)
      0
    (+ (* (expt 2 (* 2 (1- m))) (zeta (1- m)))
       (sum-zeta (1- m)))))

(defun sum-pp4 (x m n)
  (if (zp m)
      0
    (+ (pp4 (1- m) x n)
       (sum-pp4 x (1- m) n))))

(local
 (defthm sum-pp4-is-sum-pp4_alt
   (implies (and (natp n)
                 (bvecp x (+ -1 n))
                 (integerp x)
                 (> n 0))
            (equal (sum-pp4 x m n)
                   (sum-pp4_alt x m n)))
   :hints (("Goal" :in-theory (e/d () (pp4 pp4_alt))))))



(defthm booth4-thm
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n)))
	     (= (+ (expt 2 n)
		   (sum-pp4 x m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x (sum-zeta m))
		   (- (* (expt 2 (* 2 (1- m))) (neg (zeta (1- m))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth4-thm_alt))
           :in-theory (e/d () (sum-zeta sum-pp4 sum-pp4_alt)))))




(defun pp4-theta (i x y n)
   (if (zerop i)
       (cat 1 1
	    (bitn (lognot (neg (theta i y))) 0) 1
	    (bmux4 (theta i y) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (theta i y))) 0) 1
	  (bmux4 (theta i y) x n) n
	  0 1
	  (neg (theta (1- i) y)) 1
	  0 (* 2 (1- i)))))

(local
  (defthm pp4-theta-is-pp4-theta_alt
    (implies (and (not (zp n))
                  (bvecp x (+ -1 n))
                  (integerp i)
                  (integerp y)
                  (integerp x))
             (equal (pp4-theta i x y n)
                    (pp4_alt-theta_alt i x y n)))
    :hints (("Goal" :in-theory (e/d (pp4_alt-theta_alt
                                     pp4-theta)
                                    ())))))



(defun sum-pp4-theta (x y m n)
  (if (zp m)
      0
    (+ (pp4-theta (1- m) x y n)
       (sum-pp4-theta x y (1- m) n))))


(local
 (defthm sum-pp4-theta-is-sum-pp4_alt-theta_alt
    (implies (and (not (zp n))
                  (bvecp x (+ -1 n))
                  (integerp i)
                  (integerp y)
                  (integerp x))
             (equal (sum-pp4-theta x y m n)
                    (sum-pp4_alt-theta_alt x y m n)))))



(defthm booth4-corollary
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (+ (expt 2 n)
		   (sum-pp4-theta x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth4-corollary-alt)))))

;;;**********************************************************************
;;;                Statically Encoded Multiplier Arrays
;;;**********************************************************************


(defun m-mu-chi (i mode)
  (cond ((equal mode 'mu)
         (if (zp i)  1
           (cons (cons 1  i) 1)))
        ((equal mode 'chi)
         (if (zp i)  0
           (cons (cons 1  i) 0)))))


(mutual-recursion
 (defun mu (i y)
   (declare (xargs :measure (m-mu-chi i 'mu)))
     (+ (bits y (1+ (* 2 i)) (* 2 i)) (chi i y)))

 (defun chi (i y)
   (declare (xargs :measure (m-mu-chi i 'chi)))
   (if (zp i)
       0
     (if (>= (mu (1- i) y) 3)
	 1
       0))))


(local
 (encapsulate ()
              (local (encapsulate ()

                                  (defun mu-chi (i y mode)
                                    (declare (xargs :measure (if (and (not (equal mode 'mu))
                                                                      (not (equal mode 'chi)))
                                                                 0
                                                               (m-mu-chi i mode))))
                                    (if (equal mode 'mu)
                                        (+ (bits y (1+ (* 2 i)) (* 2 i)) (mu-chi i y 'chi))
                                      (if (equal mode 'chi)
                                          (if (zp i)
                                              0
                                            (if (>= (mu-chi (1- i) y 'mu) 3)
                                                1
                                              0))
                                        nil)))


                                  (defthm mu-chi-is
                                    (equal (mu-chi i y mode)
                                           (if (equal mode 'mu)
                                               (mu_alt i y)
                                             (if (equal mode 'chi)
                                                 (chi_alt i y)
                                               (mu-chi i y mode))))
                                    :rule-classes nil)





                                  (defthm mu-chi-is-2
                                    (equal (mu-chi i y mode)
                                           (if (equal mode 'mu)
                                               (mu i y)
                                             (if (equal mode 'chi)
                                                 (chi i y)
                                               (mu-chi i y mode))))
                                    :rule-classes nil)
                                  ))

              (defthm mu-is-mu
                (equal (mu i y)
                       (mu_alt i y))
                :hints (("Goal" :use ((:instance mu-chi-is
                                                 (mode 'mu))
                                      (:instance mu-chi-is-2
                                                 (mode 'mu))))))



              (defthm chi-is-chi
                (equal (chi i y)
                       (chi_alt i y))
                :hints (("Goal" :use ((:instance mu-chi-is
                                                 (mode 'chi))
                                      (:instance mu-chi-is-2
                                                 (mode 'chi))))))


              ))




(defun phi (i y)
  (if (= (bits (mu i y) 1 0) 3)
      -1
    (bits (mu i y) 1 0)))

(local
 (defthm phi-is-phi_alt
   (equal (phi i y)
          (phi_alt i y))))



(defthm phi-bnd
    (member (phi i y) '(-1 0 1 2))
    :hints (("Goal" :in-theory (e/d (phi-bnd-alt)
                                    (phi phi_alt)))))


(defun sum-odd-powers-of-2 (m)
  (if (zp m)
      0
    (+ (expt 2 (1- (* 2 m)))
       (sum-odd-powers-of-2 (1- m)))))



(defthm chi-m
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (equal (chi m y) 0))
  :rule-classes()
  :hints (("Goal" :use ((:instance chi_alt-m)))))



(defthm phi-m-1
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (>= (phi (1- m) y) 0))
  :rule-classes()
  :hints (("Goal" :use ((:instance phi_alt-m-1)))))


(defun sum-phi (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (phi (1- m) y))
	(sum-phi (1- m) y))))


(local
 (defthm sum-phi-is-sum-phi_alt
   (equal (sum-phi m y)
          (sum-phi_alt m y))
   :hints (("Goal" :in-theory (e/d () (phi_alt
                                       phi))))))



(defthm sum-phi-lemma
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (equal y (sum-phi m y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sum-phi_alt-lemma)))))


(defun pp4-phi (i x y n)
   (if (zerop i)
       (cat 1 1
	    (bitn (lognot (neg (phi i y))) 0) 1
	    (bmux4 (phi i y) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (phi i y))) 0) 1
	  (bmux4 (phi i y) x n) n
	  0 1
	  (neg (phi (1- i) y)) 1
	  0 (* 2 (1- i)))))


(local
 (defthm pp4-phi-is-pp4_alt-phi_alt
   (implies (and (integerp x)
                 (natp n)
                 (> n 0))
            (equal (pp4-phi i x y n)
                   (pp4_alt-phi_alt i x y n)))
   :hints (("Goal" :in-theory (e/d () (phi_alt
                                       phi
                                       pp4_alt
                                       pp4
                                       bmux4_alt
                                       bmux4))))))




(defun sum-pp4-phi (x y m n)
  (if (zp m)
      0
    (+ (pp4-phi (1- m) x y n)
       (sum-pp4-phi x y (1- m) n))))

(local
 (defthm sum-pp4-phi-is-sum-pp4_alt-phi_alt
   (implies (and (integerp x)
                 (natp n)
                 (> n 0))
            (equal (sum-pp4-phi x y m n)
                   (sum-pp4_alt-phi_alt x y m n)))
   :hints (("Goal" :in-theory (e/d ()
                                   (pp4_alt-phi_alt
                                    pp4-phi))))))




(defthm static-booth
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
                  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (= (+ (expt 2 n)
		   (sum-pp4-phi x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance static-booth-alt)))))


;;;**********************************************************************
;;;                Encoding Redundant Representations
;;;**********************************************************************


(defun gamma (i a b c)
   (if (zp i)
       (bitn c 0)
     (logior (bitn  a (+ -1  (* 2 i)))
 	     (bitn  b (+ -1  (* 2 i))))))

(local
 (defthm gamma-is-gamma_alt
   (equal (gamma i a b c)
          (gamma_alt i a b c))
   :hints (("Goal" :in-theory (e/d (gamma_alt gamma) ())))))



(defun delta (i a b c d)
  (if (zp i)
      (bitn d 0)
    (logand (logior (logand (bitn a (+ -2 (* 2 i)))
			    (bitn b (+ -2 (* 2 i))))
		    (logior (logand (bitn a (+ -2 (* 2 i)))
				    (gamma (1- i) a b c))
			    (logand (bitn b (+ -2 (* 2 i)))
				    (gamma (1- i) a b c))))
	    (lognot (logxor (bitn a (1- (* 2 i)))
			    (bitn b (1- (* 2 i))))))))


(local
 (defthm delta-is-delta_alt
   (equal (delta i a b c d)
          (delta_alt i a b c d))
   :hints (("Goal" :in-theory (e/d (delta_alt delta) ())))))



(defun psi (i a b c d)
  (if (not (natp i))
      0
    (+ (bits a (1+ (* 2 i)) (* 2 i))
       (bits b (1+ (* 2 i)) (* 2 i))
       (gamma i a b c)
       (delta i a b c d)
       (* -4 (+ (gamma (1+ i) a b c)
                (delta (1+ i) a b c d))))))


(local
 (defthm psi-is-psi_alt
   (equal (psi i a b c d)
          (psi_alt i a b c d))
   :hints (("Goal" :in-theory (e/d () (delta_alt
                                       delta
                                       gamma_alt
                                       gamma))))))



(defthm psi-m-1
    (implies (and (natp m)
                  (>= m 1)
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1))
	     (and (equal (gamma m a b c) 0)
		  (equal (delta m a b c d) 0)
		  (>= (psi (1- m) a b c d) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance psi_alt-m-1))
           :in-theory (e/d ()
                           (psi
                            psi_alt
                            gamma
                            gamma_alt
                            delta_alt
                            delta)))))



(defun sum-psi (m a b c d)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (psi (1- m) a b c d))
	(sum-psi (1- m) a b c d))))


(local
 (defthm sum-psi-is-sum-psi
   (equal (sum-psi m a b c d)
          (sum-psi_alt m a b c d))
   :hints (("Goal" :in-theory (e/d () (psi psi_alt))))))



(defthm sum-psi-lemma
    (implies (and (natp m)
                  (<= 1 M) ;; add
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1))
	     (equal (+ a b c d) (sum-psi m a b c d)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sum-psi_alt-lemma)))))




(defthmd psi-bnd
  (and (integerp (psi i a b c d))
       (<= (psi i a b c d) 2)
       (>= (psi i a b c d) -2))
  :hints (("Goal" :use ((:instance psi_alt-bnd)))))

(defun pp4-psi (i x a b c d n)
   (if (zerop i)
       (cat 1 1
	    (bitn (lognot (neg (psi i a b c d))) 0) 1
	    (bmux4 (psi i a b c d) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (psi i a b c d))) 0) 1
	  (bmux4 (psi i a b c d) x n) n
	  0 1
	  (neg (psi (1- i) a b c d)) 1
	  0 (* 2 (1- i)))))


(local
 (defthm pp4-psi-is-pp4_alt-psi_alt
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (pp4-psi i x a b c d n)
                   (pp4_alt-psi_alt i x a b c d n)))
   :hints (("Goal" :in-theory (e/d ()
                                   (bmux4_alt
                                    bmux4
                                    psi_alt
                                    psi))))))


(defun sum-pp4-psi (x a b c d m n)
  (if (zp m)
      0
    (+ (pp4-psi (1- m) x a b c d n)
       (sum-pp4-psi x a b c d (1- m) n))))


(local
 (defthm sum-pp4-psi-is-sum-pp4-psi
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (sum-pp4-psi x a b c d m n)
                   (sum-pp4_alt-psi_alt x a b c d m n)))
   :hints (("Goal" :in-theory (e/d ()
                                   (pp4_alt-psi_alt
                                    pp4-psi))))))





(defthm redundant-booth
    (implies (and (natp m)
                  (<= 1 m)
                  (not (zp n))
		  (bvecp x (1- n))
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1)
		  (= y (+ a b c d)))
	     (= (+ (expt 2 n)
		   (sum-pp4-psi x a b c d m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance redundant-booth_alt)))))

;;;**********************************************************************
;;;			Radix-8 Booth Encoding
;;;**********************************************************************



(defun eta (i y)
  (+ (bitn y (1- (* 3 i)))
     (bitn y (* 3 i))
     (* 2 (bitn y (1+ (* 3 i))))
     (* -4 (bitn y (+ 2 (* 3 i))))))


(local
 (defthm eta-is-eta_alt
   (equal (eta i y)
          (eta_alt i y))))


(defun sum-eta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 3 (1- m))) (eta (1- m) y))
	(sum-eta (1- m) y))))

(local
 (defthm sum-eta-is-sum-eta_alt
   (equal (sum-eta m y)
          (sum-eta_alt m y))))


(defthm sum-eta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 3 m))))
	     (equal y (sum-eta m y)))
  :rule-classes ()
  :hints (("Goal"   :use ((:instance sum-eta_alt-lemma)))))




(defun bmux8 (zeta x n)
  (case zeta
    (1  x)
    (-1 (bits (lognot x) (1- n) 0))
    (2  (* 2 x))
    (-2 (bits (lognot (* 2 x)) (1- n) 0))
    (3  (* 3 x))
    (-3 (bits (lognot (* 3 x)) (1- n) 0))
    (4  (* 4 x))
    (-4 (bits (lognot (* 4 x)) (1- n) 0))
    (0  0)))



(local
 (defthm bmux8-is-bmux8_alt
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (bmux8 zeta x n)
                   (bmux8_alt zeta x n)))
   :hints (("Goal" :in-theory (e/d (bmux8 bmux8_alt) ())))))


(encapsulate ((xi (i) t))
 (local (defun xi (i) (declare (ignore i)) 0))
 (defthm xi-bnd
     (and (integerp (xi i))
	  (<= (xi i) 4)
	  (>= (xi i) -4))))



(defun pp8 (i x n)
  (if (zerop i)
      (cat 3 2
	   (bitn (lognot (neg (xi i))) 0) 1
	   (bmux8 (xi i) x n) n)
    (cat 3 2
	 (bitn (lognot (neg (xi i))) 0) 1
	 (bmux8 (xi i) x n) n
	 0 2
	 (neg (xi (1- i))) 1
	 0 (* 3 (1- i)))))


(local
 (defthm pp8-is-pp8_alt
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (pp8 i x n)
                   (pp8_alt i x n)))
   :hints (("Goal" :in-theory (e/d () (bmux8_alt
                                       bmux8))))))

(defun sum-xi (m)
  (if (zp m)
      0
    (+ (* (expt 2 (* 3 (1- m))) (xi (1- m)))
       (sum-xi (1- m)))))

(defun sum-pp8 (x m n)
  (if (zp m)
      0
    (+ (pp8 (1- m) x n)
       (sum-pp8 x (1- m) n))))


(local
 (defthm sum-pp8-sum-pp8_alt
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (sum-pp8 x m n)
                   (sum-pp8_alt x m n)))
   :hints (("Goal" :in-theory (e/d () (pp8 pp8_alt))))))



(defthm booth8-thm
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2)))
	     (= (+ (expt 2 n)
		   (sum-pp8 x m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x (sum-xi m))
		   (- (* (expt 2 (* 3 (1- m))) (neg (xi (1- m))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth8-thm_alt))
           :in-theory (e/d () (sum-pp8 sum-pp8_alt)))))


(defun pp8-eta (i x y n)
  (if (zerop i)
      (cat 3 2
	   (bitn (lognot (neg (eta i y))) 0) 1
	   (bmux8 (eta i y) x n) n)
    (cat 3 2
	 (bitn (lognot (neg (eta i y))) 0) 1
	 (bmux8 (eta i y) x n) n
	 0 2
	 (neg (eta (1- i) y)) 1
	 0 (* 3 (1- i)))))


(local
 (defthm pp8-eta-is-pp8-eta_alt
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (pp8-eta i x y n)
                   (pp8_alt-eta_alt i x y n)))
   :hints (("Goal" :in-theory (e/d (pp8-eta pp8_alt-eta_alt) ())))))


(defun sum-pp8-eta (x y m n)
  (if (zp m)
      0
    (+ (pp8-eta (1- m) x y n)
       (sum-pp8-eta x y (1- m) n))))



(local
 (defthm sum-pp8-eta-is-sum-pp8_alt-eta_alt
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (sum-pp8-eta x y m n)
                   (sum-pp8_alt-eta_alt x y m n)))
   :hints (("Goal" :in-theory (e/d () (pp8-eta
                                       pp8_alt-eta_alt))))))


(defthm booth8-corollary
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2))
		  (bvecp y (1- (* 3 m))))
	     (= (+ (expt 2 n)
		   (sum-pp8-eta x y m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth8-corollary_alt)))))
