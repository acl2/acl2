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

(include-book "add-new")

(local (include-book "../lib2/top"))
(local (include-book "../../arithmetic/top"))
(local (include-book "log-support"))

(local
 (encapsulate ()
              (local (include-book "bits-new-proofs"))

             (defthm bits_alt-is-bits
               (equal (bits_alt x i j)
                      (bits x i j)))


             (defthm bitn_alt-is-bitn
               (equal (bitn_alt x n)
                      (bitn x n)))


             (defthm binary-cat_alt-is-binary-cat
               (equal (binary-cat_alt x m y n)
                      (binary-cat x m y n)))

             ))



;;;**********************************************************************
;;;			Radix-4 Booth Encoding
;;;**********************************************************************


(defun theta_alt (i y)
  (+ (bitn_alt y (1- (* 2 i)))
     (bitn_alt y (* 2 i))
     (* -2 (bitn_alt y (1+ (* 2 i))))))

(local
 (defthm theta_alt-is-theta
   (equal (theta_alt i y)
          (theta i y))))



(defun sum-theta_alt (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (theta_alt (1- m) y))
	(sum-theta_alt (1- m) y))))


(local
 (defthm sum-theta_alt-is-sum-theta
   (equal (sum-theta_alt m y)
          (sum-theta m y))))


(defthm sum-theta_alt-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 2 m))))
	     (equal y (sum-theta_alt m y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sum-theta-lemma)))))





(defun bmux4_alt (zeta x n)
  (case zeta
    (1  x)
    (-1 (bits_alt (lognot x) (1- n) 0))
    (2  (* 2 x))
    (-2 (bits_alt (lognot (* 2 x)) (1- n) 0))
    (0  0)))




(local
 (defthm bmux4_alt-is-bmux4
   (implies (and (natp n)
                 (integerp x)
                 (> n 0))
            (equal (bmux4_alt zeta x n)
                   (bmux4 zeta x n)))
   :hints (("Goal" :in-theory (e/d (lnot-lognot) ())))))


(defun neg (x) (if (< x 0) 1 0))

(encapsulate ((zeta (i) t))
 (local (defun zeta (i) (declare (ignore i)) 0))
 (defthm zeta-bnd
     (and (integerp (zeta i))
	  (<= (zeta i) 2)
	  (>= (zeta i) -2))))


(defun pp4_alt (i x n)
  (if (zerop i)
      (cat_alt 1 1
	   (bitn_alt (lognot (neg (zeta i))) 0) 1
	   (bmux4_alt (zeta i) x n) n)
    (cat_alt 1 1
	 (bitn_alt (lognot (neg (zeta i))) 0) 1
	 (bmux4_alt (zeta i) x n) n
	 0 1
	 (neg (zeta (1- i))) 1
	 0 (* 2 (1- i)))))

(local
 (defthm bvecp-mux4
   (implies (and (bvecp x (+ -1 m))
                 (natp m)
                 (>= m n))
            (BVECP (BMUX4 (ZETA 0) X N) m))
   :hints (("Goal" :in-theory (e/d (bvecp bmux4
                                          expt-2-reduce-leading-constant) (ZETA-BND))
            :use ((:instance zeta-bnd
                             (i 0)))))))



(local
 (defthm integerp-bmux4
   (implies (integerp x)
            (integerp (BMUX4 (ZETA i) X N)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (e/d (bmux4
                                    expt-2-reduce-leading-constant) (ZETA-BND))
            :use ((:instance zeta-bnd
                             (i i)))))))


(local
 (defthm bvecp-0
   (BVECP 0 n)
   :hints (("Goal" :in-theory (e/d (bvecp) ())))))


(local
 (defthm pp4_alt-is-pp4
   (implies (and (natp n)
                 (natp i)
                 (bvecp x (+ -1 n))
                 (integerp x)
                 (> n 0))
            (equal (pp4_alt i x n)
                   (pp4 i x n)))
   :hints (("Goal" :in-theory (e/d (lnot-lognot
                                    bvecp-monotone
                                    cat)
                                   (bmux4 bmux4_alt))))))




(defun sum-zeta (m)
  (if (zp m)
      0
    (+ (* (expt 2 (* 2 (1- m))) (zeta (1- m)))
       (sum-zeta (1- m)))))

(defun sum-pp4_alt (x m n)
  (if (zp m)
      0
    (+ (pp4_alt (1- m) x n)
       (sum-pp4_alt x (1- m) n))))

(local
 (defthm sum-pp4_alt-is-sum-pp4
   (implies (and (natp n)
                 (natp i)
                 (bvecp x (+ -1 n))
                 (integerp x)
                 (> n 0))
            (equal (sum-pp4_alt x m n)
                   (sum-pp4 x m n)))
   :hints (("Goal" :in-theory (e/d () (pp4_alt pp4))))))



(defthm booth4-thm_alt
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n)))
	     (= (+ (expt 2 n)
		   (sum-pp4_alt x m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x (sum-zeta m))
		   (- (* (expt 2 (* 2 (1- m))) (neg (zeta (1- m))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth4-thm))
           :in-theory (e/d () (sum-pp4_alt sum-pp4)))))



(defun pp4_alt-theta_alt (i x y n)
   (if (zerop i)
       (cat_alt 1 1
	    (bitn_alt (lognot (neg (theta_alt i y))) 0) 1
	    (bmux4_alt (theta_alt i y) x n) n)
     (cat_alt 1 1
	  (bitn_alt (lognot (neg (theta_alt i y))) 0) 1
	  (bmux4_alt (theta_alt i y) x n) n
	  0 1
	  (neg (theta_alt (1- i) y)) 1
	  0 (* 2 (1- i)))))



(local
 (defthm bvecp-mux4-theta
   (implies (and (bvecp x (+ -1 m))
                 (natp m)
                 (>= m n))
            (BVECP (BMUX4 (theta i y) X N) m))
   :hints (("Goal" :in-theory (e/d (bvecp bmux4
                                          expt-2-reduce-leading-constant) (ZETA-BND))
            :use ((:instance bitn-0-1
                             (x y)
                             (n (1- (* 2 I))))
                  (:instance bitn-0-1
                             (x y)
                             (n (* 2 I)))
                  (:instance bitn-0-1
                             (x y)
                             (n (+ 1 (* 2 I)))))))))






(local
 (defthm integerp-bmux4-theta
   (implies (integerp x)
            (integerp (BMUX4 (theta i y) X N)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (e/d (bmux4
                                    expt-2-reduce-leading-constant) (ZETA-BND))
            :use ((:instance bitn-0-1
                             (x y)
                             (n (1- (* 2 I))))
                  (:instance bitn-0-1
                             (x y)
                             (n (* 2 I)))
                  (:instance bitn-0-1
                             (x y)
                             (n (+ 1 (* 2 I)))))))))




(local
  (defthm pp4_alt-theta_alt-is-pp4-theta
    (implies (and (not (zp n))
                  (bvecp x (+ -1 n))
                  (integerp i)
                  (integerp y)
                  (integerp x))
             (equal (pp4_alt-theta_alt i x y n)
                    (pp4-theta i x y n)))
    :hints (("Goal" :in-theory (e/d ()
                                    (theta_alt
                                     theta
                                     bmux4_alt
                                     bmux4))))))



(defun sum-pp4_alt-theta_alt (x y m n)
  (if (zp m)
      0
    (+ (pp4_alt-theta_alt (1- m) x y n)
       (sum-pp4_alt-theta_alt x y (1- m) n))))


(local
 (defthm sum-pp4_alt-theta_alt-is-sum-pp4-theta
    (implies (and (not (zp n))
                  (bvecp x (+ -1 n))
                  (integerp i)
                  (integerp y)
                  (integerp x))
             (equal (sum-pp4_alt-theta_alt x y m n)
                    (sum-pp4-theta x y m n)))))



(defthm booth4-corollary-alt
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (+ (expt 2 n)
		   (sum-pp4_alt-theta_alt x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth4-corollary)))))

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
 (defun mu_alt (i y)
   (declare (xargs :measure (m-mu-chi i 'mu)))
     (+ (bits_alt y (1+ (* 2 i)) (* 2 i)) (chi_alt i y)))

 (defun chi_alt (i y)
   (declare (xargs :measure (m-mu-chi i 'chi)))
   (if (zp i)
       0
     (if (>= (mu_alt (1- i) y) 3)
	 1
       0))))


(local
 (encapsulate ()
              (local (encapsulate ()

                                  (defun mu-chi_alt (i y mode)
                                    (declare (xargs :measure (if (and (not (equal mode 'mu))
                                                                      (not (equal mode 'chi)))
                                                                 0
                                                               (m-mu-chi i mode))))
                                    (if (equal mode 'mu)
                                        (+ (bits_alt y (1+ (* 2 i)) (* 2 i)) (mu-chi_alt i y 'chi))
                                      (if (equal mode 'chi)
                                          (if (zp i)
                                              0
                                            (if (>= (mu-chi_alt (1- i) y 'mu) 3)
                                                1
                                              0))
                                        nil)))


                                  (defthm mu-chi_alt-is
                                    (equal (mu-chi_alt i y mode)
                                           (if (equal mode 'mu)
                                               (mu_alt i y)
                                             (if (equal mode 'chi)
                                                 (chi_alt i y)
                                               (mu-chi_alt i y mode))))
                                    :rule-classes nil)





                                  (defthm mu-chi_alt-is-2
                                    (equal (mu-chi_alt i y mode)
                                           (if (equal mode 'mu)
                                               (mu i y)
                                             (if (equal mode 'chi)
                                                 (chi i y)
                                               (mu-chi_alt i y mode))))
                                    :rule-classes nil)
                                  ))

              (defthm mu_alt-is-mu
                (equal (mu_alt i y)
                       (mu i y))
                :hints (("Goal" :use ((:instance mu-chi_alt-is
                                                 (mode 'mu))
                                      (:instance mu-chi_alt-is-2
                                                 (mode 'mu))))))



              (defthm chi_alt-is-chi
                (equal (chi_alt i y)
                       (chi i y))
                :hints (("Goal" :use ((:instance mu-chi_alt-is
                                                 (mode 'chi))
                                      (:instance mu-chi_alt-is-2
                                                 (mode 'chi))))))


              ))




(defun phi_alt (i y)
  (if (= (bits_alt (mu_alt i y) 1 0) 3)
      -1
    (bits_alt (mu_alt i y) 1 0)))

(local
 (defthm phi_alt-is-phi
   (equal (phi_alt i y)
          (phi i y))))



(defthm phi-bnd-alt
    (member (phi_alt i y) '(-1 0 1 2))
    :hints (("Goal" :in-theory (e/d (phi-bnd) (phi_alt phi)))))





(defun sum-odd-powers-of-2 (m)
  (if (zp m)
      0
    (+ (expt 2 (1- (* 2 m)))
       (sum-odd-powers-of-2 (1- m)))))



(defthm chi_alt-m
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (equal (chi_alt m y) 0))
  :rule-classes()
  :hints (("Goal" :use ((:instance chi-m))
           :in-theory (e/d () (chi_alt chi)))))


(defthm phi_alt-m-1
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (>= (phi_alt (1- m) y) 0))
  :rule-classes()
  :hints (("Goal" :use ((:instance phi-m-1))
           :in-theory (e/d () (phi_alt phi)))))


(defun sum-phi_alt (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (phi_alt (1- m) y))
	(sum-phi_alt (1- m) y))))


(local
 (defthm sum-phi_alt-is-sum-phi
   (equal (sum-phi_alt m y)
          (sum-phi m y))
   :hints (("Goal" :in-theory (e/d () (phi_alt
                                       phi))))))



(defthm sum-phi_alt-lemma
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (equal y (sum-phi_alt m y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sum-phi-lemma)))))


(defun pp4_alt-phi_alt (i x y n)
   (if (zerop i)
       (cat_alt 1 1
	    (bitn_alt (lognot (neg (phi_alt i y))) 0) 1
	    (bmux4_alt (phi_alt i y) x n) n)
     (cat_alt 1 1
	  (bitn_alt (lognot (neg (phi_alt i y))) 0) 1
	  (bmux4_alt (phi_alt i y) x n) n
	  0 1
	  (neg (phi_alt (1- i) y)) 1
	  0 (* 2 (1- i)))))


(local
 (defthm pp4_alt-phi_alt-is-pp4-phi
   (implies (and (integerp x)
                 (natp n)
                 (> n 0))
            (equal (pp4_alt-phi_alt i x y n)
                   (pp4-phi i x y n)))
   :hints (("Goal" :in-theory (e/d () (phi_alt
                                       phi
                                       pp4_alt
                                       pp4
                                       bmux4_alt
                                       bmux4))))))




(defun sum-pp4_alt-phi_alt (x y m n)
  (if (zp m)
      0
    (+ (pp4_alt-phi_alt (1- m) x y n)
       (sum-pp4_alt-phi_alt x y (1- m) n))))

(local
 (defthm sum-pp4_alt-phi_alt-is-sum-pp4-phi
   (implies (and (integerp x)
                 (natp n)
                 (> n 0))
            (equal (sum-pp4_alt-phi_alt x y m n)
                   (sum-pp4-phi x y m n)))
   :hints (("Goal" :in-theory (e/d ()
                                   (pp4-phi
                                    pp4_alt-phi_alt))))))




(defthm static-booth-alt
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
                  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (= (+ (expt 2 n)
		   (sum-pp4_alt-phi_alt x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance static-booth)))))


;;;**********************************************************************
;;;                Encoding Redundant Representations
;;;**********************************************************************


(defun gamma_alt (i a b c)
   (if (zp i)
       (bitn_alt c 0)
     (logior (bitn_alt  a (+ -1  (* 2 i)))
 	     (bitn_alt  b (+ -1  (* 2 i))))))

(local
 (defthm gamma_alt-is-gamma
   (equal (gamma_alt i a b c)
          (gamma i a b c))
   :hints (("Goal" :use ((:instance bitn-0-1
                                    (x a)
                                    (n (+ -1 (* 2 I))))
                         (:instance bitn-0-1
                                    (x b)
                                    (n (+ -1 (* 2 I)))))))))



(defun delta_alt (i a b c d)
  (if (zp i)
      (bitn_alt d 0)
    (logand (logior (logand (bitn_alt a (+ -2 (* 2 i)))
			    (bitn_alt b (+ -2 (* 2 i))))
		    (logior (logand (bitn_alt a (+ -2 (* 2 i)))
				    (gamma_alt (1- i) a b c))
			    (logand (bitn_alt b (+ -2 (* 2 i)))
				    (gamma_alt (1- i) a b c))))
	    (lognot (logxor (bitn_alt a (1- (* 2 i)))
			    (bitn_alt b (1- (* 2 i))))))))



(local
 (DEFTHM LOGAND-BVECP-G_alt
   (IMPLIES (AND (NATP N) (BVECP Y N) (INTEGERP X))
            (BVECP (LOGAND X Y) N))
   :hints (("Goal" :use ((:instance logand-bvecp-g
                                    (x y)
                                    (y x)))
            :in-theory (e/d () (logand-bvecp-g))))))



(local
 (defthm delta_alt-is-delta
   (equal (delta_alt i a b c d)
          (delta i a b c d))
   :hints (("Goal" :in-theory (e/d (land-logand
                                    logand-bitn-reduce
                                    lnot-lognot
                                    lxor-logxor
                                    lior-logior)
                                   (gamma_alt
                                    gamma))))))


;;;;
;;;;
;;;;

(defun psi_alt (i a b c d)
  (if (not (natp i))
      0
    (+ (bits_alt a (1+ (* 2 i)) (* 2 i))
       (bits_alt b (1+ (* 2 i)) (* 2 i))
       (gamma_alt i a b c)
       (delta_alt i a b c d)
       (* -4 (+ (gamma_alt (1+ i) a b c)
                (delta_alt (1+ i) a b c d))))))


(local
 (defthm psi_alt-is-psi
   (equal (psi_alt i a b c d)
          (psi i a b c d))
   :hints (("Goal" :in-theory (e/d () (delta_alt
                                       delta
                                       gamma_alt
                                       gamma))))))



(defthm psi_alt-m-1
    (implies (and (natp m)
                  (>= m 1)
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1))
	     (and (equal (gamma_alt m a b c) 0)
		  (equal (delta_alt m a b c d) 0)
		  (>= (psi_alt (1- m) a b c d) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance psi-m-1))
           :in-theory (e/d ()
                           (psi_alt
                            psi
                            gamma_alt
                            gamma
                            delta_alt
                            delta)))))



(defun sum-psi_alt (m a b c d)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (psi_alt (1- m) a b c d))
	(sum-psi_alt (1- m) a b c d))))


(local
 (defthm sum-psi_alt-is-sum-psi
   (equal (sum-psi_alt m a b c d)
          (sum-psi m a b c d))
   :hints (("Goal" :in-theory (e/d () (psi_alt psi))))))



(defthm sum-psi_alt-lemma
    (implies (and (natp m)
                  (<= 1 M) ;; add
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1))
	     (equal (+ a b c d) (sum-psi_alt m a b c d)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sum-psi-lemma)))))




(defthmd psi_alt-bnd
  (and (integerp (psi_alt i a b c d))
       (<= (psi_alt i a b c d) 2)
       (>= (psi_alt i a b c d) -2))
  :hints (("Goal" :use ((:instance psi-bnd)))))

(defun pp4_alt-psi_alt (i x a b c d n)
   (if (zerop i)
       (cat_alt 1 1
	    (bitn_alt (lognot (neg (psi_alt i a b c d))) 0) 1
	    (bmux4_alt (psi_alt i a b c d) x n) n)
     (cat_alt 1 1
	  (bitn_alt (lognot (neg (psi_alt i a b c d))) 0) 1
	  (bmux4_alt (psi_alt i a b c d) x n) n
	  0 1
	  (neg (psi_alt (1- i) a b c d)) 1
	  0 (* 2 (1- i)))))


(local
 (defthm pp4_alt-psi_alt-is-pp4-psi
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (pp4_alt-psi_alt i x a b c d n)
                   (pp4-psi i x a b c d n)))
   :hints (("Goal" :in-theory (e/d ()
                                   (bmux4_alt
                                    bmux4
                                    psi_alt
                                    psi))))))


(defun sum-pp4_alt-psi_alt (x a b c d m n)
  (if (zp m)
      0
    (+ (pp4_alt-psi_alt (1- m) x a b c d n)
       (sum-pp4_alt-psi_alt x a b c d (1- m) n))))


(local
 (defthm sum-pp4_alt-psi_alt-is-sum-pp4-psi
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (sum-pp4_alt-psi_alt x a b c d m n)
                   (sum-pp4-psi x a b c d m n)))
   :hints (("Goal" :in-theory (e/d ()
                                   (pp4_alt-psi_alt
                                    pp4-psi))))))





(defthm redundant-booth_alt
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
		   (sum-pp4_alt-psi_alt x a b c d m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance redundant-booth)))))

;;;**********************************************************************
;;;			Radix-8 Booth Encoding
;;;**********************************************************************



(defun eta_alt (i y)
  (+ (bitn_alt y (1- (* 3 i)))
     (bitn_alt y (* 3 i))
     (* 2 (bitn_alt y (1+ (* 3 i))))
     (* -4 (bitn_alt y (+ 2 (* 3 i))))))


(local
 (defthm eta_alt-is-eta
   (equal (eta_alt i y)
          (eta i y))))


(defun sum-eta_alt (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 3 (1- m))) (eta_alt (1- m) y))
	(sum-eta_alt (1- m) y))))

(local
 (defthm sum-eta_alt-is-sum-eta
   (equal (sum-eta_alt m y)
          (sum-eta m y))))


(defthm sum-eta_alt-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 3 m))))
	     (equal y (sum-eta_alt m y)))
  :rule-classes ()
  :hints (("Goal"   :use ((:instance sum-eta-lemma)))))




(defun bmux8_alt (zeta_alt x n)
  (case zeta_alt
    (1  x)
    (-1 (bits_alt (lognot x) (1- n) 0))
    (2  (* 2 x))
    (-2 (bits_alt (lognot (* 2 x)) (1- n) 0))
    (3  (* 3 x))
    (-3 (bits_alt (lognot (* 3 x)) (1- n) 0))
    (4  (* 4 x))
    (-4 (bits_alt (lognot (* 4 x)) (1- n) 0))
    (0  0)))



(local
 (defthm bmux8_alt-is-bmux8
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (bmux8_alt zeta x n)
                   (bmux8 zeta x n)))
   :hints (("Goal" :in-theory (e/d (lnot-lognot) ())))))


(encapsulate ((xi (i) t))
 (local (defun xi (i) (declare (ignore i)) 0))
 (defthm xi-bnd
     (and (integerp (xi i))
	  (<= (xi i) 4)
	  (>= (xi i) -4))))



(defun pp8_alt (i x n)
  (if (zerop i)
      (cat_alt 3 2
	   (bitn_alt (lognot (neg (xi i))) 0) 1
	   (bmux8_alt (xi i) x n) n)
    (cat_alt 3 2
	 (bitn_alt (lognot (neg (xi i))) 0) 1
	 (bmux8_alt (xi i) x n) n
	 0 2
	 (neg (xi (1- i))) 1
	 0 (* 3 (1- i)))))


(local
 (defthm pp8_alt-is-pp8
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (pp8_alt i x n)
                   (pp8 i x n)))
   :hints (("Goal" :in-theory (e/d () (bmux8_alt
                                       bmux8))))))

(defun sum-xi (m)
  (if (zp m)
      0
    (+ (* (expt 2 (* 3 (1- m))) (xi (1- m)))
       (sum-xi (1- m)))))

(defun sum-pp8_alt (x m n)
  (if (zp m)
      0
    (+ (pp8_alt (1- m) x n)
       (sum-pp8_alt x (1- m) n))))


(local
 (defthm sum-pp8_alt-sum-pp8
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (sum-pp8_alt x m n)
                   (sum-pp8 x m n)))
   :hints (("Goal" :in-theory (e/d () (pp8_alt pp8))))))



(defthm booth8-thm_alt
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2)))
	     (= (+ (expt 2 n)
		   (sum-pp8_alt x m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x (sum-xi m))
		   (- (* (expt 2 (* 3 (1- m))) (neg (xi (1- m))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth8-thm))
           :in-theory (e/d () (sum-pp8_alt sum-pp8)))))


(defun pp8_alt-eta_alt (i x y n)
  (if (zerop i)
      (cat_alt 3 2
	   (bitn_alt (lognot (neg (eta_alt i y))) 0) 1
	   (bmux8_alt (eta_alt i y) x n) n)
    (cat_alt 3 2
	 (bitn_alt (lognot (neg (eta_alt i y))) 0) 1
	 (bmux8_alt (eta_alt i y) x n) n
	 0 2
	 (neg (eta_alt (1- i) y)) 1
	 0 (* 3 (1- i)))))

(local
 (defthm pp8_alt-eta_alt-is-pp8-eta
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (pp8_alt-eta_alt i x y n)
                   (pp8-eta i x y n)))
   :hints (("Goal" :in-theory (e/d (lnot-lognot)
                                   (bmux8_alt
                                    bmux8
                                    eta_alt
                                    eta))))))


(defun sum-pp8_alt-eta_alt (x y m n)
  (if (zp m)
      0
    (+ (pp8_alt-eta_alt (1- m) x y n)
       (sum-pp8_alt-eta_alt x y (1- m) n))))



(local
 (defthm sum-pp8_alt-eta_alt-is-sum-pp8-eta
   (implies (and (natp n)
                 (> n 0)
                 (integerp x))
            (equal (sum-pp8_alt-eta_alt x y m n)
                   (sum-pp8-eta x y m n)))
   :hints (("Goal" :in-theory (e/d () (pp8_alt-eta_alt
                                       pp8-eta))))))


(defthm booth8-corollary_alt
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2))
		  (bvecp y (1- (* 3 m))))
	     (= (+ (expt 2 n)
		   (sum-pp8_alt-eta_alt x y m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth8-corollary)))))
