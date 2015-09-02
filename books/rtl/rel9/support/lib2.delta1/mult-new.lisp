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

(set-enforce-redundancy t)

(include-book "add-new")

(local (include-book "mult-new-proofs"))


(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;;;**********************************************************************
;;;			Radix-4 Booth Encoding
;;;**********************************************************************


(defun theta_alt (i y)
  (+ (bitn_alt y (1- (* 2 i)))
     (bitn_alt y (* 2 i))
     (* -2 (bitn_alt y (1+ (* 2 i))))))


(defun sum-theta_alt (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (theta_alt (1- m) y))
	(sum-theta_alt (1- m) y))))


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



(defun sum-pp4_alt-theta_alt (x y m n)
  (if (zp m)
      0
    (+ (pp4_alt-theta_alt (1- m) x y n)
       (sum-pp4_alt-theta_alt x y (1- m) n))))


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



(defun phi_alt (i y)
  (if (= (bits_alt (mu_alt i y) 1 0) 3)
      -1
    (bits_alt (mu_alt i y) 1 0)))


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


(defun sum-pp4_alt-phi_alt (x y m n)
  (if (zp m)
      0
    (+ (pp4_alt-phi_alt (1- m) x y n)
       (sum-pp4_alt-phi_alt x y (1- m) n))))



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


;;;;;;


(defun psi_alt (i a b c d)
  (if (not (natp i))
      0
    (+ (bits_alt a (1+ (* 2 i)) (* 2 i))
       (bits_alt b (1+ (* 2 i)) (* 2 i))
       (gamma_alt i a b c)
       (delta_alt i a b c d)
       (* -4 (+ (gamma_alt (1+ i) a b c)
                (delta_alt (1+ i) a b c d))))))


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


(defun sum-pp4_alt-psi_alt (x a b c d m n)
  (if (zp m)
      0
    (+ (pp4_alt-psi_alt (1- m) x a b c d n)
       (sum-pp4_alt-psi_alt x a b c d (1- m) n))))


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


(defun sum-eta_alt (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 3 (1- m))) (eta_alt (1- m) y))
	(sum-eta_alt (1- m) y))))


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


(defun sum-pp8_alt-eta_alt (x y m n)
  (if (zp m)
      0
    (+ (pp8_alt-eta_alt (1- m) x y n)
       (sum-pp8_alt-eta_alt x y (1- m) n))))


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
