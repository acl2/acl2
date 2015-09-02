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

(include-book "add")

(local (include-book "../lib3/top"))

(set-inhibit-warnings "theory")
(local (in-theory nil))


;;;**********************************************************************
;;;			Radix-4 Booth Encoding
;;;**********************************************************************


(defun theta (i y)
  (+ (bitn y (1- (* 2 i)))
     (bitn y (* 2 i))
     (* -2 (bitn y (1+ (* 2 i))))))


(defun sum-theta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (theta (1- m) y))
	(sum-theta (1- m) y))))



(defthm sum-theta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 2 m))))
	     (equal y (sum-theta m y)))
  :rule-classes ())


(defun bmux4 (zeta x n)
  (case zeta
    (1  x)
    (-1 (bits (lognot x) (1- n) 0))
    (2  (* 2 x))
    (-2 (bits (lognot (* 2 x)) (1- n) 0))
    (0  0)))

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


(defthm booth4-thm
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n)))
	     (= (+ (expt 2 n)
		   (sum-pp4 x m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x (sum-zeta m))
		   (- (* (expt 2 (* 2 (1- m))) (neg (zeta (1- m))))))))
  :rule-classes ())

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

(defun sum-pp4-theta (x y m n)
  (if (zp m)
      0
    (+ (pp4-theta (1- m) x y n)
       (sum-pp4-theta x y (1- m) n))))


(defthm booth4-corollary
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (+ (expt 2 n)
		   (sum-pp4-theta x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ())

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


(defun phi (i y)
  (if (= (bits (mu i y) 1 0) 3)
      -1
    (bits (mu i y) 1 0)))

(defthm phi-bnd
    (member (phi i y) '(-1 0 1 2)))

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
  :rule-classes())


(defthm phi-m-1
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (>= (phi (1- m) y) 0))
  :rule-classes())

(defun sum-phi (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (phi (1- m) y))
	(sum-phi (1- m) y))))


(defthm sum-phi-lemma
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (equal y (sum-phi m y)))
  :rule-classes ())

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

(defun sum-pp4-phi (x y m n)
  (if (zp m)
      0
    (+ (pp4-phi (1- m) x y n)
       (sum-pp4-phi x y (1- m) n))))


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
  :rule-classes ())

;;;**********************************************************************
;;;                Encoding Redundant Representations
;;;**********************************************************************


(defun gamma (i a b c)
   (if (zp i)
       (bitn c 0)
     (logior (bitn  a (+ -1  (* 2 i)))
 	     (bitn  b (+ -1  (* 2 i))))))

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

(defun psi (i a b c d)
  (if (not (natp i))
      0
    (+ (bits a (1+ (* 2 i)) (* 2 i))
       (bits b (1+ (* 2 i)) (* 2 i))
       (gamma i a b c)
       (delta i a b c d)
       (* -4 (+ (gamma (1+ i) a b c)
                (delta (1+ i) a b c d))))))


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
  :rule-classes ())


(defun sum-psi (m a b c d)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (psi (1- m) a b c d))
	(sum-psi (1- m) a b c d))))


(defthm sum-psi-lemma
    (implies (and (natp m)
                  (<= 1 M) ;; add
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1))
	     (equal (+ a b c d) (sum-psi m a b c d)))
  :rule-classes ())



(defthmd psi-bnd
  (and (integerp (psi i a b c d))
       (<= (psi i a b c d) 2)
       (>= (psi i a b c d) -2)))

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

(defun sum-pp4-psi (x a b c d m n)
  (if (zp m)
      0
    (+ (pp4-psi (1- m) x a b c d n)
       (sum-pp4-psi x a b c d (1- m) n))))



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
  :rule-classes ())

;;;**********************************************************************
;;;			Radix-8 Booth Encoding
;;;**********************************************************************



(defun eta (i y)
  (+ (bitn y (1- (* 3 i)))
     (bitn y (* 3 i))
     (* 2 (bitn y (1+ (* 3 i))))
     (* -4 (bitn y (+ 2 (* 3 i))))))


(defun sum-eta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 3 (1- m))) (eta (1- m) y))
	(sum-eta (1- m) y))))


(defthm sum-eta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 3 m))))
	     (equal y (sum-eta m y)))
  :rule-classes ())



;; (defun bmux8 (zeta x n)
;;   (case zeta
;;     (1  x)
;;     (-1 (bits (lognot x) (1- n) 0))
;;     (2  (* 2 x))
;;     (-2 (bits (lognot (* 2 x)) (1- n) 0))
;;     (3  (* 3 x))
;;     (-3 (bits (lognot (* 3 x)) (1- n) 0))
;;     (4  (* 4 x))
;;     (-4 (bits (lognot (* 4 x)) (1- n) 0))
;;     (0  0)))


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


(defthm booth8-thm
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2)))
	     (= (+ (expt 2 n)
		   (sum-pp8 x m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x (sum-xi m))
		   (- (* (expt 2 (* 3 (1- m))) (neg (xi (1- m))))))))
  :rule-classes ())

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

(defun sum-pp8-eta (x y m n)
  (if (zp m)
      0
    (+ (pp8-eta (1- m) x y n)
       (sum-pp8-eta x y (1- m) n))))


(defthm booth8-corollary
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2))
		  (bvecp y (1- (* 3 m))))
	     (= (+ (expt 2 n)
		   (sum-pp8-eta x y m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x y))))
  :rule-classes ())
