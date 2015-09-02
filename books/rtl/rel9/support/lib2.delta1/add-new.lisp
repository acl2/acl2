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

(include-book "round-new")

(local (include-book "add-new-proofs"))



(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;;;**********************************************************************
;;;                      Bit Vector Addition
;;;**********************************************************************

(defthm half-adder_alt
  (implies (and (bvecp u 1)
                (bvecp v 1))
           (equal (+ u v)
                  (cat_alt (logand u v) 1 (logxor u v) 1)))
  :rule-classes ())

(defthm add-2_alt
    (implies (and (natp x) (natp y))
	     (equal (+ x y)
		    (+ (logxor x y)
		       (* 2 (logand x y)))))
  :rule-classes ())

(defthm full-adder_alt
  (implies (and (bvecp u 1)
                (bvecp v 1)
                (bvecp w 1))
           (equal (+ u v w)
                  (cat_alt (logior (logand u v) (logior (logand u w) (logand v w))) 1
                       (logxor u (logxor v w)) 1)))
  :rule-classes ())

(defthm add-3_alt
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (= (+ x y z)
		(+ (logxor x (logxor y z))
		   (* 2 (logior (logand x y)
				(logior (logand x z)
					(logand y z)))))))
  :rule-classes ())


(defun rc-carry_alt (x y k)
  (if (zp k)
      0
    (logior (logand (bitn_alt x (1- k)) (bitn_alt y (1- k)))
	    (logior (logand (bitn_alt x (1- k)) (rc-carry_alt x y (1- k)))
		    (logand (bitn_alt y (1- k)) (rc-carry_alt x y (1- k)))))))



(defun rc-sum_alt (x y k)
  (if (zp k)
      0
    (cat_alt (logxor (bitn_alt x (1- k))
                     (logxor (bitn_alt y (1- k)) (rc-carry_alt x y (1- k))))
	 1
	 (rc-sum_alt x y (1- k))
	 (1- k))))


(defthm ripple-carry_alt
  (implies (and (natp x)
                (natp y)
                (natp n))
           (equal (+ (bits_alt x (1- n) 0) (bits_alt y (1- n) 0))
                  (cat_alt (rc-carry_alt x y n) 1 (rc-sum_alt x y n) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ripple-carry)))))


(defun gen_alt (x y i j)
  (declare (xargs :measure (nfix (1+ i))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn_alt x i) (bitn_alt y i))
	  (bitn_alt x i)
	(gen_alt x y (1- i) j))
    0))


(defun prop_alt (x y i j)
  (declare (xargs :measure (nfix (1+ i))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn_alt x i) (bitn_alt y i))
	  0
	(prop_alt x y (1- i) j))
    1))



(defthm bvecp-1-gen_alt
  (bvecp (gen_alt x y i j) 1)
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((gen_alt x y i j)))))

(defthm bvecp-1-prop_alt
  (bvecp (prop_alt x y i j) 1)
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((prop_alt x y i j)))))

(defthmd gen_alt-val
  (implies (and (natp j) (>= i j))
           (equal (gen_alt x y i j)
                  (if (>= (+ (bits_alt x i j) (bits_alt y i j))
                          (expt 2 (1+ (- i j))))
                      1
                    0)))
  :hints (("Goal" :use ((:instance gen-val)))))

(defthmd gen_alt-val-cor1
  (implies (natp j)
           (equal (gen_alt x y i j)
                  (bitn_alt (+ (bits_alt x i j) (bits_alt y i j))
			(1+ (- i j)))))
  :hints (("Goal" :use ((:instance gen-val-cor1)))))

(defthmd gen_alt-val-cor2
  (implies (and (natp x)
                (natp y)
		(natp i))
           (equal (+ (bits_alt x i 0) (bits_alt y i 0))
		  (+ (* (expt 2 (1+ i)) (gen_alt x y i 0))
		     (bits_alt (+ x y) i 0))))
  :hints (("Goal" :use ((:instance gen-val-cor2)))))


(defthm gen_alt-special-case
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (bitn_alt (+ (bits_alt x i j) (bits_alt y i j)) (- i j)) 0))
           (equal (gen_alt x y i j)
                  (logior (bitn_alt x i) (bitn_alt y i))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance gen-special-case)))))





(defthmd prop_alt-val
  (implies (and (integerp i) (natp j) (>= i j))
           (equal (prop_alt x y i j)
                  (if (= (+ (bits_alt x i j) (bits_alt y i j))
                         (1- (expt 2 (1+ (- i j)))))
                      1
                    0)))
  :hints (("Goal" :use ((:instance prop-val)))))


(defthmd prop_alt-as-logxor
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (natp x)
                (natp y))
           (equal (prop_alt x y i j)
                  (if (equal (logxor (bits_alt x i j) (bits_alt y i j))
                             (1- (expt 2 (1+ (- i j)))))
                      1
                    0)))
  :hints (("Goal" :use ((:instance prop-as-lxor)))))


(defthm gen_alt-extend
    (implies (and (integerp i)
		  (integerp j)
		  (integerp k)
		  (> i k)
		  (>= k j)
		  (>= j 0))
	     (equal (gen_alt x y i j)
		    (logior (gen_alt x y i (1+ k))
			    (logand (prop_alt x y i (1+ k))
				    (gen_alt x y k j)))))
    :rule-classes ()
    :hints (("Goal" :use ((:instance gen-extend)))))


(defthm gen_alt-extend-cor
  (implies (and (natp x)
                (natp y)
                (natp i)
                (natp j)
                (natp k)
                (> i k)
                (>= k j))
           (equal (gen_alt x y i j)
                  (bitn_alt (+ (bits_alt x i (1+ k))
                           (bits_alt y i (1+ k))
                           (gen_alt x y k j))
                        (- i k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance gen-extend-cor)))))

(defthm prop_alt-extend
    (implies (and (integerp i)
		  (integerp j)
		  (integerp k)
		  (> i k)
		  (>= k j)
		  (>= j 0))
	     (equal (prop_alt x y i j)
		    (logand (prop_alt x y i (1+ k))
			    (prop_alt x y k j))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance prop-extend)))))

(defthm bits_alt-sum
  (implies (and (integerp x) (integerp y))
           (equal (bits_alt (+ x y) i j)
                  (bits_alt (+ (bits_alt x i j)
                           (bits_alt y i j)
                           (gen_alt x y (1- j) 0))
                        (- i j) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-sum)))))

(defthmd bits_alt-sum-swallow
  (implies (and (equal (bitn_alt x k) 0)
                (natp x)
                (natp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= i j)
                (> j k)
                (>= k 0)
                (<= y (expt 2 k)))
           (equal (bits_alt (+ x y) i j)
                  (bits_alt x i j)))
  :hints (("Goal" :use ((:instance bits-sum-swallow)))))

(defthmd bits_alt-sum-cor
  (implies (and (integerp x)
                (integerp y)
                (>= i j)
                (>= j 0)
                (= (gen_alt x y i j) 0)
                (= (gen_alt x y (1- j) 0) 0))
           (equal (bits_alt (+ x y) i j)
                  (+ (bits_alt x i j) (bits_alt y i j))))
  :hints (("Goal" :use ((:instance bits-sum-cor)))))

(defthm bits_alt-sum-3
  (implies (and (integerp x) (integerp y) (integerp z))
           (equal (bits_alt (+ x y z) i j)
                  (bits_alt (+ (bits_alt x i j)
                           (bits_alt y i j)
                           (bits_alt z i j)
                           (gen_alt x y (1- j) 0)
                           (gen_alt (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-sum-3)))))



(defthm bits_alt-sum-plus-1
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i)
		  (integerp j)
		  (>= i j)
		  (>= j 0))
	     (equal (bits_alt (+ 1 x y) i j)
		    (bits_alt (+ (bits_alt x i j)
			     (bits_alt y i j)
			     (logior (prop_alt x y (1- j) 0)
				     (gen_alt x y (1- j) 0) ))
			  (- i j) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-sum-plus-1)))))


(defthmd logand-gen_alt-0
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (logand (bits_alt x i j) (bits_alt y i j)) 0))
           (equal (gen_alt x y i j) 0))
  :hints (("Goal" :use ((:instance land-gen-0)))))

(defthm logand-gen_alt-0-cor
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (logand x y) 0))
           (equal (bits_alt (+ x y) i j)
                  (+ (bits_alt x i j) (bits_alt y i j))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-gen_alt-0)
                        (:instance logand-gen_alt-0
                                   (i (+ -1 j))
                                   (j 0))
                        (:instance bits_alt-sum-cor)
                        (:instance bits_alt-logand)
                        (:instance bits_alt-logand
                                   (i (+ -1 j))
                                   (j 0))))))



(defthmd gen_alt-plus
  (implies (and (natp x)
                (natp y)
		(natp k)
		(bvecp z (1+ k))
		(= (logand z y) 0)
		(= (gen_alt x y k 0) 1))
	   (equal (gen_alt (+ x y) z k 0) 0))
  :hints (("Goal" :use ((:instance gen-plus)
                        (:instance land-logand-g
                                   (x z)
                                   (y y)
                                   (n (+ 1 k)))
                        (:instance bits_alt-logand
                                   (x z)
                                   (y y)
                                   (i k)
                                   (j 0))))))



(defthmd gen_alt-extend-3
    (implies (and (natp i)
		  (natp j)
		  (> i j)
		  (natp x)
		  (natp y)
		  (bvecp z (1+ j))
		  (= (logand y z) 0))
	     (equal (gen_alt (+ x y) z i 0)
		    (logand (prop_alt x y i (1+ j))
			    (gen_alt (+ x y) z j 0))))
    :hints (("Goal" :use ((:instance gen-extend-3)
                          (:instance land-logand-g
                                     (x z)
                                     (y y)
                                     (n (+ 1 j)))
                        (:instance bits_alt-logand
                                   (x z)
                                   (y y)
                                   (i j)
                                   (j 0))))))


;;;**********************************************************************
;;;                  Leading One Prediction
;;;**********************************************************************

(defund lop_alt (a b d k)
  (let ((c (- (bitn_alt a (1- k)) (bitn_alt b (1- k)))))
    (if (and (integerp k) (>= k 0))
	(if (= k 0)
	    0
	  (if (= d 0)
	      (lop_alt a b c (1- k))
	    (if (= d (- c))
		(lop_alt a b (- c) (1- k))
	      k)))
      0)))

(defthm lop_alt-bnds
  (implies (and (integerp a)
                (integerp b)
                (integerp n)
                (>= a 0)
                (>= b 0)
                (>= n 0)
                (not (= a b))
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (or (= (lop_alt a b 0 n) (expo (- a b)))
               (= (lop_alt a b 0 n) (1+ (expo (- a b))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lop-bnds)))))



;;;

(defthm lop_alt-thm-1
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (= e (expo a))
		  (< (expo b) e)
		  (= lambda
		     (logior (* 2 (mod a (expt 2 e)))
			     (bits_alt (lognot (* 2 b)) e 0))))
	     (or (= (expo (- a b)) (expo lambda))
		 (= (expo (- a b)) (1- (expo lambda)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lop-thm-1)))))



(defun lamt_alt (a b e)
  (logxor a (bits_alt (lognot b) e 0)))


(defun lamg_alt (a b e)
  (logand a (bits_alt (lognot b) e 0)))


(defun lamz_alt (a b e)
  (bits_alt (lognot (logior a (bits_alt (lognot b) e 0))) e 0))



(defun lam1_alt (a b e)
  (logand (bits_alt (lamt_alt a b e) e 2)
	  (logand (bits_alt (lamg_alt a b e) (1- e) 1)
		  (bits_alt (lognot (lamz_alt a b e)) (- e 2) 0))))


(defun lam2_alt (a b e)
  (logand (bits_alt (lognot (lamt_alt a b e)) e 2)
	  (logand (bits_alt (lamz_alt a b e) (1- e) 1)
		  (bits_alt (lognot (lamz_alt a b e)) (- e 2) 0))))


(defun lam3_alt (a b e)
  (logand (bits_alt (lamt_alt a b e) e 2)
	  (logand (bits_alt (lamz_alt a b e) (1- e) 1)
		  (bits_alt (lognot (lamg_alt a b e)) (- e 2) 0))))


(defun lam4_alt (a b e)
  (logand (bits_alt (lognot (lamt_alt a b e)) e 2)
	  (logand (bits_alt (lamg_alt a b e) (1- e) 1)
		  (bits_alt (lognot (lamg_alt a b e)) (- e 2) 0))))


(defun lam0_alt (a b e)
  (logior (lam1_alt a b e)
	  (logior (lam2_alt a b e)
		  (logior (lam3_alt a b e)
			  (lam4_alt a b e)))))



(defun lamb_alt (a b e)
  (+ (* 2 (lam0_alt a b e))
     (bitn_alt (lognot(lamt_alt a b e)) 0)))


(defthm lop_alt-thm-2
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (not (= a b))
		  (= e (expo a))
		  (= e (expo b))
		  (> e 1))
	     (and (not (= (lamb_alt a b e) 0))
		  (or (= (expo (- a b)) (expo (lamb_alt a b e)))
		      (= (expo (- a b)) (1- (expo (lamb_alt a b e)))))))
  :rule-classes ())



;;;**********************************************************************
;;;                    Trailing One Prediction
;;;**********************************************************************

(defthm top-thm-1-alt
  (implies (and (natp n)
                (natp k)
                (< k n)
                (integerp a)
                (integerp b))
           (equal (equal (bits_alt (+ a b 1) k 0) 0)
		  (equal (bits_alt (lognot (logxor a b)) k 0) 0)))
  :rule-classes ())


(defthm top-thm-2-alt
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n)
                (or (equal c 0) (equal c 1)))
           (equal (equal (bits_alt (+ a b c) k 0) 0)
                  (equal (bits_alt (logxor (logxor a b)
                                       (cat_alt (logior a b) n c 1))
                               k 0)
                         0)))
  :rule-classes ())
