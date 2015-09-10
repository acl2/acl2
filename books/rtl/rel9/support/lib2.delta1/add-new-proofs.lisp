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

(include-book "round-new")

(local (include-book "../lib2/top"))




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
;;;                      Bit Vector Addition
;;;**********************************************************************

(encapsulate ()
    (local (include-book "../../arithmetic/top"))

(local
 (defthm bvecp-fl-1/2
   (implies (bvecp x (+ 1 n))
            (BVECP (FL (* 1/2 X)) n))
   :hints (("Goal" :in-theory (e/d (bvecp
                                    expt-2-reduce-leading-constant) ())))))

(local
 (defthm bvecp-mod-2
   (implies (integerp x)
            (BVECP (MOD X 2) 1))
   :hints (("Goal" :in-theory (e/d (bvecp) ())))))



(local
 (defthm land-logand
   (implies (and (bvecp x n)
                 (bvecp y n)
                 (natp n))
            (equal (land x y n)
                   (logand x y)))
   :hints (("Goal" :in-theory (e/d (binary-land)
                                   ())
            :induct (binary-land x y n))
           ("Subgoal *1/4" :use ((:instance logand-def
                                            (i x)
                                            (j y)))))))



(local
 (defthm lxor-logxor
   (implies (and (bvecp x n)
                 (bvecp y n)
                 (natp n))
            (equal (lxor x y n)
                   (logxor x y)))
   :hints (("Goal" :in-theory (e/d (binary-lxor)
                                   ())
            :induct (binary-lxor x y n))
           ("Subgoal *1/4" :use ((:instance logxor-def
                                            (i x)
                                            (j y)))))))
(local
 (defthm logior-1-x
   (implies (bvecp x 1)
            (equal (logior 1 x) 1))
   :hints (("Goal" :in-theory (e/d (bvecp) ())
            :cases ((equal x 0))))))


(local
 (defthm lior-logior
   (implies (and (bvecp x n)
                 (bvecp y n)
                 (natp n))
            (equal (lior x y n)
                   (logior x y)))
   :hints (("Goal" :in-theory (e/d (binary-lior)
                                   ())
            :induct (binary-lior x y n))
           ("Subgoal *1/4" :use ((:instance logior-def
                                            (i x)
                                            (j y)))))))

(defthm half-adder_alt
  (implies (and (bvecp u 1)
                (bvecp v 1))
           (equal (+ u v)
                  (cat_alt (logand u v) 1 (logxor u v) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance half-adder)))))

(local
 (defthm bvecp-1-plus
   (implies (natp x)
            (bvecp x (+ 1 (expo x))))
   :hints (("Goal" :in-theory (e/d (bvecp) ())))))


(local
 (defthm bvecp-max-1
   (implies (and (natp x)
                 (integerp m))
            (bvecp x (max (+ 1 (expo x)) m)))
   :hints (("Goal" :use ((:instance bvecp-monotone
                                    (x x)
                                    (m m)
                                    (n (+ 1 (expo x)))))))))



(local
 (defthm bvecp-max-2
   (implies (and (natp x)
                 (integerp m))
            (bvecp x (max m (+ 1 (expo x)))))
   :hints (("Goal" :use ((:instance bvecp-monotone
                                    (x x)
                                    (m m)
                                    (n (+ 1 (expo x)))))))))



(defthm add-2_alt
    (implies (and (natp x) (natp y))
	     (equal (+ x y)
		    (+ (logxor x y)
		       (* 2 (logand x y)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d () (max))
           :use ((:instance add-2
                            (n (max (+ 1 (expo x))
                                    (+ 1 (expo y)))))))))

(defthm full-adder_alt
  (implies (and (bvecp u 1)
                (bvecp v 1)
                (bvecp w 1))
           (equal (+ u v w)
                  (cat_alt (logior (logand u v) (logior (logand u w) (logand v w))) 1
                       (logxor u (logxor v w)) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance full-adder)))))


(local
 (defthm bvecp-max-backchain-1
   (implies (and (natp x)
                 (integerp m)
                 (integerp n)
                 (bvecp x n))
            (bvecp x (MAX n m)))
   :hints (("Goal" :use ((:instance bvecp-monotone
                                    (x x)
                                    (m m)
                                    (n n)))))))



(local
 (defthm bvecp-max-backchain-2
   (implies (and (natp x)
                 (integerp m)
                 (integerp n)
                 (bvecp x m))
            (bvecp x (MAX n m)))
   :hints (("Goal" :use ((:instance bvecp-monotone
                                    (x x)
                                    (m n)
                                    (n m)))))))



(defthm add-3_alt
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (= (+ x y z)
		(+ (logxor x (logxor y z))
		   (* 2 (logior (logand x y)
				(logior (logand x z)
					(logand y z)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d () (max))
           :use ((:instance add-3
                            (n (max (+ 1 (expo x))
                                    (max (+ 1 (expo y))
                                         (+ 1 (expo z))))))))))

)

(defun rc-carry_alt (x y k)
  (if (zp k)
      0
    (logior (logand (bitn_alt x (1- k)) (bitn_alt y (1- k)))
	    (logior (logand (bitn_alt x (1- k)) (rc-carry_alt x y (1- k)))
		    (logand (bitn_alt y (1- k)) (rc-carry_alt x y (1- k)))))))



(local (include-book "../../arithmetic/top"))

(local
 (defthm logand-1-x-g
   (implies (integerp x)
            (equal (LOGAND 1 x)
                   (bitn x 0)))
   :hints (("Goal" :in-theory (e/d (logand bitn mod
                                           evenp
                                           bits-mod)
                                   (bits-n-n-rewrite))))))




(local
 (encapsulate ()
              (local (include-book "../support/logior"))
              (defthm logior-1-x
                (implies (bvecp x 1)
                         (equal (logior 1 x) 1)))))

(local
 (defthm rc-carry_alt-is-rc-carry
   (equal (rc-carry_alt x y k)
          (rc-carry x y k))
   :hints (("Goal" :induct (rc-carry_alt x y k))
           ("Subgoal *1/2" :use ((:instance bitn-0-1
                                            (x x)
                                            (n (+ -1 k)))
                                 (:instance bitn-0-1
                                            (x y)
                                            (n (+ -1 k))))))))

(defun rc-sum_alt (x y k)
  (if (zp k)
      0
    (cat_alt (logxor (bitn_alt x (1- k))
                     (logxor (bitn_alt y (1- k)) (rc-carry_alt x y (1- k))))
	 1
	 (rc-sum_alt x y (1- k))
	 (1- k))))




(local
 (defthm logxor-1-x-g
   (implies (bvecp x 1)
            (equal (LOGXOR 1 x)
                   (lnot x 1)))
   :hints (("Goal" :in-theory (enable bvecp)
            :cases ((equal x 0))))))

(local
 (defthm lxor-1
   (implies (case-split (bvecp y 1))
            (equal (lxor 1 y 1)
                   (lnot y 1)))
   :hints (("Goal" :in-theory (enable bvecp)
            :cases ((equal x 0))))))



(local
 (defthm lxor-0-g
   (implies (case-split (bvecp y 1))
            (equal (lxor 0 y 1)
                   y))
   :hints (("Goal" :in-theory (enable bvecp)
            :cases ((equal x 0))))))

(local
 (defthm bvecp-1-rc-carry
   (bvecp (rc-carry x y k) 1)))

(local
 (defthm rc-sum_alt-is-rc-sum
   (equal (rc-sum_alt x y k)
          (rc-sum x y k))
   :hints (("Goal" :induct (rc-sum_alt x y k))
           ("Subgoal *1/2" :use ((:instance bitn-0-1
                                            (x x)
                                            (n (+ -1 k)))
                                 (:instance bitn-0-1
                                            (x y)
                                            (n (+ -1 k))))))))


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


(local
 (defthm gen_alt-is-gen
   (equal (gen_alt x y i j)
          (gen x y i j))))




(defun prop_alt (x y i j)
  (declare (xargs :measure (nfix (1+ i))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn_alt x i) (bitn_alt y i))
	  0
	(prop_alt x y (1- i) j))
    1))


(local
 (defthm prop_alt-is-prop
   (equal (prop_alt x y i j)
          (prop x y i j))))



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


(local
 (defthm lior-bitn-is
   (equal (lior (bitn x i)
                (bitn y i)
                1)
          (logior (bitn x i)
                  (bitn y i)))
   :hints (("Goal" :use ((:instance bitn-0-1
                                    (x x)
                                    (n i))
                         (:instance bitn-0-1
                                    (x y)
                                    (n i)))))))


;;                                       (LIOR (BITN X I) (BITN Y I) 1)))



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


(local
 (defthm bvecp-fl-1/2
   (implies (bvecp x (+ 1 n))
            (BVECP (FL (* 1/2 X)) n))
   :hints (("Goal" :in-theory (e/d (bvecp
                                    expt-2-reduce-leading-constant) ())))))

(local
 (defthm bvecp-mod-2
   (implies (integerp x)
            (BVECP (MOD X 2) 1))
   :hints (("Goal" :in-theory (e/d (bvecp) ())))))

(local
 (defthm lxor-bits-are-g
   (implies (and (bvecp x n)
                 (bvecp y n)
                 (natp n))
            (equal (lxor x y n)
                   (logxor x y)))
   :hints (("Goal" :in-theory (e/d (binary-lxor)
                                   ())
            :induct (binary-lxor x y n))
           ("Subgoal *1/4" :use ((:instance logxor-def
                                            (i x)
                                            (j y)))))))



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




(local
 (defthm lior-logior
   (implies (and (bvecp x n)
                 (bvecp y n)
                 (natp n))
            (equal (lior x y n)
                   (logior x y)))
   :hints (("Goal" :in-theory (e/d (binary-lior)
                                   ())
            :induct (binary-lior x y n))
           ("Subgoal *1/4" :use ((:instance logior-def
                                            (i x)
                                            (j y)))))))



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



(local
 (defthm land-logand
   (implies (and (bvecp x n)
                 (bvecp y n)
                 (natp n))
            (equal (land x y n)
                   (logand x y)))
   :hints (("Goal" :in-theory (e/d (binary-land)
                                   ())
            :induct (binary-land x y n))
           ("Subgoal *1/4" :use ((:instance logand-def
                                            (i x)
                                            (j y)))))))



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



;; (local (include-book "../../arithmetic/top"))

;; (local
;;  (defthmd bitn-mod-2
;;    (implies (integerp x)
;;             (equal (bitn (mod x 2) 0)
;;                    (mod x 2)))
;;    :hints (("Goal" :in-theory (e/d (bitn bits-mod)
;;                                    (bits-n-n-rewrite))))))

(local
 (defthm bits-land-specific
   (implies (and (natp n)
                 (> n 0))
            (equal (LAND (BITS X (+ -1 N) 0)
                         (BITS Y (+ -1 N) 0)
                         N)
                   (land x y n)))
   :hints (("Goal" :cases ((equal (bits (land x y n) (+ -1 n) 0)
                                  (land x y n))))
           ("Subgoal 2" :cases ((bvecp (land x y n) n))
            :in-theory (e/d () (bits-land))))))




(local
 (defthmd land-logand-g
   (implies (and (natp n)
                 (> n 0)
                 (natp x)
                 (natp y))
            (equal (land x y n)
                   (logand (bits x (+ -1 n) 0)
                           (bits y (+ -1 n) 0))))
   :hints (("Goal" :use ((:instance land-logand
                                    (x (bits x (+ -1 n) 0))
                                    (y (bits y (+ -1 n) 0))
                                    (n n)))
            :in-theory (e/d (bits-land-specific)
                            (land-logand))))))




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

(local
 (defthm lop_alt-is-lop
   (equal (lop_alt a b d k)
          (lop a b d k))
   :hints (("Goal" :in-theory (e/d (lop_alt lop) ())))))



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


;; (defthm olop-thm-1
;;     (implies (and (integerp a)
;; 		  (> a 0)
;; 		  (integerp b)
;; 		  (> b 0)
;; 		  (= e (expo a))
;; 		  (< (expo b) e)
;; 		  (= lambda
;; 		     (logior (* 2 (mod a (expt 2 e)))
;; 			     (lnot (* 2 b) (1+ e)))))
;; 	     (or (= (expo (- a b)) (expo lambda))
;; 		 (= (expo (- a b)) (1- (expo lambda)))))
;;   :rule-classes ()
;;   :hints (("Goal" :in-theory (disable logior lop)
;; 		  :use (lop2-27
;; 			(:instance expo-upper-bound (x b))
;; 			(:instance expo-monotone (x 1) (y a))
;; 			(:instance expt-weak-monotone (n (1+ (expo b))) (m e))
;; 			(:instance expo-upper-bound (x a))
;; 			(:instance lop-bnds (n (1+ e)))))))
;;


;; (local
;;  (defthm lior-logior
;;    (implies (and (bvecp x n)
;;                  (bvecp y n)
;;                  (natp n))
;;             (equal (lior x y n)
;;                    (logior x y)))
;;    :hints (("Goal" :in-theory (e/d (binary-lior)
;;                                    ())
;;             :induct (binary-lior x y n))
;;            ("Subgoal *1/4" :use ((:instance logior-def
;;                                             (i x)
;;                                             (j y)))))))

(local
 (defthm bvecp-2-muliply
   (implies (integerp a)
            (bvecp (* 2 (mod a (expt 2 e))) (+ 1 e)))
   :hints (("Goal" :in-theory (e/d (bvecp
                                    expt-2-reduce-leading-constant
                                    ) ())))))



(local
 (defund bvequal (v1 v2 n)
  (equal (sumbits v1 n)
         (sumbits v2 n))))


(local
 (defthm bvequal-then-equal
  (implies (and (bvequal x y n)
                (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal x y))
  :hints (("Goal" :use ((:instance sumbits-thm
                                   (x x))
                        (:instance sumbits-thm
                                   (x y)))
           :in-theory (enable bvequal)))
  :rule-classes nil))

(local
 (encapsulate ()
              (local (include-book "log-new"))


              (defthmd bitn-lognot-g
                (implies (and (integerp x)
                              (integerp n)
                              (>= n 0))
                         (not (equal (bitn (lognot x) n)
                                     (bitn x n))))
                :hints (("Goal" :cases ((equal n 0)))
                        ("Subgoal 2" :use ((:instance bitn_alt-lognot)))
                        ("Subgoal 1" :in-theory (e/d (lognot bitn-def mod)
                                                     ()))))
              ))




(local
 (defthmd bitn-lnot-lognot-bvequal-lemma
   (implies (and (integerp x)
                 (natp n)
                 (> n 0)
                 (natp n)
                 (natp i)
                 (<= i (+ -1 n)))
            (equal (bitn (lnot x n) i)
                   (bitn (bits (lognot x) (+ -1 n) 0) i)))
   :hints (("Goal" :in-theory (e/d (bitn-lnot) ())
            :use ((:instance bitn-lognot-g
                             (n i))
                  (:instance bitn-0-1
                             (x x)
                             (n i)))))))


(local
 (defthm lnot-lognot-bvequal
   (implies (and (integerp x)
                 (natp n)
                 (> n 0)
                 (natp n)
                 (natp i)
                 (<= i n))
            (bvequal (lnot x n)
                     (bits (lognot x) (+ -1 n) 0)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal bitn-lnot-lognot-bvequal-lemma) (bitn-bits))))))



(local
 (defthm lnot-lognot
  (implies (and (natp n)
                (> n 0)
                (integerp x))
           (equal (lnot x n)
                  (bits (lognot x) (+ -1 n) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (lnot x n))
                                   (y (bits (lognot x) (+ -1 n) 0))
                                   (n n)))
           :in-theory (e/d (lnot-lognot-bvequal) ())))))



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


;;;
;;;
;;; We need set of theorem about how lxor is equal logxor
;;;
;;;                                  land is logand
;;;
;;

(defun lamt_alt (a b e)
  (logxor a (bits_alt (lognot b) e 0)))


(local
 (encapsulate ()
              (local (include-book "log-new-proofs"))

              (defthmd bitn_alt-logxor
                (implies (and (case-split (integerp x))
                              (case-split (integerp y))
                              (case-split (integerp n)))
                         (equal (bitn_alt (logxor x y) n)
                                (logxor (bitn_alt x n) (bitn_alt y n)))))
              ))






(local
 (defthmd bitn-lxor-logxor-bvequal-lemma
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i (+ -1 n)))
            (equal (bitn (lxor x y n) i)
                   (bitn (bits (logxor x y) (+ -1 n)  0) i)))
   :hints (("Goal" :in-theory (e/d (bitn-lxor) ())
            :use ((:instance bitn_alt-logxor
                             (n i))
                  (:instance bitn-0-1
                             (x x)
                             (n i))
                  (:instance bitn-0-1
                             (x y)
                             (n i)))))))




(local
 (defthmd lxor-logxor-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i n))
            (bvequal (lxor x y n)
                     (bits (logxor x y) (+ -1 n)  0)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal bitn-lxor-logxor-bvequal-lemma)
                                   ())))))

(local
(defthm lxor-logxor
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (lxor x y n)
                  (bits (logxor x y) (+ -1 n) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (lxor x y n))
                                   (y (bits (logxor x y) (+ -1 n) 0))
                                   (n n)))
           :in-theory (e/d (lxor-logxor-bvequal) ())))))



(local
 (defthm lamt_alt-is-lamt
   (implies (and (natp e)
                 (integerp a)
                 (integerp b))
            (equal (bits (lamt_alt a b e) e 0)
                   (lamt a b e)))
   :hints (("Goal" :in-theory (e/d (lxor-logxor
                                    lnot-lognot)
                                   ())
            :use ((:instance bits_alt-logxor
                             (x a)
                             (y (bits (lognot b) e 0))
                             (i e)
                             (j 0)))))))





(local
 (defthm lamt_alt-is-lamt-g
   (implies (and (natp e)
                 (natp i)
                 (<= i e)
                 (integerp a)
                 (integerp b))
            (equal (bits (lamt_alt a b e) e i)
                   (bits (lamt a b e) e i)))
   :hints (("Goal" :in-theory (e/d (lxor-logxor
                                    lnot-lognot)
                                   ())
            :use ((:instance bits_alt-logxor
                             (x a)
                             (y (bits (lognot b) e 0))
                             (i e)
                             (j i)))))))



(defun lamg_alt (a b e)
  (logand a (bits_alt (lognot b) e 0)))




(local
 (encapsulate ()
              (local (include-book "log-new-proofs"))

              (defthmd bitn_alt-logand
                (implies (and (integerp x)
                              (integerp y)
                              (integerp n))
                         (equal (bitn_alt (logand x y) n)
                                (logand (bitn_alt x n) (bitn_alt y n)))))
              ))



(local
 (defthmd bitn-land-logand-bvequal-lemma
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i (+ -1 n)))
            (equal (bitn (land x y n) i)
                   (bitn (bits (logand x y) (+ -1 n)  0) i)))
   :hints (("Goal" :in-theory (e/d (bitn-land) ())
            :use ((:instance bitn_alt-logand
                             (n i))
                  (:instance bitn-0-1
                             (x x)
                             (n i))
                  (:instance bitn-0-1
                             (x y)
                             (n i)))))))




(local
 (defthmd land-logand-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i n))
            (bvequal (land x y n)
                     (bits (logand x y) (+ -1 n)  0)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal bitn-land-logand-bvequal-lemma)
                                   ())))))


(local
 (defthmd land-logand-g2
   (implies (and (natp n)
                 (> n 0)
                 (integerp x)
                (integerp y))
            (equal (land x y n)
                  (bits (logand x y) (+ -1 n) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (land x y n))
                                   (y (bits (logand x y) (+ -1 n) 0))
                                   (n n)))
           :in-theory (e/d (land-logand-bvequal) ())))))



;; (defthm logand-bvecp-g
;;   (implies (and (natp n)
;;                 (bvecp x n)
;;                 (integerp y))
;;            (bvecp (logand x y) n))
;;   :hints (("Goal" :use ((:instance logand-bnd))
;;            :in-theory (e/d (bvecp) ()))))

;; (i-am-here) ;; Mon Feb 16 14:49:46 2009

(local
 (defthm lamg_alt-is-lamg
   (implies (and (natp e)
                 (integerp a)
                 (integerp b))
            (equal (lamg_alt a b e)
                   (lamg a b e)))
   :hints (("Goal" :in-theory (e/d (land-logand
                                    land-logand-g2
                                    lnot-lognot)
                                   ())
            :use ((:instance bits_alt-logand
                             (x a)
                             (y (bits (lognot b) e 0))
                             (i e)
                             (j 0)))
            :cases ((bvecp (logand a (bits (lognot b) e 0)) (+ 1 e))))
           ("Subgoal 2" :use ((:instance logand-bvecp-g
                                         (x (bits (lognot b) e 0))
                                         (y a)
                                         (n (+ 1 e))))
            :in-theory (e/d (logand-bvecp-g) ())))))




(defun lamz_alt (a b e)
  (bits_alt (lognot (logior a (bits_alt (lognot b) e 0))) e 0))




(local
 (encapsulate ()
              (local (include-book "log-new-proofs"))

              (defthmd bitn_alt-logior
                (implies (and (integerp x)
                              (integerp y)
                              (integerp n))
                         (equal (bitn_alt (logior x y) n)
                                (logior (bitn_alt x n) (bitn_alt y n)))))
              ))



(local
 (defthmd bitn-lior-logior-bvequal-lemma
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i (+ -1 n)))
            (equal (bitn (lior x y n) i)
                   (bitn (bits (logior x y) (+ -1 n)  0) i)))
   :hints (("Goal" :in-theory (e/d (bitn-lior) ())
            :use ((:instance bitn_alt-logior
                             (n i))
                  (:instance bitn-0-1
                             (x x)
                             (n i))
                  (:instance bitn-0-1
                             (x y)
                             (n i)))))))





(local
 (defthmd lior-logior-bvequal
   (implies (and (integerp x)
                 (integerp y)
                 (natp n)
                 (> n 0)
                 (natp i)
                 (<= i n))
            (bvequal (lior x y n)
                     (bits (logior x y) (+ -1 n)  0)
                     i))
   :hints (("Goal" :in-theory (e/d (bvequal bitn-lior-logior-bvequal-lemma)
                                   ())))))




(local
 (defthmd lior-logior-g
   (implies (and (natp n)
                 (> n 0)
                 (integerp x)
                 (integerp y))
            (equal (lior x y n)
                   (bits (logior x y) (+ -1 n) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (lior x y n))
                                   (y (bits (logior x y) (+ -1 n) 0))
                                   (n n)))
           :in-theory (e/d (lior-logior-bvequal) ())))))


(local
 (defthmd bits-lognot-is-specific
   (implies (and (integerp x)
                 (natp e))
            (equal  (bits (lognot (bits x e 0)) e 0)
                    (bits (lognot x) e 0)))
   :hints (("Goal" :in-theory (e/d (lognot bits-mod mod) ())))))



(local
 (defthm lamz_alt-is-lamz
   (implies (and (natp e)
                 (integerp a)
                 (integerp b))
            (equal (lamz_alt a b e)
                   (lamz a b e)))
   :hints (("Goal" :in-theory (e/d (lnot-lognot lior-logior-g
                                                bits-lognot-is-specific
                                                ) ())))))



(defun lam1_alt (a b e)
  (logand (bits_alt (lamt_alt a b e) e 2)
	  (logand (bits_alt (lamg_alt a b e) (1- e) 1)
		  (bits_alt (lognot (lamz_alt a b e)) (- e 2) 0))))

(local
 (defthm lam1_alt-is-lam1
   (implies (and (integerp a)
                 (integerp b)
                 (natp e))
            (equal (lam1_alt a b e)
                   (lam1 a b e)))
   :hints (("Goal" :in-theory (e/d (land-logand-g2
                                    bits-lognot-is-specific
                                    lnot-lognot)
                                   (lamg_alt
                                    lamz_alt
                                    lamt_alt
                                    lamt
                                    lamg
                                    lamz))
            :cases ((<= 2 e))))))



(defun lam2_alt (a b e)
  (logand (bits_alt (lognot (lamt_alt a b e)) e 2)
	  (logand (bits_alt (lamz_alt a b e) (1- e) 1)
		  (bits_alt (lognot (lamz_alt a b e)) (- e 2) 0))))



(local
 (defthmd bits-bits-specific
   (implies (and (natp e)
                 (natp i)
                 (> i 0)
                 (<= i e))
            (equal (bits (lognot x) e i)
                   (bits (bits (lognot x) e 0) e i)))))


(local
 (defthmd bits-lognot-is-specific-2
   (implies (and (integerp x)
                 (natp e)
                 (natp i)
                 (<= i e))
            (equal  (bits (lognot (bits x e 0)) e  i)
                    (bits (lognot x) e i)))
   :hints (("Goal" :in-theory (e/d (bits-bits-specific
                                    bits-lognot-is-specific)
                                   (bits-bits))
            :cases ((equal i 0))))))




;;               (defthmd bitn-lognot-g
;;                 (implies (and (integerp x)
;;                               (integerp n)
;;                               (>= n 0))
;;                          (not (equal (bitn (lognot x) n)
;;                                      (bitn x n))))
;;                 :hints (("Goal" :cases ((equal n 0)))
;;                         ("Subgoal 2" :use ((:instance bitn_alt-lognot)))
;;                         ("Subgoal 1" :in-theory (e/d (lognot bitn-def mod)
;;                                                      ()))))



(local
 (defthm bitn-bits-lognot-bits-lognot-bvequal-lemma
   (implies (and (integerp x)
                 (natp e)
                 (natp i)
                 (<= i e)
                 (natp j)
                 (<= j (+ e (* -1 i))))
            (equal (bitn (bits (lognot (bits x e 0)) e i) j)
                   (bitn (bits (lognot (bits x e i))
                               (+ e (* -1 i))
                               0)
                         j)))
   :hints (("Goal" :in-theory (e/d (bitn-bits) ())
            :use ((:instance bitn-lognot-g
                             (x (BITS X E 0))
                             (n (+ i j)))
                  (:instance bitn-lognot-g
                             (x (BITS X E i))
                             (n j))
                  (:instance bitn-0-1
                             (x x)
                             (n (+ i j))))))))







(local
 (defthm bits-lognot-bits-lognot-bvequal
   (implies (and (integerp x)
                 (natp e)
                 (natp i)
                 (<= i e)
                 (natp j)
                 (<= j (+ 1  e (* -1 i))))
            (bvequal (bits (lognot (bits x e 0))
                           e i)
                     (bits (lognot (bits x e i))
                           (+ e (* -1 i))
                           0)
                     j))
   :hints (("Goal" :in-theory (e/d (bvequal
                                    bitn-bits-lognot-bits-lognot-bvequal-lemma
                                    ) ())))))



(local
 (defthmd bits-lognot-is-specific-3
   (implies (and (integerp x)
                 (natp e)
                 (natp i)
                 (<= i e))
            (equal  (bits (lognot (bits x e 0)) e  i)
                    (bits (lognot (bits x e i)) (+ e (* -1 i)) 0)))
  :hints (("Goal" :use ((:instance bvequal-then-equal
                                   (x (bits (lognot (bits x e 0)) e  i))
                                   (y (bits (lognot (bits x e i)) (+ e (* -1 i)) 0))
                                   (n (+ 1 e (* -1 i)))))
           :in-theory (e/d (bits-lognot-bits-lognot-bvequal) ())))))










(local
 (defthm lam2_alt-is-lam2
   (implies (and (integerp a)
                 (integerp b)
                 (natp e))
            (equal (lam2_alt a b e)
                   (lam2 a b e)))
   :hints (("Goal" :in-theory (e/d (land-logand-g2
                                    bits-lognot-is-specific
                                    lnot-lognot)
                                   (lamz_alt
                                    lamt_alt
                                    lamt
                                    lamz
                                    bits-bits))
            :cases ((<= 2 e)))
           ("Subgoal 1" :use ((:instance bits-lognot-is-specific-2
                                         (i 2)
                                         (x (LAMT_ALT A B E)))
                              (:instance bits-lognot-is-specific-3
                                         (x (lamt a b e))
                                         (i 2)))))))


(defun lam3_alt (a b e)
  (logand (bits_alt (lamt_alt a b e) e 2)
	  (logand (bits_alt (lamz_alt a b e) (1- e) 1)
		  (bits_alt (lognot (lamg_alt a b e)) (- e 2) 0))))


;; (defthm bvecp-lamg
;;   (implies (and (equal n (+ 1 e))
;;                 (natp e))
;;            (bvecp (lamg a b e) n)))

(local
 (defthm lam3_alt-is-lam3
   (implies (and (integerp a)
                 (integerp b)
                 (natp e))
            (equal (lam3_alt a b e)
                   (lam3 a b e)))
   :hints (("Goal" :in-theory (e/d (land-logand-g2
                                    lnot-lognot)
                                   (lamz_alt
                                    lamg_alt
                                    lamt_alt
                                    lamt
                                    lamg
                                    lamz))
            :cases ((<= 2 e)))
           ("Subgoal 1" :use ((:instance bits-lognot-is-specific-2
                                         (i 0)
                                         (e (+ -2 e))
                                         (x (LAMG A B E))))))))





(defun lam4_alt (a b e)
  (logand (bits_alt (lognot (lamt_alt a b e)) e 2)
	  (logand (bits_alt (lamg_alt a b e) (1- e) 1)
		  (bits_alt (lognot (lamg_alt a b e)) (- e 2) 0))))



(local
 (defthm lam4_alt-is-lam4
   (implies (and (integerp a)
                 (integerp b)
                 (natp e))
            (equal (lam4_alt a b e)
                   (lam4 a b e)))
   :hints (("Goal" :in-theory (e/d (land-logand-g2
                                    lnot-lognot)
                                   (lamz_alt
                                    lamg_alt
                                    lamt_alt
                                    lamt
                                    lamg
                                    lamz))
            :cases ((<= 2 e)))
           ("Subgoal 1" :use ((:instance bits-lognot-is-specific-2
                                         (i 2)
                                         (x (LAMT_ALT A B E)))
                              (:instance bits-lognot-is-specific-3
                                         (x (lamt a b e))
                                         (i 2))
                              (:instance bits-lognot-is-specific-2
                                         (i 0)
                                         (e (+ -2 e))
                                         (x (LAMG A B E))))))))



(defun lam0_alt (a b e)
  (logior (lam1_alt a b e)
	  (logior (lam2_alt a b e)
		  (logior (lam3_alt a b e)
			  (lam4_alt a b e)))))


;; (defthmd bits_alt-logior
;;    (implies (and (integerp x)
;;                  (integerp y)
;;                  (integerp i)
;;                  (integerp j))
;;             (equal (bits_alt (logior x y) i j)
;;                    (logior (bits_alt x i j) (bits_alt y i j))))
(local
   (DEFTHMD BITS-LOGIOR
     (IMPLIES (AND (INTEGERP X)
                   (INTEGERP Y)
                   (INTEGERP I)
                   (INTEGERP J))
              (EQUAL (BITS (LOGIOR X Y) I J)
                     (LOGIOR (BITS X I J)
                             (BITS Y I J))))
     :hints (("Goal" :use ((:instance bits_alt-logior))))))


(local
 (defthmd lam0_alt-is-lam0-lemma
   (implies (and (integerp a)
                 (integerp b)
                 (natp e)
                 (> e 1))
            (equal (bits (lam0_alt a b e) (+ -2 e) 0)
                   (lam0 a b e)))
   :hints (("Goal" :in-theory (e/d (lior-logior-g
                                    BITS-LOGIOR
                                    lnot-lognot)
                                   (lamz_alt
                                    lamg_alt
                                    lamt_alt
                                    lamt
                                    lamg
                                    lamz
                                    lam1_alt
                                    lam1
                                    lam2_alt
                                    lam2
                                    lam3_alt
                                    lam3
                                    lam4_alt
                                    lam4))))))



(local
 (defthm lam0_alt-is-lam0
   (implies (and (integerp a)
                 (integerp b)
                 (natp e)
                 (> e 1))
            (equal (lam0_alt a b e)
                   (lam0 a b e)))
   :hints (("Goal" :cases ((bvecp (lam0_alt a b e) (+ -1 e))))
           ("Subgoal 1" :use ((:instance lam0_alt-is-lam0-lemma))))))





(defun lamb_alt (a b e)
  (+ (* 2 (lam0_alt a b e))
     (bitn_alt (lognot(lamt_alt a b e)) 0)))




;; (local
;;  (defthmd bits-lognot-is-specific-2
;;    (implies (and (integerp x)
;;                  (natp e)
;;                  (natp i)
;;                  (<= i e))
;;             (equal  (bits (lognot (bits x e 0)) e  i)
;;                     (bits (lognot x) e i)))
;;    :hints (("Goal" :in-theory (e/d (bits-bits-specific
;;                                     bits-lognot-is-specific)
;;                                    (bits-bits))
;;             :cases ((equal i 0))))))



;; (local
;;  (defthm lamt_alt-is-lamt-g
;;    (implies (and (natp e)
;;                  (natp i)
;;                  (<= i e)
;;                  (integerp a)
;;                  (integerp b))
;;             (equal (bits (lamt_alt a b e) e i)
;;                    (bits (lamt a b e) e i)))
;;    :hints (("Goal" :in-theory (e/d (lxor-logxor
;;                                     lnot-lognot)
;;                                    ())
;;             :use ((:instance bits_alt-logxor
;;                              (x a)
;;                              (y (bits (lognot b) e 0))
;;                              (i e)
;;                              (j i)))))))


;; (BITN (LOGNOT (LAMT_ALT A B E)) 0)
;; (BITN (LOGNOT (BITN (LAMT A B E) 0))
;;                      0)))


(local
 (defthm bitn-lamt_alt-is-lamt
   (implies (and (natp e)
                 (natp i)
                 (<= i e)
                 (integerp a)
                 (integerp b))
            (equal (bitn (lamt_alt a b e) i)
                   (bitn (lamt a b e) i)))
   :hints (("Goal" :use ((:instance lamt_alt-is-lamt))))))






(local
 (defthm lamb_alt-is-lamb
   (implies (and (integerp a)
                 (integerp b)
                 (natp e)
                 (> e 1))
            (equal (lamb_alt a b e)
                   (lamb a b e)))
   :hints (("Goal" :in-theory (e/d ()
                                   (lamt_alt
                                    lam0
                                    lam0_alt
                                    lamt
                                    bitn_alt-lognot))
            :use ((:instance BITN-LOGNOT-g
                             (x (lamt_alt a b e))
                             (n 0))
                  (:instance bitn-0-1
                             (x (lamt a b e))
                             (n 0)))))))




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
  :rule-classes ()
  :hints (("Goal" :use ((:instance lop-thm-2))
           :in-theory (e/d ()
                           (lamb_alt
                            lamb)))))


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
  :rule-classes ()
  :hints (("Goal" :use ((:instance top-thm-1)
                        (:instance bits-lognot-is-specific-2
                                   (i 0)
                                   (e k)
                                   (x (BITS (LOGXOR A B) (+ -1 N) 0)))
                        (:instance bits-lognot-is-specific-2
                                   (i 0)
                                   (e k)
                                   (x (LOGXOR A B)))))))




;; >  D          (DEFTHM BITS_ALT-LOGXOR
;;                       (IMPLIES (AND (CASE-SPLIT (INTEGERP X))
;;                                     (CASE-SPLIT (INTEGERP Y))
;;                                     (CASE-SPLIT (INTEGERP I))
;;                                     (CASE-SPLIT (INTEGERP J)))
;;                                (EQUAL (BITS_ALT (LOGXOR X Y) I J)
;;                                       (LOGXOR (BITS_ALT X I J)
;;                                               (BITS_ALT Y I J)))))

(local
 (defthm bits-logxor
   (implies (and (integerp x)
                 (integerp y)
                 (integerp i)
                 (integerp j))
            (equal (bits (logxor x y) i j)
                   (logxor (bits x i j)
                           (bits y i j))))
   :hints (("Goal" :use ((:instance bits_alt-logxor))))))


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
  :rule-classes ()
  :hints (("Goal" :use ((:instance top-thm-2)
                        (:instance bitn-0-1
                                   (x a)
                                   (n 0))
                        (:instance bitn-0-1
                                   (x b)
                                   (n 0)))
           :in-theory (e/d (bits-cat
                            BITS-LOGIOR
                            bits-logxor
                            ) ()))))


;;;;
;;;;
