(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "../support/fadd"))
(local (include-book "../support/bits-extra"))
(local (include-book "../support/guards"))
(include-book "float")

;;;**********************************************************************
;;;                     GENERATE AND PROPAGATE
;;;**********************************************************************

;;Recognize whether a carry is generated:
(defun gen (x y i j)
  (declare (xargs :measure (nfix (1+ i))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn x i) (bitn y i))
	  (bitn x i)
	(gen x y (1- i) j))
    0))

;;Recognize whether a carry is propagated:
(defun prop (x y i j)
  (declare (xargs :measure (nfix (1+ i))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn x i) (bitn y i))
	  0
	(prop x y (1- i) j))
    1))

(defthmd gen-val
  (implies (and (natp j) (>= i j))
           (equal (gen x y i j)
                  (if (>= (+ (bits x i j) (bits y i j))
                          (expt 2 (1+ (- i j))))
                      1
                    0))))

(defthmd prop-val
  (implies (and (integerp i) (natp j) (>= i j))
           (equal (prop x y i j)
                  (if (= (+ (bits x i j) (bits y i j))
                         (1- (expt 2 (1+ (- i j)))))
                      1
                    0))))

(defthmd prop-as-lxor
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (natp x)
                (natp y))
           (equal (prop x y i j)
                  (log= (lxor (bits x i j) (bits y i j) (1+ (- i j)))
                        (1- (expt 2 (1+ (- i j))))))))

(defthmd gen-extend
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (> i k)
                (>= k j)
                (>= j 0))
           (equal (lior (gen x y i (1+ k))
                        (land (gen x y k j)
                              (prop x y i (1+ k))
                              1)
                        1)
                  (gen x y i j))))

(defthm gen-extend-cor
  (implies (and (natp x)
                (natp y)
                (natp i)
                (natp j)
                (natp k)
                (> i k)
                (>= k j))
           (equal (gen x y i j)
                  (bitn (+ (bits x i (1+ k))
                           (bits y i (1+ k))
                           (gen x y k j))
                        (- i k))))
  :rule-classes ())

(defthm prop-extend
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (> i k)
                (>= k j)
                (>= j 0))
           (equal (prop x y i j)
                  (land (prop x y i (1+ k))
                        (prop x y k j)
                        1)))
  :rule-classes ())

(defthm gen-special-case
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (bitn (+ (bits x i j) (bits y i j)) (- i j)) 0))
           (equal (gen x y i j)
                  (lior (bitn x i) (bitn y i) 1)))
  :rule-classes ())

(defthm land-gen-0
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (land (bits x i j) (bits y i j) (1+ (- i j))) 0))
           (equal (gen x y i j) 0)))

(defthmd gen-as-bitn
  (implies (and (integerp i)
		(integerp j)
		(<= 0 j)
		(<= j i))
           (equal (gen x y i j)
                  (bitn (+ (bits x i j)
                           (bits y i j))
                        (1+ (- i j))))))

;;See also bits.lisp for an alternate version, bits-sum.

(defthm bits-sum-with-gen
  (implies (and (integerp x) (integerp y))
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (gen x y (1- j) 0))
                        (- i j) 0)))
  :rule-classes ())

(defthm bits-sum-3-with-gen
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp i)
                (integerp j))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :rule-classes ())

(defthm bits-sum-corollary
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n i)
                (>= i j)
                (>= j 0)
                (= (land x y n) 0))
           (equal (bits (+ x y) i j)
                  (+ (bits x i j) (bits y i j))))
  :rule-classes ())

;;See also bits.lisp for an alternate version, bits-sum-plus-1.

(defthm bits-sum-plus-1-with-prop-gen
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0))
           (equal (bits (+ 1 x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (lior (prop x y (1- j) 0)
                                 (gen x y (1- j) 0)
                                 1))
                        (- i j) 0)))
  :rule-classes ())

(defthm bvecp-1-gen
  (bvecp (gen x y i j) 1)
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((gen x y i j)))))

(defthm bvecp-1-prop
  (bvecp (prop x y i j) 1)
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((prop x y i j)))))


;;;**********************************************************************
;;;                     ADDERS
;;;**********************************************************************

(defthm add-2
    (implies (and (not (zp n))
		  (bvecp x n)
		  (bvecp y n))
	     (equal (+ x y)
		    (+ (lxor x y n)
		       (* 2 (land x y n)))))
  :rule-classes ())

(defthm add-3
    (implies (and (not (zp n))
		  (bvecp x n)
		  (bvecp y n)
		  (bvecp z n))
	     (equal (+ x y z)
		    (+ (lxor x (lxor y z n) n)
		       (* 2 (lior (land x y n)
				  (lior (land x z n)
					(land y z n)
					n)
				  n)))))
  :rule-classes ())


;;;**********************************************************************
;;;                    TRAILING ONE PREDICTION
;;;**********************************************************************

(defthm top-thm-1
  (implies (and (natp n)
                (natp k)
                (< k n)
                (integerp a)
                (integerp b))
           (equal (equal (bits (+ a b 1) k 0) 0)
		  (equal (bits (lnot (lxor a b n) n) k 0) 0)))
  :rule-classes ())

(defthm top-thm-2
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n)
                (or (equal c 0) (equal c 1)))
           (equal (equal (bits (+ a b c) k 0) 0)
                  (equal (bits (lxor (lxor a b n)
                                     (cat (lior a b n) n c 1)
                                     (1+ n))
                               k 0)
                         0)))
  :rule-classes ())

(defthm top-thm-3
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n))
           (equal (equal (bits (+ a b 1) k 0) 0)
		  (equal (bits (lnot (lxor (lxor a b n)
				           (cat (land a b n) n 0 1)
					   (1+ n))
				     (1+ n))
			       k 0)
			 0)))
  :rule-classes ())


;;;**********************************************************************
;;;                  LEADING ONE PREDICTION
;;;**********************************************************************

(defthm lop-thm-1
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (= e (expo a))
		  (< (expo b) e)
		  (= lambda
		     (lior (* 2 (mod a (expt 2 e)))
			   (lnot (* 2 b) (1+ e))
			   (1+ e))))
	     (or (= (expo (- a b)) (expo lambda))
		 (= (expo (- a b)) (1- (expo lambda)))))
  :rule-classes ())

(defun lamt (a b e)
  (lxor a (lnot b (1+ e)) (1+ e)))

(defun lamg (a b e)
  (land a (lnot b (1+ e)) (1+ e)))

(defun lamz (a b e)
  (lnot (lior a (lnot b (1+ e)) (1+ e)) (1+ e)))

(defun lam1 (a b e)
  (land (bits (lamt a b e) e 2)
	(land (bits (lamg a b e) (1- e) 1)
	      (lnot (bits (lamz a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam2 (a b e)
  (land (lnot (bits (lamt a b e) e 2) (1- e))
	(land (bits (lamz a b e) (1- e) 1)
	      (lnot (bits (lamz a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam3 (a b e)
  (land (bits (lamt a b e) e 2)
	(land (bits (lamz a b e) (1- e) 1)
	      (lnot (bits (lamg a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam4 (a b e)
  (land (lnot (bits (lamt a b e) e 2) (1- e))
	(land (bits (lamg a b e) (1- e) 1)
	      (lnot (bits (lamg a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam0 (a b e)
  (lior (lam1 a b e)
	(lior (lam2 a b e)
	      (lior (lam3 a b e)
		    (lam4 a b e)
		    (1- e))
	      (1- e))
	(1- e)))

(defun lamb (a b e)
  (+ (* 2 (lam0 a b e))
     (lnot (bitn (lamt a b e) 0) 1)))

(defthm lop-thm-2
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (not (= a b))
		  (= e (expo a))
		  (= e (expo b))
		  (> e 1))
	     (and (not (= (lamb a b e) 0))
		  (or (= (expo (- a b)) (expo (lamb a b e)))
		      (= (expo (- a b)) (1- (expo (lamb a b e)))))))
  :rule-classes ())
