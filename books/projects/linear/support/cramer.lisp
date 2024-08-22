(in-package "DM")

(include-book "fdet")
(include-book "reduction")

;; We shall show that a is invertible iff (fdet a n) <> (f0).
;; First note that if a is invertible and (fdet a n) = 0, then by fdet-id-fmat, invertiblep-sufficient,
;; and fdet-multiplicative,

;;    (f1) = (fdet (id-fmat n) n)
;;         = (fdet (fmat* a (inverse-mat a)) n)
;;         = (f* (fdet a n) (fdet (inverse-mat a) n))
;;         = (f* (f0) (fdet (inverse-mat a) n))
;;         = (f0),

;; a contradiction:

(defthmd invertiblep-fdet-not-zero
  (implies (and (fmatp a n n) (posp n) (invertiblep a n))
           (not (equal (fdet a n) (f0))))
  :hints (("Goal" :use (invertiblep-sufficient
                        (:instance fdet-multiplicative (b (inverse-mat a)))))))

;; On the other hand, assume n > 0 and (fdet a n) <> (f0).  By fmat*-adjoint-fmat,

;;    (fmat* a (adjoint-fmat a n)) = (fmat-scalar-mul (fdet a n) (id-fmat n)),

;; which implies

;;    (fmat* a (fmat-scalar-mul (f/ (fdet a n)) (adjoint-fmat a n)))
;;      = (fmat-scalar-mul (f/ (fdet a n)) (fmat* a (adjoint-fmat a n)))
;;      = (fmat-scalar-mul (f/ (fdet a n)) (fmat-scalar-mul (fdet a n) (id-fmat n)))
;;      = (id-fmat n),

;; and by invertiblep-necessary, a is invertible.  This also establishes an alternative method for
;; computing the inverse:

(local-defthmd fmat-scalar-mul-f1
  (implies (fmatp a m n)
           (equal (fmat-scalar-mul (f1) a)
	          a))
  :hints (("Goal" :in-theory (enable fmatp))))

(local-defthmd invertiblep-fdet-not-zero-1
  (implies (and (fmatp a n n) (natp n) (> n 1) (not (equal (fdet a n) (f0))))
	   (equal (fmat* a (fmat-scalar-mul (f/ (fdet a n)) (adjoint-fmat a n)))
	          (id-fmat n)))
  :hints (("Goal" :use (fmat*-adjoint-fmat
                        (:instance fmat-scalar-mul-f1 (m n) (a (id-fmat n)))
                        (:instance fmat*-fmat-scalar-mul-2 (m n) (p n) (c (f/ (fdet a n))) (b (adjoint-fmat a n)))
			(:instance fmat-scalar-mul-assoc (m n) (c (f/ (fdet a n))) (d (fdet a n)) (a (id-fmat n)))))))

(defthmd fdet-not-invertiblep-zero
  (implies (and (fmatp a n n) (natp n) (> n 1) (not (equal (fdet a n) (f0))))
	   (and (invertiblep a n)
		(equal (inverse-mat a)
		       (fmat-scalar-mul (f/ (fdet a n)) (adjoint-fmat a n)))))
  :hints (("Goal" :in-theory (enable fmatp-fmat-scalar-mul)
                  :use (invertiblep-fdet-not-zero-1
                        (:instance invertiblep-inverse (b (fmat-scalar-mul (f/ (fdet a n)) (adjoint-fmat a n))))))))


;;---------------------------------------------------------------------------------------------------------

;; Our results on cofactor expansion lead to an alternative method of solving a system of linear 
;; equations in the case of a unique solution, known as Cramer's rule.  Let a be an invertible nxn
;; matrix, where n > 1, let (flistnp b n), (flistnp x n), and assume that x is  the unique solution of

;;     (fmat* a (col-mat x)) = (col-mat b).
;; 
;; Let 0 <= i < n.  We shall substitute a' = (replace-row (transpose-mat a) i b) for a in 
;; fdot-cofactor-fmat-row-fdet.  By nth-replace-row,

;;    (row i a') = b.

;; By nth-cofactor-fmat and cofactor-fmat-transpose,

;;    (cofactor-fmat-row i a' n) = (cofactor-fmat-row i (transpose-mat a) n)
;;                               = (row i (cofactor-fmat (transpose-mat a) n))
;;                               = (row i (adjoint-fmat a n)),

;; and by fdet-transpose,

;;    (fdet a' n) = (fdet (transpose-fmat (replace-col a i b)) n) = (fdet (replace-col a i b) n),

(local-defthmd fdot-row-adjoint-fmat-1
  (implies (and (fmatp a n n) (natp n) (> n 1) (flistnp b n) (natp i) (< i n))
           (let ((a1 (replace-row (transpose-mat a) i b)))
	     (and (fmatp a1 n n)
	          (equal (row i a1) b)
		  (equal (cofactor-fmat-row i a1 n)
		         (row i (adjoint-fmat a n)))
	          (equal (fdet a1 n)
		         (fdet (replace-col a i b) n)))))
  :hints (("Goal" :in-theory (enable replace-col)
                  :use (cofactor-fmat-transpose
                        (:instance fmatp-transpose (m n))
                        (:instance nth-cofactor-fmat (a (transpose-mat a)))
			(:instance fdet-transpose (a (replace-row (transpose-mat a) i b)))))))
		  
;; Thus, the substitution yields the following:

(defthmd fdot-row-adjoint-fmat
  (implies (and (fmatp a n n) (natp n) (flistnp b n) (> n 1) (natp i) (< i n))
           (equal (fdot b (row i (adjoint-fmat a n)))
                  (fdet (replace-col a i b) n)))
  :hints (("Goal" :use (fdot-row-adjoint-fmat-1
                        (:instance fdot-cofactor-fmat-row-fdet (a (replace-row (transpose-mat a) i b)))))))

;; Multiplying the equation (fmat* a (col-mat x)) = (col-mat b) by (adjoint-fmat a n) yields

;;    (fmat* (adjoint-fmat a n) (fmat* a (col-mat x))) = (fmat* (adjoint-fmat a n) (col-mat b)).

;; But

;;    (fmat* (adjoint-fmat a n) (fmat* a (col-mat x)))
;;      = (fmat* (fmat* (adjoint-fmat a n) a) (col-mat x))
;;      = (fmat* (flist-scalar-mul (fdet a n) (id-fmat n)) (col-mat x))
;;      = (flist-scalar-mul (fdet a n) (fmat* (id-fmat n) (col-mat x)))	 
;;      = (flist-scalar-mul (fdet a n) (col-mat x)),

(local-defthmd cramer-1
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (flistnp b n) (flistnp x n) (solutionp x a b))
           (equal (fmat* (adjoint-fmat a n) (fmat* a (col-mat x)))
	          (fmat* (adjoint-fmat a n) (col-mat b))))
  :hints (("Goal" :in-theory (enable solutionp))))

(local-defthm cramer-2
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (flistnp b n) (flistnp x n) (solutionp x a b))
           (equal (fmat* (adjoint-fmat a n) (fmat* a (col-mat x)))
	          (fmat* (fmat* (adjoint-fmat a n) a) (col-mat x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fmat*-assoc (m n) (p n) (q 1) (a (adjoint-fmat a n)) (b a) (c (col-mat x)))))))

(local-defthmd cramer-3
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n))
           (equal (fmat* (fmat-scalar-mul (f/ (fdet a n)) (adjoint-fmat a n))
	                 a)
	          (id-fmat n)))
  :hints (("Goal" :use (invertiblep-fdet-not-zero fdet-not-invertiblep-zero
                        invertiblep-sufficient
                        (:instance invertiblep-inverse (b (fmat-scalar-mul (f/ (fdet a n)) (adjoint-fmat a n))))))))

(local-defthmd cramer-4
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n))
           (equal (fmat* (adjoint-fmat a n) a)
	          (fmat-scalar-mul (fdet a n) (id-fmat n))))
  :hints (("Goal" :use (cramer-3 invertiblep-fdet-not-zero
                        (:instance fmat*-fmat-scalar-mul-1 (m n) (p n) (c (f/ (fdet a n))) (a (adjoint-fmat a n)) (b a))
			(:instance fmatp-fmat* (a (adjoint-fmat a n)) (b a) (m n) (p n))
			(:instance fmat-scalar-mul-f1 (a (FMAT* (ADJOINT-FMAT A N) A)) (m n))
			(:instance fmat-scalar-mul-assoc (m n)
			                                 (c (fdet a n))
			                                 (d (f/ (fdet a n)))
							 (a (fmat* (adjoint-fmat a n) a)))))))

(local-defthmd cramer-5
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n)
                (flistnp b n) (flistnp x n) (solutionp x a b))
           (equal (fmat* (fmat-scalar-mul (fdet a n) (id-fmat n)) (col-mat x))
	          (fmat* (adjoint-fmat a n) (col-mat b))))
  :hints (("Goal" :use (cramer-1 cramer-2 cramer-4))))

(local-defthmd cramer-6
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n)
                (flistnp b n) (flistnp x n) (solutionp x a b))
           (equal (fmat-scalar-mul (fdet a n) (col-mat x))
	          (fmat* (adjoint-fmat a n) (col-mat b))))
  :hints (("Goal" :use (cramer-5
                        (:instance id-fmat-left (m n) (n 1) (a (col-mat x)))
                        (:instance fmat*-fmat-scalar-mul-1 (m n) (p 1) (c (fdet a n)) (a (id-fmat n)) (b (col-mat x)))))))

(local-defthmd nth-col-mat-1
  (implies (flistnp l 1)
           (equal (list (car l)) l)))

(local-defthmd nth-col-mat-2
  (implies (and (posp n) (flistnp x n) (natp i) (< i n))
           (flistnp (nth i (col-mat x)) 1))
  :hints (("Goal" :use ((:instance flistnp-row (a (col-mat x)) (m n) (n 1))))))

(local-defthmd nth-col-mat-3
  (implies (and (posp n) (flistnp x n) (natp i) (< i n))
           (equal (nth i (col-mat x))
	          (list (entry i 0 (col-mat x)))))
  :hints (("Goal" :use (nth-col-mat-2 (:instance nth-col-mat-1 (l (nth i (col-mat x))))))))

(local-defthmd nth-col-mat-4
  (implies (and (posp n) (flistnp x n) (natp i) (< i n))
           (equal (nth i (col-mat x))
	          (list (nth i x))))
  :hints (("Goal" :in-theory (enable col-mat row-mat)
                  :use (nth-col-mat-3 fmatp-row-mat (:instance transpose-fmat-entry (a (row-mat x)) (m 1) (j i) (i 0))))))

(local-defthmd cramer-7
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n)
                (flistnp b n) (flistnp x n) (solutionp x a b)
		(natp i) (< i n))
           (equal (entry i 0 (fmat-scalar-mul (fdet a n) (col-mat x)))
	          (f* (fdet a n) (nth i x))))
  :hints (("Goal" :use (nth-col-mat-4
                        (:instance row-fmat-scalar-mul (m n) (n 1) (c (fdet a n)) (a (col-mat x)))))))

(local-defthm col-0-col-mat
  (implies (and (posp n) (flistnp b n))
           (equal (col 0 (col-mat b)) b))
  :hints (("Goal" :in-theory (enable fmatp col-mat row-mat)
                  :use ((:instance col-transpose-fmat (a (row-mat b)) (m 1) (j 0))))))

(local-defthmd cramer-8
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n)
                (flistnp b n) (flistnp x n) (solutionp x a b)
		(natp i) (< i n))
           (equal (entry i 0 (fmat* (adjoint-fmat a n) (col-mat b)))
	          (fdot (row i (adjoint-fmat a n)) b)))
  :hints (("Goal" :use ((:instance fmat*-entry (m n) (p 1) (j 0) (a (adjoint-fmat a n)) (b (col-mat b)))))))

(local-defthmd cramer-9
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n)
                (flistnp b n) (flistnp x n) (solutionp x a b)
		(natp i) (< i n))
           (equal (f* (fdet a n) (nth i x))
	          (fdot (row i (adjoint-fmat a n)) b)))
  :hints (("Goal" :use (cramer-6 cramer-7 cramer-8))))

(local-defthmd cramer-10
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n)
                (flistnp b n) (flistnp x n) (solutionp x a b)
		(natp i) (< i n))
           (equal (f* (fdet a n) (nth i x))
	          (fdet (replace-col a i b) n)))
  :hints (("Goal" :use (cramer-9 fdot-row-adjoint-fmat
                        (:instance fdot-comm (x b) (y (row i (adjoint-fmat a n))))
			(:instance flistnp-row (a (adjoint-fmat a n)) (m n))))))

;; and hence

;;    (flist-scalar-mul (fdet a n) (col-mat x)) = (fmat* (adjoint-fmat a n) (col-mat b)).

;; Equating the entry in row i and column 0 of each side of this equation, we have

;;    (f* (fdet a n) (nth i x)) = (fdot b (row i (adjoint-fmat a n)))
;;                              = (fdet (replace-col a i b) n),

;; which is Cramer's rule:

(defthmd cramer
  (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n)
                (flistnp b n) (flistnp x n) (solutionp x a b)
		(natp i) (< i n))
           (equal (nth i x)
	          (f* (f/ (fdet a n))
		      (fdet (replace-col a i b) n))))
  :hints (("Goal" :use (cramer-10 invertiblep-fdet-not-zero
                        (:instance f*assoc (x (f/ (fdet a n))) (y (fdet a n)) (z (nth i x)))))))
	

	 
