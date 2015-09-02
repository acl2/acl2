;;;;; Contains method for generating a zero matrix (matrix where all entries are 0).
;;;;; Also contains theorems for row-count, col-count and a logical definition in terms
;;;;; of col-cons.
(in-package "ACL2")

(include-book "mdefthms")

(defmacro mzero-guard (r c)
  `(and (integerp ,r)
        (integerp ,c)
        (<= 0 ,r)
        (<= 0 ,c)))

;;; Creates a zero matrix with r rows and c columns if r and c are positive integers.
;;; Otherwise creates the m-empty.
(defun mzero (r c)
  (declare (xargs :guard (mzero-guard r c)
		  :verify-guards nil))
  (if (or (zp r) (zp c))
      nil
    (row-cons (vzero c)
	      (mzero (1- r) c))))

(local
 (defthm zero-bootstrap
   (and (matrixp (mzero r c))
	(equal (col-count (mzero r c))
	       (if (or (zp c) (zp r)) 0 c)))))

(verify-guards mzero)

(defthm matrixp-zero
  (matrixp (mzero r c)))

(defthm m-empty-zero
  (equal (m-emptyp (mzero r c))
	 (or (zp r) (zp c))))

(defthm col-count-zero
  (equal (col-count (mzero r c))
	 (if (or (zp c) (zp r)) 0 c)))

(defthm row-count-zero
  (equal (row-count (mzero r c))
	 (if (or (zp c) (zp r)) 0 r)))

(defthm zero-by-col-def
  (equal (mzero r c)
	 (if (or (zp r) (zp c))
	     nil
	   (col-cons (vzero r)
		     (if (= c 1)
			 nil
		       (mzero r (1- c))))))
  :hints (("Goal" :induct (mzero r c)))
  :rule-classes :definition)
