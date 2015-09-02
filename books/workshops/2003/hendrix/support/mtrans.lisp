;;;;; Matrix transpose
;;;;; Contains definition of matrix transpose and basis properties.
;;;;; Includes relations with mzero, madd, mid, mmult, and mentry.
(in-package "ACL2")

(include-book "mdefthms")

(defun mtrans (m)
  (declare (xargs :guard (matrixp m)
                  :verify-guards nil))
  (if (m-emptyp m)
      (m-empty)
    (col-cons (row-car m) (mtrans (row-cdr m)))))

(defthm m-emptyp-mtrans
  (equal (m-emptyp (mtrans m))
         (m-emptyp m)))

(defthm row-count-mtrans
  (implies (matrixp m)
           (equal (row-count (mtrans m))
                  (col-count m))))

(defthm matrixp-mtrans
  (implies (matrixp m)
           (matrixp (mtrans m))))

(local
 (defun col-cdr-recurse (m)
   (if (m-emptyp m)
       0
     (col-cdr-recurse (col-cdr m)))))

(defthm col-count-mtrans
  (implies (matrixp m)
           (equal (col-count (mtrans m))
                  (row-count m)))
  :hints (("Subgoal *1/3"
           :use (:instance col-count-def
                           (m (col-cons (row-car m)
                                        (mtrans (row-cdr m))))))))

(verify-guards mtrans)

(defthm mtrans-by-col-def
  (implies (matrixp m)
           (equal (mtrans m)
                  (if (m-emptyp m)
                      (m-empty)
                    (row-cons (col-car m)
                              (mtrans (col-cdr m))))))
  :hints (("Goal" :induct (mtrans m)))
  :rule-classes :definition)

(defthm mtrans-mtrans
  (implies (matrixp m)
           (equal (mtrans (mtrans m))
                  m)))

(include-book "mzero")

(defthm mtrans-zero
  (equal (mtrans (mzero r c))
         (mzero c r)))

(include-book "madd")

(defthm distr+mtrans
  (implies (and (matrixp m)
                (matrixp n))
           (equal (mtrans (m+ m n))
                  (m+ (mtrans m) (mtrans n))))
  :hints (("Goal" :induct (m+ m n))))

(include-book "mid")

(defthm mtrans-id
  (equal (mtrans (mid n))
         (mid n)))

(include-book "mscal")

(defthm sm*-trans
  (implies (matrixp m)
           (equal (mtrans (sm* s m))
                  (sm* s (mtrans m)))))

(include-book "mmult")

(defthm col*-mtrans
  (implies (row*-guard l m)
           (equal (col* l (mtrans m))
                  (row* l m))))

(defthm row*-mtrans
  (implies (col*-guard l m)
           (equal (row* l (mtrans m))
                  (col* l m))))

(defthm mtrans-m*
  (implies (m*-guard m n)
           (equal (mtrans (m* m n))
                  (m* (mtrans n) (mtrans m))))
  :hints (("Goal" :induct (m* m n))))

(include-book "mentry")

(defthm row-trans
  (implies (matrixp m)
           (equal (row i (mtrans m))
                  (col i m))))

(defthm col-trans
  (implies (matrixp m)
           (equal (col i (mtrans m))
                  (row i m)))
; :With directive added 3/14/06 by Matt Kaufmann for after v2-9-4.
  :hints (("Goal" :expand (:with mtrans (mtrans m)))))

(defthm entry-trans
  (implies (matrixp m)
           (equal (mentry r c (mtrans m))
                  (mentry c r m)))
  :hints (("Subgoal *1/2.4'" :use (:instance row-by-col-def (i c)))))
