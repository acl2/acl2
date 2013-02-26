;;;;; Provides indexed access to rows, columns and entries in a matrix.
(in-package "ACL2")

;;; If (nfix i) is greater then the length of a list, then the nth equals nil.
(defthm nth-over
  (implies (<= (len l) (nfix i))
           (equal (nth i l) nil)))

(include-book "mdefthms")

(defmacro row-guard (i m)
  `(and (matrixp ,m)
        (integerp ,i)
        (<= 0 ,i)
        (< ,i (row-count ,m))))

;;; Returns row at index i in matrix m.
(defun row (i m)
  (declare (xargs :guard (row-guard i m)))
  (cond ((m-emptyp m) nil)
        ((zp i) (row-car m))
        (t (row (1- i) (row-cdr m)))))

;;; Provide an alterate definition of row that uses col-cdr instead of row-cdr.
(defthm row-by-col-def
  (implies (matrixp m)
           (equal (row i m)
                  (if (or (m-emptyp m)
                          (>= (nfix i) (row-count m)))
                      nil
                    (cons (nth i (col-car m))
                          (row i (col-cdr m))))))
  :hints (("Goal" :induct (row i m)))
  :rule-classes :definition)

(defthm mvectorp-row
  (implies (matrixp m)
           (mvectorp (row i m)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-row
  (implies (matrixp m)
           (equal (len (row i m))
                  (if (< (nfix i) (row-count m))
                      (col-count m)
                    0)))
  :hints (("Goal" :induct (row i m))))

(defthm consp-row
  (implies (matrixp m)
           (equal (consp (row i m))
                  (< (nfix i) (row-count m))))
  :hints (("Subgoal *1/6"
           :cases ((< (1- i) (row-count (row-cdr m)))))))

(defmacro col-guard (i m)
  `(and (matrixp ,m)
        (integerp ,i)
        (<= 0 ,i)
        (< ,i (col-count ,m))))

(defun col (i m)
  (declare (xargs :guard (col-guard i m)))
  (cond ((m-emptyp m) nil)
        ((zp i) (col-car m))
        (t (col (1- i) (col-cdr m)))))

(defthm col-by-row-def
  (implies (matrixp m)
           (equal (col i m)
                  (if (or (m-emptyp m)
                          (>= (nfix i) (col-count m)))
                      nil
                    (cons (nth i (row-car m))
                          (col i (row-cdr m))))))
  :hints (("Goal" :induct (col i m)))
  :rule-classes :definition)

(defthm mvectorp-col
  (implies (matrixp m)
           (mvectorp (col i m)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-col
  (implies (matrixp m)
           (equal (len (col i m))
                  (if (< (nfix i) (col-count m))
                      (row-count m)
                    0))))

(defthm consp-col
  (implies (matrixp m)
           (equal (consp (col i m))
                  (< (nfix i) (col-count m))))
  :hints (("Subgoal *1/6"
           :cases ((< (1- i) (col-count (col-cdr m)))))))

(defmacro mentry-guard (r c m)
  `(and (matrixp ,m)
        (integerp ,r)
        (<= 0 ,r)
        (< ,r (row-count ,m))
        (integerp ,c)
        (<= 0 ,c)
        (< ,c (col-count ,m))))

;;; Return the entry at the specified row and column
(defun mentry (r c m)
  (declare (xargs :guard (mentry-guard r c m)))
  (nth c (row r m)))

;;; Provide an alterate equivalent definition of mentry.
(defthmd mentry-by-col
  (implies (matrixp m)
           (equal (mentry r c m)
                  (nth r (col c m))))
  :rule-classes :definition)

