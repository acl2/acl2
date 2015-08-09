;;;;; Matrix multiplication and vector matrix multiplication.
;;;;; This includes col* (normally called multiplication of a matrix
;;;;; by a vector in math), row* (multiplication of a vector by each row
;;;;; in a matrix), and and matrix multiplication.
;;;;; Basic properties are proven as well as relations to the mzero, madd,
;;;;; mid, and mentry books.  This includes the group properties.

(in-package "ACL2")

(include-book "mdefthms")

;;;; Definition of col* and basic properties
(defmacro col*-guard (r m)
  `(and (matrixp ,m)
        (mvectorp ,r)
        (or (m-emptyp ,m)
            (equal (len ,r) (row-count ,m)))))

;;; Returns list containing dot product of each column in m and r.
(defun col* (r m)
  (declare (xargs :guard (col*-guard r m)))
  (if (m-emptyp m)
      nil
    (cons (dot* r (col-car m))
          (col* r (col-cdr m)))))

(defthm mvectorp-col*
  (mvectorp (col* r m))
  :rule-classes (:rewrite :type-prescription))

(defthm consp-col*
  (implies (not (m-emptyp m))
           (consp (col* r m)))
  :rule-classes :type-prescription)

(defthm len-col*
  (implies (matrixp m)
           (equal (len (col* r m))
                  (col-count m))))

(defthm col*-by-row-def
  (implies (matrixp m)
           (equal (col* l m)
                  (if (m-emptyp m)
                      nil
                    (v+ (sv* (car l) (row-car m))
                        (col* (cdr l) (row-cdr m))))))
  :hints (("Goal" :induct (col* l m)))
  :rule-classes :definition)

;;;; Definition of row* and basic properties

(defmacro row*-guard (c m)
  `(and (matrixp ,m)
        (mvectorp ,c)
        (or (m-emptyp ,m)
            (equal (len ,c) (col-count ,m)))))

;;; Returns list containing dot product of each row in m and c.
(defun row* (c m)
  (declare (xargs :guard (row*-guard c m)))
  (if (m-emptyp m)
      nil
    (cons (dot* c (row-car m))
          (row* c (row-cdr m)))))

(defthm mvectorp-row*
  (mvectorp (row* c m))
  :rule-classes (:rewrite :type-prescription))

(defthm consp-row*
  (implies (not (m-emptyp m))
           (consp (row* c m)))
  :rule-classes :type-prescription)

(defthm len-row*
  (implies (matrixp m)
           (equal (len (row* c m))
                  (row-count m))))

(defthm row*-by-col-def
  (implies (matrixp m)
           (equal (row* l m)
                  (if (m-emptyp m)
                      nil
                    (v+ (sv* (car l) (col-car m))
                        (row* (cdr l) (col-cdr m))))))
  :hints (("Goal" :induct (row* l m)))
  :rule-classes :definition)

;;; The dot product of col* and row* are related.
(defthm dot*-col*
  (implies (and (matrixp m)
                (or (m-emptyp m)
                    (and (equal (len k) (col-count m))
                         (equal (len l) (row-count m)))))
           (equal (dot* k (col* l m))
                  (dot* l (row* k m))))
  :hints (("Goal" :induct (row-cons k m)

; Added by Matt Kaufmann, 2/25/06, to accommodate fix for runic designators
; to match their spec, where disabling the name of a defthm disables all rules
; generated for that defthm (in this case, row-cons-def).

           :in-theory (enable (:induction row-cons-def))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((dot* k (col* l m))
                                  (dot* l (row* k m))))))

;;;; Definition of m* and basic properties
(defmacro m*-guard (m n)
  `(and (matrixp ,m)
        (matrixp ,n)
        (equal (col-count ,m) (row-count ,n))))

(defun m* (m n)
  (declare (xargs :guard (m*-guard m n)
                  :verify-guards nil))
  (if (or (m-emptyp m) (m-emptyp n))
      (m-empty)
    (row-cons (col* (row-car m) n)
                (if (m-emptyp (row-cdr m))
                    (m-empty)
                  (m* (row-cdr m) n)))))

(local
 (defthm m*-bootstrap
   (implies (and (matrixp m)
                 (matrixp n))
            (and (matrixp (m* m n))
                 (equal (col-count (m* m n))
                        (if (m-emptyp m) 0 (col-count n)))))
   :hints (("Goal" :induct (m* m n)))))

(verify-guards m*)

(defthm matrixp-m*
  (implies (and (matrixp m)
                (matrixp n))
           (matrixp (m* m n))))

(defthm col-count-m*
  (implies (and (matrixp m)
                (matrixp n))
           (equal (col-count (m* m n))
                  (if (m-emptyp m)
                      0
                    (col-count n)))))

(defthm row-count-m*
  (equal (row-count (m* m n))
         (if (m-emptyp n) 0 (row-count m))))

(defthm m-empty-m*
  (equal (m-emptyp (m* m n))
         (or (m-emptyp m)
             (m-emptyp n))))

(defthm m*-by-col-def
  (implies (and (matrixp m)
                (matrixp n)
                (or (m-emptyp m)
                    (m-emptyp n)
                    (equal (col-count m) (row-count n))))
           (equal (m* m n)
                  (if (or (m-emptyp m) (m-emptyp n))
                      (m-empty)
                    (col-cons (row* (col-car n) m)
                              (m* m (col-cdr n))))))
  :hints (("Goal" :induct (m* m n)))
  :rule-classes :definition)

(defthm col*-m*
  (implies (and (matrixp m)
                (matrixp n)
                (equal (len l) (row-count m))
                (equal (col-count m) (row-count n)))
           (equal (col* l (m* m n))
                  (col* (col* l m) n)))
  :hints (("Goal" :induct (col* l n))
          ("Subgoal *1/2"
           :cases ((m-emptyp m)))
          ("Subgoal *1/2.2"
           :use (:instance dot*-col* (k (col-car n))))))

(defthm row*-m*
  (implies (and (matrixp m)
                (matrixp n)
                (mvectorp l)
                (equal (len l) (col-count n))
                (equal (col-count m) (row-count n)))
           (equal (row* l (m* m n))
                  (row* (row* l n) m)))
  :hints (("Goal" :induct (row* l m))
          ("Subgoal *1/2"
           :use (:instance dot*-col*
                           (k l)
                           (l (row-car m))
                           (m n)))))

(defthm m*-assoc
  (implies (and (matrixp m)
                (matrixp n)
                (matrixp p)
                (equal (col-count m) (row-count n))
                (equal (col-count n) (row-count p)))
           (equal (m* (m* m n) p)
                  (m* m (m* n p))))
  :hints (("Goal" :induct (m* m n))))

(include-book "mzero")

(defthm col*-zero-left
  (implies (matrixp m)
           (equal (col* (vzero r) m)
                  (vzero (col-count m)))))

(defthm col*-zero-right
  (equal (col* l (mzero r c))
         (if (zp r) nil (vzero c)))
  :hints (("Goal" :induct (vzero c))))

(defthm row*-zero-left
  (implies (matrixp m)
           (equal (row* (vzero c) m)
                  (vzero (row-count m))))
  :hints (("Goal" :induct (row* l m))))

(defthm row*-zero-right
  (equal (row* l (mzero r c))
         (if (zp c) nil (vzero r)))
  :hints (("Goal" :induct (vzero r))))

(defthm m*-zero-left
  (implies (and (matrixp m)
                (equal (row-count m) c))
           (equal (m* (mzero r c) m)
                  (mzero r (col-count m)))))

(defthm m*-zero-right
  (implies (and (matrixp m)
                (if (zp c)
                    (m-emptyp m)
                  (equal (col-count m) r)))
           (equal (m* m (mzero r c))
                  (mzero (row-count m) c))))

(include-book "madd")

(defthm dist-col*-v+
  (implies (and (matrixp m)
                (or (m-emptyp m)
                    (equal (len j) (row-count m))))
           (equal (col* (v+ j k) m)
                  (v+ (col* j m) (col* k m)))))

(defthm dist-col*-m+
  (implies (and (matrixp m)
                (matrixp n)
                (equal (row-count m) (row-count n))
                (equal (col-count m) (col-count n))
                (or (m-emptyp m)
                    (equal (len l) (row-count m))))
           (equal (col* l (m+ m n))
                  (v+ (col* l m) (col* l n))))
  :hints (("Goal" :induct (m+-by-col-recursion m n))))

(defthm dist-row*-v+
  (implies (and (matrixp m)
                (or (m-emptyp m)
                    (equal (len j) (col-count m))))
           (equal (row* (v+ j k) m)
                  (v+ (row* j m) (row* k m))))
  :hints (("Goal" :induct (row* k m))))

(defthm dist-row*-m+
  (implies (and (matrixp m)
                (matrixp n)
                (equal (row-count m) (row-count n))
                (equal (col-count m) (col-count n))
                (or (m-emptyp m)
                    (equal (len l) (col-count m))))
           (equal (row* l (m+ m n))
                  (v+ (row* l m) (row* l n))))
  :hints (("Goal" :induct (m+ m n))))

(defthm dist-m*+
  (implies (and (matrixp m)
                (matrixp n)
                (matrixp p)
                (equal (col-count m) (row-count n))
                (equal (row-count n) (row-count p))
                (equal (col-count n) (col-count p)))
           (equal (m* m (m+ n p))
                  (m+ (m* m n) (m* m p))))
  :hints (("Goal" :induct (m* m n))))

(defthm dist-m+*
  (implies (and (matrixp m)
                (matrixp n)
                (matrixp p)
                (equal (row-count m) (row-count n))
                (equal (col-count m) (col-count n))
                (equal (col-count n) (row-count p)))
           (equal (m* (m+ m n) p)
                  (m+ (m* m p) (m* n p))))
  :hints (("Goal" :induct (m+ m n))))

(include-book "mscal")
(defthm dist-col*-sv*
  (implies (and (matrixp m)
                (or (m-emptyp m)
                    (equal (len l) (row-count m))))
           (equal (col* (sv* a l) m)
                  (sv* a (col* l m)))))

(defthm dist-col*-sm*
  (implies (and (matrixp m)
                (or (m-emptyp m)
                    (equal (len l) (row-count m))))
           (equal (col*  l (sm* a m))
                  (sv* a (col* l m))))
  :hints (("Subgoal *1/3.2"
              :use (:instance sm*-by-col-def (s a)))))

(defthm dist-row*-sv*
  (implies (and (matrixp m)
                (or (m-emptyp m)
                    (equal (len l) (col-count m))))
           (equal (row* (sv* a l) m)
                  (sv* a (row* l m))))
  :hints (("Goal" :induct (row* l m))))

(defthm dist-row*-sm*
  (implies (and (matrixp m)
                (or (m-emptyp m)
                    (equal (len l) (col-count m))))
           (equal (row*  l (sm* a m))
                  (sv* a (row* l m))))
  :hints (("Goal" :induct (row* l m))))

(defthm dist-m*-sm*-left
  (implies (and (matrixp m)
                (matrixp n)
                (equal (col-count m) (row-count n)))
           (equal (m* (sm* a m) n)
                  (sm* a (m* m n))))
  :hints (("Goal" :induct (m* m n))))

(defthm dist-m*-sm*-right
  (implies (and (matrixp m)
                (matrixp n)
                (equal (col-count m) (row-count n)))
           (equal (m* m (sm* a n))
                  (sm* a (m* m n))))
  :hints (("Goal" :induct (m* m n))))

(include-book "mid")

(defthm col*-1-left
  (implies (matrixp m)
           (equal (col* (cons 1 (vzero r)) m)
                  (row-car m)))
  :hints (("Goal" :induct (row-car m))
          ("Subgoal *1/2.5.2" :expand ((dot* (col-car m) (cons 1 (vzero r)))))))

(defthm col*-id
  (implies (and (mvectorp l)
                (equal (len l) n))
           (equal (col* l (mid n)) l)))

(defthm row*-1-left
  (implies (matrixp m)
           (equal (row* (cons 1 (vzero c)) m)
                  (col-car m)))
  :hints (("Goal" :induct (col-car m))))

(defthm row*-id
  (implies (and (mvectorp l)
                (equal (len l) n))
           (equal (row* l (mid n)) l)))

(defthm m*-id-left
  (implies (and (matrixp m)
                (equal (row-count m) n))
           (equal (m* (mid n) m) m))
  :hints (("Goal" :induct (col* l m))))

(defthm m*-id-right
  (implies (and (matrixp m)
                (equal (col-count m) n))
  (equal (m* m (mid n)) m))
  :hints (("Goal" :induct (row* l m))))

(include-book "mentry")

(defthm nth-col*
  (implies (matrixp m)
           (equal (nth i (col* v m))
                  (if (< (nfix i) (col-count m))
                      (dot* v (col (nfix i) m))
                    nil)))
  :hints (("Goal" :induct (col i m))
; :With directive added 3/14/06 by Matt Kaufmann for after v2-9-4.
          ("Subgoal *1/2'''" :expand (:with col* (col* v m)))))

(defthm col-m*
  (implies (and (matrixp m)
                (matrixp n))
           (equal (col i (m* m n))
                  (if (< (nfix i) (col-count n))
                      (row* (col i n) m)
                    nil)))
  :hints (("Goal" :induct (m* m n))
; :With directive added 3/14/06 by Matt Kaufmann for after v2-9-4.
          ("Subgoal *1/2" :expand (:with col* (col* (row-car m) n)))))

(defthm nth-row*
  (implies (matrixp m)
           (equal (nth i (row* v m))
                  (if (< (nfix i) (row-count m))
                      (dot* v (row i m))
                    nil)))
  :hints (("Goal" :induct (row i m))
; :With directive added 3/14/06 by Matt Kaufmann for after v2-9-4.
          ("Subgoal *1/2" :expand (:with row* (row* v m)))))

(defthm row-m*
  (implies (and (matrixp m)
                (matrixp n))
           (equal (row i (m* m n))
                  (if (< (nfix i) (row-count m))
                      (col* (row i m) n)
                    nil)))
  :hints (("Goal" :induct (row i m))
; :With directive added 3/14/06 by Matt Kaufmann for after v2-9-4.
          ("Subgoal *1/2.1'" :expand (:with m* (m* m n)))))

(defthm entry-m*
  (implies (and (matrixp m)
                (matrixp n))
           (equal (mentry r c (m* m n))
                  (if (and (< (nfix r) (row-count m))
                           (< (nfix c) (col-count n)))
                      (dot* (row r m) (col c n))
                    nil))))
