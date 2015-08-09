;;;;; Matrix addition.
;;;;; Defines m+ and basic properties.  This includes associativity,
;;;;; commutativity, a definition by column operations, and properties
;;;;; involving mentry and mzero.
(in-package "ACL2")

(include-book "mdefthms")

(defmacro m+-guard (m n)
  `(and (matrixp ,m)
        (matrixp ,n)
        (equal (row-count ,m) (row-count ,n))
        (equal (col-count ,m) (col-count ,n))))

(defun m+ (m n)
  (declare (xargs :guard (m+-guard m n)
                  :verify-guards nil))
  (if (m-emptyp m)
      (m-empty)
    (row-cons (v+ (row-car m) (row-car n))
              (m+ (row-cdr m) (row-cdr n)))))

(defthm m-emptyp-m+
  (equal (m-emptyp (m+ m n))
         (m-emptyp m)))

(defthm row-count-m+
  (equal (row-count (m+ m n))
         (row-count m)))

(defthm col-count-m+
  (implies (matrixp m)
           (equal (col-count (m+ m n))
                  (col-count m)))
  :hints (("Goal" :induct (m+ m n))))

(defthm matrixp-m+
  (implies (matrixp m)
           (matrixp (m+ m n))))

(verify-guards m+)


(defthm col-count-m+
  (implies (matrixp m)
           (equal (col-count (m+ m n))
                  (col-count m))))

(defthm row-count-m+
  (equal (row-count (m+ m n))
         (row-count m)))

(local
 (defthm col-car-m+
   (implies (and (matrixp m) (matrixp n))
            (equal (col-car (m+ m n))
                   (v+ (col-car m) (col-car n))))
   :hints (("Goal" :induct (m+ m n))
           ("Subgoal *1/2.2" :expand ((v+ (row-car m) (row-car n)))))))

(defun m+-by-col-recursion (m n)
  (declare (xargs :guard (m+-guard m n)
                  :guard-hints
                  (("Subgoal 2"
                    :cases ((m-emptyp (col-cdr m))))
                   ("Subgoal 2.2'4'"
                    :cases ((m-emptyp (col-cdr n))))
                   ("Subgoal 1" :cases ((m-emptyp (col-cdr m)))))))
  (if (or (m-emptyp m) (m-emptyp n))
      nil
    (m+-by-col-recursion (col-cdr m) (col-cdr n))))

(defthm m+-by-col-def
  (implies (and (matrixp m)
                (matrixp n))
           (equal (m+ m n)
                  (if (m-emptyp m)
                      (m-empty)
                    (col-cons (v+ (col-car m) (col-car n))
                              (m+ (col-cdr m) (col-cdr n))))))
  :hints (("Goal" :in-theory (enable row-cons-def)
                  :induct (m+ m n)))
  :rule-classes :definition)

(defthm m+-assoc
  (implies (and (m+-guard m n)
                (matrixp p))
           (equal (m+ (m+ m n) p)
                  (m+ m (m+ n p))))
  :hints (("Goal" :induct (and (m+ m n)
                               (m+ n p)))))
(defthm m+-assoc2
  (implies (and (m+-guard m n)
                (matrixp p))
           (equal (m+ m (m+ n p))
                  (m+ n (m+ m p))))
  :hints (("Goal" :induct (and (m+ m n)
                               (m+ n p)))))

(defthm m+-comm
  (implies (m+-guard m n)
           (equal (m+ m n)
                  (m+ n m)))
  :hints (("Goal" :induct (m+ m n))))

;;;; Properties about adding zero to a matrix.
;;;; These currently use (mzero (row-count m) (col-count m)) in
;;;; their definition.  This may not match as much as we would like,
;;;; so it may be smart to change this to (mzero r c) and add
;;;; appropriate conditions.
(include-book "mzero")

(defthm m+zero
  (implies (matrixp m)
           (equal (m+ m (mzero (row-count m) (col-count m))) m))
  :hints (("Goal" :induct (m+ m m))
; :With directed added 3/13/06 by Matt Kaufmann for after v2-9-4.
          ("Subgoal *1/2'''" :expand ((:with mzero (mzero 1 (col-count m)))))))

(defthm zero+m
  (implies (matrixp m)
           (equal (m+ (mzero (row-count m) (col-count m)) m) m))
  :hints (("Goal" :induct (m+ m m))
; :With directed added 3/13/06 by Matt Kaufmann for after v2-9-4.
          ("Subgoal *1/2'''" :expand ((:with mzero (mzero 1 (col-count m)))))))

;;;; Properties related to mentry
(include-book "mentry")

(defthm row-m+
  (implies (and (matrixp m)
                (matrixp n))
           (equal (row i (m+ m n))
                  (if (< (nfix i) (row-count m))
                      (v+ (row i m) (row i n))
                    nil)))
  :hints (("Goal" :induct (and (and (row i m)
                                    (m+ m n))))))

(defthm col-m+
  (implies (and (matrixp m)
                (matrixp n))
           (equal (col i (m+ m n))
                  (if (< (nfix i) (col-count m))
                      (v+ (col i m) (col i n))
                    nil)))
  :hints (("Goal" :induct (m+ m n))))

(defthm entry-m+
  (implies (and (matrixp m)
                (matrixp n))
           (equal (mentry r c (m+ m n))
                  (if (and (< (nfix r) (row-count m))
                           (< (nfix c) (col-count m)))
                      (+ (mentry r c m) (mentry r c n))
                    nil))))
