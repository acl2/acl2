;;;;; Matrix multiplication by a scalar.
;;;;; This includes basic properties, collecting multiple multiplications,
;;;;; and relations to mzero, madd, and mentry book contents.
(in-package "ACL2")

(include-book "mdefthms")

(defun sm* (s m)
  (declare (xargs :guard (and (acl2-numberp s)
                              (matrixp m))
                  :verify-guards nil))
  (if (m-emptyp m)
      (m-empty)
    (row-cons (sv* s (row-car m))
              (sm* s (row-cdr m)))))

(local
 (defthm sm*-bootstrap
   (implies (matrixp m)
            (and (matrixp (sm* s m))
                 (equal (col-count (sm* s m))
                        (col-count m))))
   :hints (("Goal" :induct (sm* s m)))))

(defthm m-empty-sm*
  (equal (m-emptyp (sm* s m))
         (m-emptyp m)))

(verify-guards sm*)

(defthm matrix-sm*
  (implies (matrixp m)
           (matrixp (sm* s m))))

(defthm col-count-sm*
  (implies (matrixp m)
           (equal (col-count (sm* s m))
                  (col-count m))))

(defthm row-count-sm*
  (equal (row-count (sm* s m))
         (row-count m)))

(defthm sm*-1
  (implies (matrixp m)
           (equal (sm* 1 m) m)))

(defthm sm*-sm*
  (implies (matrixp m)
           (equal (sm* a (sm* b m))
                  (sm* (* a b) m))))

(local
 (defthm col-car-sm*
   (implies (matrixp m)
            (equal (col-car (sm* s m))
                   (sv* s (col-car m))))
   :hints (("Goal" :in-theory (enable col-car-row-cons))
           ("Subgoal *1/3" :expand ((sv* s (row-car m)))))))

(defthm sm*-by-col-def
  (implies (matrixp m)
           (equal (sm* s m)
                  (if (m-emptyp m)
                      (m-empty)
                    (col-cons (sv* s (col-car m))
                              (sm* s (col-cdr m))))))
  :hints (("Subgoal *1/1.3'"
           :use (:instance row-cons-def
                           (l (list (* s (car (col-car m)))))
                           (m (sm* s (row-cdr m))))))
  :rule-classes :definition)

;;;; Properties about scalar multiplication and zero.
(include-book "mzero")

(defthm sm*-0-left
  (implies (matrixp m)
           (equal (sm* 0 m)
                  (mzero (row-count m) (col-count m))))
  :hints (("Goal" :induct (sm* 0 m))))

(defthm sm*-0-right
  (equal (sm* s (mzero r c))
         (mzero r c))
  :hints (("Goal" :induct (vzero r))))

;;;; Properties about scalar multiplication and addition.
(include-book "madd")

(defthm sm*-collect
  (implies (matrixp m)
           (equal (m+ m m)
                  (sm* 2 m))))

(defthm sm*-collect-left
  (implies (matrixp m)
           (equal (m+ (sm* a m) m)
                  (sm* (1+ a) m))))

(defthm sm*-collect-right
  (implies (matrixp m)
           (equal (m+ m (sm* a m))
                  (sm* (1+ a) m))))

(defthm sm*-collect-both
  (implies (matrixp m)
           (equal (m+ (sm* a m) (sm* b m))
                  (sm* (+ a b) m))))

(defthm sm*-dist
  (implies (m+-guard m n)
           (equal (sm* a (m+ m n))
                  (m+ (sm* a m) (sm* a n))))
  :hints (("Goal" :induct (m+ m n))))

;;;; Properties about scalar multiplication and entries.
(include-book "mentry")

(defthm row-sm*
  (implies (matrixp m)
           (equal (row i (sm* a m))
                  (sv* a (row (nfix i) m))))
  :hints (("Goal" :induct (row i m))
; :With directive added 3/14/06 by Matt Kaufmann for after v2-9-4.
          ("Subgoal *1/2'''" :expand ((:with sm* (sm* a m))))))

(defthm col-sm*
  (implies (matrixp m)
           (equal (col i (sm* a m))
                  (sv* a (col i m)))))

(defthm entry-sm*
  (implies (matrixp m)
           (equal (mentry r c (sm* a m))
                  (if (and (< (nfix r) (row-count m))
                           (< (nfix c) (col-count m)))
                      (* a (mentry r c m))
                    nil))))
