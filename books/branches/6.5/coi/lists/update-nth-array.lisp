#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; update-nth-array.lisp
;; Rules about update-nth-array.

;bzo Do we want to disable update-nth-array or not (it's non-recursive!)? -ews

(in-package "LIST")

(include-book "nth-and-update-nth")
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (disable UPDATE-NTH-EQUAL-REWRITE
                           UPDATE-NTH-EQUAL-UPDATE-NTH-REWRITE))) ;bzo why?

;; A first observation is that update-nth-array respects equiv for its list argument.

(defcong equiv equiv (update-nth-array j key val l) 4)

(defthm true-listp-update-nth-array
  (implies (true-listp l)
           (true-listp (update-nth-array n i v l)))
  :rule-classes :type-prescription)

(defthm true-listp-update-nth-array-rewrite
  (implies (true-listp l)
           (true-listp (update-nth-array n i v l))))
;; Theorems about Update-Nth-Array

(local (in-theory (disable update-nth-array)))

(defthm firstn-update-nth-array
  (implies (and (integerp n)
                (<= 0 n)
                (integerp n2)
                (<= 0 n2))
           (equal (firstn n (update-nth-array n2 i v l))
                  (if (<= n n2)
                      (append (firstn n l) (repeat (- n (len l)) nil))
                    (update-nth-array n2 i v (firstn n l)))))
  :hints (("Goal" :in-theory (enable firstn update-nth-array))))

(defthm nthcdr-update-nth-array
  (implies (and (integerp n)
                (<= 0 n)
                (integerp n2)
                (<= 0 n2))
           (equal (nthcdr n (update-nth-array n2 i v l))
                  (if (< n2 n)
                      (nthcdr n l)
                    (update-nth-array (- n2 n) i v (nthcdr n l)))))
  :hints (("Goal" :in-theory (enable nthcdr update-nth-array))))



;bzo can we improve the phrasing of this using a clear operation? -ews
(defthm equal-update-nth-array-casesplit
  (implies (and (integerp n)
                (<= 0 n))
           (equal (equal (update-nth-array n i v l1) L2)
                  (and (equal (update-nth i v (nth n l1)) (nth n l2))
                       (< n (len l2))
                       (equal (firstn n (append l1 (repeat (- n (len l1)) nil))) (firstn n l2))
                       (equal (nthcdr (1+ n) l1) (nthcdr (1+ n) l2)))))
  :hints (("Goal" :in-theory (enable update-nth-array
                                     equal-update-nth-casesplit))))

(defthm equal-update-nth-array-update-nth-array
  (implies (and (integerp n)
                (<= 0 n)
                (equal (len l1) (len l2)))
           (equal (equal (update-nth-array n i v1 l1) 
                         (update-nth-array n i v2 l2))
                  (and
                   (equal (update-nth i v1 (nth n l1)) 
                          (update-nth i v2 (nth n l2)))
                   (equal (firstn n l1) 
                          (firstn n l2))
                   (equal (nthcdr (1+ n) l1) 
                          (nthcdr (1+ n) l2)))))
  :hints (("Goal" :in-theory (enable equal-update-nth-casesplit
                                     update-nth-array))))

;; len-update-nth-better in fcp2k model
(defthm len-update-nth-array-better
  (equal (len (update-nth-array n i v l))
         (max (1+ (nfix n)) (len l)))
  :hints (("Goal" :in-theory (enable update-nth-array max))))


(defthm update-nth-array-update-nth-array-diff
  (implies (not (equal (nfix i1) (nfix i2)))
           (equal (update-nth-array i1 j1 v1
                                    (update-nth-array i2 j2 v2 l))
                  (update-nth-array i2 j2 v2
                                    (update-nth-array i1 j1 v1 l))))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2))))
  :hints (("Goal" :in-theory (enable update-nth-array))))

(defthm update-nth-array-update-nth-diff
  (implies
   (not (equal (nfix i1) (nfix i2)))
   (equal (update-nth-array i1 j1 v1
                      (update-nth i2 v2 l))
          (update-nth i2 v2
                      (update-nth-array i1 j1 v1 l))))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2))))
  :hints (("Goal" :in-theory (enable update-nth-array))))

(defthm update-nth-update-nth-array-diff
  (implies
   (not (equal (nfix i1) (nfix i2)))
   (equal (update-nth i1 v1
                      (update-nth-array i2 j2 v2 l))
          (update-nth-array i2 j2 v2
                      (update-nth i1 v1 l))))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2))))
  :hints (("Goal" :in-theory (enable update-nth-array))))

(defthm update-nth-array-update-nth-array-same
  (and
   (implies
    (not (equal (nfix j1) (nfix j2)))
    (equal (update-nth-array i j1 v1 (update-nth-array i j2 v2 l))
           (update-nth-array i j2 v2 (update-nth-array i j1 v1 l))))
   (equal (update-nth-array i j1 v1 (update-nth-array i j1 v2 l))
          (update-nth-array i j1 v1 l)))
  :rule-classes ((:rewrite :loop-stopper ((j1 j2))))
  :hints (("Goal" :in-theory (enable update-nth-array))))
