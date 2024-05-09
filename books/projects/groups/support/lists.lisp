(in-package "DM")

(include-book "rtl/rel11/lib/top" :dir :system)

;; Proper list of distinct non-nil elements:

(defun dlistp (l)
  (if (consp l)
      (and (not (member-equal (car l) (cdr l)))
           (dlistp (cdr l)))
    (null l)))

(defthm dlistp-true-listp
  (implies (dlistp l)
           (true-listp l)))

(defthm member-nth
  (implies (and (natp n)
                (< n (len l)))
	   (member (nth n l) l)))

(defthmd dlistp-len-1
  (implies (and (dlistp l) (equal (len l) 1))
           (equal (list (car l)) l))
  :hints (("Goal" :expand ((dlistp l)))))

(defthm nth-dlist-distinct
  (implies (and (dlistp l) (natp i) (natp j) (< i (len l)) (< j (len l)) (not (= i j)))
            (not (equal (nth i l) (nth j l))))
  :hints (("Subgoal *1/11" :use ((:instance member-nth (n (1- j)) (l (cdr l)))))))

;; Index of x in l:

(defun index (x l)
  (if (consp l)
      (if (equal x (car l))
          0
	(1+ (index x (cdr l))))
    0))

(verify-guards index)

(defthmd index-1-to-1
  (implies (and (member x l)
                (member y l)
		(not (equal x y)))
           (not (= (index x l) (index y l)))))

(defthm nth-ind
  (implies (member x l)
	   (equal (nth (index x l) l)
	          x)))

(defthm ind<len
  (implies (member x l)
           (and (natp (index x l))
	        (< (index x l) (len l)))))

(defthm ind-nth
  (implies (and (dlistp l)
                (natp i)
                (< i (len l)))
	   (equal (index (nth i l) l)
	          i)))

(defthm index-append
  (equal (index x (append l m))
         (if (member-equal x l)
	     (index x l)
	   (+ (len l) (index x m)))))

;; If 2 dlists of the same length are unequal, then they must have different members at some index less than the length.
;; This index is provided by the following witness function nth-diff.  The purpose of the lemma nth-diff-diff is to
;; conclude that 2 dlists are equal once we have shown that they agree at each index:

(defun nth-diff (x y)
  (if (consp x)
      (if (equal (car x) (car y))
	  (1+ (nth-diff (cdr x) (cdr y)))
	0)
    ()))

(defthmd nth-diff-diff
  (implies (and (true-listp x)
		(true-listp y)
		(equal (len x) (len y))
		(not (equal x y)))
	   (let ((n (nth-diff x y)))
	     (and (natp n)
		  (< n (len x))
		  (not (equal (nth n x) (nth n y)))))))

;; If a true-list is not a dlist, then it has a member that occurs at 2 distinct indices, which are provided
;; by the following witness functions.  The purpose of the following lemma is to conclude that a list is a
;; dlist once we have shown that it has distincct elements at every pair of distinct indices:

(defun dcex1 (l)
  (if (consp l)
      (if (member-equal (car l) (cdr l))
          0
	(1+ (dcex1 (cdr l))))
    0))

(defun dcex2 (l)
  (if (consp l)
      (if (member-equal (car l) (cdr l))
          (1+ (index (car l) (cdr l)))
	(1+ (dcex2 (cdr l))))
    0))

(defthm dcex-lemma
  (implies (and (true-listp l) (not (dlistp l)))
           (let ((d1 (dcex1 l)) (d2 (dcex2 l)))
	     (and (natp d1) (natp d2) (< d1 d2) (< d2 (len l))
	          (equal (nth d1 l) (nth d2 l))))))

;; Sublists:

(defun sublistp (l m)
  (if (consp l)
      (and (member-equal (car l) m)
           (sublistp (cdr l) m))
    t))

(defthm member-sublist
  (implies (and (member-equal x l)
                (sublistp l m))
	   (member-equal x m)))

(defthm sublistp-cons
  (implies (sublistp l m)
           (sublistp l (cons x m))))

(defthm sublistp-self
  (sublistp l l))

(defthmd sublistp-sublistp
  (implies (And (sublistp l m) (sublistp m n))
           (sublistp l n)))

(defthm sublistp-remove1
  (implies (and (sublistp l m)
                (not (member x l)))
	   (sublistp l (remove1-equal x m))))

(defthm remove1-sublistp
  (sublistp (remove1-equal x l) l))

(defthm dlistp-remove1
  (implies (dlistp l)
           (and (dlistp (remove1-equal x l))
	        (not (member-equal x (remove1-equal x l))))))

(defthm remove1-member
  (implies (not (member-equal x l))
	   (not (member-equal x (remove1 y l)))))

(defthm member-remove1
  (implies (and (member-equal x l)
                (not (equal x y)))
	   (member-equal x (remove1-equal y l))))

(defthm sublistp-append
  (implies (and (sublistp l g)
                (sublistp m g))
	   (sublistp (append l m) g)))

(defthm len-remove1-equal
  (implies (member x l)
           (equal (len (remove1-equal x l))
	          (1- (len l)))))

(defun sublistp-induct (l m)
  (declare (irrelevant m))
  (if (consp l)
      (sublistp-induct (cdr l) (remove1-equal (car l) m))
    ()))

(defthmd sublistp-<=-len
  (implies (and (dlistp l)
		(sublistp l m))
	   (<= (len l) (len m)))
  :hints (("Goal" :induct (sublistp-induct l m))))

(defthmd sublistp-equal-len
  (implies (and (dlistp l)
                (dlistp m)
		(sublistp l m)
		(sublistp m l))
	   (equal (len l) (len m)))
  :hints (("Goal" :use (sublistp-<=-len (:instance sublistp-<=-len (l m) (m l))))))

(defthmd len-proper-sublist
  (implies (and (sublistp l m)
                (dlistp l)
		(member-equal x m)
		(not (member-equal x l)))
	   (< (len l) (len m)))
  :hints (("Goal" :use ((:instance sublistp-<=-len (m (remove1-equal x m)))))))

(local-defthmd equal-len-sublistp-1
  (implies (and (dlistp l)
		(sublistp l m)
		(<= (len m) (len l))
		(sublistp n m))
	   (sublistp n l))
  :hints (("Subgoal *1/3" :use ((:instance len-proper-sublist (x (car n)))))))

(defthmd equal-len-sublistp
  (implies (and (dlistp l)
		(sublistp l m)
		(<= (len m) (len l)))
	   (sublistp m l))
  :hints (("Goal" :use ((:instance equal-len-sublistp-1 (n m))))))

;; If l is not a sublist of m, then it has a member that is not a member of m, which is provided by the
;; following witness function.  Then purpose of the following lemma is to conclude that l is a sublist
;; of m once we have shown that each of its members is a member of m:

(defun scex1 (l m)
  (if (consp l)
      (if (member-equal (car l) m)
          (scex1 (cdr l) m)
	(car l))
    0))

(defthmd scex1-lemma
  (implies (not (sublistp l m))
           (let ((x (scex1 l m)))
	     (and (member-equal x l) (not (member-equal x m))))))
                        
;; If l is not a sublist of m, then it has a member that is not a member of m, the index of which is provided
;; by the following witness function.  Then purpose of the following lemma is to conclude that l is a sublist
;; of m once we have shown that its member at every index is a member of m:

(defun scex2 (l m)
  (if (consp l)
      (if (member-equal (car l) m)
          (1+ (scex2 (cdr l) m))
	0)
    0))

(defthmd scex2-lemma
  (implies (not (sublistp l m))
           (let ((k (scex2 l m)))
	     (and (natp k) (< k (len l)) (not (member-equal (nth k l) m))))))
                        
;; Append a list of lists:

(defun append-list (l)
  (if (consp l)
      (append (car l) (append-list (cdr l)))
    ()))

(defthmd member-append-list
  (implies (and (member-equal x l) (member l m))
           (member x (append-list m))))

;; Disjoint lists:
		  
(defun disjointp (l m)
  (if (consp l)
      (and (not (member-equal (car l) m))
           (disjointp (cdr l) m))
    t))

(defthm disjointp-disjoint
  (implies (and (disjointp l m)
                (member-equal x l))
	   (not (member-equal x m))))

(defthm disjointp-cons
  (implies (and (disjointp m l)
                (not (member-equal x m)))
	   (disjointp m (cons x l))))

(defthmd disjointp-symmetric
  (implies (disjointp l m)
           (disjointp m l)))

(defthmd sublistp-disjointp
  (implies (and (sublistp l1 l2)
                (disjointp l2 m))
	   (disjointp l1 m)))

(defthmd sublistp-sublistp-disjointp
  (implies (and (sublistp l1 l2)
                (sublistp m1 m2)
                (disjointp l2 m2))
	   (disjointp l1 m1))
  :hints (("Goal" :use ((:instance disjointp-symmetric (l l2) (m m2))
                        (:instance disjointp-symmetric (l m1) (m l2))
			(:instance sublistp-disjointp (l1 m1) (l2 m2) (m l2))
			(:instance sublistp-disjointp (l1 m1) (m m1))))))

(defthm dlistp-append
  (implies (and (dlistp l)
                (dlistp m)
		(disjointp l m))
	   (dlistp (append l m))))

(defun disjointp-list (l m)
  (if (consp m)
      (and (disjointp l (car m))
	   (disjointp-list l (cdr m)))
    t))

(defthm disjointp-append-list
  (implies (disjointp-list l m)
           (disjointp l (append-list m))))

(defun disjointp-pairwise (l)
  (if (consp l)
      (and (disjointp-list (car l) (cdr l))
	   (disjointp-pairwise (cdr l)))
    t))

(defthm disjointp-pairwise-sublistp
  (implies (and (sublistp l m)
                (dlistp l)
                (disjointp-pairwise m))
	   (disjointp-pairwise l)))

(defun dlistp-list (l)
  (if (consp l)
      (and (dlistp (car l))
           (dlistp-list (cdr l)))
    t))

(defthm dlistp-list-sublist
  (implies (and (sublistp l m)
                (dlistp-list m))
	   (dlistp-list l)))

(defthm dlistp-append-list
  (implies (and (dlistp-list l)
                (disjointp-pairwise l))
	   (dlistp (append-list l))))

;; If two lists are not disjoint, then they have a common member:

(defun common-member (l m)
  (if (consp l)
      (if (member-equal (car l) m)
          (car l)
	(common-member (cdr l) m))
    ()))

(defthm common-member-shared
  (implies (not (disjointp l m))
           (and (member-equal (common-member l m) l)
	        (member-equal (common-member l m) m)))
  :hints (("Goal" :induct (true-listp l))))

;; The lemma len-x-y below may be functionally instantiated to show that two list have the same length:

(encapsulate (((x) => *) ((y) => *) ((xy *) => *) ((yx *) => *))
  (local (defun x () '(0)))
  (local (defun y () '(0)))
  (local (defun xy (a) (declare (ignore a)) 0))
  (local (defun yx (a) (declare (ignore a)) 0))
  (defthm dlistp-x (dlistp (x)))
  (defthm dlistp-y (dlistp (y)))
  (defthm yx-xy
    (implies (member-equal a (x))
             (and (member-equal (xy a) (y))
	          (equal (yx (xy a)) a))))
  (defthm xy-yx
    (implies (member-equal a (y))
             (and (member-equal (yx a) (x))
	          (equal (xy (yx a)) a)))))

(local-defun xy-in (x y)
  (if (consp x)
      (and (member-equal (xy (car x)) y)
           (xy-in (cdr x) y))
    t))

(local-defun yx-in (y x)
  (if (consp y)
      (and (member-equal (yx (car y)) x)
           (yx-in (cdr y) x))
    t))

(local-defthm xy-inj
  (implies (and (member-equal x1 (x))
                (member-equal x2 (x))
		(equal (xy x1) (xy x2)))
	   (equal x1 x2))
  :rule-classes ()
  :hints (("Goal" :use ((:instance yx-xy (a x1))
                        (:instance yx-xy (a x2))))))

(local-defthm yx-inj
  (implies (and (member-equal y1 (y))
                (member-equal y2 (y))
		(equal (yx y1) (yx y2)))
	   (equal y1 y2))
  :rule-classes ()
  :hints (("Goal" :use ((:instance xy-yx (a y1))
                        (:instance xy-yx (a y2))))))

(local-defthm xy-in-remove-1
  (implies (and (dlistp x)
                (sublistp x (x))
		(xy-in x y)
		(member-equal x1 (x))
		(not (member-equal x1 x)))
	   (xy-in x (remove1-equal (xy x1) y)))
  :hints (("Goal" :induct (dlistp x))
          ("Subgoal *1/1" :use ((:instance xy-inj (x2 (car x)))))))
	   
(local-defthm xy-in-remove
  (implies (and (dlistp x)
                (dlistp y)
                (sublistp x (x))
		(xy-in x y))
	   (xy-in (cdr x) (remove1-equal (xy (car x)) y)))
  :hints (("Goal" :use ((:instance xy-in-remove-1 (x (cdr x)))))))

(local-defthm yx-in-cdr-1
  (implies (and (dlistp y)
                (sublistp y (y))
		(yx-in y x)
		(member-equal y1 (y))
		(not (member-equal (xy (car x)) y)))
	   (yx-in y (cdr x))))

(local-defthm yx-in-cdr
  (implies (and (dlistp y)
                (sublistp y (y))
		(yx-in y x))
	   (yx-in (remove1-equal (xy (car x)) y) (cdr x)))
  :hints (("Goal" :use ((:instance yx-in-cdr-1 (y (remove1-equal (xy (car x)) y)))))))

(local-defun xy-induct (x y)
  (declare (irrelevant y))
  (if (consp x)
      (xy-induct (cdr x) (remove1-equal (xy (car x)) y))
    ()))

(local-defthmd sublistp-trans
  (implies (and (sublistp l m)
                (sublistp m p))
	   (sublistp l p)))

(local-defthmd len-x-y
  (implies (and (dlistp x)
                (dlistp y)
		(sublistp x (x))
		(sublistp y (y))
		(xy-in x y)
		(yx-in y x))
	   (equal (len x) (len y)))
  :hints (("Goal" :induct (xy-induct x y))
          ("Subgoal *1/1" :use ((:instance sublistp-trans (l (remove1-equal (xy (car x)) y)) (m y) (p (y)))))))

(local-defthm xy-in-x-y
  (implies (sublistp x (x))
           (xy-in x (y))))

(local-defthm yx-in-y-x
  (implies (sublistp y (y))
           (yx-in y (x))))

(defthmd len-1-1-equal
  (equal (len (x)) (len (y)))
  :hints (("Goal" :use ((:instance len-x-y (x (x)) (y (y)))))))


;;---------------------------------------------------------------------------------------------------------------

;; Some properties of intersection-equal:

(local-defthmd sublistp-intersection-1
  (implies (sublistp l1 l)
           (and (sublistp (intersection-equal l1 m) m)
	        (sublistp (intersection-equal l1 m) l)))
  :hints (("Goal" :expand ((INTERSECTION-EQUAL L1 M) (INTERSECTION-EQUAL NIL M)))))

(defthm sublistp-intersection
  (and (sublistp (intersection-equal l m) m)
       (sublistp (intersection-equal l m) l))
  :hints (("Goal" :use ((:instance sublistp-intersection-1 (l1 l))))))

(local-defthmd dlistp-intersection-1
  (implies (and (dlistp l1) (sublistp l1 l))
           (dlistp (intersection-equal l1 m)))
  :hints (("Goal" :expand ((INTERSECTION-EQUAL L1 M) (INTERSECTION-EQUAL NIL M)))))

(defthm dlistp-intersection
  (implies (dlistp l)
           (dlistp (intersection-equal l m)))
  :hints (("Goal" :use ((:instance dlistp-intersection-1 (l1 l))))))

(local-defthmd sublistp-append-intersection-1-1
  (implies (and (sublistp m1 m) (sublistp m1 (append l1 l2)))
           (sublistp m1 (append (intersection-equal l1 m) (intersection-equal l2 m)))))

(defthmd sublistp-append-intersection-1
  (implies (sublistp m (append l1 l2))
           (sublistp m (append (intersection-equal l1 m) (intersection-equal l2 m))))
  :hints (("Goal" :use ((:instance sublistp-append-intersection-1-1 (m1 m))))))

(local-defthmd sublistp-append-intersection-2-1
  (implies (and (sublistp l1 l) (sublistp l1 (append m1 m2)))
           (sublistp l1 (append (intersection-equal l m1) (intersection-equal l m2)))))

(defthmd sublistp-append-intersection-2
  (implies (sublistp l (append m1 m2))
           (sublistp l (append (intersection-equal l m1) (intersection-equal l m2))))
  :hints (("Goal" :use ((:instance sublistp-append-intersection-2-1 (l1 l))))))

(local-defthmd disjointp-append-intersection-1-1
  (implies (and (sublistp l3 l1) (disjointp l1 l2))
           (disjointp (intersection-equal l3 m)
	              (intersection-equal l2 m)))
  :hints (("Goal" :expand ((INTERSECTION-EQUAL L3 M)))))

(defthmd disjointp-append-intersection-1
  (implies (disjointp l1 l2)
           (disjointp (intersection-equal l1 m)
	              (intersection-equal l2 m)))
  :hints (("Goal" :use ((:instance disjointp-append-intersection-1-1 (l3 l1))))))

(defthmd disjointp-append-intersection-2
  (implies (disjointp m1 m2)
           (disjointp (intersection-equal l m1)
	              (intersection-equal l m2)))
  :hints (("Goal" :induct (len l) :expand ((INTERSECTION-EQUAL L M1) (INTERSECTION-EQUAL L M2)))))

(defthmd len-append-intersection-1
  (implies (and (dlistp m)
                (dlistp l1)
                (dlistp l2)
                (disjointp l1 l2)
		(sublistp m (append l1 l2)))
           (equal (+ (len (intersection-equal l1 m))
	             (len (intersection-equal l2 m)))
		  (len m)))
  :hints (("Goal" :use (disjointp-append-intersection-1
                        sublistp-append-intersection-1
			(:instance sublistp-equal-len (l (append (intersection-equal l1 m) (intersection-equal l2 m))))
                        (:instance sublistp-intersection (l l1))
			(:instance sublistp-intersection (l l2))
			(:instance dlistp-intersection (l l1))
			(:instance dlistp-intersection (l l2))))))

(defthmd len-append-intersection-2
  (implies (and (dlistp l)
                (dlistp m1)
                (dlistp m2)
                (disjointp m1 m2)
		(sublistp l (append m1 m2)))
           (equal (+ (len (intersection-equal l m1))
	             (len (intersection-equal l m2)))
		  (len l)))
  :hints (("Goal" :use (disjointp-append-intersection-2
                        sublistp-append-intersection-2
			(:instance sublistp-equal-len (l (append (intersection-equal l m1) (intersection-equal l m2))) (m l))
                        (:instance sublistp-intersection (m m1))
			(:instance sublistp-intersection (m m2))
			(:instance dlistp-intersection (m m1))
			(:instance dlistp-intersection (m m2))))))
