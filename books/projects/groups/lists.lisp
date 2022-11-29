;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")

(local (include-book "support/lists"))

;; Proper list of distinct non-nil elements:

(defun dlistp (l)
  (if (consp l)
      (and (not (member-equal (car l) (cdr l)))
           (dlistp (cdr l)))
    (null l)))

(defthm dlistp-true-listp
  (implies (dlistp l)
           (true-listp l)))

(defthm nth-dlist-distinct
  (implies (and (dlistp l) (natp i) (natp j) (< i (len l)) (< j (len l)) (not (= i j)))
            (not (equal (nth i l) (nth j l)))))

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

(defthm member-nth
  (implies (and (natp n)
                (< n (len l)))
	   (member (nth n l) l)))

(defthm ind-nth
  (implies (and (dlistp l)
                (natp i)
                (< i (len l)))
	   (equal (index (nth i l) l)
	          i)))

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
  (implies (and (dlistp x)
		(dlistp y)
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

(defthm sublistp-append
  (implies (and (sublistp l g)
                (sublistp m g))
	   (sublistp (append l m) g)))

(defthmd sublistp-<=-len
  (implies (and (dlistp l)
		(sublistp l m))
	   (<= (len l) (len m))))

(defthmd sublistp-equal-len
  (implies (and (dlistp l)
                (dlistp m)
		(sublistp l m)
		(sublistp m l))
	   (equal (len l) (len m))))

(defthmd len-proper-sublist
  (implies (and (sublistp l m)
                (dlistp l)
		(member-equal x m)
		(not (member-equal x l)))
	   (< (len l) (len m))))

(defthmd equal-len-sublistp
  (implies (and (dlistp l)
		(sublistp l m)
		(<= (len m) (len l)))
	   (sublistp m l)))

(defthm sublistp-remove1
  (implies (and (sublistp l m)
                (not (member x l)))
	   (sublistp l (remove1-equal x m))))

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
                        
;; remove1-equal:

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

(defthm len-remove1-equal
  (implies (member x l)
           (equal (len (remove1-equal x l))
	          (1- (len l)))))

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
	   (disjointp l1 m1)))

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

(defthmd disjointp-pairwise-sublistp
  (implies (and (disjointp-pairwise m)
                (sublistp l m)
		(dlistp l))
	   (disjointp-pairwise l)))

(defun dlistp-list (l)
  (if (consp l)
      (and (dlistp (car l))
           (dlistp-list (cdr l)))
    t))

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
	        (member-equal (common-member l m) m))))

;; The lemma len-1-1-equal may be functionally instantiated to show that two list have the same length:

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

(defthmd len-1-1-equal
  (equal (len (x)) (len (y))))
