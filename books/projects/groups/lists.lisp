;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")

(include-book "projects/numbers/euclid" :dir :system)
(local (include-book "support/lists"))
(local (include-book "support/perms"))

;;---------------------------------------------------------------------------------------------------
;; Lists of Distinct Elements
;;---------------------------------------------------------------------------------------------------

(defun dlistp (l)
  (if (consp l)
      (and (not (member-equal (car l) (cdr l)))
           (dlistp (cdr l)))
    (null l)))

(defthm dlistp-true-listp
  (implies (dlistp l)
           (true-listp l)))

(defthmd dlistp-len-1
  (implies (and (dlistp l) (equal (len l) 1))
           (equal (list (car l)) l)))

(defthm nth-dlist-distinct
  (implies (and (dlistp l) (natp i) (natp j) (< i (len l)) (< j (len l)) (not (= i j)))
            (not (equal (nth i l) (nth j l)))))

;; Index of a member of a dlist:

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

;; The lemma len-1-1-equal below may be functionally instantiated to show that two list have the same length:

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

;; remove1-equal:

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

;;---------------------------------------------------------------------------------------------------
;; Sublists
;;---------------------------------------------------------------------------------------------------

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

(defthm remove1-sublistp
  (sublistp (remove1-equal x l) l))

(defthm sublistp-remove1
  (implies (and (sublistp l m)
                (not (member x l)))
	   (sublistp l (remove1-equal x m))))

(defthmd sublistp-remove1-sublistp
  (implies (and (sublistp (remove1-equal x l) m)
	        (member-equal x m))
	   (sublistp l m)))

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
                        
;;---------------------------------------------------------------------------------------------------
;; Disjoint Lists
;;---------------------------------------------------------------------------------------------------
		  
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

;; Append a list of lists:

(defun append-list (l)
  (if (consp l)
      (append (car l) (append-list (cdr l)))
    ()))

(defthmd member-append-list
  (implies (and (member-equal x l) (member l m))
           (member x (append-list m))))

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
	        (member-equal (common-member l m) m))))


;;---------------------------------------------------------------------------------------------------
;; Peermutations
;;---------------------------------------------------------------------------------------------------

(defun permutationp (l m)
  (if (consp l)
      (and (member-equal (car l) m)
           (permutationp (cdr l) (remove1-equal (car l) m)))
    (endp m)))

(defthmd permutationp-member-iff
  (implies (permutationp l m)
	   (iff (member-equal x l) (member-equal x m))))

(defthmd permutationp-eq-len
  (implies (permutationp l m)
	   (equal (len l) (len m))))

;; We shall derive an equivalent formulation of permutationp, based on the following function,
;; which counts the numnber of occurrences of x in l:

(defun hits (x l)
  (if (consp l)
      (if (equal x (car l))
          (1+ (hits x (cdr l)))
        (hits x (cdr l)))
    0))

(defthm hits-member
  (implies (not (member-equal x l))
	   (equal (hits x l) 0)))

(defthm hits-consp
  (implies (not (consp l))
	   (equal (hits x l) 0)))

(defthm hits-cdr
  (implies (consp l)
           (equal (hits a (cdr l))
                  (if (equal a (car l))
	              (1- (hits a l))
	            (hits a l)))))

(defthm hits-remove1
  (equal (hits a (remove1-equal x l))
         (if (and (equal a x) (member-equal x l))
	     (1- (hits a l))
	   (hits a l))))

;; Search for an x that has different numbers of occurrences in l and m:

(defun hits-diff-aux (test l m)
  (if (consp test)
      (if (equal (hits (car test) l) (hits (car test) m))
          (hits-diff-aux (cdr test) l m)
	(list (car test)))
    ()))

(defund hits-diff (l m)
  (hits-diff-aux (append l m) l m))

(defund hits-cex (l m)
  (car (hits-diff l m)))

;; If (hits-diff l m) is non-nil, then (hits-cex l m) has different numbers of occurrences in l an m;
;; if nil, then every object has the same number of occurrences in l and m:

(defthmd hits-diff-diff
  (if (hits-diff l m)
      (not (equal (hits (hits-cex l m) l)
                  (hits (hits-cex l m) m)))
   (equal (hits x l) (hits x m))))

;; l is a permutation of m iff every object has the same number of occurrences in l and m:

(defthmd hits-diff-perm
  (iff (permutationp l m)
       (not (hits-diff l m))))

(defthmd perm-equal-hits
  (implies (permutationp l m)
           (equal (hits x l) (hits x m))))

;; Using hits-diff-diff, permutationp is easily shown to be an equivalence relation:

(defthm permutationp-reflexive
  (permutationp l l))

(defthmd permutationp-symmetric
  (implies (permutationp l m)
	   (permutationp m l)))

(defthmd permutationp-transitive
  (implies (and (permutationp l m)
	        (permutationp m n))
	   (permutationp l n)))


;; We are primarily interested in permutations of dlists.  In this case, we have another
;; equivalent formulation:

(defund permp (l m)
  (and (dlistp l)
       (dlistp m)
       (sublistp l m)
       (sublistp m l)))

(defthmd permp-permutationp
  (implies (and (dlistp l) (dlistp m))
           (iff (permutationp l m)
	        (permp l m))))

(defthmd eq-len-permp
  (implies (permp l m)
	   (equal (len l) (len m))))

;; Under the condition that one of the dlists is a sublist of the other, we have the converse of eq-len-permp:

(defthmd permp-eq-len
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (equal (len l) (len m)))
	   (permp l m)))

;; perms constructs a list of all permutations of a dlist:

(defun conses (x l)
  (if (consp l)
      (cons (cons x (car l)) (conses x (cdr l)))
    ()))

(mutual-recursion

  (defun perms-aux (l m)
    (declare (xargs :measure (list (acl2-count m) (acl2-count l) 0)))
    (if (and (consp l) (member (car l) m))
        (append (conses (car l) (perms (remove1-equal (car l) m)))
                (perms-aux (cdr l) m))
      ()))

  (defund perms (m)
    (declare (xargs :measure (list (acl2-count m) (acl2-count m) 1)))
    (if (consp m)
        (perms-aux m m)
      (list ())))
)

(defthmd len-perms
  (implies (dlistp l)
	   (equal (len (perms l))
		  (fact (len l)))))

(defthmd permp-perms
  (implies (and (dlistp l) (member-equal p (perms l)))
           (permp p l)))

(defthmd perms-permp
  (implies (and (dlistp l) (permp p l))
           (member-equal p (perms l))))

(defthm dlistp-perms
  (implies (dlistp l)
           (dlistp (perms l))))

(defthmd car-perms
  (implies (and (dlistp l) (consp l))
           (equal (car (perms l))
                  l)))


;;---------------------------------------------------------------------------------------------------
;; Intersections
;;---------------------------------------------------------------------------------------------------

;; intersect-equal is a built-in function:

(defthm sublistp-intersection
  (and (sublistp (intersection-equal l m) m)
       (sublistp (intersection-equal l m) l)))

(defthm dlistp-intersection
  (implies (dlistp l)
           (dlistp (intersection-equal l m))))

(defthmd sublistp-append-intersection-1
  (implies (sublistp m (append l1 l2))
           (sublistp m (append (intersection-equal l1 m) (intersection-equal l2 m)))))

(defthmd sublistp-append-intersection-2
  (implies (sublistp l (append m1 m2))
           (sublistp l (append (intersection-equal l m1) (intersection-equal l m2)))))

(defthmd disjointp-append-intersection-1
  (implies (disjointp l1 l2)
           (disjointp (intersection-equal l1 m)
	              (intersection-equal l2 m))))

(defthmd disjointp-append-intersection-2
  (implies (disjointp m1 m2)
           (disjointp (intersection-equal l m1)
	              (intersection-equal l m2))))

(defthmd len-append-intersection-1
  (implies (and (dlistp m)
                (dlistp l1)
                (dlistp l2)
                (disjointp l1 l2)
		(sublistp m (append l1 l2)))
           (equal (+ (len (intersection-equal l1 m))
	             (len (intersection-equal l2 m)))
		  (len m))))

(defthmd len-append-intersection-2
  (implies (and (dlistp l)
                (dlistp m1)
                (dlistp m2)
                (disjointp m1 m2)
		(sublistp l (append m1 m2)))
           (equal (+ (len (intersection-equal l m1))
	             (len (intersection-equal l m2)))
		  (len l))))


