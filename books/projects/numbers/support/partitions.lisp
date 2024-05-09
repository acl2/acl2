(in-package "DM")

(include-book "projects/groups/lists" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "projects/groups/cauchy" :dir :system)
(in-theory (enable divides))

;; A partition of a positive integer n is a list of positive integers the sum of which is n:

(defun sum-list (l)
  (if (consp l)
      (+ (car l) (sum-list (cdr l)))
    0))

(defun pos-listp (l)
  (if (consp l)
      (and (posp (car l))
           (pos-listp (cdr l)))
    (null l)))

(defun partp (l n)
  (and (pos-listp l)
       (equal (sum-list l) n)))

;; We consider two sets of partitions.  The first consists of those that contain only odd
;; integers.  We shall refer to these as "odd partitions":

(defun odd-listp (l)
  (if (consp l)
      (and (oddp (car l))
	   (odd-listp (cdr l)))
    (null l)))

(defun odd-partp (l n)
  (and (partp l n)
       (odd-listp l)))

;; The second set consists of those partitions with pairwise distinct members.  We shall
;; refer to these as "distinct partitions":

(defun dis-partp (l n)
  (and (partp l n)
       (dlistp l)))

;; Two partitions are considered to be equivalent if one is a permutation of the other.
;; Note that each of the sets of partitions of interest consists of a union of equivalence
;; classes:

(defthm sum-listp-remove1
  (implies (and (pos-listp l) (member-equal x l))
           (equal (sum-list (remove1-equal x l))
	          (- (sum-list l) x))))

(defthm pos-listp-remove1
  (implies (pos-listp l)
           (pos-listp (remove1-equal x l))))

(defthmd sum-list-perm
  (implies (and (pos-listp l) (pos-listp m) (permutationp l m))
           (equal (sum-list l) (sum-list m))))

(defthmd odd-listp-remove1
  (implies (and (pos-listp l) (oddp x) (odd-listp (remove1-equal x l)))
           (odd-listp l)))

(defthmd odd-listp-perm
  (implies (and (posp n) (pos-listp l) (pos-listp m) (odd-listp l) (permutationp l m))
           (odd-listp m))
  :hints (("Subgoal *1/5" :use ((:instance odd-listp-remove1 (x (car l)) (l m))))))

(defthmd odd-partp-inv
  (implies (and (posp n) (pos-listp l) (pos-listp m) (odd-partp l n) (permutationp m l))
           (odd-partp m n))
  :hints (("Goal" :use (sum-list-perm odd-listp-perm (:instance permutationp-symmetric (l m) (m l))))))

(defthm pos-listp-true-listp
  (implies (pos-listp l)
	   (true-listp l)))

(defthmd dlistp-perm
  (implies (and (dlistp l) (true-listp m) (permutationp m l))
	   (dlistp m))
  :hints (("Subgoal *1/5" :use ((:instance permutationp-member-iff (x (car m)) (m (remove1-equal (car m) l)) (l (cdr m)))))))

(defthmd dis-partp-inv
  (implies (and (posp n) (pos-listp l) (pos-listp m) (dis-partp l n) (permutationp m l))
           (dis-partp m n))
  :hints (("Goal" :use (sum-list-perm dlistp-perm permutationp-symmetric (:instance permutationp-symmetric (l m) (m l))))))

;; Euler's partition theorem states that the number of equivalence classes of odd
;; partitions of n is equal to the number of equivalence classes of distinct partitions of n.

;; How do we count these equivalence classes?  For each of the two sets of partitions, we 
;; shall construct a dlist of partitions belonging to the set and prove the following two
;; properties:
;;   (1) No member of the list is a permutation of another;
;;   (2) Every element of the set is a permutation of some member of the list.
;; We may then conclude that the number of equivalence classes is the length of the list,
;; and we need only show that the two lists have the same length.

;; For the odd partitions, our list will consist of all odd sorted partitions of n, i.e.,
;; those that are monotonically increasing with respect to the usual ordering of the integers.
;; For distinct partitions, we shall do something similar, but it will be convenient to use
;; a different ordering of the positive integers.  We must show that (1) and (2) hold for each
;; list.  In fact, we shall prove a general result:  Given a total order t<= on the positive
;; integers and a predicate pred defined on lists of positive integers, if predl is a dlist
;; consisting of all lists of positive integers that satisfy pred and are ordered with respect
;; to t<=, then predl satisfies (1) and (2).

;; For this we use encapsulation and functional instantiation.


;;------------------------------------------------------------------------------------------------

;; The function t<= is constrained to be a total order of the positive integers:

(encapsulate (((t<= * *) => *))
  (local (defun t<= (x y) (<= x y)))
  (defthmd t<=-reflex
    (implies (posp x) (t<= x x)))
  (defthmd t<=-assoc
    (implies (and (posp x) (posp y) (posp z) (t<= x y) (t<= y z))
             (t<= x z)))
  (defthm t<=-antisym
    (implies (and (posp x) (posp y) (t<= x y) (t<= y x))
             (equal x y))
    :rule-classes ())
  (defthmd t<=-total
    (implies (and (posp x) (posp y))
             (or (t<= x y) (t<= y x)))))

;; A list is sorted with respect to t<= if it satisfies the following:

(defun tsortedp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (t<= (car l) (cadr l))
           (tsortedp (cdr l)))
    t))

;; A second encapsulation constrains pred and predl:

(encapsulate (((pred *) => *) ((predl) => *))

  ;; pred is a predicate on lists of positives that is invariant under permutation:
  
  (local (defun pred (l) (declare (ignore l)) ()))
  
  (defthmd pred-inv
    (implies (and (pos-listp l) (pos-listp m) (pred l) (permutationp m l))
             (pred m)))

  ;; (predl) is a dlist consisting of all ordered lists that satisfy pred:
  
  (local (defun predl () ()))
  
  (defthmd dlistp-predl
    (dlistp (predl)))
    
  (defthmd member-predl
    (iff (member-equal l (predl))
         (and (pos-listp l) (tsortedp l) (pred l)))))

;; We shall prove the following:
;;   (1) No member of (predl) is a permutation of another member of (predl);
;;   (2) Every list that satisfies pred is a permutation of some member of (predl).

;; The minimal member of a list:

(defun tleast-aux (x l)
  (if (consp l)
      (if (t<= x (car l))
          (tleast-aux x (cdr l))
	(tleast-aux (car l) (cdr l)))
    x))

(defthmd member-pos-list
  (implies (and (pos-listp l) (member-equal x l))
           (posp x)))

(defthmd member-tleast-aux
  (implies (and (posp x) (pos-listp l))
           (and (posp (tleast-aux x l))
	        (or (equal (tleast-aux x l) x)
	            (member-equal (tleast-aux x l) l))
		(t<= (tleast-aux x l) x)
                (implies (member-equal y l)
                         (t<= (tleast-aux x l) y))))
  :hints (("Subgoal *1/3" :use (t<=-reflex))
          ("Subgoal *1/2" :use ((:instance t<=-total (y (car l)))
	                        (:instance member-pos-list (x (tleast-aux (car l) (cdr l))))
                                (:instance t<=-assoc (x (tleast-aux (car l) (cdr l))) (y (car l)) (z x))))
	  ("Subgoal *1/1" :use ((:instance t<=-assoc (x (tleast-aux x (cdr l))) (y (car l)) (z x))
	                        (:instance t<=-assoc (x (tleast-aux x (cdr l))) (y x) (z (car l)))
	                        (:instance member-pos-list (x (tleast-aux x (cdr l))))))))

(defun tleast (l)
  (tleast-aux (car l) (cdr l)))

(defthmd member-tleast
  (implies (and (consp l) (pos-listp l))
           (and (posp (tleast l))
	        (member-equal (tleast l) l)
	        (implies (member-equal x l)
                         (t<= (tleast l) x))))
  :hints (("Goal" :in-theory (enable tleast)
                  :use ((:instance member-tleast-aux (x (car l)) (l (cdr l)) (y x))))))

(defthmd tleast-aux-tsorted
  (implies (and (posp x) (pos-listp l) (tsortedp l) (or (null l) (t<= x (car l))))
           (equal (tleast-aux x l) x))
  :hints (("Subgoal *1/1" :use ((:instance t<=-assoc (y (car l)) (z (cadr l)))))))

(defthmd tleast-tsorted
  (implies (and (consp l) (pos-listp l) (tsortedp l))
           (equal (tleast l) (car l)))
  :hints (("Goal" :in-theory (enable tleast)
                  :use ((:instance tleast-aux-tsorted (x (car l)) (l (cdr l)))))))

(defthmd tleast-perm
  (implies (and (consp l) (pos-listp l) (pos-listp m) (permutationp l m))
           (equal (tleast l) (tleast m)))
  :hints (("Goal" :use ((:instance member-tleast (x (tleast m)))
                        (:instance member-tleast (l m) (x (tleast l)))
			(:instance permutationp-member-iff (x (tleast l)))
			(:instance permutationp-member-iff (x (tleast m)))
			(:instance t<=-antisym (x (tleast l)) (y (tleast m)))))))

(defthm tsortedp-perm-equal-cars
  (implies (and (consp l)
                (pos-listp l)
                (pos-listp m)
		(tsortedp l)
		(tsortedp m)
		(permutationp l m))
	   (equal (car l) (car m)))
  :hints (("Goal" :use (tleast-perm tleast-tsorted
                        (:instance tleast-tsorted (l m)))))           
  :rule-classes ())

;; No sorted list of positive integers is a permutation of another:

(defthm tsortedp-perm-equal
  (implies (and (pos-listp l)
                (pos-listp m)
		(tsortedp l)
		(tsortedp m)
		(permutationp l m))
	   (equal l m))
  :rule-classes ()
  :hints (("Subgoal *1/6" :use (tsortedp-perm-equal-cars))
          ("Subgoal *1/4" :use (tsortedp-perm-equal-cars))
          ("Subgoal *1/2" :use (tsortedp-perm-equal-cars))))

;;  (1) No member of (predl) is a permutation of another:

(defthm predl-perm-equal
  (implies (and (member-equal l (predl))
                (member-equal m (predl))
		(permutationp l m))
	   (equal l m))
  :rule-classes ()
  :hints (("Goal" :use (tsortedp-perm-equal member-predl
                        (:instance member-predl (l m))))))
		

;; A sorting function:

(defun tsort (l)
  (declare (xargs :measure (len l)))
  (if (and (consp l) (pos-listp l) (member-equal (tleast l) l))
      (cons (tleast l)
            (tsort (remove1 (tleast l) l)))
    ()))

;; Every list of positive integers is a permutation of some sorted list:

(defthmd perm-tsort
  (implies (pos-listp l)
           (permutationp (tsort l) l))
  :hints (("Subgoal *1/3" :use (member-tleast))))

(defthmd tsortedp-tsort
  (implies (pos-listp l)
           (and (pos-listp (tsort l))
                (tsortedp (tsort l))))
  :hints (("Subgoal *1/1" :use ((:instance member-tleast (x (car (tsort (remove1-equal (tleast l) l)))))
                                (:instance perm-tsort (l (remove1-equal (tleast l) l)))
				(:instance permutationp-member-iff (l (tsort l)) (m l)
				                                   (x (car (tsort (remove1-equal (tleast l) l)))))))))

(defthmd perm-tsortedp-tsort
  (implies (pos-listp l)
           (and (pos-listp (tsort l))
                (permutationp (tsort l) l)
		(tsortedp (tsort l))))
  :hints (("Goal" :use (perm-tsort tsortedp-tsort))))

;; (2) Every list that satisfies pred is a permutation of some member of (predl):

(defthmd perm-predl
  (implies (and (pos-listp l) (pred l))
           (and (member-equal (tsort l) (predl))
	        (permutationp (tsort l) l)))
  :hints (("Goal" :use (perm-tsortedp-tsort
                        (:instance pred-inv (m (tsort l)))
			(:instance member-predl (l (tsort l)))))))

;; We shall functionally instantiate the above results twice, first for the odd partitions of n and
;; then the distinct partitions of n.


;;------------------------------------------------------------------------------------------------

;; For the odd partitions, we substitute the standard order <= for t<=.  The predicate corresponding
;; to tsorted is defined as follows:

(defun sortedp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (<= (car l) (cadr l))
	   (sortedp (cdr l)))
    t))

;; The predicate corresponding to pred is (lambda (l) (odd-partp l n)).  Corresponding to the list
;; predl,  we construct a list of all sorted odd partitions of n.  First, given odd k, we construct
;; a list of all sorted odd partitions p of n with (car p) >= k:

(defun odd-parts-aux (n k)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (posp n) (posp k))
      (if (= k n)
	  (list (list n))
	(if (< k n)
            (append (conses k (odd-parts-aux (- n k) k))
                    (odd-parts-aux n (+ k 2)))
	  ()))
    ()))

;; A list of all ordered odd partitions of n:

(defun odd-parts (n)
  (odd-parts-aux n 1))

;; The sorting function corresponding to tsort:

(defun least-aux (x l)
  (if (consp l)
      (if (<= x (car l))
          (least-aux x (cdr l))
	(least-aux (car l) (cdr l)))
    x))

(defun least (l)
  (least-aux (car l) (cdr l)))

(defun sort (l)
  (declare (xargs :measure (len l)))
  (if (and (consp l) (pos-listp l) (member-equal (least l) l))
      (cons (least l)
            (sort (remove1 (least l) l)))
    ()))

;; Since <= is known to be a total order and we have already proved odd-partp-inv we need only
;; derive the properties corresponding to dlistp-predl and member-predl.

(defun odd-parts-aux-induct (n k p)
  (declare (irrelevant p) (xargs :measure (nfix (- n k))))
  (if (and (posp n) (posp k) (< k n))
      (list (odd-parts-aux-induct (- n k) k (cdr p))
            (odd-parts-aux-induct n (+ k 2) p))
    t))

(defthm member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
	   (member-equal x m))))

(defthm member-conses
  (iff (member-equal p (conses k l))
	   (and (consp p)
		(equal (car p) k)
		(member-equal (cdr p) l))))

(defthmd odd-partp-odd-parts-aux
  (implies (and (posp n) (posp k) (oddp k)
		(member-equal l (odd-parts-aux n k)))
	   (and (odd-partp l n)
		(sortedp l)
		(>= (car l) k)))
  :hints (("Goal" :induct (odd-parts-aux-induct n k l))))

(defthmd disjointp-conses
  (implies (and (posp n) (posp k) (oddp k))
	   (disjointp (conses k (odd-parts-aux (+ (- k) n) k))
                      (odd-parts-aux n (+ 2 k))))
  :hints (("Goal" :in-theory (disable common-member-shared)
	          :use ((:instance odd-partp-odd-parts-aux (k (+ 2 k))
				                           (l (common-member (conses k (odd-parts-aux (+ (- k) n) k))
                                                                             (odd-parts-aux n (+ 2 k)))))
			(:instance common-member-shared (l (conses k (odd-parts-aux (+ (- k) n) k)))
				   (m (odd-parts-aux n (+ 2 k))))))))

(defthm dlistp-conses
  (implies (dlistp l)
	   (dlistp (conses k l)))
  :hints (("Subgoal *1/2" :use ((:instance member-conses (p (cons k (car l))) (l (cdr l)))))))
  
(defthmd dlistp-odd-parts-aux
  (implies (and (posp n) (posp k) (oddp k))
	   (dlistp (odd-parts-aux n k)))
  :hints (("subgoal *1/13" :use (disjointp-conses
				 (:instance dlistp-append (l (conses k (odd-parts-aux (+ (- k) n) k)))
					    (m (odd-parts-aux n (+ 2 k))))))))

(defthmd dlistp-odd-parts
  (implies (posp n)
	   (dlistp (odd-parts n)))
  :hints (("Goal" :use ((:instance dlistp-odd-parts-aux (k 1))))))

(defthmd car-pos-list
  (implies (and (consp l) (pos-listp l))
	   (<= (car l) (sum-list l))))

(defthmd car-cdr-pos-list
  (implies (and (consp l) (pos-listp l) (cdr l))
	   (< (car l) (sum-list l))))

(defthm oddp+2
  (implies (and (posp k) (posp n)
		(oddp k) (oddp n)
		(<= k n) (< n (+ k 2)))
	   (equal k n))
  :rule-classes ())

(defthmd member-odd-parts-aux
  (implies (and (posp n) (posp k) (oddp k)
		(odd-partp l n)
		(sortedp l)
		(>= (car l) k))
	   (member-equal l (odd-parts-aux n k)))
  :hints (("Goal" :induct (odd-parts-aux-induct n k l))
	  ("Subgoal *1/2" :use (car-pos-list car-cdr-pos-list))
	  ("Subgoal *1/1" :use (car-pos-list car-cdr-pos-list odd-parts-aux
                                (:instance oddp+2 (n (car l)))))))

(defthmd member-odd-parts
  (implies (posp n)
           (iff (member-equal l (odd-parts n))
	        (and (odd-partp l n)
		     (sortedp l))))
  :hints (("Goal" :use ((:instance odd-partp-odd-parts-aux (k 1))
                        (:instance member-odd-parts-aux (k 1))))))

;; In particular, (odd-parts n) is a list of odd partitions:

(defthmd odd-partp-odd-parts
  (implies (and (posp n) (member-equal l (odd-parts n)))
	   (odd-partp l n))
  :hints (("Goal" :use (member-odd-parts))))


;;------------------------------------------------------------------------------------------------

;; The desired results follow by functional instantiation of predl-perm-equal and perm-predl:

(defthm odd-parts-perm-equal
  (implies (and (posp n)
                (member-equal l (odd-parts n))
		(member-equal m (odd-parts n))
		(permutationp l m))
	   (equal l m))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance predl-perm-equal
                          (t<= (lambda (x y) (if (posp n) (<= x y) (t<= x y))))
                          (pred (lambda (l) (if (posp n) (odd-partp l n) (pred l))))
			  (predl (lambda () (if (posp n) (odd-parts n) (predl))))
                          (tsortedp (lambda (l) (if (posp n) (sortedp l) (tsortedp l))))
                          (tleast-aux (lambda (x l) (if (posp n) (least-aux x l) (tleast-aux x l))))
			  (tleast (lambda (l) (if (posp n) (least l) (tleast l)))))))
	  ("Subgoal 6" :use (t<=-total))
	  ("Subgoal 5" :use (t<=-antisym))
	  ("Subgoal 4" :use (t<=-assoc))
	  ("Subgoal 3" :use (t<=-reflex))	  
	  ("Subgoal 2" :use (member-predl member-odd-parts))
	  ("Subgoal 1" :use (pred-inv odd-partp-inv))))

(defthmd perm-odd-parts
  (implies (and (posp n)
                (odd-partp l n))
	   (and (member-equal (sort l) (odd-parts n))
	        (permutationp (sort l) l)))
  :hints (("Goal" :use ((:functional-instance perm-predl
                          (t<= (lambda (x y) (if (posp n) (<= x y) (t<= x y))))
                          (pred (lambda (l) (if (posp n) (odd-partp l n) (pred l))))
			  (predl (lambda () (if (posp n) (odd-parts n) (predl))))
                          (tsortedp (lambda (l) (if (posp n) (sortedp l) (tsortedp l))))
                          (tleast-aux (lambda (x l) (if (posp n) (least-aux x l) (tleast-aux x l))))
			  (tleast (lambda (l) (if (posp n) (least l) (tleast l))))
			  (tsort (lambda (l) (if (posp n) (sort l) (tsort l)))))))))
		

;;------------------------------------------------------------------------------------------------

;; We define a total order on the positive integers based on the factorization of an integer as
;; the product of a power of 2 and an odd integer:

(defun pow2 (n)
  (if (and (posp n) (evenp n))
      (* 2 (pow2 (/ n 2)))
    1))

(defthmd pow2-divides
  (implies (posp n)
           (divides (pow2 n) n)))

(defthm pow2-power-2
  (implies (posp n)
           (powerp (pow2 n) 2)))

(defun oddf (n)
  (/ n (pow2 n)))

(defthmd posp-oddf
  (implies (posp n)
           (posp (oddf n)))
  :hints (("Goal" :use (pow2-divides))))

(defthmd oddp-oddf
  (implies (posp n)
           (oddp (oddf n))))

(defun d<= (x y)
  (or (< (oddf x) (oddf y))
      (and (= (oddf x) (oddf y))
	   (<= x y))))

;; d<= is trivially verified to be a total order on the positive integers:

(defthmd d<=-reflex
  (implies (posp x) (d<= x x)))

(defthmd d<=-assoc
  (implies (and (posp x) (posp y) (posp z) (d<= x y) (d<= y z))
           (d<= x z)))

(defthm d<=-antisym
  (implies (and (posp x) (posp y) (d<= x y) (d<= y x))
           (equal x y))
  :rule-classes ())

(defthmd d<=-total
  (implies (and (posp x) (posp y))
           (or (d<= x y) (d<= y x))))

;; A sorted list with respect to d<=:

(defun dsortedp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (d<= (car l) (cadr l))
           (dsortedp (cdr l)))
    t))

;; The sorting function:
  
(defun dleast-aux (x l)
  (if (consp l)
      (if (d<= x (car l))
          (dleast-aux x (cdr l))
	(dleast-aux (car l) (cdr l)))
    x))

(defun dleast (l)
  (dleast-aux (car l) (cdr l)))

(defun dsort (l)
  (declare (xargs :measure (len l)))
  (if (and (consp l) (pos-listp l) (member-equal (dleast l) l))
      (cons (dleast l)
            (dsort (remove1 (dleast l) l)))
    ()))

;; We shall construct a dlist (dis-parts n) consisting of the distinct partitions of n that are 
;; sorted with respect to d<=, based on a function odd2dis that converts an odd partition to 
;; a distinct partition.  This function is in turn based on a decomposition of a sorted odd 
;; partition l as the appending of 2 lists: (1) the initial segment consisting of all occurrences 
;; of (car l) and (2) the remaining tail:

(defun copies (k n)
  (if (posp k)
      (cons n (copies (1- k) n))
    ()))

(defun count-init (x l)
  (if (and (consp l) (= x (car l)))
      (1+ (count-init x (cdr l)))
    0))

(defthmd opd-1
  (implies (and (posp n) (odd-partp l n))
           (posp (count-init (car l) l))))

(defthmd opd-2
  (implies (and (pos-listp l)
                (natp k) (posp x) (<= k (count-init x l)))
           (equal (append (copies k x) (nthcdr k l))
	          l)))

(defthmd opd-3
  (implies (and (pos-listp l)
                (natp k) (posp x))
           (equal (sum-list (append (copies k x) l))
	          (+ (* k x) (sum-list l)))))

(defthmd opd-4
  (implies (and (odd-listp l) (natp cnt))
           (odd-listp (nthcdr cnt l))))

(defthmd opd-5
  (implies (and (sortedp l) (natp cnt))
           (sortedp (nthcdr cnt l))))

(defthmd opd-6
  (implies (and (pos-listp l) (natp cnt))
           (pos-listp (nthcdr cnt l))))

(defthmd opd-7
  (implies (pos-listp l)
           (natp (sum-list l))))

(defthmd opd-8
  (implies (and (sortedp l) (natp k) (< k (len l)))
           (<= (car l) (car (nthcdr k l)))))

(defthmd opd-9
  (implies (and (pos-listp l) (sortedp l) (natp k) (consp (nthcdr k l)))
           (< k (len l))))

(defthmd opd-10
  (let ((k (count-init x l)))
    (not (and (consp (nthcdr k l)) (equal (car (nthcdr k l)) x)))))

(defthmd odd-part-decomp
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (let* ((x (car l))
	          (cnt (count-init x l))
		  (tail (nthcdr cnt l)))
	     (and (equal (append (copies cnt x) tail) l)
	          (posp cnt)
		  (<= (* cnt x) n)
		  (odd-partp tail (- n (* cnt x)))
		  (sortedp tail)
		  (or (null tail) (> (car tail) x)))))
  :hints (("Goal" :use (opd-1
                        (:instance opd-2 (x (car l)) (k (count-init (car l) l)))
                        (:instance opd-3 (x (car l)) (k (count-init (car l) l)) (l (nthcdr  (count-init (car l) l)l)))
                        (:instance opd-4 (cnt (count-init (car l) l)))
                        (:instance opd-5 (cnt (count-init (car l) l)))
                        (:instance opd-6 (cnt (count-init (car l) l)))
                        (:instance opd-7 (l (nthcdr (count-init (car l) l) l)))
			(:instance opd-8 (k (count-init (car l) l)))
			(:instance opd-9 (k (count-init (car l) l)))
			(:instance opd-10 (x (car l)))))))

;; The function odd2dis also depends on the decomposition of a natural number n as a
;; sum of powers of 2:

(defun bin-decomp-aux (n k)
  (if (zp n)
      ()
    (if (evenp n)
	(bin-decomp-aux (ash n -1) (1+ k))
      (cons (ash 1 k) (bin-decomp-aux (ash n -1) (1+ k))))))

(defun bin-decomp (n)
  (bin-decomp-aux n 0))

;; (bin-decomp n) is the unique sorted dlist of powers of 2 that sums to n:

(defthmd bin-decomp-aux-bound
  (implies (and (posp n) (natp k)
           (member-equal x (bin-decomp-aux n k)))
           (and (posp x) (>= x (ash 1 k))))
  :hints (("Goal" :nonlinearp t)))

(defun pow2-listp (l)
  (if (consp l)
      (and (powerp (car l) 2)
           (pow2-listp (cdr l)))
    (null l)))

(defthmd sortedp-bin-decomp-aux
  (implies (and (posp n) (natp k))
           (let ((l (bin-decomp-aux n k)))
	     (and (pow2-listp l)
	          (sortedp l)
		  (dlistp l))))
  :hints (("Goal" :nonlinearp t)
          ("Subgoal *1/3" :use ((:instance bin-decomp-aux-bound (x (ash 1 k)) (n (ash n -1)) (k (1+ k)))
	                        (:instance bin-decomp-aux-bound (x (cadr (bin-decomp-aux n k))) (n (ash n -1)) (k (1+ k)))))))

(defthmd sum-list-bin-decomp-aux
  (implies (and (posp n) (natp k))
           (equal (sum-list (bin-decomp-aux n k))
	          (ash n k))))

(defthmd bin-decomp-properties
  (implies (posp n)
           (let ((l (bin-decomp n)))
	     (and (pow2-listp l)
	          (sortedp l)
		  (dlistp l)
		  (equal (sum-list l) n))))
  :hints (("Goal" :use ((:instance sortedp-bin-decomp-aux (k 0))
                        (:instance sum-list-bin-decomp-aux (k 0))))))

(defthmd plse-1
  (implies (and (powerp x 2) (powerp y 2) (<= x y))
           (divides x y))
  :hints (("Goal" :use ((:instance powerp-log (p 2) (n x))
                        (:instance powerp-log (p 2) (n y))))))

(defthmd plse-2
  (implies (and (powerp x 2) (powerp y 2) (< x y))
           (< (log x 2) (log y 2)))
  :hints (("Goal" :use ((:instance powerp-log (p 2) (n x))
                        (:instance powerp-log (p 2) (n y))))))

(defthmd plse-3
  (implies (and (powerp x 2) (powerp y 2) (< x y))
           (divides (* 2 x) y))
  :hints (("Goal" :use (plse-2
                        (:instance powerp-log (p 2) (n x))
                        (:instance powerp-log (p 2) (n y))
			(:instance max-power-p-dividing (p 2) (k (1+ (log x 2))) (n y))))))

(defthmd plse-4
  (implies (and (consp l)
                (pow2-listp l)
	        (sortedp l)
	        (dlistp l))
	   (divides (car l) (sum-list l)))
  :hints (("Subgoal *1/1" :use ((:instance plse-1 (x (car l)) (y (cadr l)))
                                (:instance divides-transitive (x (car l)) (y (cadr l)) (z (sum-list (cdr l))))))))

(defthmd plse-5
  (implies (and (consp l)
                (pow2-listp l)
	        (sortedp l)
	        (dlistp l))
	   (divides (* 2 (car l)) (sum-list (cdr l))))
  :hints (("Subgoal *1/1" :use ((:instance plse-4 (l (cdr l)))
                                (:instance plse-3 (x (car l)) (y (cadr l)))
                                (:instance divides-transitive (x (* 2 (car l))) (y (cadr l)) (z (sum-list (cdr l))))))))

(defthmd plse-6
  (implies (and (consp l)
                (pow2-listp l)
	        (sortedp l)
	        (dlistp l))
	   (not (divides (* 2 (car l)) (sum-list l))))
  :hints (("Goal" :use (plse-5))))

(defthmd plse-7
  (implies (and (consp l)
                (pow2-listp l)
	        (sortedp l)
	        (dlistp l))
	   (equal (car l) (expt 2 (log (car l) 2))))
  :hints (("Goal" :use (plse-6
                        (:instance powerp-log (p 2) (n (car l)))))))

(defthmd plse-8
  (implies (and (consp l)
                (pow2-listp l)
	        (sortedp l)
	        (dlistp l))
	   (not (divides (* 2 (expt 2 (log (car l) 2))) (sum-list l))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (plse-6 plse-7))))

(defthmd plse-9
  (implies (and (consp l)
                (pow2-listp l)
	        (sortedp l)
	        (dlistp l)
		(natp k)
		(> k (log (car l) 2)))
	   (not (divides (expt 2 k) (sum-list l))))
  :hints (("Goal" :in-theory (disable sum-list)
                  :use (plse-8
			(:instance divides-transitive (x (expt 2 (1+ (log (car l) 2)))) (y (expt 2 k)) (z (sum-list l)))))))

(defthmd plse-10
  (implies (and (consp l)
                (pow2-listp l))
	   (posp (sum-list l))))

(defthmd plse-11
  (implies (and (pow2-listp l)
	        (sortedp l)
	        (dlistp l)
		(pow2-listp m)
	        (sortedp m)
	        (dlistp m)
		(equal (sum-list l) (sum-list m)))
	   (equal (car l) (car m)))
  :hints (("Goal" :use (plse-4 plse-10 plse-7
                        (:instance plse-10 (l m))
                        (:instance plse-4 (l m))
			(:instance plse-7 (l m))
			(:instance plse-9 (k (log (car m) 2)))
			(:instance plse-9 (k (log (car l) 2)) (l m))))))

(defun cdr2-induct (l m)
  (if (consp l)
      (list (cdr2-induct (cdr l) (cdr m)))
    (cons l m)))

(defthm pow2-list-sum-equal
  (implies (and (pow2-listp l)
	        (sortedp l)
	        (dlistp l)
		(pow2-listp m)
	        (sortedp m)
	        (dlistp m)
		(equal (sum-list l) (sum-list m)))
	   (equal l m))
  :rule-classes ()  
  :hints (("Goal" :induct (cdr2-induct l m))
          ("Subgoal *1/2" :use ((:instance plse-10 (l m))))	  
          ("Subgoal *1/1" :use (plse-11))))
                          
(defthmd bin-decomp-unique
  (implies (and (consp l)
                (pow2-listp l)
	        (sortedp l)
	        (dlistp l))
           (equal (bin-decomp (sum-list l))
	          l))
  :hints (("Goal" :use ((:instance bin-decomp-properties (n (sum-list l)))
                        (:instance pow2-list-sum-equal (m (bin-decomp (sum-list l))))))))


(defun prods (l n)
  (if (consp l)
      (cons (* (car l) n) (prods (cdr l) n))
    ()))

(defund odd2dis-prefix (l)
  (prods (bin-decomp (count-init (car l) l)) (car l)))

(defun odd2dis (l)
  (if (consp l)
      (append (odd2dis-prefix l)
              (odd2dis (nthcdr (count-init (car l) l) l)))
    ()))


;;------------------------------------------------------------------------------------------------

;; We construct a list by applying odd2dis to each member of (odd-parts n):

(defun odd2dis-list (l)
  (if (consp l)
      (cons (odd2dis (car l)) (odd2dis-list (cdr l)))
    ()))

(defun dis-parts (n)
  (odd2dis-list (odd-parts n)))

;; Clearly, (odd-parts n) and (dis-parts n) have the same length:

(defthm len-odd2dis-list
  (equal (len (odd2dis-list l))
	 (len l)))

(defthm len-dis-parts
  (equal (len (dis-parts n))
	 (len (odd-parts n))))

;; We must derive the properties of (dis-parts n) corresponding to dlistp-predl and member-predl,
;; i.e., we must show that (dis-parts n) is a dlist consisting of all ordered distinct partitions
;; of n.  To this end, we define the inverse of odd2dis, which converts a sorted distinct partition
;; of n to a sorted odd partition of n.  This is based on a decomposition of a sorted distinct
;; partition as the appending of 2 lists: (1) the initial segment consisting of all members with 
;; minimal odd component and (2) the remaining tail:

(defun oddf-init-aux (x l)
  (if (consp l)
      (if (= (oddf (car l)) x)
          (cons (car l) (oddf-init-aux x (cdr l)))
	())
    ()))

(defun oddf-init (l)
  (oddf-init-aux (oddf (car l)) l))		 

(defun all-oddf-p (x l)
  (if (consp l)
      (and (= (oddf (car l)) x)
           (all-oddf-p x (cdr l)))
    t))

(defthmd dpd-1
  (implies (and (posp n) (dis-partp l n))
           (consp (oddf-init l))))

(defthm dpd-2-a
  (implies (member-equal n (oddf-init-aux x l))
           (member-equal n l)))

(defthmd dpd-2
  (implies (and (pos-listp l) (dlistp l) (dsortedp l) (posp x))
           (let ((prefix (oddf-init-aux x l)))
	     (and (all-oddf-p x prefix)
	          (pos-listp prefix)
		  (dlistp prefix)
		  (dsortedp prefix)))))

(in-theory (disable dpd-2-a))

(defthmd dpd-3
  (implies (and (pos-listp l) (posp x))
           (equal (append (oddf-init-aux x l) (nthcdr (len (oddf-init-aux x l)) l))
	          l)))

(defthmd dpd-4
  (implies (and (pos-listp l) (posp x))
           (equal (sum-list (append (oddf-init-aux x l) (nthcdr (len (oddf-init-aux x l)) l)))
	          (+ (sum-list (oddf-init-aux x l)) (sum-list (nthcdr (len (oddf-init-aux x l)) l))))))

(defthmd dpd-5
  (implies (and (dlistp l) (natp cnt))
           (dlistp (nthcdr cnt l))))

(defthmd dpd-6
  (implies (and (dsortedp l) (natp cnt))
           (dsortedp (nthcdr cnt l))))

(defthmd dpd-7
  (implies (and (dsortedp l) (natp k) (< k (len l)))
           (<= (oddf (car l)) (oddf (car (nthcdr k l))))))

(defthmd dpd-8
  (implies (and (pos-listp l) (dsortedp l) (natp k) (consp (nthcdr k l)))
           (< k (len l))))

(defthmd dpd-9
  (let ((k (len (oddf-init-aux x l))))
    (not (and (consp (nthcdr k l)) (equal (oddf (car (nthcdr k l))) x)))))

(defthmd dpd-10
  (implies (posp n) (posp (oddf n))))

(defthmd dis-part-decomp
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (let* ((x (oddf (car l)))
	          (prefix (oddf-init l))
		  (sum (sum-list prefix))
		  (tail (nthcdr (len prefix) l)))
	     (and (equal (append prefix tail) l)
	          (consp prefix)
	          (dis-partp prefix sum)
	          (all-oddf-p x prefix)
	          (<= sum n)
		  (dis-partp tail (- n (sum-list prefix)))
		  (dsortedp tail)
		  (or (null tail) (> (oddf (car tail)) x)))))
  :hints (("Goal" :use (dpd-1
                        (:instance dpd-2 (x (oddf (car l))))
                        (:instance dpd-3 (x (oddf (car l))))
                        (:instance dpd-4 (x (oddf (car l))))
                        (:instance dpd-5 (cnt (len (oddf-init l))))
                        (:instance dpd-6 (cnt (len (oddf-init l))))
                        (:instance dpd-7 (k (len (oddf-init l))))
			(:instance dpd-8 (k (len (oddf-init l))))
			(:instance dpd-9 (x (oddf (car l))))
			(:instance dpd-10 (n (car l)))
			(:instance opd-6 (cnt (len (oddf-init l))))
			(:instance opd-7 (l (nthcdr (len (oddf-init l)) l)))))))

;; (dis2odd l) is computed by appending 2 lists.  The first is computed by converting
;; (oddf-init l) to a list of copies of (oddf (car l)):

(defund dis2odd-prefix (l)
  (copies (/ (sum-list (oddf-init l)) (oddf (car l)))
          (oddf (car l))))

;; The second is computed by applying dis2odd recursively to the rest of l:

(defun dis2odd (l)
  (if (consp l)
      (append (dis2odd-prefix l)
	      (dis2odd (nthcdr (len (oddf-init l)) l)))
    ()))


;;------------------------------------------------------------------------------------------------

;; Let l be a sorted odd partition of n and let m = (odd2dis m).  We shall show that m is a sorted
;; distinct partition of n and (dis2odd m) = l.  This will imply that (dis-parts n) is a dlist.

(in-theory (disable bin-decomp))

(defthmd bin-decomp-count-init
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (let ((bd (bin-decomp (count-init (car l) l))))
	     (and (posp (count-init (car l) l))
	          (consp bd)
	          (pow2-listp bd)
		  (sortedp bd)
		  (dlistp bd)
		  (equal (sum-list bd) (count-init (car l) l)))))
  :hints (("Goal" :use (odd-part-decomp
                        (:instance bin-decomp-properties (n (count-init (car l) l)))))))

(defthmd consp-prods
  (implies (consp l) (consp (prods l n))))

(defthmd consp-prods-bin-decomp
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (consp (prods (bin-decomp (count-init (car l) l)) (car l))))
  :hints (("Goal" :use (bin-decomp-count-init
                        (:instance consp-prods (l (bin-decomp (count-init (car l) l))) (n (car l)))))))

(defthmd pos-listp-prods
  (implies (and (pow2-listp l) (posp x))
           (pos-listp (prods l x))))

(defthmd pos-listp-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (and (consp (odd2dis-prefix l))
                (pos-listp (odd2dis-prefix l))))
  :hints (("Goal" :in-theory (enable odd2dis-prefix)
                  :use (consp-prods-bin-decomp bin-decomp-count-init		  
		        (:instance pos-listp-prods (x (car l)) (l (bin-decomp (count-init (car l) l))))))))

(defthmd all-oddf-prods
  (implies (and (pow2-listp l) (posp n) (oddp n))
           (all-oddf-p n (prods l n))))

(defthmd all-oddf-p-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (all-oddf-p (car l) (odd2dis-prefix l)))
  :hints (("Goal" :in-theory (enable odd2dis-prefix)
                  :use (bin-decomp-count-init		  
		        (:instance all-oddf-prods (n (car l)) (l (bin-decomp (count-init (car l) l))))))))

(defthmd oddf-car-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (equal (oddf (car (odd2dis-prefix l)))
	          (car l)))
  :hints (("Goal" :use (pos-listp-prefix all-oddf-p-prefix))))

(in-theory (disable oddf))

(defthmd car-append
  (implies (consp l)
           (equal (car (append l m)) (car l))))

(defthmd oddf-car-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (equal (oddf (car (odd2dis l)))
	          (car l)))
  :hints (("Goal" :use (oddf-car-prefix pos-listp-prefix
                        (:instance car-append (l (odd2dis-prefix l)) (m (odd2dis (nthcdr (count-init (car l) l) l)))))
                  :expand ((odd2dis l)))))

(defthmd sortedp-prods-1
  (implies (and (pow2-listp l) (posp n) (posp c)
                (member-equal (* n c) (prods l n)))
	   (member-equal c l)))

(defthmd sortedp-prods
  (implies (and (pow2-listp l) (sortedp l) (dlistp l) (posp n))
           (and (sortedp (prods l n))
	        (dlistp (prods l n))))
  :hints (("Subgoal *1/1" :use ((:instance sortedp-prods-1 (c (car l)) (l (cdr l)))))))		
		
(defthmd sortedp-dlist-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (and (sortedp (odd2dis-prefix l))
	        (dlistp (odd2dis-prefix l))))
  :hints (("Goal" :in-theory (enable odd2dis-prefix)
                  :use (bin-decomp-count-init		  
		        (:instance sortedp-prods (n (car l)) (l (bin-decomp (count-init (car l) l))))))))

(defthmd sum-list-prods
  (implies (and (pow2-listp l) (posp n))
           (equal (sum-list (prods l n))
	          (* n (sum-list l)))))

(defthmd sum-list-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (equal (sum-list (odd2dis-prefix l))
	          (* (car l) (count-init (car l) l))))
  :hints (("Goal" :in-theory (enable odd2dis-prefix)
                  :use (bin-decomp-count-init
		        (:instance bin-decomp-properties (n (count-init (car l) l)))
		        (:instance sum-list-prods (n (car l)) (l (bin-decomp (count-init (car l) l))))))))

(defthmd dpo-1
  (implies (and (pos-listp l)
                (dsortedp l)
		(member-equal c l))
	   (<= (oddf (car l)) (oddf c))))

(defthmd dpo-2
  (implies (and (posp x)
                (pos-listp prefix)
		(all-oddf-p x prefix)
		(sortedp prefix)
		(dlistp prefix)
		(dis-partp tail (sum-list tail))
		(or (null tail) (> (oddf (car tail)) x))
		(dsortedp tail))
	    (let ((app (append prefix tail)))
	      (and (dis-partp app (+ (sum-list prefix) (sum-list tail)))
	           (dsortedp app))))
  :hints (("Subgoal *1/2" :use ((:instance dpo-1 (c (car prefix)) (l tail))))))

(defthm dpo-3
  (implies (and (pos-listp l) l)
           (posp (sum-list l)))
  :rule-classes ())

(defthmd dpo-4
  (implies (and (posp n) (odd-partp l n) (sortedp l) (= n (* (car l) (count-init (car l) l))))
           (null (nthcdr (count-init (car l) l) l)))
  :hints (("Goal" :use (odd-part-decomp (:instance dpo-3 (l (nthcdr (count-init (car l) l) l)))))))

(defun odd2dis-induct (l n)
  (declare (xargs :measure (len l)))
  (if (and (posp n) (odd-partp l n))
      (odd2dis-induct (nthcdr (count-init (car l) l) l)
                      (- n (* (car l) (count-init (car l) l))))
    ()))

(defthmd dis-partp-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (and (dis-partp (odd2dis l) n)
	        (dsortedp (odd2dis l))))
  :hints (("Goal" :induct (odd2dis-induct l n))
          ("Subgoal *1/" :use (pos-listp-prefix all-oddf-p-prefix sortedp-dlist-prefix sum-list-prefix odd-part-decomp dpo-4
                               (:instance dpo-2 (x (car l))
                                                (prefix (odd2dis-prefix l))
					        (tail (odd2dis (nthcdr (count-init (car l) l) l))))
			       (:instance oddf-car-odd2dis (n (sum-list (nthcdr (count-init (car l) l) l)))
	                                                   (l (nthcdr (count-init (car l) l) l)))))))

(defthmd oio-1
  (implies (and (pos-listp l) (all-oddf-p x l) (or (null m) (> (oddf (car m)) x)))
           (equal (oddf-init-aux x (append l m))
	          l)))

(defthmd oio-2
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (let ((m (odd2dis (nthcdr (count-init (car l) l) l))))
	     (or (null m) (> (oddf (car m)) (car l)))))
  :hints (("Goal" :use (pos-listp-prefix all-oddf-p-prefix sortedp-dlist-prefix sum-list-prefix odd-part-decomp dpo-4
                               (:instance dpo-2 (x (car l))
                                                (prefix (odd2dis-prefix l))
					        (tail (odd2dis (nthcdr (count-init (car l) l) l))))
			       (:instance oddf-car-odd2dis (n (sum-list (nthcdr (count-init (car l) l) l)))
	                                                   (l (nthcdr (count-init (car l) l) l)))))))

(defthmd oddf-init-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (equal (oddf-init (odd2dis l))
	          (odd2dis-prefix l)))
  :hints (("Goal" :use (oio-2 pos-listp-prefix all-oddf-p-prefix oddf-car-odd2dis
			(:instance oio-1 (x (car l)) (l (odd2dis-prefix l)) (m (odd2dis (nthcdr (count-init (car l) l) l))))))))

(defthmd dis2odd-prefix-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (equal (dis2odd-prefix (odd2dis l))
	          (copies (count-init (car l) l) (car l))))
  :hints (("Goal" :in-theory (enable sum-list-prefix dis2odd-prefix)
                  :use (oddf-car-odd2dis oddf-init-odd2dis))))

(defthmd no-1
  (equal (nthcdr (len l) (append l m))
         m))

(defthmd nthcdr-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (equal (nthcdr (len (oddf-init (odd2dis l))) (odd2dis l))
	          (odd2dis (nthcdr (count-init (car l) l) l))))
  :hints (("Goal" :use (oddf-init-odd2dis
                        (:instance no-1 (l (odd2dis-prefix l)) (m (odd2dis (nthcdr (count-init (car l) l) l))))))))

(defthmd do-1
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (equal (append (copies (count-init (car l) l) (car l)) (nthcdr (count-init (car l) l) l))
	          l))
  :hints (("Goal" :use (odd-part-decomp))))

(defthmd do-2
  (implies (and (pos-listp l) l)
           (posp (sum-list l))))

(defthmd do-3
  (implies (and (pos-listp l)
                (<= (SUM-LIST (NTHCDR (COUNT-INIT (CAR L) L) L)) 0))
	   (null (NTHCDR (COUNT-INIT (CAR L) L) L)))
  :hints (("Goal" :use ((:instance opd-6 (cnt (count-init (car l) l)))
                        (:instance do-2 (l (NTHCDR (COUNT-INIT (CAR L) L) L)))))))

(defthmd dis2odd-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (equal (dis2odd (odd2dis l))
	          l))
  :hints (("Subgoal *1/6" :use ((:instance do-1 (n (sum-list l)))
                                (:instance nthcdr-odd2dis (n (sum-list l)))
				(:instance dis2odd-prefix-odd2dis (n (sum-list l)))))				
          ("Subgoal *1/2" :use (do-3
	                        (:instance do-1 (n (sum-list l)))
                                (:instance nthcdr-odd2dis (n (sum-list l)))
				(:instance dis2odd-prefix-odd2dis (n (sum-list l)))))))
	  
(defthm odd2dis-1-1
  (implies (and (posp n) (odd-partp l n) (sortedp l) (odd-partp m n) (sortedp m)
                (equal (odd2dis l) (odd2dis m)))
           (equal l m))
  :rule-classes ()
  :hints (("Goal" :use (dis2odd-odd2dis (:instance dis2odd-odd2dis (l m))))))


(defthm ddp-1
  (implies (and (posp n) (sublistp l (odd-parts n)) (odd-partp p n) (sortedp p)
                (member (odd2dis p) (odd2dis-list l)))
	   (member p l))
  :hints (("Subgoal *1/4" :use ((:instance odd2dis-1-1 (n (sum-list p)) (l p) (m (car l)))
                                (:instance member-odd-parts (l (car l)) (n (sum-list p)))))))

(defthm ddp-2
  (implies (and (posp n) (sublistp l (odd-parts n)) (dlistp l))
           (dlistp (odd2dis-list l)))
  :hints (("Subgoal *1/3" :use ((:instance ddp-1 (p (car l)) (l (cdr l)))
                                (:instance member-odd-parts (l (car l)))))))

(defthmd dlistp-dis-parts
  (implies (posp n)
	   (dlistp (dis-parts n)))
  :hints (("Goal" :use ((:instance ddp-2 (l (odd-parts n)))))))


;;------------------------------------------------------------------------------------------------

;; Now let l be a sorted distinct partition of n and let m = (dis2odd l).  We shall show that m is 
;; a sorted odd partition of n and (odd2dis m) = l.  This implies that l belongs to (dis-parts n).

(defun pow2-list (l)
  (if (consp l)
      (cons (pow2 (car l)) (pow2-list (cdr l)))
    ()))

(defthmd pow2-listp-pow2-list
  (implies (pos-listp l)
           (pow2-listp (pow2-list l))))

(defthmd sum-list-pow2-list
  (implies (and (pos-listp l) (all-oddf-p x l))
           (equal (sum-list (pow2-list l))
	          (/ (sum-list l) x)))	          
  :hints (("Goal" :in-theory (enable oddf))))

(defthmd dis2odd-prefix-rewrite
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (dis2odd-prefix l)
	          (copies (sum-list (pow2-list (oddf-init l))) (oddf (car l)))))
  :hints (("Goal" :in-theory (enable dis2odd-prefix)
                  :use (dis-part-decomp
		        (:instance sum-list-pow2-list (l (oddf-init l)) (x (oddf (car l))))))))

(defthmd odd-partp-append
  (implies (and (posp x)
                (oddp x)
                (natp n)
		(odd-partp tail (sum-list tail))
		(sortedp tail)
		(or (null tail) (> (car tail) x)))
	   (let ((m (append (copies n x) tail)))
	     (and (odd-partp m (+ (* n x) (sum-list tail)))
	          (sortedp m)
		  (or (zp n) (equal (car m) x))
		  (equal (count-init x m) n))))
  :hints (("Goal" :induct (fact n))))

(defthmd dpd-1
  (implies (and (posp n) (dis-partp l n))
           (consp (oddf-init l))))

(defthm dpo-3
  (implies (and (pos-listp l) l)
           (posp (sum-list l)))
  :rule-classes ())

(defthmd cd2o-1
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (and (pow2-list (oddf-init l))
	        (pos-listp (pow2-list (oddf-init l))))))

(defthmd cd2o-2
  (implies (posp n)
           (and (copies n x)
	        (equal (car (copies n x)) x))))

(defthmd cd2o-3
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (and (dis2odd-prefix l)
	        (equal (car (dis2odd-prefix l)) (oddf (car l)))))
  :hints (("Goal" :in-theory (enable dis2odd-prefix-rewrite)
                  :use (cd2o-1
		        (:instance dpo-3 (l (pow2-list (oddf-init l))))
			(:instance cd2o-2 (n (sum-list (pow2-list (oddf-init l)))) (x (oddf (car l))))))))

(defthmd car-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (car (dis2odd l)) (oddf (car l))))
  :hints (("Goal" :use (cd2o-3
                        (:instance car-append (l (dis2odd-prefix l))
			                      (m (dis2odd (nthcdr (len (oddf-init l)) l))))))))

(defthmd opd2o-1
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (or (null (dis2odd (nthcdr (len (oddf-init l)) l)))
	       (> (car (dis2odd (nthcdr (len (oddf-init l)) l))) (oddf (car l)))))
  :hints (("Goal" :use (dis-part-decomp
                        (:instance dpo-3 (l (nthcdr (len (oddf-init l)) l)))
                        (:instance car-dis2odd (l (nthcdr (len (oddf-init l)) l))
		                               (n (- n (sum-list (oddf-init l)))))))))

(defthmd opd2o-2
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (posp (sum-list (pow2-list (oddf-init l)))))
  :hints (("Goal" :use (cd2o-1 (:instance dpo-3 (l (pow2-list (oddf-init l))))))))
 
(defthmd opd2o-3
  (implies (and (posp n) (dis-partp l n) (dsortedp l)
                (odd-partp (dis2odd (nthcdr (len (oddf-init l)) l))
		           (sum-list (nthcdr (len (oddf-init l)) l)))
                (sortedp (dis2odd (nthcdr (len (oddf-init l)) l))))
           (and (odd-partp (dis2odd l)
	                   (+ (* (sum-list (pow2-list (oddf-init l))) (oddf (car l)))
			      (sum-list (nthcdr (len (oddf-init l)) l))))
	        (sortedp (dis2odd l))
		(equal (car (dis2odd l)) (oddf (car l)))
		(equal (count-init (oddf (car l)) (dis2odd l)) (sum-list (pow2-list (oddf-init l))))))
  :hints (("Goal" :in-theory (enable dis2odd-prefix-rewrite)
                  :use (opd2o-1 opd2o-2
                        (:instance odd-partp-append (x (oddf (car l)))
                                                    (n (sum-list (pow2-list (oddf-init l))))
					            (tail (dis2odd (nthcdr (len (oddf-init l)) l))))		  
                        (:instance posp-oddf (n (car l)))
                        (:instance oddp-oddf (n (car l)))))))

(defthmd opd2o-4
  (implies (and (pos-listp l) (all-oddf-p x l))
           (equal (* x (sum-list (pow2-list l)))
	          (sum-list l)))
  :hints (("Goal" :in-theory (enable oddf))))

(defthmd opd2o-5
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (+ (* (sum-list (pow2-list (oddf-init l))) (oddf (car l)))
	             (sum-list (nthcdr (len (oddf-init l)) l)))
		  n))
  :hints (("Goal" :use (dis-part-decomp
                        (:instance opd2o-4 (l (oddf-init l)) (x (oddf (car l))))))))

(defthmd opd2o-6
  (implies (and (posp n) (dis-partp l n) (dsortedp l)
                (odd-partp (dis2odd (nthcdr (len (oddf-init l)) l))
		           (sum-list (nthcdr (len (oddf-init l)) l)))
                (sortedp (dis2odd (nthcdr (len (oddf-init l)) l))))
           (and (odd-partp (dis2odd l) n)
	        (sortedp (dis2odd l))))
  :hints (("Goal" :use (opd2o-3 opd2o-5))))

(defthmd opd2o-7
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (and (dis-partp (nthcdr (len (oddf-init l)) l) (sum-list (nthcdr (len (oddf-init l)) l)))
	        (dsortedp (nthcdr (len (oddf-init l)) l))))
  :hints (("Goal" :use (dis-part-decomp
                        (:instance dpo-3 (l (nthcdr (len (oddf-init l)) l)))))))

(defun opd2o-induct (l n)
  (declare (xargs :measure (len l)))
  (if (and (posp n) (dis-partp l n))
      (opd2o-induct (nthcdr (len (oddf-init l)) l)
                    (sum-list (nthcdr (len (oddf-init l)) l)))
    ()))
  
(defthmd odd-partp-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (and (odd-partp (dis2odd l) n)
	        (sortedp (dis2odd l))))	
  :hints (("Goal" :induct (opd2o-induct l n))
          ("Subgoal *1/" :use (opd2o-6 opd2o-7 (:instance dpo-3 (l (nthcdr (len (oddf-init l)) l)))))))
                                
(defthm count-init-append
  (implies (and (natp n) (natp x) (or (null tail) (> (car tail) x)))
           (equal (count-init x (append (copies n x) tail))
	          n)))

(defthmd count-init-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (count-init (car (dis2odd l)) (dis2odd l))
	          (sum-list (pow2-list (oddf-init l)))))
  :hints (("Goal" :in-theory (e/d (dis2odd-prefix-rewrite) (oddf-init sortedp))
                  :use (car-dis2odd opd2o-1
                        (:instance posp-oddf (n (car l)))
		        (:instance count-init-append (x (car (dis2odd l)))
                                                     (n (sum-list (pow2-list (oddf-init l))))
						     (tail (dis2odd (nthcdr (len (oddf-init l)) l))))))))

(defthmd bdcid-1
  (implies (and (posp x)
                (all-oddf-p x l)
	        (pos-listp l))
	   (equal (prods (pow2-list l) x)
	          l))
  :hints (("Goal" :in-theory (enable oddf))))

(defthmd bdcid-2
  (implies (and (posp x)
                (all-oddf-p x l)
		(dsortedp l))
	   (sortedp l)))

(defthmd bdcid-3
  (implies (and (posp x)
	        (pos-listp l)
		(member-equal n l))
	   (member-equal (* x n) (prods l x))))

(defthmd bdcid-4
  (implies (and (posp x)
	        (pos-listp l)
		(dlistp (prods l x))
		(sortedp (prods l x)))
	   (and (dlistp l)
	        (sortedp l)))
  :hints (("Subgoal *1/1" :use ((:instance bdcid-3 (n (car l)) (l (cdr l)))))))

(defthmd bdcid-5
  (implies (pos-listp l)
           (pos-listp (pow2-list l))))

(defthmd bdcid-6
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (and (dlistp (pow2-list (oddf-init l)))
	        (sortedp (pow2-list (oddf-init l)))))
  :hints (("Goal" :use ((:instance dpd-2 (x (oddf (car l))))
                        (:instance posp-oddf (n (car l)))
                        (:instance bdcid-1 (l (oddf-init l)) (x (oddf (car l))))
			(:instance bdcid-2 (l (oddf-init l)) (x (oddf (car l))))
			(:instance bdcid-5 (l (oddf-init l)))
			(:instance bdcid-4 (l (pow2-list (oddf-init l))) (x (oddf (car l))))))))

;; A consequence of bin-decomp-unique:

(defthmd bin-decomp-count-init-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (bin-decomp (sum-list (pow2-list (oddf-init l))))
	          (pow2-list (oddf-init l))))
  :hints (("Goal" :use (bdcid-6 cd2o-1
                        (:instance posp-oddf (n (car l)))
                        (:instance dpd-2 (x (oddf (car l))))
			(:instance pow2-listp-pow2-list (l (oddf-init l)))
			(:instance  bin-decomp-unique (l (pow2-list (oddf-init l))))))))

(defthmd prods-pow2-list-oddf-init
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (prods (pow2-list (oddf-init l)) (oddf (car l)))
	          (oddf-init l)))
  :hints (("Goal" :use ((:instance dpd-2 (x (oddf (car l))))
                        (:instance posp-oddf (n (car l)))
                        (:instance bdcid-1 (l (oddf-init l)) (x (oddf (car l))))))))

(defthmd odd2dis-prefix-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (odd2dis-prefix (dis2odd l))
	          (oddf-init l)))
  :hints (("Goal" :in-theory (enable odd2dis-prefix)
                  :use (count-init-dis2odd car-dis2odd bin-decomp-count-init-dis2odd prods-pow2-list-oddf-init))))

(defthmd o2d2o-1
  (equal (nthcdr (len l) (append l m))
         m))

(defthm len-copies
  (implies (natp n)
           (equal (len (copies n x)) n)))

(defthmd o2d2o-2
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (nthcdr (count-init (car (dis2odd l)) (dis2odd l)) (dis2odd l))
	          (dis2odd (nthcdr (len (oddf-init l)) l))))
  :hints (("Goal" :use (count-init-dis2odd dis2odd-prefix-rewrite
                        (:instance o2d2o-1(l (dis2odd-prefix l)) (m (dis2odd (nthcdr (len (oddf-init l)) l))))))))

(in-theory (disable oddf-init))

(defthmd o2d2o-3
  (implies (and (posp n) (dis-partp l n) (dsortedp l)
                (equal (odd2dis (dis2odd (nthcdr (len (oddf-init l)) l)))
		       (nthcdr (len (oddf-init l)) l)))
           (equal (odd2dis (dis2odd l))
	          l))	
  :hints (("Goal" :use (dis-part-decomp opd2o-7 o2d2o-2 odd2dis-prefix-dis2odd))))

(defthmd odd2dis-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (odd2dis (dis2odd l))
	          l))	
  :hints (("Goal" :induct (opd2o-induct l n))
          ("Subgoal *1/" :use (opd2o-7 o2d2o-3 odd2dis-prefix-dis2odd (:instance dpo-3 (l (nthcdr (len (oddf-init l)) l)))))))
                        
(defthmd mdp-1
  (implies (and (posp n) (sublistp l (odd-parts n)) (member-equal p (odd2dis-list l)))
           (and (dis-partp p n) (dsortedp p)))
  :hints (("Subgoal *1/1" :use ((:instance member-odd-parts (l (car l)))
                               (:instance dis-partp-odd2dis (l (car l)))))))

(defthmd mdp-2
  (implies (member-equal p l)
           (member-equal (odd2dis p) (odd2dis-list l))))

(defthmd mdp-3
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (member-equal l (dis-parts n)))
  :hints (("Goal" :use (odd-partp-dis2odd odd2dis-dis2odd
                        (:instance member-odd-parts (l (dis2odd l)))
			(:instance mdp-2 (p (dis2odd l)) (l (odd-parts n)))))))

(defthmd member-dis-parts
  (implies (posp n)
           (iff (member-equal l (dis-parts n))
	        (and (dis-partp l n)
		     (dsortedp l))))
  :hints (("Goal" :use (mdp-3 (:instance mdp-1 (p l) (l (odd-parts n)))))))

;; In particular, (dis-parts n) is a list of distinct partitions:

(defthmd dis-partp-dis-parts
  (implies (and (posp n) (member-equal l (dis-parts n)))
	   (dis-partp l n))
  :hints (("Goal" :use (member-dis-parts))))


;;------------------------------------------------------------------------------------------------

;; The desired results follow by functional instantiation of predl-perm-equal and perm-predl:

(defthm dis-parts-perm-equal
  (implies (and (posp n)
                (member-equal l (dis-parts n))
		(member-equal m (dis-parts n))
		(permutationp l m))
	   (equal l m))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance predl-perm-equal
                          (t<= (lambda (x y) (if (posp n) (d<= x y) (t<= x y))))
                          (pred (lambda (l) (if (posp n) (dis-partp l n) (pred l))))
			  (predl (lambda () (if (posp n) (dis-parts n) (predl))))
                          (tsortedp (lambda (l) (if (posp n) (dsortedp l) (tsortedp l))))
                          (tleast-aux (lambda (x l) (if (posp n) (dleast-aux x l) (tleast-aux x l))))
			  (tleast (lambda (l) (if (posp n) (dleast l) (tleast l)))))))
	  ("Subgoal 7" :use (t<=-total))
	  ("Subgoal 6" :use (t<=-antisym))
	  ("Subgoal 5" :use (t<=-assoc))
	  ("Subgoal 4" :use (t<=-reflex))	  
	  ("Subgoal 3" :use (member-predl member-dis-parts))
	  ("Subgoal 2" :use (dlistp-dis-parts pred-inv dis-partp-inv))
	  ("Subgoal 1" :use (pred-inv member-predl predl-perm-equal sum-list-perm permutationp-symmetric dlistp-perm
	                     (:instance permutationp-symmetric (l m) (m l))
	                     (:instance dlistp-perm (l m) (m l))
	                     (:instance predl-perm-equal (l m))))))

(defthmd perm-dis-parts
  (implies (and (posp n)
                (dis-partp l n))
	   (and (member-equal (dsort l) (dis-parts n))
	        (permutationp (dsort l) l)))
  :hints (("Goal" :use ((:functional-instance perm-predl
                          (t<= (lambda (x y) (if (posp n) (d<= x y) (t<= x y))))
                          (pred (lambda (l) (if (posp n) (dis-partp l n) (pred l))))
			  (predl (lambda () (if (posp n) (dis-parts n) (predl))))
                          (tsortedp (lambda (l) (if (posp n) (dsortedp l) (tsortedp l))))
                          (tleast-aux (lambda (x l) (if (posp n) (dleast-aux x l) (tleast-aux x l))))
			  (tleast (lambda (l) (if (posp n) (dleast l) (tleast l))))
			  (tsort (lambda (l) (if (posp n) (dsort l) (tsort l)))))))))


;;------------------------------------------------------------------------------------------------

;; In summary, we have established the following properties of the list (odd-parts n).

;; (odd-parts n) is a dlist of odd partitions of n:

(defthmd dlistp-odd-parts
  (implies (posp n)
	   (dlistp (odd-parts n))))

(defthmd odd-partp-odd-parts
  (implies (and (posp n) (member-equal l (odd-parts n)))
	   (odd-partp l n)))

;; No 2 members of (odd-parts n) are equivalent:

(defthm odd-parts-perm-equal
  (implies (and (posp n)
                (member-equal l (odd-parts n))
		(member-equal m (odd-parts n))
		(permutationp l m))
	   (equal l m))
  :rule-classes ())

;; Every odd partition of n is equivalent to e member of (odd-parts n):

(defthmd perm-odd-parts
  (implies (and (posp n)
                (odd-partp l n))
	   (and (member-equal (sort l) (odd-parts n))
	        (permutationp (sort l) l))))

;; Thus, the number of equivalence classes of odd partitions of n is (len (odd-parts n)).

;; We have established the following analogous properties of the list (dis-parts n).

(defthmd dlistp-dis-parts
  (implies (posp n)
	   (dlistp (dis-parts n))))

(defthmd dis-partp-dis-parts
  (implies (and (posp n) (member-equal l (dis-parts n)))
	   (dis-partp l n)))

(defthm dis-parts-perm-equal
  (implies (and (posp n)
                (member-equal l (dis-parts n))
		(member-equal m (dis-parts n))
		(permutationp l m))
	   (equal l m))
  :rule-classes ())

(defthmd perm-dis-parts
  (implies (and (posp n)
                (dis-partp l n))
	   (and (member-equal (dsort l) (dis-parts n))
	        (permutationp (dsort l) l))))

;; Thus, the number of equivalence classes of distinct partitions of n is (len (dis-parts n)).

;; We have also proved that these 2 lists have the same length:

(defthm len-dis-parts
  (equal (len (dis-parts n))
	 (len (odd-parts n))))

;; Thus, the number of equivalence classes of odd partitions of n is equal to the number
;; of equivalence classes of distinct partitions of n
