(in-package "DM")

(include-book "subsets")
(include-book "binomial")

;; We begin with the basic definitions of the union and the intersection of a list of lists:

(defun union-list (l)
  (if (consp l)
      (if (consp (cdr l))
	  (union-equal (car l) (union-list (cdr l)))
	(car l))
    ()))

(defun int-list (l)
  (if (consp l)
      (if (consp (cdr l))
	  (intersection-equal (car l) (int-list (cdr l)))
	(car l))
    ()))

;; Apply int-list to each member of a list of lists of lists:

(defun int-list-list (l)
  (if (consp l)
      (cons (int-list (car l))
            (int-list-list (cdr l)))
    ()))

;; Sum the lengths of a list of lists:

(defun sum-lens (l)
  (if (consp l)
      (+ (len (car l))
         (sum-lens (cdr l)))
    0))

;; Let u be an arbitrary dlist, our universe.  Let l be a dlist and a sublist of (subsets u).
;; In view of the properties of (subsets u) proved in subsets.lisp, we may think of the members
;; of l as subsets of u and their lengths as the orders of these subsets.  We shall derive a
;; formula for the number of elements of u that belong to the union of l, i.e., the length of
;; (union-list l), expressed in terms of the lengths of the intersections of various sublists
;; of l.

;; First we define, for a given list m = (m0 m1 ...) of sublists of l, the sum of the orders
;; of their intersections, (len (int-list m0)) + (len (int-list m1)) + ... :

(defun sum-len-int (m)
  (sum-lens (int-list-list m)))

;; Here is our formula for (len (union-list l)):

(defun inc-exc-aux (l k)
  (declare (xargs :measure (nfix (1+ (- (len l) k)))))
  (if (and (posp k) (<= k (len l)))
      (- (sum-len-int (subsets-of-order k l))
         (inc-exc-aux l (1+ k)))
    0))

(defund inc-exc (l)
  (inc-exc-aux l 1))

;; Thus, our objective is the following theorem:

;; (defthmd inclusion-exclusion-principle
;;   (implies (and (dlistp u)
;;                 (dlistp l)
;;                 (sublistp l (subsets u)))
;;            (equal (inc-exc l)
;;                   (len (union-list l)))))

;; As an illustration, suppose l is a list of 4 sets, l = (list s1 s2 s3 s4).  Then 

;;   (inc-exc l) =   (sum-len-int (subsets-of-order 1 l)) 
;;                 - (sum-len-int (subsets-of-order 2 l))
;;                 + (sum-len-int (subsets-of-order 3 l))
;;		   - (sum-len-int (subsets-of-order 4 l))

;; where (sum-len-int (subsets-of-order 1 l) is the sum of the orders of the intersections 
;; of the subsets of order 1 of l,

;;   (sum-len-int (subsets-of-order 1 l) = 
;;       (len (int-list (list s4)))
;;     + (len (int-list (list s3)))
;;     + (len (int-list (list s2)))
;;     + (len (int-list (list s1))),

;; and similarly,

;;   (sum-len-int (subsets-of-order 2 l)) = 
;;       (len (int-list (list s3 s4)))
;;     + (len (int-list (list s2 s4)))
;;     + (len (int-list (list s2 s3)))
;;     + (len (int-list (list s1 s4)))
;;     + (len (int-list (list s1 s3)))
;;     + (len (int-list (list s1 s2)))

;;   (sum-len-int (subsets-of-order 3 l)) = 
;;       (len (int-list (list s2 s3 s4)))
;;     + (len (int-list (list s1 s3 s4)))
;;     + (len (int-list (list s1 s2 s4)))
;;     + (len (int-list (list s1 s2 s3)))

;; and since l has only 1 subset of order 4, 

;;   (sum-len-int (subsets-of-order 4 l) = (len (int-list (list s1 s2 s3 s4))).

;; To make this more concrete, suppose our universe is u = (A B C D E) and the 4 sets are
;; s1 = (A C E), s2 = (B C), s3 = (A B D), and s4 = (B), i.e., l = ((A C E) (B C) (A B D) (B)).
;; Evaluating the above terms, we have

;;   (sum-len-int (subsets-of-order 1 l) = 1 + 3 + 2 + 3 = 9
;;   (sum-len-int (subsets-of-order 2 l) = 1 + 1 + 1 + 0 + 1 + 1 = 5
;;   (sum-len-int (subsets-of-order 3 l) = 1 + 0 + 0 + 0 = 1
;;   (sum-len-int (subsets-of-order 4 l) = 0

;; and

;;   (inc-exc l) =  9 - 5 + 1 - 0 = 5 = (len (union-list l)).

;; Our strategy for proving inclusion-exclusion-principle:

;;  (1) Derive an expression (inc-exc-contrib x l k) for the contribution of a member x of u
;;      to the sum (inc-exc-aux l k), and prove that (inc-exc-aux l k) is indeed the sum of all
;;      such contributions.
;;  (2) Using the binomial theorem, prove that (inc-exc-contrib x l 1) = 1 if x is a member of 
;;      (union-list l) and 0 if not, and the theorem follows.

;;-----------------------------------------------------------------------------------------------

;; The contribution of x to (inc-exc-aux l k)  is based on an auxiliary function, which counts
;; the number of members of a list of lists m of which x is a member:

(defun num-memberships (x m)
  (if (consp m)
      (if (member-equal x (car m))
          (1+ (num-memberships x (cdr m)))
	(num-memberships x (cdr m)))
    0))

(defun inc-exc-contrib (x l k)
  (declare (xargs :measure (nfix (1+ (- (len l) k)))))
  (if (and (posp k) (<= k (len l)))
      (- (num-memberships x (int-list-list (subsets-of-order k l)))
         (inc-exc-contrib x l (1+ k)))
    0))

;; The sum of all such contributions:

(defun sum-inc-exc-contribs (u l k)
  (if (consp u)
      (+ (inc-exc-contrib (car u) l k)
         (sum-inc-exc-contribs (cdr u) l k))
    0))

;; We shall show that under suitable conditions, (sum-inc-exc-contribs u l k) = (inc-exc-aux l k)),
;; by showing that each of these terms is equal to an intermediate term, (intermediate-sum u l k):

(defun sum-memberships (u m)
  (if (consp u)
      (+ (num-memberships (car u) m)
         (sum-memberships (cdr u) m))
    0))

(defun intermediate-sum (u l k)
  (declare (xargs :measure (nfix (1+ (- (len l) k)))))
  (if (and (posp k) (<= k (len l)))
      (- (sum-memberships u (int-list-list (subsets-of-order k l)))
         (intermediate-sum u l (1+ k)))
    0))

;; It is easily proved that (intermediate-sum u l k) = (sum-inc-exc-contribs u l k):

(local-defun intermediate-sum-induct (u k)
  (if (consp u)
      (list (intermediate-sum-induct (cdr u) (1+ k))
            (intermediate-sum-induct (cdr u) k))
    (list u k)))

(defthmd sum-inc-exc-contribs-intermediate-sum
  (implies (and (posp k) (<= k (len l)))
           (equal (sum-inc-exc-contribs u l k)
                  (intermediate-sum u l k)))
  :hints (("Goal" :induct (intermediate-sum-induct u k))
          ("Subgoal *1/1" :expand ((intermediate-sum u l (+ 1 k))
	                           (intermediate-sum u l k)))))

;; Next we show that (intermediate-sum u l k) = (inc-exc-aux l k).  The proof depends on
;; an alternative formulation of sum-memberships:

(defun num-members (u s)
  (if (consp u)
      (if (member-equal (car u) s)
          (1+ (num-members (cdr u) s))
	(num-members (cdr u) s))
    0))

(defun sum-members (u m)
  (if (consp m)
      (+ (num-members u (car m))
         (sum-members u (cdr m)))
    0))

(local-defun sum-memberships-sum-members-induct (u m)
  (declare (xargs :measure (+ (len u) (len m))))
  (if (and (consp u) (consp m))
      (list (sum-memberships-sum-members-induct (cdr u) m)
            (sum-memberships-sum-members-induct u (cdr m))
            (sum-memberships-sum-members-induct (cdr u) (cdr m)))
    (list u m)))

(defthmd sum-memberships-sum-members
  (equal (sum-memberships u m)
         (sum-members u m))
  :hints (("Goal" :induct (sum-memberships-sum-members-induct u m))))

;; If s is a dlist sublist of u, then the number of members of u that are members of s is (len s):

(local-defun num-members-len-induct (u s)
  (if (consp u)
      (list (num-members-len-induct (cdr u) s)
            (num-members-len-induct (cdr u) (remove1-equal (car u) s)))
    (list u s)))

(local-defthm num-members-len-1
  (implies (not (member-equal x u))
           (equal (num-members u (remove1-equal x s))
	          (num-members u s))))

(local-defthm num-members-len-2
  (implies (and (dlistp u) (dlistp s) (sublistp s u))
           (sublistp (remove1-equal (car u) s) (cdr u))))

(defthm num-members-len
  (implies (and (dlistp u) (dlistp s) (sublistp s u))
           (equal (num-members u s)
	          (len s)))
  :hints (("Goal" :induct (num-members-len-induct u s))))

;; It follows that if every member of m is a dlist and a sublist of u, then
;; (sum-memberships u m) = (sum-lens m):

(defun dlist-sublist-listp (m u)
  (if (consp m)
      (and (dlistp (car m))
           (sublistp (car m) u)
	   (dlist-sublist-listp (cdr m) u))
    t))

(defthmd sum-members-lens
  (implies (and (dlistp u)
                (dlist-sublist-listp m u))
	   (equal (sum-members u m)
	          (sum-lens m))))

(defthmd sum-memberships-lens
  (implies (and (dlistp u)
                (dlist-sublist-listp m u))
	   (equal (sum-memberships u m)
	          (sum-lens m)))
  :hints (("Goal" :use (sum-memberships-sum-members sum-members-lens))))

;; Substitute (int-list-list (subsets-of-order k l) for m in the preceding result,
;; after showing that this list satisfies its hypothesis:

(local-defun dlist-sublist-cex (s u)
  (if (consp s)
      (if (and (dlistp (car s)) (sublistp (car s) u))
          (dlist-sublist-cex (cdr s) u)
	(car s))
    ()))

(local-defthmd dlist-sublist-cex-lemma
  (implies (not (dlist-sublist-listp s u))
           (let ((x (dlist-sublist-cex s u)))
	     (and (member-equal x s)
	          (or (not (dlistp x))
		      (not (sublistp x u))))))
  :hints (("Goal" :in-theory '(member-equal dlist-sublist-cex dlist-sublist-listp))))

(local-defthm intermediate-sum-inc-exc-aux-1
  (implies (and (dlistp u)
                (dlistp l)
		(sublistp l (subsets u))
		(sublistp r l))
	   (and (dlistp (int-list r))
                (sublistp (int-list r) u)))
  :hints (("Subgoal *1/1" :in-theory (disable sublistp-intersection)
                          :use ((:instance sublistp-intersection (l (car r)) (m (int-list (cdr r))))))))

(local-defthm intermediate-sum-inc-exc-aux-2
  (implies (and (dlistp u)
                (dlistp l)
		(sublistp l (subsets u))
		(sublistp s (subsets l))
		(member-equal x (int-list-list s)))
	   (and (dlistp x)
                (sublistp x u)))
  :hints (("Goal" :induct (int-list-list s))))
 
(local-defthm intermediate-sum-inc-exc-aux-3
  (sublistp (subsets-of-order k l)
            (subsets l)))

(local-defthm intermediate-sum-inc-exc-aux-4
  (implies (and (dlistp u)
                (dlistp l)
		(sublistp l (subsets u)))
	   (dlist-sublist-listp (int-list-list (subsets-of-order k l)) u))
  :hints (("Goal" :in-theory '(intermediate-sum-inc-exc-aux-3)
                  :use ((:instance dlist-sublist-cex-lemma (s (int-list-list (subsets-of-order k l))))
		        (:instance intermediate-sum-inc-exc-aux-2 (s (subsets-of-order k l))
			                                          (x (dlist-sublist-cex (int-list-list (subsets-of-order k l)) u)))))))

(defthmd intermediate-sum-inc-exc-aux
  (implies (and (dlistp u)
                (dlistp l)
		(sublistp l (subsets u))
		(natp k))
	   (equal (intermediate-sum u l k)
	          (inc-exc-aux l k)))
  :hints (("Subgoal *1/3" :use (intermediate-sum-inc-exc-aux-4
                                (:instance sum-memberships-lens (m (int-list-list (subsets-of-order k l))))))))

;; Combine sum-inc-exc-contribs-intermediate-sum and intermediate-sum-inc-exc-aux:

(defthmd inc-exc-aux-sum-inc-exc-contribs
  (implies (and (dlistp u)
                (dlistp l)
		(sublistp l (subsets u))
		(posp k)
		(<= k (len l)))
	   (equal (inc-exc-aux l k)
	          (sum-inc-exc-contribs u l k)))	          
  :hints (("Goal" :use (sum-inc-exc-contribs-intermediate-sum intermediate-sum-inc-exc-aux))))

;; Instantiate with k = 1:

(local-defthmd consp-len-1
  (implies (consp l)
           (and (posp 1) (<= 1 (len l)))))

(defthmd inc-exc-sum-inc-exc-contribs
  (implies (and (dlistp u)
                (dlistp l)
		(consp l)
		(sublistp l (subsets u)))
	   (equal (inc-exc l)
	          (sum-inc-exc-contribs u l 1)))	          
  :hints (("Goal" :in-theory '(inc-exc)
                  :use (consp-len-1 (:instance inc-exc-aux-sum-inc-exc-contribs (k 1))))))

(local (in-theory (disable intermediate-sum-inc-exc-aux-1 intermediate-sum-inc-exc-aux-2 intermediate-sum-inc-exc-aux-3
                    intermediate-sum-inc-exc-aux-4)))


;;-----------------------------------------------------------------------------------------------

(defun inc-exc-contrib (x l k)
  (declare (xargs :measure (nfix (1+ (- (len l) k)))))
  (if (and (posp k) (<= k (len l)))
      (- (num-memberships x (int-list-list (subsets-of-order k l)))
         (inc-exc-contrib x l (1+ k)))
    0))

;; Our next objective is the evaluation of (inc-exc-contrib x l k).  This requires the
;; evaluation of (num-memberships x (int-list-list (subsets-of-order k l))), which is 
;; the number of members r of (subsets-of-order k l) such that (int-list r) contains x.

;; If x is not a member of (union-list l), then (inc-exc-contrib x l k) is easily shown
;; to be 0:

(local-defthm inc-exc-contrib-0-1
  (implies (and (not (member-equal x (union-list l)))
                (member-equal s l))
	   (not (member-equal x s))))

(local-defthmd inc-exc-contrib-0-2
  (implies (and (not (member-equal x (union-list l)))
                (sublistp r l))
	   (not (member-equal x (int-list r)))))

(local-defthm inc-exc-contrib-0-3
  (implies (and (dlistp l)
                (not (member-equal x (union-list l)))
                (member-equal r (subsets l)))
	   (not (member-equal x (int-list r))))	   
  :hints (("Goal" :use (inc-exc-contrib-0-2))))

(local-defthm inc-exc-contrib-0-4
  (implies (and (dlistp l)
                (not (member-equal x (union-list l)))
                (sublistp s (subsets l))
		(member r (int-list-list s)))
	   (not (member-equal x r)))	   
  :hints (("Goal" :induct (int-list-list s))))

(local-defthmd inc-exc-contrib-0-5
  (implies (and (dlistp l)
                (not (member-equal x (union-list l)))
                (sublistp s (subsets l))
		(sublistp q (int-list-list s)))
	   (equal (num-memberships x q) 0))
  :hints (("Goal" :induct (num-memberships x q))))

(local-defthm inc-exc-contrib-0-6
  (implies (and (dlistp l)
                (not (member-equal x (union-list l))))
	   (equal (num-memberships x (int-list-list (subsets-of-order k l))) 0))
  :hints (("Goal" :use ((:instance inc-exc-contrib-0-5 (s (subsets-of-order k l))
                                                       (q (int-list-list (subsets-of-order k l))))))))

(defthmd inc-exc-contrib-0
  (implies (and (dlistp l)
                (not (member-equal x (union-list l))))
           (equal (inc-exc-contrib x l k)
	          0)))

(local (in-theory (disable inc-exc-contrib-0-3 inc-exc-contrib-0-4 inc-exc-contrib-0-6)))

;; Now suppose x is a member of (union-list l).  We define the list of all members of l that
;; contain x:

(defun sets-containing (x l)
  (if (consp l)
      (if (member-equal x (car l))
          (cons (car l) (sets-containing x (cdr l)))
	(sets-containing x (cdr l)))
    ()))

(defthm sets-containing-subset
  (implies (dlistp l)
           (member-equal (sets-containing x l)
	                 (subsets l))))

(defthm len-sets-containing
  (equal (len (sets-containing x l))
         (num-memberships x l)))

(local-defun member-sets-containing-induct (s l)
  (if (consp l)
      (list (member-sets-containing-induct s (cdr l))
            (member-sets-containing-induct (car l) (cdr l)))
    (list s l)))

(defthm member-sets-containing
  (iff (member-equal s (sets-containing x l))
       (and (member-equal s l)
	    (member-equal x s)))
  :hints (("Goal" :induct (member-sets-containing-induct s l))))

(local-defthm member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
	   (member-equal x m))))

(local-defthm member-conses
  (iff (member-equal p (conses k l))
	   (and (consp p)
		(equal (car p) k)
		(member-equal (cdr p) l))))

(local-defthm member-nil-subsets
  (member-equal () (subsets l)))

(local-defthm member-intersection
  (iff (member-equal x (intersection-equal a b))
       (and (member-equal x a)
            (member-equal x b))))

(local-defthmd num-memberships-choose-1
  (implies (and (consp r)
                (sublistp r l)
                (sublistp r (sets-containing x l)))
	   (member-equal x (int-list r))))

(local-defthmd num-memberships-choose-2
  (implies (and (consp r)
                (sublistp r l)
                (member-equal x (int-list r)))
	   (sublistp r (sets-containing x l))))

;; For any subset r of l, x belongs to (int-list r) iff r is a sublist of (sets-containing x l)):
	        
(defthmd member-int-list-subset
  (implies (and (dlistp l)
                (consp r)
                (member-equal r (subsets l)))
	   (iff (member-equal x (int-list r))
	        (sublistp r (sets-containing x l))))
  :hints (("Goal" :use (num-memberships-choose-1 num-memberships-choose-2))))

;; Consequently, the number of members r of (subsets-of-order k l) such that (int-list r)
;; contains x is equal to the number of members of (subsets-of-order k l) that are sublists
;; of (sets-containing x l):

(defun sublists-of (c s)
  (if (consp s)
      (if (sublistp (car s) c)
          (cons (car s) (sublists-of c (cdr s)))
	(sublists-of c (cdr s)))
    ()))

(local-defthm member-sublists-of
  (iff (member-equal y (sublists-of c s))
       (and (member-equal y s)
            (sublistp y c)))
  :hints (("Goal" :induct (member-sets-containing-induct y s))))

(local-defthm dlistp-sublists-of
  (implies (dlistp s)
           (dlistp (sublists-of c s))))

(local-defthmd num-memberships-choose-4
  (implies (and (dlistp l)
		(sublistp s (subsets-of-order k l))
		(posp k))
           (equal (num-memberships x (int-list-list s))
                  (len (sublists-of (sets-containing x l) s))))
  :hints (("Goal" :induct (int-list-list s))
          ("Subgoal *1/1" :use ((:instance member-int-list-subset (r (car s)))))))

(defthmd num-memberships-len-sublists-of
  (implies (and (dlistp l)
		(posp k))
           (equal (num-memberships x (int-list-list (subsets-of-order k l)))
                  (len (sublists-of (sets-containing x l) (subsets-of-order k l)))))
  :hints (("Goal" :use ((:instance num-memberships-choose-4 (s (subsets-of-order k l)))))))

;; By subset-subset, the subsets of order k l that are sublists of (sets-containing x l)) 
;; are just the subsets of or order k (sets-containing x l)):

(defthmd member-sublists-of-sets-containing
  (implies (and (dlistp l)
		(posp k))
           (iff (member-equal y (sublists-of (sets-containing x l) (subsets-of-order k l)))
	        (member-equal y (subsets-of-order k (sets-containing x l)))))
  :hints (("Goal" :use ((:instance subset-subset (x y) (s (sets-containing x l)))))))

;; Thus, the two lists are permutations of each other and therefore have the same length:

(defthmd len-sublists-of-sets-containing
  (implies (and (dlistp l)
		(posp k))
           (equal (len (sublists-of (sets-containing x l) (subsets-of-order k l)))
	          (len (subsets-of-order k (sets-containing x l)))))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance scex1-lemma (l (sublists-of (sets-containing x l) (subsets-of-order k l)))
                                               (m (subsets-of-order k (sets-containing x l))))
			(:instance scex1-lemma (m (sublists-of (sets-containing x l) (subsets-of-order k l)))
                                               (l (subsets-of-order k (sets-containing x l))))
			(:instance eq-len-permp (l (sublists-of (sets-containing x l) (subsets-of-order k l)))
                                                (m (subsets-of-order k (sets-containing x l))))
			(:instance member-sublists-of-sets-containing
			   (y (scex1 (sublists-of (sets-containing x l) (subsets-of-order k l))
                                     (subsets-of-order k (sets-containing x l)))))
			(:instance member-sublists-of-sets-containing
			   (y (scex1 (subsets-of-order k (sets-containing x l))
			             (sublists-of (sets-containing x l) (subsets-of-order k l)))))))))

;; Combine the last two results with len-subsets-of-order:
                                     
(defthm num-memberships-choose
  (implies (and (dlistp l)
		(posp k))
           (equal (num-memberships x (int-list-list (subsets-of-order k l)))
                  (choose (num-memberships x l) k)))
  :hints (("Goal" :use (num-memberships-len-sublists-of len-sublists-of-sets-containing))))

(local-defthmd len-num-memberships-bound
  (<= (num-memberships x l)
      (len l)))

(local-defthm inc-exc-contrib-binomial-1
  (implies (and (dlistp l)
		(posp k)
		(> k (num-memberships x l)))
           (equal (inc-exc-contrib x l k) 0))
  :hints (("Goal" :in-theory (enable choose))))

(local-defthm inc-exc-contrib-binomial-2
  (implies (and (dlistp l)
                (member-equal x (union-list l)))
	   (> (num-memberships x l) 0))
  :hints (("Goal" :induct (num-memberships x q))))

;; Now consider the binomial expansion of (expt (+ -1 1) n), where n = (num-memberships x l)).
;; The following is a consequence of num-memberships-choose and the definitions of
;; inc-exc-contrib and binomial-expansion:

(defthmd inc-exc-contrib-binomial
  (implies (and (dlistp l)
		(posp k)
		(<= k (num-memberships x l)))
           (equal (inc-exc-contrib x l k)
                  (if (evenp k)
                      (sum-list (binomial-expansion -1 1 k (num-memberships x l)))
	            (- (sum-list (binomial-expansion -1 1 k (num-memberships x l)))))))
   :hints (("Subgoal *1/1" :use (len-num-memberships-bound))))

;; The case of interest is k = 1:

(defthmd member-union-l-inc-exc-contrib-binomial
  (implies (and (dlistp l)
                (member-equal x (union-list l)))
           (equal (inc-exc-contrib x l 1)
                  (- (sum-list (binomial-expansion -1 1 1 (num-memberships x l))))))
  :hints (("Goal" :use ((:instance inc-exc-contrib-binomial (k 1))))))

;; Now apply the binomial theorem:

;;   0 = (expt (+ -1 1) (num-memberships x l))
;;     = (sum-list (cons (* (choose n 0) (expt -1 0) (expt 1 k))
;;	                 (binomial-expansion -1 1 1 n)))
;;     = (+ 1 (sum-list (binomial-expansion -1 1 1 n)))

;; Thus, (sum-list (binomial-expansion -1 1 1 n)) = -1, and we have the following:

(defthmd inc-exc-contrib-1
  (implies (and (dlistp l)
                (member-equal x (union-list l)))
           (equal (inc-exc-contrib x l 1)
                  1))
  :hints (("Goal" :in-theory (enable choose)
                  :use (member-union-l-inc-exc-contrib-binomial
                        (:instance binomial-theorem (x -1) (y 1) (n (num-memberships x l)))))))

;; Combine inc-exc-contrib-0 and inc-exc-contrib-1:

(defthmd sum-inc-exc-contribs-len-union-1
  (implies (dlistp l)
           (equal (sum-inc-exc-contribs u l 1)
	          (num-members u (union-list l))))
  :hints (("Goal" :in-theory (enable inc-exc-contrib-0 inc-exc-contrib-1))))

;; Move to lists.lisp:

(defthm member-union
  (iff (member-equal x (union-equal l m))
       (or (member-equal x l)
           (member-equal x m))))

(defthm dlistp-union
  (implies (and (dlistp l) (dlistp m))
           (dlistp (union-equal l m))))

(defthm dlistp-union-list
  (implies (and (dlistp u)
                (consp l)
                (sublistp l (subsets u)))
           (dlistp (union-list l)))
  :hints (("Goal" :induct (union-list l))))

(defthm sublistp-union
  (implies (and (sublistp l u) (sublistp m u))
           (sublistp (union-equal l m) u)))

(defthm sublistp-union-list
  (implies (and (dlistp u)
                (consp l)
                (sublistp l (subsets u)))
           (sublistp (union-list l) u))
  :hints (("Goal" :induct (union-list l))))

;; Apply num-members-len:

(defthmd sum-inc-exc-contribs-len-union
  (implies (and (dlistp u)
                (dlistp l)
		(consp l)
		(sublistp l (subsets u)))
           (equal (sum-inc-exc-contribs u l 1)
	          (len (union-list l))))
  :hints (("Goal" :use (sum-inc-exc-contribs-len-union-1))))

(defthm inc-exc-nil
  (implies (not (consp l))
           (equal (inc-exc l) 0))
  :hints (("Goal" :in-theory (enable inc-exc))))

(defthm union-list-nil
  (implies (not (consp l))
           (equal (union-list l) ())))

;; Finally, our main result follows from inc-exc-sum-inc-exc-contribs:

(defthmd inclusion-exclusion-principle
  (implies (and (dlistp u)
                (dlistp l)
                (sublistp l (subsets u)))
           (equal (inc-exc l)
                  (len (union-list l))))
  :hints (("Goal" :use (sum-inc-exc-contribs-len-union inc-exc-sum-inc-exc-contribs))))

