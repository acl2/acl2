(in-package "DM")

(include-book "projects/groups/groups" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

;; Given a random set of k people, what is the probability that at least one pair of them
;; have the same birthday?  What is the smallest k for which this probability is greater
;; than 1/2?

;; An assignment of birthdays to k people will be represented as a list of dates of length
;; k, where a date is represented as a natural number less than 365.  (As a simplification
;; of the problem, we shall pretend that there are no leap years.)  We shall construct a
;; list of all possible birthday assignments and a sublist consisting of the assignmemts
;; that contain duplicates.  The desired probability is the ratio of the lengths of these
;; lists.

;; Given a list m of distinct members (a "dlist") and a sublist l that is also a dlist,
;; (lists l m k) is a list of all dlist sublists of m that begin with a member of l.

(encapsulate ()
  (local (include-book "ordinals/lexicographic-book" :dir :system))
  (set-well-founded-relation acl2::l<)
  
  (defun lists (l m k)
    (declare (xargs :measure (list (acl2-count k) (acl2-count l))))
    (if (posp k)
        (if (consp l)
            (append (conses (car l) (lists m m (1- k)))
		    (lists (cdr l) m k))
  	  ())
      (list ())))

  (defun lists-induct (l m k x)
    (declare (xargs :measure (list (acl2-count k) (acl2-count l))))
    (if (zp k)
        (list l m x)
      (if (consp l)
	  (list (lists-induct (cdr l) m k x)
	        (lists-induct m m (1- k) (cdr x)))
        ())))
  )

(defthmd member-lists
  (implies (and (sublistp l m) (natp k))
           (iff (member-equal x (lists l m k))
		(and (true-listp x)
		     (or (zp k) (member-equal (car x) l))
		     (sublistp x m)
		     (equal (len x) k))))
  :hints (("Goal" :induct (lists-induct l m k x))))

(local-defthmd car-member-conses
  (iff (member-equal y (conses x l))
       (and (consp y) (equal (car y) x) (member-equal (cdr y) l))))

(defthm disjointp-append
  (implies (and (disjointp l m) (disjointp l p))
           (disjointp l (append m p)))
  :hints (("Goal" :use ((:instance disjointp-append-list (m (list m p)))))))

(local-defthm dlistp-lists-1
  (implies (and (sublistp l m) (natp k) (not (member-equal x l)))
	   (disjointp (conses x p) (lists l m k)))
  :hints (("Subgoal *1/17" :use ((:instance common-member-shared (l (conses x p)) (m '(())))
				 (:instance car-member-conses (y (common-member (conses x p) '(()))) (l p))))
          ("Subgoal *1/16" :use ((:instance common-member-shared (l (conses x p)) (m ()))))
          ("Subgoal *1/15" :use ((:instance common-member-shared (l (conses x p)) (m (CONSES (CAR L) (LISTS M M (+ -1 K)))))
				 (:instance car-member-conses (y (common-member (conses x p) (CONSES (CAR L) (LISTS M M (+ -1 K)))))
				                              (l p))
				 (:instance car-member-conses (y (common-member (conses x p) (CONSES (CAR L) (LISTS M M (+ -1 K)))))
					                      (x (car l)) (l (LISTS M M (+ -1 K))))))
          ("Subgoal *1/14" :use ((:instance common-member-shared (l (conses x p)) (m (CONSES (CAR L) (LISTS M M (+ -1 K)))))
				 (:instance car-member-conses (y (common-member (conses x p) (CONSES (CAR L) (LISTS M M (+ -1 K)))))
				                              (l p))
				 (:instance car-member-conses (y (common-member (conses x p) (CONSES (CAR L) (LISTS M M (+ -1 K)))))
					                      (x (car l)) (l (LISTS M M (+ -1 K))))))))

(local-defthm not-member-conses
  (implies (not (member-equal y l))
           (not (member (cons x y) (conses x l)))))

(local-defthm dlistp-conses
  (implies (dlistp l) (dlistp (conses x l))))

(defthm dlistp-lists
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (natp k))
	   (dlistp (lists l m k))))

;; If l = m = (ninit k), the list of the first k naturals, then we have the list of all
;; possible birthday assignments to a group of k people:

(defund birthday-lists (k)
  (lists (ninit 365) (ninit 365) k))

(defthmd member-birthday-lists
  (implies (natp k)
	   (iff (member-equal x (birthday-lists k))
		(and (true-listp x)
		     (sublistp x (ninit 365))
		     (equal (len x) k))))
  :hints (("Goal" :in-theory (e/d (birthday-lists) (member-equal))
	   :use ((:instance member-lists (l (ninit 365)) (m (ninit 365)))))))

(defthmd dlistp-birthday-lists
  (implies (natp k)
	   (dlistp (birthday-lists k)))
  :hints (("Goal" :in-theory (enable birthday-lists)
                  :use ((:instance dlistp-lists (l (ninit 365)) (m (ninit 365)))))))

;; The sublist of (lists l m k) consisting of all dlists:

(encapsulate ()
  (local (include-book "ordinals/lexicographic-book" :dir :system))
  (set-well-founded-relation acl2::l<)
  
  (defun dlists (l m k)
    (declare (xargs :measure (list (acl2-count k) (acl2-count l))))
    (if (posp k)
        (if (consp l)
            (append (conses (car l)
			    (dlists (remove1-equal (car l) m)
				    (remove1-equal (car l) m)
				    (1- k)))
		    (dlists (cdr l) m k))
  	  ())
      (list ())))
      
  (defun dlists-induct (l m k x)
    (declare (xargs :measure (list (acl2-count k) (acl2-count l))))
    (if (zp k)
        (list l m x)
      (if (consp l)
	  (list (dlists-induct (cdr l) m k x)
	        (dlists-induct (remove1-equal (car l) m) (remove1-equal (car l) m) (1- k) (cdr x)))
        ())))

  (defun dlistp-dlists-induct (l m k)
    (declare (xargs :measure (list (acl2-count k) (acl2-count l))))
    (if (zp k)
        (list l m)
      (if (consp l)
	  (list (dlistp-dlists-induct (cdr l) m k)
	        (dlistp-dlists-induct (remove1-equal (car l) m) (remove1-equal (car l) m) (1- k)))
        ())))
)

(local-defthm member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
           (member-equal x m))))

(local-defthm sublistp-sublistp-remove1
  (implies (sublistp l (remove1-equal x m))
           (sublistp l m)))

(defthm member-dlists
  (implies (and (sublistp l m) (dlistp l) (dlistp m) (natp k))
           (iff (member-equal x (dlists l m k))
		(and (true-listp x)
		     (or (zp k) (member-equal (car x) l))
		     (sublistp x m)
		     (equal (len x) k)
		     (dlistp x))))
  :hints (("Goal" :induct (dlists-induct l m k x))
          ("Subgoal *1/2" :use ((:instance car-member-conses (y x) (x (car l))
	                                                     (l (dlists (remove1-equal (car l) m)
                                                                        (remove1-equal (car l) m)
                                                                        (+ -1 k))))
				(:instance member-sublist (x (car l)) (l (cdr x)) (m (remove1-equal (car l) m)))))))

(defthmd member-dlists-lists
  (implies (and (sublistp l m) (dlistp l) (dlistp m) (natp k))
           (iff (member-equal x (dlists l m k))
		(and (member-equal x (lists l m k))
		     (dlistp x))))
  :hints (("Goal" :in-theory '(member-lists member-dlists))))

(local-defthm dlistp-dlists-1
  (implies (and (sublistp l m) (dlistp l) (dlistp m) (natp k) (not (member-equal x l)))
	   (disjointp (conses x p) (dlists l m k)))
  :hints (("Subgoal *1/1" :expand ((dlists l m k))  
                          :use ((:instance car-member-conses (y (cons x (car p))) (x (car l))
			                                     (l (DLISTS (REMOVE1-EQUAL (CAR L) M) (REMOVE1-EQUAL (CAR L) M) (+ -1 K))))
                                (:instance member-dlists (x (cons x (car p))) (l (cdr l)))))))

(defthm dlistp-dlists
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (natp k))
	   (dlistp (dlists l m k)))
  :hints (("Goal" :induct (dlistp-dlists-induct l m k))))

(defthm dlistp-dlists-ninit
  (implies (natp k)
           (dlistp (dlists (ninit 365) (ninit 365) k))))

;; If l = m = (ninit k), the list of the first k naturals, then we have the list of all
;; possible birthday assignments to a group of k people that have no duplicates.  We are
;; interested in the complement of that list:

(defund birthday-lists-with-repetition (k)
  (set-difference-equal (birthday-lists k)
			(dlists (ninit 365) (ninit 365) k)))

(local-defthmd sublistp-dlists-1
  (implies (and (sublistp l m) (dlistp l) (dlistp m) (natp k) (member-equal x (dlists l m k)))
           (member-equal x (lists l m k)))
  :hints (("Goal" :use (member-lists member-dlists))))

(defthmd sublistp-dlists
  (implies (and (sublistp l m) (dlistp l) (dlistp m) (natp k))
           (sublistp (dlists l m k) (lists l m k)))
  :hints (("Goal" :use ((:instance sublistp-dlists-1 (x (scex1 (dlists l m k) (lists l m k))))
			(:instance scex1-lemma (l (dlists l m k)) (m (lists l m k)))))))

(defthmd sublistp-birthday-lists
  (implies (natp k)
	   (sublistp (dlists (ninit 365) (ninit 365) k)
		     (birthday-lists k)))
  :hints (("Goal" :in-theory (e/d (birthday-lists) ((ninit) member-equal))
	   :use ((:instance sublistp-dlists (l (ninit 365)) (m (ninit 365)))))))

(defthmd member-set-difference
  (iff (member-equal x (set-difference-equal l m))
       (and (member-equal x l)
            (not (member-equal x m)))))

(local-defthm dlistp-ninit-365
  (and (dlistp (ninit 365))
       (sublistp (ninit 365) (ninit 365))))

(defthmd member-birthday-lists-with-repetition
  (implies (natp k)
	   (iff (member-equal x (birthday-lists-with-repetition k))
		(and (member-equal x (birthday-lists k))
		     (not (dlistp x)))))
  :hints (("Goal" :in-theory '(dlistp-ninit-365 birthday-lists birthday-lists-with-repetition)
                  :use (sublistp-birthday-lists dlistp-birthday-lists dlistp-dlists-ninit
		        (:instance member-dlists-lists (l (ninit 365)) (m (ninit 365)))
		        (:instance member-set-difference (l (birthday-lists k)) (m (dlists (ninit 365) (ninit 365) k)))))))

(defthm dlistp-set-difference
  (implies (dlistp l)
	   (dlistp (set-difference-equal l m)))
  :hints (("Goal" :in-theory (enable member-set-difference))))

(defthm dlistp-birthday-lists-with-repetition
  (implies (natp k)
	   (dlistp (birthday-lists-with-repetition k)))
  :hints (("Goal" :in-theory (e/d (birthday-lists-with-repetition) (member-equal)))))

(local-defthm len-conses
  (equal (len (conses x l))
         (len l)))

(local-defthm len-append
  (equal (len (append l m))
         (+ (len l) (len m))))

(defthm len-lists
  (implies (and (sublistp l m) (natp k))
	   (equal (len (lists l m k))
		  (if (posp k)
		      (* (len l)
		         (expt (len m) (1- k)))
		    1))))

(defthm len-birthday-lists
  (implies (natp k)
	   (equal (len (birthday-lists k))
		  (expt 365 k)))
  :hints (("Goal" :in-theory (enable birthday-lists))))

(defthm len-dlists
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (natp k) (<= k (len m)))
	   (equal (len (dlists l m k))
		  (if (posp k)
		      (* (len l)
		         (/ (fact (1- (len m)))
			    (fact (- (len m) k))))
		    1)))
  :hints (("Goal" :induct (dlistp-dlists-induct l m k))))

(defthm len-dlists-ninit-365
  (implies (and (natp k) (<= k 365))
	   (equal (len (dlists (ninit 365) (ninit 365) k))
	          (/ (fact 365) (fact (- 365 k)))))
  :hints (("Goal" :use ((:instance len-dlists (l (ninit 365)) (m (ninit 365))))
	          :in-theory (disable len-dlists (ninit) ninit))))	      

(local-defthmd len-set-difference
  (equal (+ (len (set-difference-equal l m))
            (len (intersection-equal l m)))
         (len l)))

(local-defthmd member-intersection
  (implies (and (member-equal x l) (member-equal x m))
	   (member-equal x (intersection-equal l m)))
  :hints (("Goal" :induct (intersection-equal l m))))

(local-defthm member-sublistp-intersection
  (implies (and (member-equal x m) (sublistp m l))
	   (member-equal x (intersection-equal l m)))
  :hints (("Goal" :use (member-intersection))))

(defthm sublist-intersection
  (implies (sublistp m l)
	   (sublistp m (intersection-equal l m)))
  :hints (("Goal" :use ((:instance scex1-lemma (l m) (m (intersection-equal l m)))))))

(defthm len-intersection-sublist
  (implies (and (sublistp m l) (dlistp l) (dlistp m))
	   (equal (len (intersection-equal l m))
		  (len m)))
  :hints (("Goal" :in-theory (enable permp)
	   :use ((:instance eq-len-permp (l m) (m (intersection-equal l m)))))))

(defthmd len-set-difference-sublist
  (implies (and (sublistp m l) (dlistp l) (dlistp m))
	   (equal (len (set-difference-equal l m))
		  (- (len l) (len m))))
  :hints (("Goal" :use (len-set-difference))))

(defthm len-birthday-lists-with-repetition
  (implies (and (natp k) (<= k 365))
	   (equal (len (birthday-lists-with-repetition k))
		  (- (expt 365 k)
                     (/ (fact 365) (fact (- 365 k))))))
  :hints (("Goal" :in-theory (e/d (birthday-lists-with-repetition) (ninit (ninit)))
	          :use (sublistp-birthday-lists dlistp-birthday-lists
			(:instance len-set-difference-sublist (l (birthday-lists k)) (m (dlists (ninit 365) (ninit 365) k)))))))

(defun probability-of-repetition (k)
  (/ (len (birthday-lists-with-repetition k))
     (len (birthday-lists k))))

(defthm probability-of-repetition-value
  (implies (and (natp k) (<= k 365))
	   (equal (probability-of-repetition k)
                  (- 1 (/ (fact 365) (* (fact (- 365 k)) (expt 365 k)))))))

(in-theory (disable (probability-of-repetition)))

(defthm probability-of-repetition-22
  (< (probability-of-repetition 22) 1/2))

(defthm probability-of-repetition-23
  (> (probability-of-repetition 23) 1/2))
