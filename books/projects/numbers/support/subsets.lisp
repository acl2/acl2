(in-package "DM")

(include-book "projects/groups/lists" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

;; Let l be a dlist of length n.  Thenl represents a set of order n, the elements
;; of which are the members of l. In this context, 2 dlists are considered equivalent
;; if they represent the same set, i.e., one is a permutation of the other.

;; We have 2 objectives (1) Compute the number of subsets of (the set represented
;; by) l as a function of the length of l; (2) compute the number of such subsets
;; of a given order k <= (len l).  For this purpose, we define the following list
;; of sublists of l:

(defun subsets (l)
  (if (consp l)
      (let ((s (subsets (cdr l))))
	(append s (conses (car l) s)))
    (list ())))

(local (defthm member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
           (member-equal x m)))))

(local (defthm car-member-conses
  (iff (member-equal y (conses x l))
       (and (consp y) (equal (car y) x) (member-equal (cdr y) l)))))

(local (defun subsets-induct (s l)
  (if (consp l)
      (list (subsets-induct s (cdr l))
	    (subsets-induct (cdr s) (cdr l)))
    (list s l))))

;; Every member of (subsets l) is a sublist of l and a dlist:

(defthm sublistp-subset
  (implies (and (dlistp l) (member-equal s (subsets l)))
	   (sublistp s l))
  :hints (("Goal" :induct (subsets-induct s l))))

(defthm dlistp-subset
  (implies (and (dlistp l) (member-equal s (subsets l)))
	   (dlistp s))
  :hints (("Goal" :induct (subsets-induct s l))))

(local (defun len-subset-bound-induct (s l)
  (if (consp l)
      (list (len-subset-bound-induct (cdr s) (cdr l))
            (len-subset-bound-induct s (cdr l)))
    (list s l))))

(defthmd len-subset-bound
  (implies (member-equal s (subsets l))
	   (<= (len s) (len l)))
  :hints (("Goal" :induct (len-subset-bound-induct s l))))

(local (defthm dlistp-conses
  (implies (dlistp l)
	   (dlistp (conses x l)))))

;; (subsets l) is itself a dlist:

(defthm dlistp-subsets
  (implies (dlistp l) (dlistp (subsets l)))
  :hints (("Subgoal *1/2" :use ((:instance common-member-shared (l (SUBSETS (CDR L)))
                                                                (m (CONSES (CAR L) (SUBSETS (CDR L)))))
				(:instance sublistp-subset (s (common-member (SUBSETS (CDR L))
                                                                             (CONSES (CAR L) (SUBSETS (CDR L)))))
							   (l (cdr l)))))))

(defthm member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
	   (member-equal x m))))

(defthm member-conses
  (iff (member-equal p (conses k l))
	   (and (consp p)
		(equal (car p) k)
		(member-equal (cdr p) l))))

(defthm member-nil-subsets
  (member-equal () (subsets l)))

(local (defun subset-subset-1-induct (x s l)
  (declare (xargs :measure (+ (len s) (len l))))
  (if (and (consp s) (consp l))
      (list (subset-subset-1-induct x (cdr s) l)
            (subset-subset-1-induct x s (cdr l))
            (subset-subset-1-induct (cdr x) (cdr s) (cdr l)))
    (list x s l))))

(local (defthmd subset-subset-1
  (implies (and (dlistp l)
                (member-equal s (subsets l))
                (member-equal x (subsets s)))
	   (member-equal x (subsets l)))
  :hints (("Goal" :induct (subset-subset-1-induct x s l))
          ("Subgoal *1/1" :cases ((member-equal x (subsets (cdr s))))))))

(local (defthm consp-subset
  (implies (and (member-equal x (subsets l))
                x)
	   (consp x))))

(local (defun subset-subset-2-induct (x s l)
  (if (consp l)
      (list (subset-subset-2-induct x s (cdr l))
            (subset-subset-2-induct x (cdr s) (cdr l))
            (subset-subset-2-induct (cdr x) (cdr s) (cdr l)))
    (list x s l))))

(local (defthmd subset-subset-2-1
  (implies (and (consp s) (sublistp x s) (not (member-equal (car s) x)))
           (sublistp x (cdr s)))))
	   
(local (defthmd subset-subset-2-2
  (implies (and (dlistp l)
                (member-equal x (subsets l))
		(sublistp x s)
		(consp s)
                (equal (car x) (car s)))
           (sublistp (cdr x) (cdr s)))
  :hints (("Goal" :in-theory (disable dlistp-subset)
                  :use ((:instance subset-subset-2-1 (x (cdr x)))
                        (:instance dlistp-subset (s x)))))))

(local (defthmd subset-subset-2
  (implies (and (dlistp l)
                (member-equal s (subsets l))
                (member-equal x (subsets l))
		(sublistp x s))
	   (member-equal x (subsets s)))
  :hints (("Goal" :induct (subset-subset-2-induct x s l))
          ("Subgoal *1/1" :cases ((member-equal x (subsets (cdr l)))))
	  ("Subgoal *1/1.2" :use (subset-subset-2-2))
	  ("Subgoal *1/1.1" :cases ((member-equal s (subsets (cdr l)))))
	  ("Subgoal *1/1.1.2" :in-theory (disable sublistp-subset)
	                      :use (subset-subset-2-1
	                            (:instance sublistp-subset (s x) (l (cdr l))))))))

(defthmd subset-subset
  (implies (and (dlistp l)
                (member-equal s (subsets l)))
	   (iff (member-equal x (subsets s))
	        (and (member-equal x (subsets l))
		     (sublistp x s))))
  :hints (("Goal" :use (subset-subset-1 subset-subset-2))))

(defthm true-listp-subset
  (implies (member-equal s (subsets l))
           (true-listp s))
  :hints (("Goal" :induct (subsets-induct s l))))

(defthm subset-self
  (implies (true-listp l)
	   (member-equal l (subsets l))))

(local (defthm member-remove1-subsets
  (implies (member-equal s (subsets l))
           (member-equal (remove1-equal x s) (subsets l)))
  :hints (("Goal" :induct (subsets-induct s l)))))

(local (defthmd perm-subset-equal-1
  (implies (and (dlistp l)
                (member-equal s (subsets (cdr l)))
		(member-equal r (subsets l))
		(permutationp r s))
	   (member-equal r (subsets (cdr l))))))

(local (defthmd perm-subset-equal-2
  (implies (and (consp l)
                (dlistp l)
                (member-equal s (subsets l))
		(member-equal r (subsets l))
		(permutationp r s))
	   (iff (member-equal r (subsets (cdr l)))
	        (member-equal s (subsets (cdr l)))))
  :hints (("Goal" :use (perm-subset-equal-1
                        (:instance perm-subset-equal-1 (r s) (s r))
			(:instance permutationp-symmetric (l r) (m s)))))))

(local (defun perm-subset-equal-induct (l r s)
  (if (consp l)
      (list (perm-subset-equal-induct (cdr l) r s)
            (perm-subset-equal-induct (cdr l) (cdr r) (cdr s)))
    (list l r s))))

;; No member of l is a permutation of another, i.e., distinct members of l
;; represent distinct subsets:

(defthm perm-subset-equal
  (implies (and (dlistp l)
                (member-equal s (subsets l))
		(member-equal r (subsets l))
		(permutationp r s))
	   (equal r s))
  :rule-classes ()
  :hints (("Goal" :induct (perm-subset-equal-induct l r s))
          ("Subgoal *1/1" :use (perm-subset-equal-2))))

;; Moreover, every dlist sublist of l is a permutation of some member of
;; (subsets l):

(defun find-subset (s l)
  (if (consp l)
      (if (member-equal (car l) s)
	  (cons (car l) (find-subset (remove1-equal (car l) s) (cdr l)))
	(find-subset s (cdr l)))
    ()))

(defthm member-find-subset-subsets
  (member-equal (find-subset s l)
                (subsets l)))

(local (defthm sublistp-remove1-cdr
  (implies (and (dlistp s) (sublistp s l))
           (sublistp (remove1-equal (car l) s)
	             (cdr l)))))

(local (defthm sublistp-cdr
  (implies (and (sublistp s l) (not (member-equal (car l) s)))
           (sublistp s (cdr l)))))

(defthm perm-find-subset
  (implies (and (dlistp l) (dlistp s) (sublistp s l))
	   (permutationp (find-subset s l) s))
  :hints (("Goal" :induct (find-subset s l))))

;; Thus, the number of subsets of l is (len (subsets l), which is easily
;; shown to be 2^n:

(local (defthm len-append
  (equal (len (append l m))
         (+ (len l) (len m)))))

(local (defthm len-conses
  (equal (len (conses x l))
         (len l))))

(defthm len-subsets
  (equal (len (subsets l))
         (expt 2 (len l))))

;; Next we consider the sublist of (subsets l) consisting of all lists
;; of a given length k:

(defun subsets-of-order-aux (k l)
  (if (consp l)
      (if (equal (len (car l)) k)
	  (cons (car l) (subsets-of-order-aux k (cdr l)))
	(subsets-of-order-aux k (cdr l)))
    ()))

(defund subsets-of-order (k l)
  (subsets-of-order-aux k (subsets l)))

(local (defthm sublistp-subsets-of-order-aux
  (sublistp (subsets-of-order-aux k l) l)))

(local (defthm dlistp-subsets-of-order-aux
  (implies (dlistp l)
	   (dlistp (subsets-of-order-aux k l)))))

(local (defthm member-subsets-of-order-aux-1
  (implies (member-equal x (subsets-of-order-aux k l))
           (and (member-equal x l)
                (equal (len x) k)))))

(local (defthm member-subsets-of-order-aux
  (iff (member-equal x (subsets-of-order-aux k l))
       (and (member-equal x l)
            (equal (len x) k)))))

(defthm sublistp-subsets-of-order
  (sublistp (subsets-of-order k l) (subsets l))
  :hints (("Goal" :in-theory (enable subsets-of-order))))

(defthm member-subsets-of-order
  (iff (member-equal x (subsets-of-order k l))
       (and (member-equal x (subsets l))
            (equal (len x) k)))
  :hints (("Goal" :in-theory (enable subsets-of-order))))

(defthmd no-subsets-of-order>len
  (implies (and (natp k) (> k (len l)))
           (equal (subsets-of-order k l)
	          ()))
  :hints (("Goal" :in-theory (disable member-subsets-of-order)
                  :use ((:instance member-subsets-of-order (x (car (subsets-of-order k l))))
                        (:instance len-subset-bound (s (car (subsets-of-order k l))))))))

(defthmd no-subsets-of-order>len
  (implies (and (natp k) (> k (len l)))
           (equal (subsets-of-order k l)
	          ()))
  :hints (("Goal" :in-theory (disable member-subsets-of-order)
                  :use ((:instance member-subsets-of-order (x (car (subsets-of-order k l))))
                        (:instance len-subset-bound (s (car (subsets-of-order k l))))))))

;; (subsets-of-order k l) is a dlist, and therefore, (len (subsets-of-order k l))
;; is the number of subsets of l of order k:

(defthm dlistp-subsets-of-order
  (implies (dlistp l)
	   (dlistp (subsets-of-order k l)))
  :hints (("Goal" :in-theory (enable subsets-of-order))))

;; We shall prove by inductions that (len (subsets-of-order k l)) = n!/(k!(n - k)!).
;; To this end, we split (subsets-of-order k l) into 2 sublists, consisting of the
;; subsets that contain (car l) and the subsets that do not contain (car l):

(defthmd member-conses-subsets-of-order
  (implies (and (dlistp l) (consp l) (posp k))
           (iff (member-equal x (conses (car l) (subsets-of-order (1- k) (cdr l))))
	        (and (member-equal x (subsets-of-order k l))
		     (member-equal (car l) x))))
  :hints (("Goal" :use (member-subsets-of-order
                        (:instance member-subsets-of-order (k (1- k)) (l (cdr l)))))))

(defthmd member-cdr-subsets-of-order
  (implies (and (dlistp l) (natp k))
           (iff (member-equal x (subsets-of-order k (cdr l)))
	        (and (member-equal x (subsets-of-order k l))
		     (not (member-equal (car l) x)))))
  :hints (("Goal" :use (member-subsets-of-order
                        (:instance member-subsets-of-order (l (cdr l)))))))

(defthmd member-subsets-of-order-append
  (implies (and (dlistp l) (consp l) (posp k))
           (iff (member-equal x (subsets-of-order k l))
	        (member-equal x (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		                        (subsets-of-order k (cdr l))))))
  :hints (("Goal" :use (member-conses-subsets-of-order member-cdr-subsets-of-order))))

(defthmd dlistp-append-subsets-of-order
  (implies (and (dlistp l) (consp l) (posp k))
           (dlistp (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		           (subsets-of-order k (cdr l)))))
  :hints (("Goal" :in-theory (disable sublistp-subset)
                  :use ((:instance common-member-shared (l (conses (car l) (subsets-of-order (1- k) (cdr l))))
                                                        (m (subsets-of-order k (cdr l))))
			(:instance sublistp-subset (s (common-member (conses (car l)
			                                                     (subsets-of-order (1- k)
									                       (cdr l)))
								     (subsets-of-order k (cdr l))))
					           (l (cdr l)))))))

;; (len (subsets-of-order k l)) is the sum of the lengths of these sublists:

(defthmd subsets-of-order-plus
  (implies (and (dlistp l) (consp l) (posp k))
           (equal (len (subsets-of-order k l))
	          (+ (len (subsets-of-order (1- k) (cdr l)))
		     (len (subsets-of-order k (cdr l))))))
  :hints (("Goal" :in-theory (enable permp)
                  :use (dlistp-append-subsets-of-order
                        (:instance scex1-lemma (l (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		                                          (subsets-of-order k (cdr l))))
				               (m (subsets-of-order k l)))
                        (:instance scex1-lemma (m (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		                                          (subsets-of-order k (cdr l))))
				               (l (subsets-of-order k l)))
		        (:instance member-subsets-of-order-append
			           (x (scex1 (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		                                     (subsets-of-order k (cdr l)))
				             (subsets-of-order k l))))
		        (:instance member-subsets-of-order-append
			           (x (scex1 (subsets-of-order k l)
				             (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		                                     (subsets-of-order k (cdr l))))))
			(:instance eq-len-permp (l (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		                                           (subsets-of-order k (cdr l))))
						(m (subsets-of-order k l)))))))

;; Since NIL is the only subset of order 0, the case k = 0 is trivial:

(local (defthm subsets-of-order-0-1
  (implies (dlistp l)
           (iff (and (member-equal s (subsets l))
	             (equal (len s) 0))
	        (equal s ())))
  :hints (("Goal" :induct (subsets-induct s l)))))
           
(local (defthmd subsets-of-order-0-2
  (implies (dlistp l)
           (iff (member-equal s (subsets-of-order 0 l))
	        (equal s ())))
  :hints (("Goal" :use (subsets-of-order-0-1)))))

(local (defthmd subsets-of-order-0-3
  (implies (dlistp l)
           (equal (subsets-of-order 0 l)
	          (list ())))
  :hints (("Goal" :in-theory (disable MEMBER-SUBSETS-OF-ORDER dlistp-subsets-of-order)
                  :use ((:instance subsets-of-order-0-2 (s (car (subsets-of-order 0 l))))
                        (:instance subsets-of-order-0-2 (s (cadr (subsets-of-order 0 l))))
                        (:instance subsets-of-order-0-2 (s ()))
			(:instance dlistp-subsets-of-order (k 0)))))))

(defthm subsets-of-order-0
  (implies (dlistp l)
           (equal (len (subsets-of-order 0 l)) 1))
  :hints (("Goal" :use (subsets-of-order-0-3))))

;; Similarly, since l is the only subset of l of length n, the case k = n is trivial:

(local (defun cdrs-induct (x l)
  (if (consp l)
      (list (cdrs-induct (cdr x) (cdr l)))
    (list x l))))

(local (defthmd max-len-subset
  (implies (and (dlistp l) (member-equal s (subsets l)))
           (<= (len s) (len l)))
  :hints (("Goal" :induct (subsets-induct s l)))))

(local (defthmd subsets-of-order-len-1
  (implies (dlistp l)
           (iff (and (member-equal s (subsets l))
	             (equal (len s) (len l)))
	        (equal s l)))
  :hints (("Goal" :induct (subsets-induct s l))
          ("Subgoal *1/1" :use ((:instance max-len-subset (l (cdr l))))))))

(local (defthmd subsets-of-order-len-2
  (implies (dlistp l)
           (iff (member-equal s (subsets-of-order (len l) l))
	        (equal s l)))
  :hints (("Goal" :use (subsets-of-order-len-1)))))

(local (defthmd subsets-of-order-len-3
  (implies (dlistp l)
           (equal (subsets-of-order (len l) l)
	          (list l)))
  :hints (("Goal" :in-theory (disable MEMBER-SUBSETS-OF-ORDER dlistp-subsets-of-order)
                  :use ((:instance subsets-of-order-len-2 (s (car (subsets-of-order (len l) l))))
                        (:instance subsets-of-order-len-2 (s (cadr (subsets-of-order (len l) l))))
                        (:instance subsets-of-order-len-2 (s l))
			(:instance dlistp-subsets-of-order (k (len l))))))))

(defthm subsets-of-order-len
  (implies (dlistp l)
           (equal (len (subsets-of-order (len l) l)) 1))
  :hints (("Goal" :use (subsets-of-order-len-3))))

;; In the remaining case, the result follows by induction:

;;     (n-1)!/((k-1)!(n-k)!) + (n-1)!/(k!(n-k+1)!)
;;       = (k(n-1)!)/(k!(n-k)!) + ((n-k)(n- 1)!)/(k!(n-k)!)
;;       = ((k+n-k)(n-1)!)/(k!(n-k)!)
;;       = n!/(k!(n-k)!).

(local (defthmd subsets-of-order-reduce-1
  (implies (and (consp l) (posp k) (< k (len l)))
           (equal (* (FACT (LEN (CDR L)))
                     (/ (* (FACT (+ -1 K))
                           (FACT (+ (LEN (CDR L)) (- (+ -1 K)))))))
		  (* k (FACT (LEN (CDR L)))
                     (/ (* (FACT k)
                           (FACT (- (LEN l) k)))))))))

(local (defthmd subsets-of-order-reduce-2
  (implies (and (rationalp a) (rationalp b) (not (= c 0)) (rationalp c))
           (equal (/ a b) (/ (* a c) (* b c))))))

(local (defthmd subsets-of-order-reduce-3
  (implies (and (consp l) (posp k) (< k (len l)))
           (equal (* (FACT (LEN (CDR L)))
                     (/ (* (FACT K)
                           (FACT (+ (LEN (CDR L)) (- K))))))
		  (* (- (len l) k) (FACT (LEN (CDR L)))
                     (/ (* (FACT K)
                           (* (- (len l) k) (FACT (+ (LEN (CDR L)) (- K)))))))))
  :hints (("Goal" :use ((:instance subsets-of-order-reduce-2 (a (FACT (LEN (CDR L))))
                                                             (b (* (FACT K) (FACT (+ (LEN (CDR L)) (- K)))))
							     (c (- (len l) k))))))))

(local (defthmd subsets-of-order-reduce-4
  (implies (and (consp l) (posp k) (< k (len l)))
           (equal (* (- (len l) k) (FACT (+ (LEN (CDR L)) (- K))))
	          (FACT (- (len l) k))))))

(local (defthmd subsets-of-order-reduce-5
  (implies (and (consp l) (posp k) (< k (len l)))
           (equal (* (FACT (LEN (CDR L)))
                     (/ (* (FACT K)
                           (FACT (+ (LEN (CDR L)) (- K))))))
		  (* (- (len l) k) (FACT (LEN (CDR L)))
                     (/ (* (FACT K)
                           (FACT (- (len l) k)))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (subsets-of-order-reduce-3 subsets-of-order-reduce-4)))))
			   
(local (defthmd subsets-of-order-reduce-6
  (implies (and (consp l) (posp k) (< k (len l)))
           (equal (+ (* k (FACT (LEN (CDR L)))
                       (/ (* (FACT k)
                             (FACT (- (LEN l) k)))))
		     (* (- (len l) k) (FACT (LEN (CDR L)))
                        (/ (* (FACT K)
                              (FACT (- (len l) k))))))
		  (* (FACT (LEN L))
                     (/ (* (FACT K)
                           (FACT (+ (LEN L) (- K))))))))))

(local (defthmd subsets-of-order-reduce
  (implies (and (consp l) (posp k) (< k (len l)))
           (equal (* (FACT (LEN L))
                     (/ (* (FACT K)
                           (FACT (+ (LEN L) (- K))))))
		  (+ (* (FACT (LEN (CDR L)))
                        (/ (* (FACT (+ -1 K))
                              (FACT (+ (LEN (CDR L)) (- (+ -1 K)))))))
		     (* (FACT (LEN (CDR L)))
                        (/ (* (FACT K)
                              (FACT (+ (LEN (CDR L)) (- K)))))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (subsets-of-order-reduce-1 subsets-of-order-reduce-5 subsets-of-order-reduce-6)))))

(local (defthmd hack
  (implies (and (dlistp l) (natp k) (<= k (len l)) (not (= k 0)) (not (= k (len l))))
           (and (posp k) (consp l) (< k (len l)) (dlistp (cdr l)) (<= k (len (cdr l)))
	        (natp (+ -1 k)) (<= (+ -1 k) (len (cdr l)))))))
		     
(local (defun len-subsets-of-order-induct (l k)
  (if (consp l)
      (list (len-subsets-of-order-induct (cdr l) k)
            (len-subsets-of-order-induct (cdr l) (1- k)))
    (list l k))))

(local (defthmd len-subsets-of-order-1
  (implies (and (dlistp l) (natp k) (<= k (len l)))
	   (equal (len (subsets-of-order k l))
		  (/ (fact (len l))
		     (* (fact k) (fact (- (len l) k))))))
  :hints (("Goal" :induct (len-subsets-of-order-induct l k))
          ("Subgoal *1/1" :cases ((= k 0) (= k (len l)))
	                  :use (subsets-of-order-0 subsets-of-order-len subsets-of-order-reduce subsets-of-order-plus))
	  ("Subgoal *1/1.3" :in-theory (theory 'minimal-theory) :use (hack)))))

(defund choose (n k)
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (/ (fact n)
	 (* (fact k) (fact (- n k))))
    0))

(defthm len-subsets-of-order
  (implies (and (dlistp l) (natp k))
	   (equal (len (subsets-of-order k l))
		  (choose (len l) k)))
  :hints (("Goal" :in-theory (enable choose)
                  :use (len-subsets-of-order-1 no-subsets-of-order>len))))
	  
