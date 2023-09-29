(in-package "DM")

(include-book "projects/groups/symmetric" :dir :system)
(include-book "sylvester")
(include-book "rtl/rel11/lib/top" :dir :system)

;; Let n >= 1.  A permutation p in (slist n) fixes k, where 0 <= k < n, if
;; (nth k p) = k.  p is a derangement if p does not fix any member of (ninit n):

(defund fixes (p k)
  (equal (nth k p) k))

(defun derangementp (p n)
  (if (posp n)
      (and (not (fixes p (1- n)))
	   (derangementp p (1- n)))
    t))

(defthm derangementp-not-fixes
  (implies (and (natp n)
                (derangementp p n)
		(natp i)
		(< i n))
	   (not (fixes p i))))

(defun fixed-pt-high (p n)
  (if (posp n)
      (if (fixes p (1- n))
          (1- n)
	(fixed-pt-high p (1- n)))
    ()))

(defthmd not-derangementp-fixes
  (implies (and (natp n)
                (not (derangementp p n)))
	   (and (natp (fixed-pt-high p n))
	        (< (fixed-pt-high p n) n)
		(fixes p (fixed-pt-high p n)))))

;; The list of all derangements:

(defun derangements-aux (u n)
  (if (consp u)
      (if (derangementp (car u) n)
	  (cons (car u) (derangements-aux (cdr u) n))
	(derangements-aux (cdr u) n))
    ()))

(defund derangements (n)
  (derangements-aux (slist n) n))

(defthm dlistp-sublistp-derangements-aux
  (implies (dlistp u)
           (and (dlistp (derangements-aux u n))
	        (sublistp (derangements-aux u n) u))))

(defthm dlistp-sublistp-derangements
  (implies (posp n)
           (and (dlistp (derangements n))
                (sublistp (derangements n) (slist n))))
  :hints (("Goal" :in-theory (enable derangements))))           

(defthm member-derangements-aux
  (implies (member-equal p u)
           (iff (member-equal p (derangements-aux u n))
	        (derangementp p n))))

(defthm member-derangements
  (implies (member-equal p (slist n))
           (iff (member-equal p (derangements n))
	        (derangementp p n)))
  :hints (("Goal" :in-theory (enable derangements))))

;; We shall prove that the length of this list is n!(1/0! - 1/1! + 1/2! - ... + (-1)^n/n!).
;; Thus, we define (num-derangements n) as follows:

(defun num-derangements-aux (k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (natp k) (natp n) (<= k n))
      (- (/ (fact k))
         (num-derangements-aux (1+ k) n))
    0))

(defund num-derangements (n)
  (* (fact n) (num-derangements-aux 0 n)))

;; Our objective is the following:

;; (defthm derangements-formula
;;   (implies (posp n)
;;            (equal (len (derangements n))
;;                   (num-derangements n))))

;; The formula holds trivially for n < 3.  For n >= 3, the proof is based on the lemma 
;; inclusion-exclusion-principle.  The universe u of the lemma is (slist n).  We begin by 
;; defining the subset of u consisting of all permutations that fix k, where 0 <= k < n:

(defun fixer-aux (u k)
  (if (consp u)
      (if (fixes (car u) k)
	  (cons (car u) (fixer-aux (cdr u) k))
	(fixer-aux (cdr u) k))
    ()))

(defund fixer (k n)
  (fixer-aux (slist n) k))

(defthm dlistp-sublistp-fixer-aux
  (implies (dlistp u)
           (and (dlistp (fixer-aux u k))
	        (sublistp (fixer-aux u k) u))))

(defthm dlistp-sublistp-fixer
  (implies (posp n)
           (and (dlistp (fixer k n))
	        (sublistp (fixer k n) (slist n))))
  :hints (("Goal" :in-theory (enable fixer))))

(defthm member-fixer-aux
  (iff (member-equal p (fixer-aux u k))
       (and (member-equal p u)
	    (fixes p k))))

(defthm member-fixer
  (iff (member-equal p (fixer k n))
       (and (member-equal p (slist n))
	    (fixes p k)))
  :hints (("Goal" :in-theory (enable fixer))))

(local (defthm member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
           (member-equal x m)))))

(local (defthm car-member-conses
  (iff (member-equal y (conses x l))
       (and (consp y) (equal (car y) x) (member-equal (cdr y) l)))))

(defthm subset-fixer-aux
  (member-equal (fixer-aux u k) (subsets u)))

(defthm subset-fixer
  (member-equal (fixer k n) (subsets (slist n)))
  :hints (("Goal" :in-theory (enable fixer))))

(defthm dlistp-fixer-aux
  (implies (dlistp u)
           (dlistp (fixer-aux u k))))

(defthm dlistp-fixer
  (implies (posp n)
           (dlistp (fixer k n)))
  :hints (("Goal" :in-theory (enable fixer))))

;; The list l of inclusion-exclusion-principle is the list of all such fixers:

(defun fixers-aux (k n)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (natp k) (natp n) (< k n))
      (cons (fixer k n)
	    (fixers-aux (1+ k) n))
    ()))

(defund fixers (n)
  (fixers-aux 0 n))

(defthmd fixes-member-union-list-fixers-aux
  (implies (and (posp n)
                (member-equal p (slist n))
                (natp k)
		(< k n)
                (natp j)
		(>= j k)
		(< j n)
		(fixes p j))
	   (member-equal p (union-list (fixers-aux k n)))))

(defthm fixes-member-union-list-fixers
  (implies (and (posp n)
                (member-equal p (slist n))
                (natp k)
		(< k n)
		(fixes p k))
	   (member-equal p (union-list (fixers n))))
  :hints (("Goal" :in-theory (enable fixers)
                  :use ((:instance fixes-member-union-list-fixers-aux (k 0) (j k))))))

(defun fixed-pt-low-aux (p k n)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (natp k) (natp n) (< k n))
      (if (fixes p k)
          k
	(fixed-pt-low-aux p (1+ k) n))
    ()))

(defund fixed-pt-low (p n)
  (fixed-pt-low-aux p 0 n))

(defthmd member-union-list-fixers-aux-fixes
  (implies (and (posp n)
                (natp k)
		(< k n)
                (member-equal p (union-list (fixers-aux k n))))
	   (and (natp (fixed-pt-low-aux p k n))
                (< (fixed-pt-low-aux p k n) n)
		(fixes p (fixed-pt-low-aux p k n)))))

(defthmd member-union-list-fixers-fixes
  (implies (and (posp n)
                (member-equal p (union-list (fixers n))))
	   (and (natp (fixed-pt-low p n))
                (< (fixed-pt-low p n) n)
		(fixes p (fixed-pt-low p n))))
  :hints (("Goal" :in-theory (enable fixers fixed-pt-low)
                  :use ((:instance member-union-list-fixers-aux-fixes (k 0))))))
	   
(defthm dlistp-sublistp-union-list-fixers-aux
  (implies (and (posp n)
                (natp k)
		(< k n))
	   (and (dlistp (union-list (fixers-aux k n)))
	        (sublistp (union-list (fixers-aux k n)) (slist n)))))

(defthm dlistp-sublistp-union-list-fixers
  (implies (posp n)
	   (and (dlistp (union-list (fixers n)))
	        (sublistp (union-list (fixers n)) (slist n))))
  :hints (("Goal" :in-theory (enable fixers))))

(defthm dlistp-sublistp-append-derangements-union-list-fixers
  (implies (posp n)
           (and (dlistp (append (derangements n) (union-list (fixers n))))
	        (sublistp (append (derangements n) (union-list (fixers n)))
		          (slist n))))
  :hints (("Goal" :use ((:instance common-member-shared (l (derangements n)) (m (union-list (fixers n))))
                        (:instance member-union-list-fixers-fixes (p (common-member (derangements n) (union-list (fixers n)))))))))

(defthm sublistp-slist-append-derangements-union-list-fixers
  (implies (posp n)
           (sublistp (slist n)
	             (append (derangements n) (union-list (fixers n)))))		          
  :hints (("Goal" :use ((:instance scex1-lemma (l (slist n)) (m (append (derangements n) (union-list (fixers n)))))
                        (:instance not-derangementp-fixes (p (scex1 (slist n) (append (derangements n) (union-list (fixers n))))))))))

(defthmd len-derangements
  (implies (posp n)
           (equal (len (derangements n))
	          (- (fact n) (len (union-list (fixers n))))))
  :hints (("Goal" :in-theory (enable permp len-slist)
                  :use ((:instance eq-len-permp (l (slist n)) (m (append (derangements n) (union-list (fixers n)))))))))








(defthm dlistp-member-fixers-aux
  (implies (and (posp n) (member-equal x (fixers-aux k n)))
           (dlistp x)))

(defthm dlistp-member-fixers
  (implies (and (posp n) (member-equal x (fixers n)))
           (dlistp x))
  :hints (("Goal" :in-theory (enable fixers))))

(defthm len-fixers-aux
  (implies (and (natp k) (natp n) (<= k n))
	   (equal (len (fixers-aux k n))
		  (- n k))))

(defthm len-fixers
  (implies (natp n)
	   (equal (len (fixers n))
		  n))
  :hints (("Goal" :in-theory (enable fixers))))

(defun nth-fixers-aux-induct (j k)
  (if (posp j)
      (list (nth-fixers-aux-induct (1- j) (1+ k)))
    (list j k)))

(defthm nth-fixers-aux
  (implies (and (natp k) (natp n) (< k n) (natp j) (< j (- n k)))
	   (equal (nth j (fixers-aux k n))
		  (fixer (+ k j) n)))
  :hints (("Goal" :induct (nth-fixers-aux-induct j k))
	  ("Subgoal *1/2" :expand (fixers-aux k n))))

(defthm nth-fixers
  (implies (and (natp n) (natp j) (< j n))
	   (equal (nth j (fixers n))
		  (fixer j n)))
  :hints (("Goal" :in-theory (enable fixers))))

;; The lemma requires that (fixers n) is a sublist of (subsets (slist n)) and a dlist:

(defthm sublistp-fixers-aux
  (implies (and (posp n) (natp k))
	   (sublistp (fixers-aux k n) (subsets (slist n)))))

(defthm sublistp-fixers
  (implies (posp n)
	   (sublistp (fixers n) (subsets (slist n))))
  :hints (("Goal" :in-theory (enable fixers))))

;; To show that (fixers n) is a dlist, we must show that for 0 <= j < k < n, there is a
;; member of u that fixes k but not j.  First we identifiy an index that is distinct from
;; both j and k:

(defun other-index (j k)
  (if (or (= j 0) (= k 0))
      (if (or (= j 1) (= k 1))
	  2
	1)
    0))

(defund fixer-mover (j k n)
  (transpose j (other-index j k) n))

(defthmd fixer-mover-member
  (implies (and (natp j) (natp k) (posp n) (>= n 3) (< j n) (< k n) (not (= j k)))
	   (and (member-equal (fixer-mover j k n) (fixer k n))
		(not (member-equal (fixer-mover j k n) (fixer j n)))))
  :hints (("Goal" :in-theory (enable member-fixer fixer-mover fixes transpose-vals)
	   :use ((:instance permp-transpose (i j) (j (other-index j k)))))))

(defthmd fixers-distinct
  (implies (and (natp j) (natp k) (posp n) (>= n 3) (< j n) (< k n) (not (= j k)))
	   (not (equal (fixer j n) (fixer k n))))
  :hints (("Goal" :use (fixer-mover-member))))

(defthm not-member-fixers-aux
  (implies (and (posp n) (>= n 3) (natp k) (natp j) (< j k))
	   (not (member-equal (fixer j n) (fixers-aux k n))))
  :hints (("Subgoal *1/4" :use (fixers-distinct))))

(defthm dlistp-fixers-aux
  (implies (and (posp n) (>= n 3) (natp k))
	   (dlistp (fixers-aux k n))))

(defthm dlistp-fixers
  (implies (and (posp n) (>= n 3))
	   (dlistp (fixers n)))
  :hints (("Goal" :in-theory (enable fixers))))

;; Let s be a subset of (fixers n) of order k.  We shall show that (len (int-list s))
;; = (n - k)!.  First we define the list of indices of the members of s:

(defun fixed-indices (s n)
  (if (consp s)
      (cons (index (car s) (fixers n))
	    (fixed-indices (cdr s) n))
    ()))

(defthm len-fixed-indices
  (equal (len (fixed-indices s n))
         (len s)))

(defthm sublistp-fixed-indices
  (implies (and (posp n) (>= n 3) (member-equal s (subsets (fixers n))))
	   (sublistp (fixed-indices s n) (ninit n)))
  :hints (("Subgoal *1/2" :in-theory (e/d () (member-sublist member-ninit))
	                  :use ((:instance ind<len (x (car s)) (l (fixers n)))
			        (:instance member-ninit (x (INDEX (CAR S) (FIXERS N))))
			        (:instance member-sublist (x (car s)) (l s) (m (fixers n)))))				
	  ("Subgoal *1/1" :in-theory (disable true-listp-subset)
	                  :use ((:instance subset-subset (x (cdr s)) (l (fixers n)))	                  
			        (:instance true-listp-subset (l (fixers n)))))))

(defthmd dlistp-fixed-indices-1
  (implies (and (posp n) (>= n 3) (sublistp cdr (fixers n)) (natp i) (member-equal i (fixed-indices cdr n)))
	   (member-equal (nth i (fixers n)) cdr)))

(defthm dlistp-fixed-indices
  (implies (and (posp n) (>= n 3) (member-equal s (subsets (fixers n))))
	   (dlistp (fixed-indices s n)))
  :hints (("Subgoal *1/2" :in-theory (e/d () (dlistp-subset sublistp-sublistp member-sublist))
                          :use ((:instance dlistp-fixed-indices-1 (cdr (cdr s)) (i (index (car s) (fixers n))))
                                (:instance sublistp-sublistp (l (cdr s)) (m s) (n (fixers n)))
				(:instance dlistp-subset (l (fixers n)))
				(:instance member-sublist (x (car s)) (l s) (m (fixers n)))))
	  ("Subgoal *1/1" :in-theory (disable true-listp-subset)
	                  :use ((:instance subset-subset (x (cdr s)) (l (fixers n)))	                  
			        (:instance true-listp-subset (l (fixers n)))))))

;; A permutation p in (slist n) belongs to (int-list s) iff p fixes every member of
;; (fixed-indices s n):

(defun fixes-list (p l)
  (if (consp l)
      (and (fixes p (car l))
           (fixes-list p (cdr l)))
    t))

(defthmd fixes-list-fixes
  (implies (and (fixes-list p l) (member-equal j l))
           (fixes p j)))

(defthm member-int-list-subset-fixers-1
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
	   (iff (member-equal p (car s))
	        (and (member-equal p (slist n))
	             (fixes p (index (car s) (fixers n))))))
  :hints (("Goal" :in-theory (disable ind<len len-fixers member-sublist nth-fixers)
                  :use (len-fixers
		        (:instance member-fixer (k (index (car s) (fixers n))))
                        (:instance nth-fixers (j (index (car s) (fixers n))))
			(:instance ind<len (x (car s)) (l (fixers n)))
			(:instance member-sublist (x (car s)) (l s) (m (fixers n)))))))

(defthm member-int-list-subset-fixers-2
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
           (member-equal (cdr s) (subsets (fixers n))))
  :hints (("Goal" :in-theory (disable true-listp-subset)
                  :use ((:instance subset-subset (x (cdr s)) (l (fixers n)))	                  
			(:instance true-listp-subset (l (fixers n)))))))

(defthmd member-int-list-subset-fixers
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
	   (iff (member-equal p (int-list s))
		(and (member-equal p (slist n))
	             (fixes-list p (fixed-indices s n))))))

;; (int-list s) is a dlist:

(defthm dlistp-car-subset-fixers
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
	   (dlistp (car s)))
  :hints (("Goal" :use ((:instance member-sublist (x (car s)) (l s) (m (fixers n)))))))

(defthm dlistp-int-list-subset-fixers
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
	   (dlistp (int-list s))))

;; The complement of (fixed-indices s n):

(defund moved-indices (s n)
  (set-difference-equal (ninit n) (fixed-indices s n)))

(in-theory (enable set-difference-equal))

(defthm sublistp-set-difference
  (sublistp (set-difference-equal l m) l))

(defthm dlistp-set-difference
  (implies (dlistp l)
           (dlistp (set-difference-equal l m))))

(defthm member-set-difference
  (iff (member-equal j (set-difference-equal l m))
       (and (member-equal j l)
            (not (member-equal j m)))))

(defthm sublistp-moved-indices
  (sublistp (moved-indices s n) (ninit n))
  :hints (("Goal" :in-theory (enable moved-indices)
                  :use ((:instance sublistp-set-difference (l (ninit n)) (m (fixed-indices s n)))))))

(defthm dlistp-moved-indices
  (implies (posp n)
           (dlistp (moved-indices s n)))
  :hints (("Goal" :in-theory (enable moved-indices)
                  :use ((:instance dlistp-set-difference (l (ninit n)) (m (fixed-indices s n)))))))

(defthm member-moved-indices
  (iff (member-equal j (moved-indices s n))
       (and (member-equal j (ninit n))
            (not (member-equal j (fixed-indices s n)))))
  :hints (("Goal" :in-theory (enable moved-indices)
                  :use ((:instance member-set-difference (l (ninit n)) (m (fixed-indices s n)))))))

(defthm dlistp-append-indices
  (implies (and (posp n) (>= n 3) (member-equal s (subsets (fixers n))))
           (dlistp (append (fixed-indices s n)
	                   (moved-indices s n))))
  :hints (("Goal" :use ((:instance common-member-shared (l (fixed-indices s n)) (m (moved-indices s n)))))))

(defthm sublistp-append-indices
  (implies (and (posp n) (>= n 3) (member-equal s (subsets (fixers n))))
           (and (sublistp (append (fixed-indices s n) (moved-indices s n))
	                  (ninit n))
		(sublistp (ninit n)
		          (append (fixed-indices s n) (moved-indices s n)))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (append (fixed-indices s n) (moved-indices s n)))
                                               (m (ninit n)))
			(:instance scex1-lemma (m (append (fixed-indices s n) (moved-indices s n)))
                                               (l (ninit n)))))))

(defthmd len-moved-indices
  (implies (and (posp n) (>= n 3) (member-equal s (subsets (fixers n))))
           (equal (len (moved-indices s n))
	          (- n (len (fixed-indices s n)))))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance eq-len-permp (m (append (fixed-indices s n) (moved-indices s n)))
                                                (l (ninit n)))))))

;; Let m = (moved-indices s n).  We define a bijection from (int-list s) to (perms m).  If p
;; is a member of (int-list s), then the image of p under this bijection is (restrict-perm p m):

(defun restrict-perm (p m)
  (if (consp m)
      (cons (nth (car m) p)
	    (restrict-perm p (cdr m)))
    ()))

;; The inverse bijection maps a member p of (perms m) to (extend-perm p m n):

(defun extend-perm (p m n)
  (if (posp n)
      (append (extend-perm p m (1- n))
              (list (if (member-equal (1- n) m)
	                (nth (index (1- n) m) p)
	              (1- n))))
    ()))

(defthmd int-list-moved-moved
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (int-list s))
		(member-equal j (moved-indices s n)))
	   (member-equal (nth j p) (moved-indices s n)))
  :hints (("Goal" :in-theory (enable fixes member-ninit member-int-list-subset-fixers)
                  :use ((:instance fixes-list-fixes (l (fixed-indices s n)) (j (nth j p)))
                        (:instance nth-perm-ninit (k j) (x p))
			(:instance nth-perm-distinct (i (nth j p)) (x p))))))

(defthmd nth-restrict-perm
  (implies (and (natp i) (< i (len m)))
	   (equal (nth i (restrict-perm p m))
	          (nth (nth i m) p))))
		  
(defthmd nth-restrict-perm-distinct
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (int-list s))
                (natp i) (natp j) (< i j) (< j (len (moved-indices s n))))
	   (not (equal (nth i (restrict-perm p (moved-indices s n)))
	               (nth j (restrict-perm p (moved-indices s n))))))
  :hints (("Goal" :in-theory (e/d (member-ninit nth-restrict-perm member-ninit member-int-list-subset-fixers) (member-moved-indices))
                  :use ((:instance nth-perm-distinct (i (nth i (moved-indices s n)))
		                                     (j (nth j (moved-indices s n)))
						     (x p))
			(:instance nth-dlist-distinct (l (moved-indices s n)))
			(:instance member-moved-indices (j (nth i (moved-indices s n))))
			(:instance member-moved-indices (j (nth j (moved-indices s n))))))))

(defthm len-restrict-perm
  (equal (len (restrict-perm p m))
         (len m)))

(defthm dlistp-restrict-perm
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (int-list s)))
	   (dlistp (restrict-perm p (moved-indices s n))))
  :hints (("Goal" :in-theory (disable dcex-lemma)
                  :use ((:instance nth-restrict-perm-distinct (i (dcex1 (restrict-perm p (moved-indices s n))))
                                                              (j (dcex2 (restrict-perm p (moved-indices s n)))))
                        (:instance dcex-lemma (l (restrict-perm p (moved-indices s n))))))))

(defthm sublistp-restrict-perm
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (int-list s)))
	   (sublistp (restrict-perm p (moved-indices s n))
	             (moved-indices s n)))
  :hints (("Goal" :in-theory (e/d (member-ninit nth-restrict-perm) (member-moved-indices))
                  :use (len-moved-indices
		        (:instance scex2-lemma (l (restrict-perm p (moved-indices s n))) (m (moved-indices s n)))
			(:instance member-moved-indices (j (nth (scex2 (restrict-perm p (moved-indices s n)) (moved-indices s n)) (moved-indices s n))))
			(:instance int-list-moved-moved (j (nth (scex2 (restrict-perm p (moved-indices s n)) (moved-indices s n)) (moved-indices s n))))))))

(defthm permp-restrict-perm
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (int-list s)))
           (permp (restrict-perm p (moved-indices s n)) (moved-indices s n)))
  :hints (("Goal" :in-theory (enable member-ninit)
                  :use ((:instance permp-eq-len (l (restrict-perm p (moved-indices s n))) (m (moved-indices s n)))))))

(defthm member-restrict-perm
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (int-list s)))
           (member-equal (restrict-perm p (moved-indices s n))
	                 (perms (moved-indices s n))))
  :hints (("Goal" :use ((:instance perms-permp (p (restrict-perm p (moved-indices s n))) (l (moved-indices s n)))))))
  

;;------------------------------------------------------------------------------------------------------

(defthm len-extend-perm
  (implies (natp n)
           (equal (len (extend-perm p m n))
                  n)))

(defthm nth-append
  (implies (natp i)
           (equal (nth i (append l m))
	          (if (< i (len l))
		      (nth i l)
		    (nth (- i (len l)) m)))))

(defthm nth-extend-perm
  (implies (and (posp n) (natp i) (< i n))
           (equal (nth i (extend-perm p m n))
	          (if (member-equal i m)
		      (nth (index i m) p)
		    i))))

(defthmd nth-extend-perm-moved-1
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(member-equal i (moved-indices s n)))
	   (equal (nth i (extend-perm p (moved-indices s n) n))
	          (nth (index i (moved-indices s n)) p)))		  
  :hints (("Goal" :in-theory (enable member-ninit))))

(defthmd nth-extend-perm-moved-2
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(member-equal i (moved-indices s n)))
	   (and (natp (index i (moved-indices s n)))
	        (< (index i (moved-indices s n)) (len p))))		
  :hints (("Goal" :use ((:instance permp-perms (l (moved-indices s n)))
		        (:instance eq-len-permp (l p) (m (moved-indices s n)))))))

(defthmd nth-extend-perm-moved-3
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(member-equal i (moved-indices s n)))
	   (member-equal (nth (index i (moved-indices s n)) p)
	                 p))
  :hints (("Goal" :use (nth-extend-perm-moved-2))))

(defthmd nth-extend-perm-moved-4
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(member-equal i (moved-indices s n)))
	   (member-equal (nth (index i (moved-indices s n)) p)
	                 (moved-indices s n)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (nth-extend-perm-moved-3
                        (:instance permp-perms (l (moved-indices s n)))
			(:instance member-sublist (x (nth (index i (moved-indices s n)) p)) (l p) (m (moved-indices s n)))))))

(defthmd nth-extend-perm-moved
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(member-equal i (moved-indices s n)))
	   (member-equal (nth i (extend-perm p (moved-indices s n) n))
	                 (moved-indices s n)))
  :hints (("Goal" :use (nth-extend-perm-moved-1 nth-extend-perm-moved-4))))

(defthmd nth-extend-perm-ninit
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(natp i) (< i n))
	   (and (natp (nth i (extend-perm p (moved-indices s n) n)))
	        (< (nth i (extend-perm p (moved-indices s n) n)) n)))
  :hints (("Goal" :in-theory (enable member-ninit)
                  :use (nth-extend-perm-moved))))

(defthmd sublistp-extend-perm-ninit
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n))))
	   (sublistp (extend-perm p (moved-indices s n) n)
	             (ninit n)))
  :hints (("Goal" :in-theory (enable member-ninit)
                  :use ((:instance scex2-lemma (l (extend-perm p (moved-indices s n) n)) (m (ninit n)))
		        (:instance nth-extend-perm-ninit (i (scex2 (extend-perm p (moved-indices s n) n) (ninit n))))))))

(defthmd nth-extend-perm-distinct-1
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(natp i) (natp j) (< i j) (< j n)
		(or (not (member-equal i (moved-indices s n)))
		    (not (member-equal j (moved-indices s n)))))
	   (not (equal (nth i (extend-perm p (moved-indices s n) n))
	               (nth j (extend-perm p (moved-indices s n) n)))))		       
  :hints (("Goal" :in-theory (e/d (member-ninit) (nth-extend-perm))
                  :use (nth-extend-perm-moved
		        (:instance nth-extend-perm (m (moved-indices s n)))
		        (:instance nth-extend-perm (i j) (m (moved-indices s n)))
		        (:instance nth-extend-perm-moved (i j))))))

(defthmd nth-extend-perm-distinct-2
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(natp i) (natp j) (< i j) (< j n)
		(member-equal i (moved-indices s n))
		(member-equal j (moved-indices s n)))
	   (and (natp (index i (moved-indices s n)))
	        (< (index i (moved-indices s n)) (len p))
		(natp (index j (moved-indices s n)))
	        (< (index j (moved-indices s n)) (len p))
		(not (equal (index i (moved-indices s n)) (index j (moved-indices s n))))))
  :hints (("Goal" :use (nth-extend-perm-moved-2
		        (:instance nth-extend-perm-moved-2 (i j))
		        (:instance index-1-to-1 (x i) (y j) (l (moved-indices s n)))))))

(defthmd nth-extend-perm-distinct-3
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(natp i) (natp j) (< i j) (< j n)
		(member-equal i (moved-indices s n))
		(member-equal j (moved-indices s n)))
	   (not (equal (nth (index i (moved-indices s n)) p)
	               (nth (index j (moved-indices s n)) p))))
  :hints (("Goal" :in-theory (enable permp)
                  :use (nth-extend-perm-distinct-2
		        (:instance nth-dlist-distinct (i (index i (moved-indices s n))) (j (index j (moved-indices s n))) (l p))
                        (:instance permp-perms (l (moved-indices s n)))))))

(defthmd nth-extend-perm-distinct
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(natp i) (natp j) (< i j) (< j n))
	   (not (equal (nth i (extend-perm p (moved-indices s n) n))
	               (nth j (extend-perm p (moved-indices s n) n)))))		       
  :hints (("Goal" :use (nth-extend-perm-moved-1 nth-extend-perm-distinct-1 nth-extend-perm-distinct-3
		        (:instance nth-extend-perm-moved-1 (i j))))))

(defthmd dlist-extend-perm
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n))))
	   (dlistp (extend-perm p (moved-indices s n) n)))
  :hints (("Goal" :use ((:instance dcex-lemma (l (extend-perm p (moved-indices s n) n)))
                        (:instance nth-extend-perm-distinct (i (dcex1 (extend-perm p (moved-indices s n) n)))
			                                    (j (dcex2 (extend-perm p (moved-indices s n) n))))))))

(defthmd permp-extend-perm
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n))))
	   (member-equal (extend-perm p (moved-indices s n) n)
	                 (slist n)))
  :hints (("Goal" :in-theory (enable slist)
                  :use (dlist-extend-perm sublistp-extend-perm-ninit
                        (:instance permp-eq-len (l (extend-perm p (moved-indices s n) n)) (m (ninit n)))
			(:instance perms-permp (p (extend-perm p (moved-indices s n) n)) (l (ninit n)))))))

(defthmd fixes-list-extend-perm
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n)))
		(sublistp l (fixed-indices s n)))
	   (fixes-list (extend-perm p (moved-indices s n) n)
	               l))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable member-ninit fixes)
	                  :use ((:instance member-sublist (x (car l)) (l (fixed-indices s n)) (m (ninit n)))))))
		       
(defthmd member-extend-perm-in-list
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n)))
                (member-equal p (perms (moved-indices s n))))
	   (member-equal (extend-perm p (moved-indices s n) n)
	                 (int-list s)))
  :hints (("Goal" :in-theory (enable member-int-list-subset-fixers fixes-list-extend-perm permp-extend-perm))))


(defthmd nth-extend-restrict-perms-1
  (let ((m (moved-indices s n)))
    (implies (and (posp n) (>= n 3)
                  (consp s)
                  (member-equal s (subsets (fixers n)))
		  (member-equal p (int-list s))
		  (member-equal i m))
             (equal (nth i (extend-perm (restrict-perm p m) m n))
	            (nth i p))))
  :hints (("Goal" :use ((:instance nth-extend-perm-moved-1 (p (restrict-perm p (moved-indices s n))))
			(:instance nth-restrict-perm (m (moved-indices s n)) (i (index i (moved-indices s n))))))))

(defthmd nth-extend-restrict-perms-2
  (let ((m (moved-indices s n)))
    (implies (and (posp n) (>= n 3)
                  (consp s)
                  (member-equal s (subsets (fixers n)))
		  (member-equal p (int-list s))
		  (member-equal i (fixed-indices s n)))
             (equal (nth i (extend-perm (restrict-perm p m) m n))
	            (nth i p))))		    
  :hints (("Goal" :in-theory (enable fixes member-int-list-subset-fixers member-ninit)
                  :use ((:instance member-sublist (x i) (l (fixed-indices s n)) (m (ninit n)))
		        (:instance fixes-list-fixes (j i) (l (fixed-indices s n)))))))

(defthmd nth-extend-restrict-perms
  (let ((m (moved-indices s n)))
    (implies (and (posp n) (>= n 3)
                  (consp s)
                  (member-equal s (subsets (fixers n)))
		  (member-equal p (int-list s))
		  (natp i) (< i n))
             (equal (nth i (extend-perm (restrict-perm p m) m n))
	            (nth i p))))		    
  :hints (("Goal" :in-theory (enable member-ninit)
                  :use (nth-extend-restrict-perms-1 nth-extend-restrict-perms-2))))

(defthm extend-restrict-perms
  (let ((m (moved-indices s n)))
    (implies (and (posp n) (>= n 3)
                  (consp s)
                  (member-equal s (subsets (fixers n)))
		  (member-equal p (int-list s)))
	     (and (member-equal (restrict-perm p m) (perms m))
		  (equal (extend-perm (restrict-perm p m) m n)
		         p))))
  :hints (("Goal" :in-theory (enable member-int-list-subset-fixers)
                  :use ((:instance nth-diff-perm (x p) (y (extend-perm (restrict-perm p (moved-indices s n)) (moved-indices s n) n)))
		        (:instance member-extend-perm-in-list (p (restrict-perm p (moved-indices s n))))
		        (:instance nth-extend-restrict-perms
			            (i (nth-diff p (extend-perm (restrict-perm p (moved-indices s n)) (moved-indices s n) n))))))))
			
(defthmd nth-restrict-extend-perms
  (let ((m (moved-indices s n)))
    (implies (and (posp n) (>= n 3)
                  (consp s)
                  (member-equal s (subsets (fixers n)))
		  (member-equal p (perms m))
		  (natp i) (< i (len (moved-indices s n))))
	    (equal (nth i (restrict-perm (extend-perm p m n) m))
		   (nth i p))))
  :hints (("Goal" :in-theory (e/d (member-ninit nth-restrict-perm) (member-moved-indices nth-extend-perm))
                  :use ((:instance nth-extend-perm (i (nth i (moved-indices s n))) (m (moved-indices s n)))
		        (:instance member-moved-indices (j (nth i (moved-indices s n))))))))

(defthmd true-listp-p
  (implies (and (posp n) (member-equal p (perms (moved-indices s n))))
           (and (true-listp p)
	        (equal (len p) (len (moved-indices s n)))))
  :hints (("Goal" :in-theory (enable permp)
                  :use  ((:instance permp-perms (l (moved-indices s n)))
		         (:instance eq-len-permp (l p) (m (moved-indices s n)))))))

(defthm restrict-extend-perms
  (let ((m (moved-indices s n)))
    (implies (and (posp n) (>= n 3)
                  (consp s)
                  (member-equal s (subsets (fixers n)))
		  (member-equal p (perms m)))
	    (and (member-equal (extend-perm p m n) (int-list s))
		 (equal (restrict-perm (extend-perm p m n) m)
		        p))))
  :hints (("Goal" ;:in-theory (enable member-int-list-subset-fixers)
                  :use (true-listp-p member-extend-perm-in-list 
		        (:instance nth-diff-diff (x p) (y (restrict-perm (extend-perm p (moved-indices s n) n) (moved-indices s n))))
		        (:instance member-restrict-perm (p (extend-perm p (moved-indices s n) n)))
		        (:instance nth-restrict-extend-perms
			            (i (nth-diff p (restrict-perm (extend-perm p (moved-indices s n) n) (moved-indices s n)))))))))

;; By functional instantiation of len-1-1-equal, (int-list s) and (perms (moved-indices s n) have the same length:

(defthmd len-int-list-perms
  (implies (and (posp n) (>= n 3)
                (consp s) (member-equal s (subsets (fixers n))))
	   (equal (len (int-list s))
	          (len (perms (moved-indices s n)))))
  :hints (("Goal" :use ((:functional-instance len-1-1-equal
                         (x (lambda () (if (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
			                   (int-list s)
					 (x))))
                         (y (lambda () (if (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
			                   (perms (moved-indices s n))
					 (y))))
			 (xy (lambda (p) (if (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
			                     (restrict-perm p (moved-indices s n))
					   (xy p))))
			 (yx (lambda (p) (if (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
			                     (extend-perm p (moved-indices s n) n)
					   (yx p)))))))))

;; Combine len-int-list-perms with len-perms, len-moved-indices, and len-fixed-indices:

(defthmd len-int-list-subset-fixers
  (implies (and (posp n) (>= n 3)
                (consp s) (member-equal s (subsets (fixers n))))
	   (equal (len (int-list s))
	          (fact (- n (len s)))))
  :hints (("Goal" :in-theory (enable len-perms len-int-list-perms len-moved-indices))))

(defthm sum-len-int-sublist
  (implies (and (posp n) (>= n 3)
		(posp k) (<= k n)
		(sublistp l (subsets-of-order k (fixers n))))
	   (equal (sum-len-int l)
	          (* (fact (- n k)) (len l))))
  :hints (("Subgoal *1/2" :use ((:instance len-int-list-subset-fixers (s (car l)))))))

(in-theory (disable sum-len-int))

(defthm sum-len-int-subsets-of-order
  (implies (and (posp n) (>= n 3)
		(posp k) (<= k n))
	   (equal (sum-len-int (subsets-of-order k (fixers n)))
	          (/ (fact n) (fact k))))
  :hints (("Goal" :in-theory (enable choose))))

(defthmd num-derangements-inc-exc-aux
  (implies (and (posp n) (>= n 3)
		(posp k) (<= k n))
	   (equal (* (fact n) (num-derangements-aux k n))
	          (inc-exc-aux (fixers n) k))))

(defthmd num-derangements-inc-exc
  (implies (and (posp n) (>= n 3))
	   (equal (num-derangements n)
	          (- (fact n) (len (union-list (fixers n))))))
  :hints (("Goal" :in-theory (enable num-derangements inc-exc)
                  :use ((:instance num-derangements-inc-exc-aux (k 1))
		        (:instance inclusion-exclusion-principle (u (slist n)) (l (fixers n)))))))

(defthm derangements-formula
  (implies (posp n)
           (equal (len (derangements n))
                  (num-derangements n)))
  :hints (("Goal" :in-theory (enable len-derangements)
                  :use (num-derangements-inc-exc)
		  :cases ((= n 1) (= n 2)))))
