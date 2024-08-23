(in-package "DM")

(include-book "rmat")
(include-book "projects/groups/symmetric" :dir :system)

;; The term contributed by a permutation p in (sym n) to the determinant of an nxn
;;  matrix a is computed as follows:
;;   (1) select an entry from each row of a, the selection from row i being the one
;;       in column (nth i p), i.e., (entry i (nth i p) a);
;;   (2) compute the product of these n entries;
;;   (3) negate the product if p is an odd permutation.

(defun rdet-prod (a p n)
  (if (zp n)
      (r1)
    (r* (rdet-prod a p (1- n))
        (entry (1- n) (nth (1- n) p) a))))

(defund rdet-term (a p n)
  (if (even-perm-p p n)
      (rdet-prod a p n)
    (r- (rdet-prod a p n))))

;; The determinant of a is the sum over (slist n) of these signed products:

(defun rdet-sum (a l n)
  (if (consp l)
      (r+ (rdet-term a (car l) n)
	  (rdet-sum a (cdr l) n))
    (r0)))

(defund rdet (a n)
  (rdet-sum a (slist n) n))

;; We shall derive an equivalent definition of rdet-prod that allows us to apply the results of
;; "ring.lisp" by functional instantiation.

;; First we define a predicate that recognizes a pair of natural numbers that determine an entry of a:

(local-defund pairp (x n)
  (and (consp x)
       (natp (car x)) (< (car x) n)
       (natp (cdr x)) (< (cdr x) n)))

(local-defund pair-val (x a)
  (entry (car x) (cdr x) a))

;; Under suitable constraints on n and a, pairp and pair-val satisfy the constraint on rargp and rval
;; (see ring.lisp):

(local-defthm rp-pair-val
  (implies (and (pairp x n) (posp n) (rmatp a n n))
           (rp (pair-val x a)))
  :hints (("Goal" :in-theory (enable pair-val pairp)
                  :use ((:instance rp-entry (m n) (i (car x)) (j (cdr x)))))))

;; A list of pairs:

(local-defun pair-listp (l n)
  (if (consp l)
      (and (pairp (car l) n)
           (pair-listp (cdr l) n))
    t))

(local-defthm pair-listp-append
  (implies (and (pair-listp l n) (pair-listp m n))
           (pair-listp (append l m) n)))

;; The product of the values of a list of pairs:

(local-defun pairs-prod (l a)
  (if (consp l)
      (r* (pair-val (car l) a)
          (pairs-prod (cdr l) a))
    (r1)))

(local-defthm rp-pairs-prod
  (implies (and (posp n) (rmatp a n n)
                (pair-listp l n))
           (rp (pairs-prod l a))))

(local-defthm pairs-prod-append
  (implies (and (rmatp a n n) (posp n)
                (pair-listp l n)
		(pairp x n))
           (equal (pairs-prod (append l (list x)) a)
                  (r* (pairs-prod l a)
		      (pair-val x a))))
  :hints (("Subgoal *1/2" :use ((:instance r*assoc (x (PAIR-VAL (CAR L) A)) (y (PAIRS-PROD (CDR L) A)) (z (PAIR-VAL X A)))))))

;; A member of (slist n) may be represented as a list of pairs:

(local-defund perm-pair (i p)
  (cons i (nth i p)))

(local-defun perm-pairs (n p)
  (if (zp n)
      ()
    (append (perm-pairs (1- n) p)
            (list (perm-pair (1- n) p)))))
          
(local-defthm pairp-perm-pair
  (implies (and (posp n) (member p (slist n))
                (natp i) (< i n))
           (pairp (perm-pair i p) n))
  :hints (("Goal" :in-theory (enable perm-pair pairp)
                  :use ((:instance member-perm (x p) (k (nth i p)))
		        (:instance len-perm (x p))))))

(local-defthm pair-listp-perm-pairs
  (implies (and (posp n) (member p (slist n))
                (natp k) (<= k n))
           (pair-listp (perm-pairs k p) n)))

(local-defthm member-append
  (iff (member x (append l m))
       (or (member x l) (member x m))))

(local-defthmd member-perm-pairs
  (implies (natp n)
           (iff (member x (perm-pairs n p))
                (and (consp x)
                     (natp (car x))
	             (< (car x) n)
	             (equal (cdr x) (nth (car x) p)))))		     
  :hints (("Subgoal *1/2" :in-theory (enable perm-pair))))

(local-defthm dlistp-perm-pairs
  (implies (and (posp n) (member p (slist n))
                (natp k) (<= k n))
           (dlistp (perm-pairs k p)))
  :hints (("Subgoal *1/5" :in-theory (e/d (perm-pair) (common-member-shared))
                          :use ((:instance dlistp-append (l (perm-pairs (1- k) p))
                                                         (m (list (perm-pair (1- k) p))))
				(:instance common-member-shared (l (perm-pairs (1- k) p))
                                                                (m (list (perm-pair (1- k) p))))
			        (:instance member-perm-pairs (n (1- k)) (x (perm-pair (1- k) p)))))))
  
;; We have the following equivalent formulation of rdet-prod:

(local-defthmd rdet-prod-rewrite
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(natp k) (<= k n))
           (equal (rdet-prod a p k)
	          (pairs-prod (perm-pairs k p) a)))		  
  :hints (("Subgoal *1/5'" :in-theory (enable pair-val perm-pair))))

;; The determinant is a ring element:

;; By pair-listp-perm-pairs and rp-pairs-prod, rdet-prod and rdet-term return ring elements:

(defthm rp-rdet-prod
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(natp k) (<= k n))
           (rp (rdet-prod a p k)))
  :hints (("Goal" :in-theory (enable rdet-prod-rewrite))))

(defthm rp-rdet-term
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n)))
           (rp (rdet-term a p n)))
  :hints (("Goal" :in-theory (enable rdet-term))))

;; The following result, which will be used in the next section, is derived by functional instantiation
;; of rval-prod-permp:

(local-defthmd pairs-prod-permp
  (implies (and (posp n) (rmatp a n n)
                (dlistp l) (pair-listp l n)
		(dlistp m) (pair-listp m n)
		(permp l m))
           (equal (pairs-prod l a)
	          (pairs-prod m a)))
  :hints (("Goal" :use ((:functional-instance rval-prod-permp
                          (rargp (lambda (x) (if (and (posp n) (rmatp a n n)) (pairp x n) (rargp x))))
                          (rval (lambda (x) (if (and (posp n) (rmatp a n n)) (pair-val x a) (rval x))))
                          (rarg-listp (lambda (x) (if (and (posp n) (rmatp a n n)) (pair-listp x n) (rarg-listp x))))
			  (rval-prod (lambda (x) (if (and (posp n) (rmatp a n n)) (pairs-prod x a) (rval-prod x)))))))))

;; We similarly derive the following functional instances of rp-rval-sum, rval-sum-append, and
;; rval-sum-permp:

(local-defthm rp-rdet-sum
  (implies (and (rmatp a n n) (posp n)
                (sublistp l (slist n)))
	   (rp (rdet-sum a l n))))

(defthm rp-rdet
  (implies (and (rmatp a n n) (posp n))
	   (rp (rdet a n)))
  :hints (("Goal" :in-theory (enable rdet))))

(local-defthmd rdet-sum-append
  (implies (and (rmatp a n n) (posp n)
                (sublistp l (slist n))
		(sublistp m (slist n)))
	   (equal (rdet-sum a (append l m) n)
	          (r+ (rdet-sum a l n)
		      (rdet-sum a m n))))
  :hints (("Subgoal *1/2" :use ((:instance r+assoc (x (RDET-TERM A (CAR L) N)) (y (RDET-SUM A (CDR L) N)) (z (RDET-SUM A M N)))))))

(local-defthmd rdet-sum-permp
  (implies (and (rmatp a n n) (posp n)
                (dlistp l) (sublistp l (slist n))
		(dlistp m) (sublistp m (slist n))
		(permp l m))
	   (equal (rdet-sum a l n)
	          (rdet-sum a m n)))		      
  :hints (("Goal" :use ((:functional-instance rval-sum-permp
                          (rargp (lambda (x) (if (and (posp n) (rmatp a n n)) (member x (slist n)) (rargp x))))
                          (rval (lambda (x) (if (and (posp n) (rmatp a n n)) (rdet-term a x n) (rval x))))
                          (rarg-listp (lambda (x) (if (and (posp n) (rmatp a n n)) (sublistp x (slist n)) (rarg-listp x))))
			  (rval-sum (lambda (x) (if (and (posp n) (rmatp a n n)) (rdet-sum a x n) (rval-sum x)))))))))


;;-------------------------------------------------------------------------------------------------------
;;   Properties of the Determinant
;;-------------------------------------------------------------------------------------------------------

(local-defthmd least-moved-perm
  (implies (and (posp n) (member p (slist n)) (not (= p (ninit n))))
           (let ((m (least-moved p)))
	     (and (natp m)
	          (< m n)
		  (not (equal (nth m p) m)))))
  :hints (("Goal" :use (least-moved-n-ninit least-moved-moved least-moved-bounds
                        (:instance len-perm (x p))))))

(local-defthmd member-least-moved-pairs
  (implies (and (posp n) (member p (slist n)) (not (= p (ninit n)))
                (natp k) (> k (least-moved p)))
	   (member (perm-pair (least-moved p) p)
	           (perm-pairs k p)))
  :hints (("Goal" :induct (perm-pairs k p))
          ("Subgoal *1/2" :use (least-moved-perm))))

(local-defthmd pairs-prod-r0
  (implies (and (posp n) (member p (slist n)) (not (= p (ninit n)))
                (pair-listp l n)
		(member (perm-pair (least-moved p) p) l))
           (equal (pairs-prod l (id-rmat n))
	          (r0)))
  :hints (("Subgoal *1/2" :in-theory (enable perm-pair pair-val)
                          :use (least-moved-perm
			        (:instance len-perm (x p))
				(:instance member-perm (x p) (k (nth (least-moved p) p)))
			        (:instance entry-id-rmat (i (least-moved p))
				                         (j (nth (least-moved p) p)))))))

(local-defthmd rdet-term-id-rmat
  (implies (and (posp n) (member p (slist n)) (not (= p (ninit n))))
           (equal (rdet-term (id-rmat n) p n)
	          (r0)))
  :hints (("Goal" :in-theory (enable rdet-prod-rewrite rdet-term)
                  :use (least-moved-perm
		        (:instance member-least-moved-pairs (k n))
			(:instance rdet-prod-rewrite (a (id-rmat n)) (k n))
			(:instance pairs-prod-r0 (l (perm-pairs n p)))))))

(local-defthmd pairs-prod-ninit
  (implies (and (posp n) (natp k) (<= k n))
           (equal (pairs-prod (perm-pairs k (ninit n)) (id-rmat n))
	          (r1)))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :in-theory (e/d (pairp pair-val perm-pair)
	                                  (pair-listp-perm-pairs pairs-prod-append))
	                  :use ((:instance pairs-prod-append (l (perm-pairs (1- k) (ninit n)))
	                                                     (a (id-rmat n))
							     (x (perm-pair (1- k) (ninit n))))
				(:instance pair-listp-perm-pairs (p (ninit n)) (k (1- k)))))))

(local-defthmd rdet-term-id-rmat-ninit
  (implies (posp n)
           (equal (rdet-term (id-rmat n) (ninit n) n)
	          (r1)))
  :hints (("Goal" :in-theory (enable rdet-term)
                  :use ((:instance pairs-prod-ninit (k n))
			(:instance rdet-prod-rewrite (a (id-rmat n)) (p (ninit n)) (k n))))))
			

(local-defthmd rdet-sum-id-rmat
  (implies (and (posp n) (dlistp l) (sublistp l (slist n)))
           (equal (rdet-sum (id-rmat n) l n)
	          (if (member (ninit n) l)
		      (r1) (r0))))		      
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use (rdet-term-id-rmat-ninit (:instance rdet-term-id-rmat (p (car l)))))))

;; To compute (rdet (id-rmat n) n), note that if p is any permutation other than (ninit n), we can find
;; i < n such that (nth i p) <> i, and hence (entry i (nth i p) (id-rmat n)) = (r0), which implies
;; (rdet-term (id-rmat p n)) = (r0).  On the other hand, (nth i (ninit n)) = i for all i, which implies
;; (rdet-term (id-rmat (ninit n) n)) = (r1).   Thus,

(defthm rdet-id-rmat
  (implies (posp n)
           (equal (rdet (id-rmat n) n)
	          (r1)))
  :hints (("Goal" :in-theory (enable rdet)
                  :use ((:instance rdet-sum-id-rmat (l (slist n)))))))


;;-------------------------------------------------------------------------------------------------------

;; rdet is invariant under transpose-mat.  This follows from the observation that the term contributed
;; to the determinant of the transpose of a by a permutation p is the same as the term contributed to
;; the determinant of a by the inverse of p:

(local-defund flip-perm-pair (i p)
  (cons (nth i p) i))

(local-defun flip-perm-pairs (n p)
  (if (zp n)
      ()
    (append (flip-perm-pairs (1- n) p)
            (list (flip-perm-pair (1- n) p)))))
          
(local-defthm pairp-flip-perm-pair
  (implies (and (posp n) (member p (slist n))
                (natp i) (< i n))
           (pairp (flip-perm-pair i p) n))
  :hints (("Goal" :in-theory (enable flip-perm-pair pairp)
                  :use ((:instance member-perm (x p) (k (nth i p)))
		        (:instance len-perm (x p))))))

(local-defthmd pair-listp-flip-perm-pairs
  (implies (and (posp n) (member p (slist n))
                (natp k) (<= k n))
           (pair-listp (flip-perm-pairs k p) n)))

(local-defthmd member-flip-perm-pairs
  (implies (natp n)
           (iff (member x (flip-perm-pairs n p))
                (and (consp x)
                     (natp (cdr x))
	             (< (cdr x) n)
	             (equal (car x) (nth (cdr x) p)))))
  :hints (("Subgoal *1/2" :in-theory (enable flip-perm-pair))))

(local-defthm dlistp-flip-perm-pairs
  (implies (and (posp n) (member p (slist n))
                (natp k) (<= k n))
           (dlistp (flip-perm-pairs k p)))
  :hints (("Subgoal *1/5" :in-theory (e/d (flip-perm-pair) (common-member-shared))
                          :use ((:instance dlistp-append (l (flip-perm-pairs (1- k) p))
                                                         (m (list (flip-perm-pair (1- k) p))))
				(:instance common-member-shared (l (flip-perm-pairs (1- k) p))
                                                                (m (list (flip-perm-pair (1- k) p))))
			        (:instance member-flip-perm-pairs (n (1- k)) (x (flip-perm-pair (1- k) p)))))))

(local-defthmd nth-perm
  (implies (and (posp n) (member p (slist n))
                (natp i) (< i n))
	   (and (natp (nth i p))
	        (< (nth i p) n)))
  :hints (("Goal" :use ((:instance len-perm (x p))
                        (:instance member-perm (x p) (k (nth i p)))))))

(local-defthmd sublistp-flip-perm-pairs
  (implies (and (posp n) (member p (slist n)))
           (sublistp (flip-perm-pairs n p)
	             (perm-pairs n (inv-perm p n))))
  :hints (("Goal" :in-theory (disable nth-ind)
                  :use ((:instance scex1-lemma (l (flip-perm-pairs n p)) (m (perm-pairs n (inv-perm p n))))
                        (:instance member-flip-perm-pairs (x (scex1 (flip-perm-pairs n p)
			                                            (perm-pairs n (inv-perm p n)))))
                        (:instance member-perm-pairs (x (scex1 (flip-perm-pairs n p)
			                                       (perm-pairs n (inv-perm p n))))
						     (p (inv-perm p n)))
			(:instance ind-nth (i (CDR (SCEX1 (FLIP-PERM-PAIRS N P)
                                                          (PERM-PAIRS N (INV-PERM P N)))))
					   (l p))
			(:instance dlistp-perm (x p))
			(:instance len-perm (x p))
			(:instance member-perm (x p)
			                       (k (CDR (SCEX1 (FLIP-PERM-PAIRS N P)
                                                       (PERM-PAIRS N (INV-PERM P N))))))
			(:instance nth-perm (i (CDR (SCEX1 (FLIP-PERM-PAIRS N P)
                                                           (PERM-PAIRS N (INV-PERM P N))))))))))

(local-defthmd sublistp-perm-pairs
  (implies (and (posp n) (member p (slist n)))
           (sublistp (perm-pairs n (inv-perm p n))
	             (flip-perm-pairs n p)))	             
  :hints (("Goal" :in-theory (disable nth-ind)
                  :use ((:instance scex1-lemma (m (flip-perm-pairs n p)) (l (perm-pairs n (inv-perm p n))))
                        (:instance member-flip-perm-pairs (x (scex1 (perm-pairs n (inv-perm p n))
			                                            (flip-perm-pairs n p))))
                        (:instance member-perm-pairs (x (scex1 (perm-pairs n (inv-perm p n))
			                                       (flip-perm-pairs n p)))			                                       
						     (p (inv-perm p n)))						     
			(:instance nth-ind (x (CAR (SCEX1 (PERM-PAIRS N (INV-PERM P N))
                                                          (FLIP-PERM-PAIRS N P))))
					   (l p))					   
			(:instance dlistp-perm (x p))
			(:instance len-perm (x p))
			(:instance member-perm (x p)
			                       (k (CaR (SCEX1 (PERM-PAIRS N (INV-PERM P N))
                                                              (FLIP-PERM-PAIRS N P)))))))))

(local-defthmd permp-flip-perm-pairs
  (implies (and (posp n) (member p (slist n)))
           (permp (flip-perm-pairs n p)
	          (perm-pairs n (inv-perm p n))))
  :hints (("Goal" :in-theory (enable permp)
                  :use (sublistp-flip-perm-pairs sublistp-perm-pairs))))
  
(local-defthmd pairs-prod-flip-perm-pairs
  (implies (and (rmatp a n n) (posp n) (member p (slist n)))
           (equal (pairs-prod (flip-perm-pairs n p) a)
	          (pairs-prod (perm-pairs n (inv-perm p n)) a)))
  :hints (("Goal" :in-theory (enable pair-listp-flip-perm-pairs)
                  :use (permp-flip-perm-pairs
                        (:instance pairs-prod-permp (l (flip-perm-pairs n p)) (m (perm-pairs n (inv-perm p n))))))))

(local-defthmd pairs-prod-perm-pairs-transpose
  (implies (and (rmatp a n n) (posp n) (member p (slist n))
                (natp k) (<= k n))
           (equal (pairs-prod (flip-perm-pairs k p) a)
	          (pairs-prod (perm-pairs k p) (transpose-mat a))))
  :hints (("Subgoal *1/5" :in-theory (enable pair-listp-perm-pairs pair-listp-flip-perm-pairs)
                          :use ((:instance rmatp-transpose (m n))))
	  ("Subgoal *1/5''" :in-theory (e/d (pair-val perm-pair flip-perm-pair) (entry))
	                    :use ((:instance transpose-rmat-entry (m n) (i (1- k)) (j (nth (1- k) p)))
			          (:instance nth-perm (i (1- k)))))))

(local-defthmd pairs-prod-inv-perm-pairs-transpose
  (implies (and (rmatp a n n) (posp n) (member p (slist n)))
           (equal (pairs-prod (perm-pairs n (inv-perm p n)) a)
	          (pairs-prod (perm-pairs n p) (transpose-mat a))))
  :hints (("Goal" :use (pairs-prod-flip-perm-pairs
                        (:instance pairs-prod-perm-pairs-transpose (k n))))))
  
(defthmd rdet-term-transpose
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n)))
           (equal (rdet-term (transpose-mat a) p n)
	          (rdet-term a (inv-perm p n) n)))
  :hints (("Goal" :in-theory (enable even-perm-p rdet-prod-rewrite rdet-term)  
                  :use (pairs-prod-inv-perm-pairs-transpose parity-inv
		        (:instance rmatp-transpose (m n))))))

(local-defun inv-perms (l n)
  (if (consp l)
      (cons (inv-perm (car l) n)
            (inv-perms (cdr l) n))
    ()))

(local-defthmd member-inv-perms
  (implies (and (posp n) (member p (slist n))
                (sublistp l (slist n)))
           (iff (member (inv-perm p n) (inv-perms l n))
	        (member p l)))
  :hints (("Subgoal *1/3" :in-theory (disable inv-inv)
                          :use ((:instance inv-inv (g (sym n)) (x p))
			        (:instance inv-inv (g (sym n)) (x (car l)))))))

(local-defthm dlistp-sublist-inv-perms
  (implies (and (posp n) (dlistp l) (sublistp l (slist n)))
           (dlistp (inv-perms l n)))
  :hints (("Subgoal *1/3" :use ((:instance member-inv-perms (l (cdr l)) (p (car l)))))))

(local-defthm dlistp-inv-perms
  (implies (posp n)
           (dlistp (inv-perms (slist n) n)))
  :hints (("Goal" :use ((:instance dlistp-sublist-inv-perms (l (slist n)))))))

(local-defthmd sublistp-slist-inv-perms
  (implies (posp n)
           (sublistp (slist n) (inv-perms (slist n) n)))
  :hints (("Goal" :use ((:instance scex1-lemma (l (slist n)) (m (inv-perms (slist n) n)))
                        (:instance inv-inv (g (sym n)) (x (scex1 (slist n) (inv-perms (slist n) n))))
			(:instance member-inv-perms (l (slist n)) (p (inv-perm (scex1 (slist n) (inv-perms (slist n) n)) n)))))))

(local-defthmd member-inv-perms-slist
  (implies (and (posp n) (sublistp l (slist n)) (member p (inv-perms l n)))
           (member p (slist n))))

(local-defthmd sublistp-inv-perms-slist
  (implies (posp n)
           (sublistp (inv-perms (slist n) n) (slist n)))
  :hints (("Goal" :use ((:instance member-inv-perms-slist (l (slist n)) (p (scex1 (inv-perms (slist n) n) (slist n))))
                        (:instance scex1-lemma (l (inv-perms (slist n) n)) (m (slist n)))))))

(local-defthm permp-inv-perms
  (implies (posp n)
           (permp (inv-perms (slist n) n)
	          (slist n)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (sublistp-inv-perms-slist sublistp-slist-inv-perms))))

(local-defthmd rdet-sum-inv-perms
  (implies (and (posp n) (rmatp a n n))
           (equal (rdet-sum a (inv-perms (slist n) n) n)
	          (rdet-sum a (slist n) n)))
  :hints (("Goal" :use (permp-inv-perms sublistp-inv-perms-slist
                        (:instance rdet-sum-permp (l (inv-perms (slist n) n)) (m (slist n)))))))

(local-defthmd rdet-sum-transpose
  (implies (and (posp n) (rmatp a n n) (sublistp l (slist n)))
           (equal (rdet-sum a (inv-perms l n) n)
	          (rdet-sum (transpose-mat a) l n)))
  :hints (("Subgoal *1/2" :use ((:instance rdet-term-transpose (p (car l)))))))

(defthmd rdet-transpose
  (implies (and (posp n) (rmatp a n n))
           (equal (rdet (transpose-mat a) n)
	          (rdet a n)))
  :hints (("Goal" :in-theory (enable rdet)
                  :use (rdet-sum-inv-perms
		        (:instance rdet-sum-transpose (l (slist n)))))))


;;-------------------------------------------------------------------------------------------------------

;; rdet is alternating, i.e., if 2 rows of a are equal, then its determinant is (r0).

(local-defun perm-pairs-alt (k p i j n)
  (if (zp k)
      ()
    (append (perm-pairs-alt (1- k) p i j n)
            (list (perm-pair (nth (1- k) (transpose i j n)) p)))))

(local-defthm pair-listp-perm-pairs-alt
  (implies (and (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j))
		(natp k) (<= k n))
           (pair-listp (perm-pairs-alt k p i j n) n))
  :hints (("Subgoal *1/5" :in-theory (enable transpose-vals))))

(local-defthm pair-listp-perm-pairs
  (implies (and (posp n) (member p (slist n))
                (natp k) (<= k n))
           (pair-listp (perm-pairs k p) n)))


(local-defthmd member-perm-pairs-alt
  (implies (and (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j))
		(natp k) (<= k n))
	   (iff (member x (perm-pairs-alt k p i j n))
	        (and (consp x)
		     (natp (car x)) (< (car x) n)
		     (< (nth (car x) (transpose i j n)) k)
		     (= (cdr x) (nth (car x) p)))))
  :hints (("Subgoal *1/2" :in-theory (enable perm-pair transpose-vals))
          ("Subgoal *1/1" :in-theory (enable transpose-vals))))

(local-defthmd dlistp-perm-pairs-alt
  (implies (and (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j))
		(natp k) (<= k n))
	   (dlistp (perm-pairs-alt k p i j n)))	   
  :hints (("Subgoal *1/5" :in-theory (e/d (perm-pair transpose-vals) (common-member-shared))
                          :use ((:instance common-member-shared (l (PERM-PAIRS-ALT (+ -1 K) P I J N))
			                                        (m (LIST (PERM-PAIR (NTH (+ -1 K) (TRANSPOSE I J N)) p))))
				(:instance member-perm-pairs-alt (k (1- k))
				                                 (x (PERM-PAIR (NTH (+ -1 K) (TRANSPOSE I J N)) p)))))))

(local-defthmd member-perm-pairs-alt-perm-pairs
  (implies (and (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (iff (member x (perm-pairs-alt n p i j n))
	        (member x (perm-pairs n p))))
  :hints (("Goal" :in-theory (enable transpose-vals)
                  :use (member-perm-pairs
		        (:instance member-perm-pairs-alt (k n))))))

(local-defthmd sublistp-perm-pairs-alt-perm-pairs
  (implies (and (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (and (sublistp (perm-pairs-alt n p i j n)
	                  (perm-pairs n p))
		(sublistp (perm-pairs n p)
		          (perm-pairs-alt n p i j n))))	                  
  :hints (("Goal" :use ((:instance scex1-lemma (l (perm-pairs-alt n p i j n)) (m (perm-pairs n p)))
                        (:instance scex1-lemma (m (perm-pairs-alt n p i j n)) (l (perm-pairs n p)))
			(:instance member-perm-pairs-alt-perm-pairs (x (scex1 (perm-pairs-alt n p i j n) (perm-pairs n p))))
			(:instance member-perm-pairs-alt-perm-pairs (x (scex1 (perm-pairs n p) (perm-pairs-alt n p i j n))))))))

(local-defthmd perm-pairs-alt-permp
  (implies (and (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j))
		(= (row i a) (row j a)))
	   (permp (perm-pairs-alt n p i j n)
	          (perm-pairs n p)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (sublistp-perm-pairs-alt-perm-pairs
		        (:instance dlistp-perm-pairs-alt (k n))))))

(local-defthmd pair-val-perm-pair-comp-perm-1
  (implies (and (rmatp a n n) (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
           (equal (pair-val (perm-pair i (comp-perm p (transpose i j n) n))  a)
                  (pair-val (perm-pair j p) a)))
  :hints (("Goal" :in-theory (enable pair-val perm-pair transpose-vals)
                  :use ((:instance nth-comp-perm (x p) (y (transpose i j n)) (k i))))))

(local-defthmd pair-val-perm-pair-comp-perm-2
  (implies (and (rmatp a n n) (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
           (equal (pair-val (perm-pair j (comp-perm p (transpose i j n) n))  a)
                  (pair-val (perm-pair i p) a)))
  :hints (("Goal" :in-theory (enable pair-val perm-pair transpose-vals)
                  :use ((:instance nth-comp-perm (x p) (y (transpose i j n)) (k i))))))

(local-defthmd pair-val-perm-pair-comp-perm-3
  (implies (and (rmatp a n n) (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(posp k) (<= k n) (not (= (1- k) i)) (not (= (1- k) j))
		(member p (slist n)))
           (equal (pair-val (perm-pair (1- k) (comp-perm p (transpose i j n) n))  a)
                  (pair-val (perm-pair (1- k) p) a)))
  :hints (("Goal" :in-theory (e/d (pair-val perm-pair transpose-vals) (nth-comp-perm))
                  :use ((:instance nth-comp-perm (x p) (y (transpose i j n)) (k (1- k)))))))

(local-defthmd pairs-prod-perm-pairs-alt-comp-perm
  (implies (and (rmatp a n n) (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(natp k) (<= k n)
		(member p (slist n)))
	   (equal (pairs-prod (perm-pairs-alt k (comp-perm p (transpose i j n) n) i j n) a)
	          (pairs-prod (perm-pairs k p) a)))
  :hints (("Subgoal *1/5" :in-theory (e/d (transpose-vals) (sym-closed))
                          :use (pair-val-perm-pair-comp-perm-1 pair-val-perm-pair-comp-perm-2
			        pair-val-perm-pair-comp-perm-3 permp-transpose
			        (:instance sym-closed (x p) (y (transpose i j n)))))))

(local-defthmd pairs-prod-perm-pairs-comp-perm
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (pairs-prod (perm-pairs n (comp-perm p (transpose i j n) n)) a)
	          (pairs-prod (perm-pairs n p) a)))
  :hints (("Goal" :in-theory (disable sym-closed)
                  :use (permp-transpose
		        (:instance pairs-prod-perm-pairs-alt-comp-perm (k n))
                        (:instance perm-pairs-alt-permp (p (comp-perm p (transpose i j n) n)))
			(:instance sym-closed (x p) (y (transpose i j n)))
			(:instance pairs-prod-permp (l (perm-pairs-alt n (comp-perm p (transpose i j n) n) i j n))
			                            (m (perm-pairs n (comp-perm p (transpose i j n) n))))))))

;; To prove this, suppose rows i and j of a are equal, where i <> j.  Given a permutation p, let
;; p' = (comp-perm p (transpose i j n) n).  Then the factors of (rdet-prod a p' n) are the same as
;; those of (rdet-prod a p n):

(defthmd rdet-prod-comp-perm
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (rdet-prod a (comp-perm p (transpose i j n) n) n)
	          (rdet-prod a p n)))
  :hints (("Goal" :in-theory (e/d (rdet-prod-rewrite) (sym-closed))
                  :use (pairs-prod-perm-pairs-comp-perm permp-transpose
			(:instance sym-closed (x p) (y (transpose i j n)))))))

;; If p is even, then p' is odd, and therefore (rdet-term a p' n) is the negative of (rdet-term a p n):

(local-defthm parity-comp-perm-transpose
  (implies (and (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (and (member (comp-perm p (transpose i j n) n)
	                (slist n))
		(iff (even-perm-p (comp-perm p (transpose i j n) n) n)
		     (not (even-perm-p p n)))))
  :hints (("Goal" :in-theory (e/d (parity-comp-perm even-perm-p odd-perm-p) (sym-closed))
                  :use (parity-0-1 transpose-odd permp-transpose
		        (:instance sym-closed (x p) (y (transpose i j n)))))))

(defthmd rdet-term-comp-perm
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (r+ (rdet-term a (comp-perm p (transpose i j n) n) n)
	              (rdet-term a p n))
		  (r0)))
  :hints (("Goal" :in-theory (enable rdet-prod-comp-perm rdet-term))))

;; Consequently, the sum of terms contributed by the odd permutations is the negative of the
;; sum of terms contributed by the even permutations:

(local-defun comp-perm-transpose-list (l n i j)
  (if (consp l)
      (cons (comp-perm (car l) (transpose i j n) n)
            (comp-perm-transpose-list (cdr l) n i j))
    ()))

(local-defthm len-comp-perm-transpose-list
  (equal (len (comp-perm-transpose-list l n i j))
         (len l)))

(local-defthmd rp-comp-perm-transpose-list
  (implies (and (posp n) (sublistp l (slist n)) (rmatp a n n)
		(natp i) (< i n) (natp j) (< j n) (not (= i j)))                
           (rp (rdet-sum a (comp-perm-transpose-list l n i j) n))))

(local-defthmd member-comp-perm-transpose-list
  (implies (and (posp n) (sublistp l (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)))                
           (iff (member x (comp-perm-transpose-list l n i j))
	        (and (member x (slist n))
		     (member (comp-perm x (transpose i j n) n) l))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (e/d (e) (group-right-identity))
	                  :use (permp-transpose transpose-involution
	                        (:instance group-right-identity (g (sym n)))
	                        (:instance group-right-identity (x (car l)) (g (sym n)))
	                        (:instance sym-assoc (y (transpose i j n)) (z (transpose i j n)))
	                        (:instance sym-assoc (x (car l)) (y (transpose i j n)) (z (transpose i j n)))))))

(local-defthmd sublistp-comp-perm-transpose-list-slist
  (implies (and (posp n) (sublistp l (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)))                
           (sublistp (comp-perm-transpose-list l n i j)
	             (slist n))))

(local-defthmd dlistp-comp-perm-transpose-list
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(dlistp l) (sublistp l (slist n)))
	   (dlistp (comp-perm-transpose-list l n i j)))
  :hints (("Subgoal *1/3" :in-theory (e/d (e) (group-right-identity))
                          :use (permp-transpose transpose-involution
	                        (:instance group-right-identity (x (car l)) (g (sym n)))
				(:instance member-comp-perm-transpose-list (x (COMP-PERM (CAR L) (TRANSPOSE I J N) N))
				                                           (l (cdr l)))
	                        (:instance sym-assoc (x (car l)) (y (transpose i j n)) (z (transpose i j n)))))))

(local-defthmd hack-1
  (implies (and (rp a) (rp d) (rp at) (rp td)
                (= (r+ at a) (r0))
		(= (r+ td d) (r0)))
	   (equal (r+ (r+ at td) (r+ a d)) (r0)))
  :hints (("Goal" :use ((:instance r+assoc (x at) (y td) (z (r+ a d)))
                        (:instance r+assoc (x td) (y a) (z d))
			(:instance r+comm (x a) (y td))
			(:instance r+assoc (x a) (y td) (z d))))))

(local-defthmd rdet-sum-comp-perm-transpose-list
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(sublistp l (slist n)))
	   (equal (r+ (rdet-sum a (comp-perm-transpose-list l n i j) n)
	              (rdet-sum a l n))
		  (r0)))
  :hints (("Subgoal *1/2" :use ((:instance hack-1 (at (RDET-TERM A (COMP-PERM (CAR L) (TRANSPOSE I J N) N) N))
                                                  (td (RDET-SUM A (COMP-PERM-TRANSPOSE-LIST (CDR L) N I J) N))
						  (a (RDET-TERM A (CAR L) N))
						  (d (RDET-SUM A (CDR L) N)))
				(:instance rdet-term-comp-perm (p (car l)))
				(:instance rp-comp-perm-transpose-list (l (cdr l)))))))

(local-defthmd member-comp-perm-transpose-list-even-perms
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(sublistp l (even-perms n))
		(member x (comp-perm-transpose-list l n i j)))
	   (not (even-perm-p x n)))	   
  :hints (("Subgoal *1/2" :use ((:instance even-perms-even (p (car l)))))))


(local-defthmd disjointp-comp-perm-transpose-list
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (disjointp (comp-perm-transpose-list (even-perms n) n i j)
	              (even-perms n)))
  :hints (("Goal" :use ((:instance common-member-shared (l (comp-perm-transpose-list (even-perms n) n i j))
				                        (m (even-perms n)))
                        (:instance member-comp-perm-transpose-list-even-perms
				     (l (even-perms n))
			             (x (common-member (comp-perm-transpose-list (even-perms n) n i j)
						       (even-perms n))))
			(:instance even-perms-even (p (common-member (comp-perm-transpose-list (even-perms n) n i j)
								     (even-perms n))))))))

(local-defthmd dlistp-append-comp-perm-transpose-list
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (dlistp (append (comp-perm-transpose-list (even-perms n) n i j)
	                   (even-perms n))))
  :hints (("Goal" :use (disjointp-comp-perm-transpose-list
                        (:instance dlistp-comp-perm-transpose-list (l (even-perms n)))))))

(local-defthm len-append
  (equal (len (append l m))
         (+ (len l) (len m))))

(local-defthmd len-append-comp-perm-transpose-list
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (equal (len (append (comp-perm-transpose-list (even-perms n) n i j)
	                       (even-perms n)))
		  (fact n)))
  :hints (("Goal" :in-theory (enable order)
                  :use (order-alt))))

(local-defthmd sublistp-append-comp-perm-transpose-list
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (sublistp (append (comp-perm-transpose-list (even-perms n) n i j)
	                     (even-perms n))
		     (slist n)))
  :hints (("Goal" :use ((:instance sublistp-comp-perm-transpose-list-slist (l (even-perms n)))))))

(local-defthmd permp--append-comp-perm-transpose-list
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (permp (append (comp-perm-transpose-list (even-perms n) n i j)
	                  (even-perms n))
		  (slist n)))
  :hints (("Goal" :use (sublistp-append-comp-perm-transpose-list dlistp-append-comp-perm-transpose-list
                        len-append-comp-perm-transpose-list len-slist
                        (:instance permp-eq-len (l (append (comp-perm-transpose-list (even-perms n) n i j) (even-perms n)))
                                                (m (slist n)))))))

(defthmd rdet-alternating
  (implies (and (rmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (equal (rdet a n) (r0)))
  :hints (("Goal" :in-theory (enable rdet)
                  :use (permp--append-comp-perm-transpose-list sublistp-append-comp-perm-transpose-list
		        dlistp-append-comp-perm-transpose-list
			(:instance sublistp-comp-perm-transpose-list-slist (l (even-perms n)))
			(:instance rdet-sum-comp-perm-transpose-list (l (even-perms n)))
			(:instance rdet-sum-append (l (comp-perm-transpose-list (even-perms n) n i j)) (m (even-perms n)))
			(:instance rdet-sum-permp (l (append (comp-perm-transpose-list (even-perms n) n i j) (even-perms n)))
			                          (m (slist n)))))))
		        

;;-------------------------------------------------------------------------------------------------------

;; rdet is n-linear, i.e, linear as a function of each row.  This property is
;; specified in terms of the basic operation of replacing a row of a with a given list.
;; For a given row i and permutation p, the term contributed by p to the determinant of
;; (replace-row a i x) by each permutation is a linear function of x:

(local-defthm pairs-prod-extend
  (implies (and (member p (slist n))
                (posp n) (rmatp a n n)                 
		(posp k) (<= k n))
           (equal (pairs-prod (perm-pairs k p) a)
                  (r* (pairs-prod (perm-pairs (1- k) p) a)
		      (pair-val (perm-pair (1- k) p) a)))))

(local-defthm pairs-prod-nil
  (equal (pairs-prod () a)
         (r1)))

(local-defthm perm-pairs-0
  (equal (perm-pairs 0 p)
         ()))

(local-in-theory (disable pairs-prod perm-pairs))

(local-defthm pair-val-perm-pair-replace-row
   (implies (and (rmatp a n n) (posp n)
                 (member p (slist n))
		 (natp i) (< i n)
		 (natp k) (< k n)
  		 (rlistnp x n))
            (equal (PAIR-VAL (PERM-PAIR k P)
                             (REPLACE-ROW A I X))
	           (if (= i k)
		       (nth (nth k p) x)
		     (entry k (nth k p) a))))
  :hints (("Goal" :in-theory (enable pair-val perm-pair))))

(local-defthmd pairs-prod-replace-row-1
    (implies (and (rmatp a n n) (posp n)
                  (member p (slist n))
  		  (rlistnp x n) (rlistnp y n) (rp c)
		  (natp i) (< i n) (natp k) (<= k i) (<= k n))
             (let ((a1 (replace-row a i x))
                   (a2 (replace-row a i y))
                   (a3 (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))
               (and (equal (pairs-prod (perm-pairs k p) a1)
	                   (pairs-prod (perm-pairs k p) a3))
	            (equal (pairs-prod (perm-pairs k p) a2)
	                   (pairs-prod (perm-pairs k p) a3)))))
  :hints (("Goal" :induct (fact k))))

(local-defthmd hack-2
  (implies (and (rp p) (rp c) (rp x) (rp y))
           (equal (r* p (r+ (r* c x) y))
	          (r+ (r* c (r* p x)) (r* p y))))
  :hints (("Goal" :use ((:instance rdist (x p) (y (r* c x)) (z y))
                        (:instance r*assoc (x p) (y c) (z x))
			(:instance r*comm (x p) (y c))
			(:instance r*assoc (x c) (y p) (z x))))))

(local-defthmd pairs-prod-replace-row-2
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(rlistnp x n) (rlistnp y n) (rp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))
             (equal (pairs-prod (perm-pairs (1+ i) p) a3)
  		    (r+ (r* c (pairs-prod (perm-pairs (1+ i) p) a1))
		  	(pairs-prod (perm-pairs (1+ i) p) a2)))))
  :hints (("Goal" :in-theory (disable nth-rlist-scalar-mul nth-rlist-add)
	          :use (nth-perm
		        (:instance pairs-prod-replace-row-1 (k i))
			(:instance nth-rlist-scalar-mul (i (nth i p)))
	                (:instance nth-rlist-add (i (nth i p)) (x (rlist-scalar-mul c x)))
			(:instance hack-2 (p (PAIRS-PROD (PERM-PAIRS I P) (REPLACE-ROW A I X)))
			                  (x (NTH (NTH I P) X))
					  (y (nth (nth i p) y)))))))

(local-defthmd hack-3
  (implies (and (rp x) (rp y) (rp a) (rp c))
           (equal (r* (r+ (r* c x) y) a)
	          (r+ (r* c (r* x a)) (r* y a))))
  :hints (("Goal" :use ((:instance rdist-comm (x (r* c x)) (z a))
                        (:instance r*assoc (x c) (y x) (z a))))))

(local-defthmd pairs-prod-replace-row-3
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(rlistnp x n) (rlistnp y n) (rp c)
                (natp i) (< i n) (natp k) (> k i) (<= k n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))
             (equal (pairs-prod (perm-pairs k p) a3)
  		    (r+ (r* c (pairs-prod (perm-pairs k p) a1))
		  	(pairs-prod (perm-pairs k p) a2)))))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :in-theory (disable nth-rlist-scalar-mul nth-rlist-add)
	                  :use (pairs-prod-replace-row-2
			        (:instance nth-perm (i (1- k)))
			        (:instance nth-rlist-scalar-mul (i (nth (1- k) p)))
	                        (:instance nth-rlist-add (i (nth (1- k) p)) (x (rlist-scalar-mul c x)))))
	  ("Subgoal *1/2.1" :in-theory (disable pairs-prod-extend)
	                    :use ((:instance rp-entry (m n) (i (1- k)) (j (nth (1- k) p)))
	                          (:instance hack-3 (x (PAIRS-PROD (PERM-PAIRS (+ -1 K) P) (REPLACE-ROW A I x)))
				                    (y (PAIRS-PROD (PERM-PAIRS (+ -1 K) P) (REPLACE-ROW A I Y)))
						    (a (NTH (NTH (+ -1 K) P) (NTH (+ -1 K) A))))))))

(local-defthmd pairs-prod-replace-row
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(rlistnp x n) (rlistnp y n) (rp c)
                (natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))
             (equal (pairs-prod (perm-pairs n p) a3)
  		    (r+ (r* c (pairs-prod (perm-pairs n p) a1))
		  	(pairs-prod (perm-pairs n p) a2)))))
  :hints (("Goal" :use ((:instance pairs-prod-replace-row-3 (k n))))))

(local-defthmd rdet-prod-replace-row
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(rlistnp x n) (rlistnp y n) (rp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))
             (equal (rdet-prod a3 p n)
	            (r+ (r* c (rdet-prod a1 p n))
			(rdet-prod a2 p n)))))
  :hints (("Goal" :in-theory (disable pairs-prod-extend)
                  :use (pairs-prod-replace-row
                        (:instance rdet-prod-rewrite (k n) (a (replace-row a i x)))
                        (:instance rdet-prod-rewrite (k n) (a (replace-row a i y)))
                        (:instance rdet-prod-rewrite (k n) (a (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))))))

(defthm rdet-term-replace-row
  (implies (and (rmatp a n n) (posp n)
                (member p (slist n))
		(rlistnp x n) (rlistnp y n) (rp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))
             (equal (rdet-term a3 p n)
	            (r+ (r* c (rdet-term a1 p n))
			(rdet-term a2 p n)))))
  :hints (("Goal" :in-theory (e/d (rdet-term rdet-prod-replace-row) (rp-rdet-prod))
                  :use ((:instance r-r+ (x (R* C (RDET-PROD (REPLACE-ROW A I X) P N)))
		                        (y (RDET-PROD (REPLACE-ROW A I Y) P N)))
			(:instance r-r* (x c) (y (RDET-PROD (REPLACE-ROW A I X) P N)))
			(:instance rp-rdet-prod (a (replace-row a i x)) (k n))
			(:instance rp-rdet-prod (a (replace-row a i y)) (k n))))))

(local-defthmd hack-4
  (implies (and (rp x1) (rp x2) (rp y1) (rp y2) (rp c))
           (equal (r+ (r+ (r* c x1) y1) (r+ (r* c x2) y2))
	          (r+ (r+ (r* c x1) (r* c x2)) (r+ y1 y2))))
  :hints (("Goal" :use ((:instance r+assoc (x (r+ (r* c x1) y1)) (y (r* c x2)) (z y2))
                        (:instance r+assoc (x (r* c x1)) (y y1) (z (r* c x2)))
			(:instance r+comm (x y1) (y (r* c x2)))
			(:instance r+assoc (x (r* c x1)) (y (r* c x2)) (z y1))
			(:instance r+assoc (x (r+ (r* c x1) (r* c x2))) (y y1) (z y2))))))

(local-defthmd rdet-sum-replace-row
  (implies (and (rmatp a n n) (posp n)
                (sublistp l (slist n))
		(rlistnp x n) (rlistnp y n) (rp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (rlist-add (rlist-scalar-mul c x) y))))
             (equal (rdet-sum a3 l n)
	            (r+ (r* c (rdet-sum a1 l n))
			(rdet-sum a2 l n)))))
  :hints (("Subgoal *1/2" :use ((:instance hack-4 (x1 (RDET-TERM (REPLACE-ROW A I X) (car l) n))
                                                  (y1 (RDET-TERM (REPLACE-ROW A I y) (car l) n))
						  (x2 (RDET-sum (REPLACE-ROW A I X) (cdr l) n))
						  (y2 (RDET-sum (REPLACE-ROW A I y) (cdr l) n)))))))

;; The desired result follows by summing over all permutations:
	          
(defthm rdet-n-linear
  (implies (and (rmatp a n n) (posp n) (natp i) (< i n)
		(rlistnp x n) (rlistnp y n) (rp c))
	   (equal (rdet (replace-row a i (rlist-add (rlist-scalar-mul c x) y)) n)
		  (r+ (r* c (rdet (replace-row a i x) n))
		      (rdet (replace-row a i y) n))))
  :hints (("Goal" :in-theory (enable rdet)
                  :use ((:instance rdet-sum-replace-row (l (slist n)))))))

;; As a consequence of rdet-n-linear, if a has a zero row, then its deteminant is (r0).
;; To prove this, we instantiate rdet-n-linear with c = (r1) and x = y = (rlistn0 n):

(defthmd rdet-replace-0-1
  (implies (and (rmatp a n n) (posp n) (natp k) (< k n))
           (equal (r+ (rdet (replace-row a k (rlistn0 n)) n)
	              (rdet (replace-row a k (rlistn0 n)) n))
		  (rdet (replace-row a k (rlistn0 n)) n)))
  :hints (("Goal" :in-theory (disable rlist-scalar-mul-r1)
                  :use ((:instance rdet-n-linear (i k) (c (r1)) (x (rlistn0 n)) (y (rlistn0 n)))
                        (:instance rlist-scalar-mul-r1 (x (rlistn0 n)))))))

;; It follows that (rdet (replace-row a k (rlistn0 n)) n) = (r0).  But if (row k a) = (rlistn0 n),
;; then (replace-row a k (rlistn0 n)) = a:

(local-defthmd rdet-replace-0
  (implies (and (rmatp a n n) (posp n) (natp k) (< k n))
           (equal (rdet (replace-row a k (rlistn0 n)) n)
	          (r0)))
  :hints (("Goal" :use (rdet-replace-0-1 (:instance r+left-cancel (x (rdet (replace-row a k (rlistn0 n)) n))
                                                                  (z (rdet (replace-row a k (rlistn0 n)) n))
							          (y (r0)))))))

(defthmd rdet-row-0
  (implies (and (rmatp a n n) (posp n) (natp k) (< k n) (= (nth k a) (rlistn0 n)))
           (equal (rdet a n)
	          (r0)))
  :hints (("Goal" :use (rdet-replace-0 (:instance replace-rmat-row-self (m n) (i k))))))


;;-------------------------------------------------------------------------------------------------------
;;   Uniqueness of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; We shall show that for given n, rdet is the unique n-linear alternating function on
;; nxn matrices such that (rdet (id-rmat n) n) = (r1).  To that end, we constrain the
;; function rdetn as follows:

(encapsulate (((n) => *))
  (local (defun n () 2))
  (defthm posp-n
    (posp (n))
    :rule-classes (:type-prescription :rewrite)))

(encapsulate (((rdetn *) => *))
  (local (defun rdetn (a) (rdet a (n))))
  (defthm rp-rdetn
    (implies (rmatp a (n) (n))
             (rp (rdetn a))))
  (defthmd rdetn-n-linear
    (implies (and (rmatp a (n) (n)) (natp i) (< i (n))
		  (rlistnp x (n)) (rlistnp y (n)) (rp c))
	     (equal (rdetn (replace-row a i (rlist-add (rlist-scalar-mul c x) y)))
		    (r+ (r* c (rdetn (replace-row a i x)))
		        (rdetn (replace-row a i y))))))
  (defthmd rdetn-adjacent-equal
    (implies (and (rmatp a (n) (n))
		  (natp i) (< i (1- (n))) (= (row i a) (row (1+ i) a)))
	     (equal (rdetn a) (r0)))
    :hints (("Goal" :use ((:instance rdet-alternating (n (n)) (j (1+ i))))))))

;; Our objective is to prove that (rdetn a) = (r* (rdet a (n)) (rdetn (id-rmat (n)))):

;; (defthmd rdet-unique
;;   (implies (rmatp a (n) (n))
;;            (equal (rdetn a)
;;                   (r* (rdet a (n))
;;                       (rdetn (id-rmat (n)))))))

;; If we also prove that for a given function f, (f a n) satisfies the constraints on (rdetn a),
;; we may conclude by functional instantiation that (f a n) = (r* (rdet a n) (f (id-rmat n))).
;; From this it follows that if f has the additional property (f (id-rmat n)) = (r1), then
;; (f a) = (rdet a (n)).

;; Note that we have replaced the property that rdetn is alternating with the weaker property
;; rdetn-adjacent-equal, which says that the value is (r0) if 2 adjacent rows are equal.  This
;; relaxes the proof obligations for functional instantiation, which will be critical for the
;; proof of correctness of cofactor expansion.  We shall show that this property together with
;; n-linearity implies that the same holds for 2 non-adjacent rows.

;; It follows from rdetn-n-linear and rdetn-adjacent-equal that transposing 2 adjacent rows negates
;; the value of rdetn:

(local-in-theory (disable nth rmatp replace-row))

(local-defthmd replace-adjacent-rows-same
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n)))
		(rlistnp x (n)))
           (equal (rdetn (replace-row (replace-row a i x) (1+ i) x))
		  (r0)))
  :hints (("Goal" :in-theory (disable len-rmatp)
                  :use ((:instance len-rmatp (m (n)) (n (n)))
                        (:instance rdetn-adjacent-equal (a (replace-row (replace-row a i x) (1+ i) x)))))))

(local-defthm rlistnp-nth
  (implies (and (natp m) (natp n) (rmatp a m n)
	        (natp i) (< i m))
           (rlistnp (nth i a) n))
  :hints (("Goal" :use (rlistnp-row))))

(local-defthmd rdetn-adjacent-alternating-1
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (r+ (rdetn (replace-row (replace-row a i (rlist-add (row i a) (row (1+ i) a)))
	                                 (1+ i)
		                         (row i a)))
	              (rdetn (replace-row (replace-row a i (rlist-add (row i a) (row (1+ i) a)))
	                                 (1+ i)
				         (row (1+ i) a))))
		  (r0)))
  :hints (("Goal" :in-theory (disable len-rmatp rlist-scalar-mul-r1)
                  :use ((:instance len-rmatp (m (n)) (n (n)))
		        (:instance rlist-scalar-mul-r1 (n (n)) (x (nth i a)))
			(:instance replace-adjacent-rows-same (x (rlist-add (row i a) (row (1+ i) a))))
		        (:instance rdetn-n-linear (a (replace-row a i (rlist-add (row i a) (row (1+ i) a))))
			                         (i (1+ i)) (c (r1)) (x (row i a)) (y (row (1+ i) a)))))))

(local-defthmd rdetn-adjacent-alternating-2
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (rdetn (replace-row (replace-row a i (rlist-add (row i a) (row (1+ i) a)))
	                             (1+ i)
		                     (row i a)))
		  (rdetn (replace-row (replace-row a (1+ i) (row i a))
		                     i
				     (rlist-add (row i a) (row (1+ i) a))))))
  :hints (("Goal" :in-theory (disable len-rmatp)
                  :use ((:instance len-rmatp (m (n)) (n (n)))
			(:instance replace-2-rmat-rows (m (n)) (n (n))
			                          (x (rlist-add (row i a) (row (1+ i) a))) (j (1+ i)) (y (row i a)))))))

(local-defthmd rdetn-adjacent-alternating-3
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (rdetn (replace-row (replace-row a (1+ i) (row i a))
		                     i
				     (rlist-add (row i a) (row (1+ i) a))))
		  (rdetn (replace-row (replace-row a (1+ i) (row i a))
		                     i
				     (row (1+ i) a)))))
  :hints (("Goal" :in-theory (disable rlist-scalar-mul-r1 len-rmatp)
                  :use ((:instance len-rmatp (m (n)) (n (n)))
		        (:instance rlist-scalar-mul-r1 (n (n)) (x (nth i a)))
			(:instance rdetn-n-linear (a (replace-row a (1+ i) (row i a)))
			                         (c (r1)) (x (row i a)) (y (row (1+ i) a)))
			(:instance rdetn-adjacent-equal (a (replace-row (replace-row a (1+ i) (row i a))
			                                               i (row i a))))))))

(local-defthmd rdetn-adjacent-alternating-4
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (rdetn (replace-row (replace-row a i (rlist-add (row i a) (row (1+ i) a)))
	                             (1+ i)
		                     (row (1+ i) a)))
		  (rdetn (replace-row a i (rlist-add (row i a) (row (1+ i) a))))))
  :hints (("Goal" :in-theory (disable len-rmatp rlist-scalar-mul-r1)
                  :use ((:instance len-rmatp (m (n)) (n (n)))
		        (:instance replace-rmat-row-self (m (n)) (n (n)) (i (1+ i))
			                            (a (replace-row a i (rlist-add (row i a) (row (1+ i) a)))))))))

(local-defthmd rdetn-adjacent-alternating-5
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (rdetn (replace-row a i (rlist-add (row i a) (row (1+ i) a))))
		  (rdetn a)))
  :hints (("Goal" :in-theory (disable len-rmatp rlist-scalar-mul-r1)
                  :use ((:instance len-rmatp (m (n)) (n (n)))
		        (:instance rlist-scalar-mul-r1 (n (n)) (x (nth i a)))
			(:instance rdetn-n-linear (c (r1)) (x (row i a)) (y (row (1+ i) a)))
			(:instance rdetn-adjacent-equal (a (replace-row a i (row (1+ i) a))))
			(:instance replace-rmat-row-self (m (n)) (n (n)))))))

(local-defthmd rdetn-adjacent-alternating-6
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (r+ (rdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))
	              (rdetn a))
		  (r0)))
  :hints (("Goal" :use (rdetn-adjacent-alternating-1 rdetn-adjacent-alternating-2 rdetn-adjacent-alternating-3
                        rdetn-adjacent-alternating-4 rdetn-adjacent-alternating-5))))

(defthmd rdetn-interchange-adjacent
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (rdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))
	          (r- (rdetn a))))
  :hints (("Goal" :use (rdetn-adjacent-alternating-6
                        (:instance rlistnp-row (n (n)) (m (n)) (i (1+ i)))
                        (:instance r-unique (x (rdetn a))
			                    (y (rdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))))
			(:instance r+comm (x (rdetn a))
			                  (y (rdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))))
		        (:instance rmatp-replace-row (m (n)) (n (n)) (k (1+ i)) (r (row i a)))
                        (:instance rmatp-replace-row (m (n)) (n (n)) (a (replace-row a (1+ i) (row i a)))
			                             (k i) (r (row (1+ i) a)))))))

;; Interchanging adjacent rows may be expressed as a permutation:

(local-defthmd rdetn-adjacent-alternating-7
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n)))
		(natp k) (< k (n)))
           (equal (nth k (replace-row (replace-row a (1+ i) (row i a))
		                      i
		                      (row (1+ i) a)))
	          (nth k (permute a (transpose i (1+ i) (n))))))
  :hints (("Goal" :in-theory (e/d (transpose-vals) (len-rmatp nth-permute len-replace-row rmatp-replace-row))
                  :use ((:instance len-rmatp (m (n)) (n (n)))
		        (:instance nth-permute (l a) (p (TRANSPOSE I (+ 1 I) (N))))
		        (:instance nth-permute (l a) (p (TRANSPOSE I (+ 1 I) (N))) (k i))
		        (:instance rmatp-replace-row (m (n)) (n (n)) (k (1+ i)) (r (row i a)))
                        (:instance rmatp-replace-row (m (n)) (n (n)) (a (replace-row a (1+ i) (row i a)))
			                             (k i) (r (row (1+ i) a)))
			(:instance len-replace-row (k (1+ i)) (r (row i a)))
                        (:instance len-replace-row (a (replace-row a (1+ i) (row i a)))
			                           (k i) (r (row (1+ i) a)))
			(:instance permp-transpose (n (n)) (j (1+ i)))))))

(local-defthm len-permute
  (equal (len (permute l p))
         (len p)))

(local-defthm true-listp-permute
  (true-listp (permute l p)))

(defthmd interchange-adjacent-rmat-permute
  (implies (and (rmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a))
	          (permute a (transpose i (1+ i) (n)))))
  :hints (("Goal" :in-theory (disable len-rmatp nth-permute len-replace-row rmatp-replace-row)
                  :use ((:instance len-rmatp (m (n)) (n (n)))
		        (:instance rmatp-replace-row (m (n)) (n (n)) (k (1+ i)) (r (row i a)))
                        (:instance rmatp-replace-row (m (n)) (n (n)) (a (replace-row a (1+ i) (row i a)))
			                             (k i) (r (row (1+ i) a)))
			(:instance len-replace-row (k (1+ i)) (r (row i a)))
                        (:instance len-replace-row (a (replace-row a (1+ i) (row i a)))
			                           (k i) (r (row (1+ i) a)))
			(:instance permp-transpose (n (n)) (j (1+ i)))
			(:instance len-perm (n (n)) (x (transpose i (1+ i) (n))))
			(:instance nth-diff-diff (x (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))
			                         (y (permute a (transpose i (1+ i) (n)))))
			(:instance rdetn-adjacent-alternating-7
			  (k (nth-diff (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a))
			               (permute a (transpose i (1+ i) (n))))))))))

(defthmd rdetn-permute-adjacent-transpose
  (implies (and (rmatp a (n) (n))
                (natp i) (< i (1- (n))))
           (equal (rdetn (permute a (transpose i (1+ i) (n))))
                  (r- (rdetn a))))
  :hints (("Goal" :use (rdetn-interchange-adjacent interchange-adjacent-rmat-permute))))

;; Note that applying any permutation to the rows of a produces a matrix of the
;; same dimensions:

(local-defthm rmatp-remove1
  (implies (and (rmatp a m n) (natp m) (member r a))
           (rmatp (remove1 r a) (1- m) n))	   
  :hints (("Goal" :in-theory (enable rmatp))))

(local-defthm member-rmatp-rlistnp
  (implies (and (rmatp a m n) (member r a))
           (rlistnp r n))
  :hints (("Goal" :in-theory (enable rmatp))))

(local-defthmd rmatp-perm
  (implies (and (rmatp a m n) (natp m) (natp n)
                (true-listp b) (permutationp b a))
	   (rmatp b m n))
  :hints (("Goal" :in-theory (enable rmatp))))

(local-defthm true-listp-permute
  (true-listp (permute l p)))

(defthm rmatp-permute
  (implies (and (rmatp a m n) (posp m) (posp n)
                (in p (sym m)))
	   (rmatp (permute a p) m n))
  :hints (("Goal" :in-theory (enable rmatp)
                  :use ((:instance permutationp-permute (l a))
                        (:instance permutationp-symmetric (l a) (m (permute a p)))
			(:instance rmatp-perm (b (permute a p)))))))

;; Next we show that rdetn-permute-adjacent-transpose applies to a transposition of any
;; 2 rows.  First note that for 0 <= i and i - 1 < j < n, (transpose i j (n)) is the
;; result of conjugating (transpose i (1- j) (n)) by (transpose (1- j) j (n)):


(local-defthmd nth-conj-adjacent-transpose-rmat
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< i (1- j)) (< j (n))
		(natp k) (< k (n)))
           (equal (nth k (comp-perm (comp-perm (transpose (1- j) j (n))
                                               (transpose i (1- j) (n))
			                       (n))
		                    (transpose (1- j) j (n))
		                    (n)))
		  (nth k (transpose i j (n)))))
  :hints (("Goal" :in-theory (enable transpose-vals)
                  :use ((:instance permp-transpose (n (n)))
		        (:instance permp-transpose (n (n)) (i (1- j)))
		        (:instance permp-transpose (n (n)) (j (1- j))))
                  :cases ((= k i) (= k j) (= k (1- j))))))

(defthmd conj-adjacent-transpose-rmat
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< i (1- j)) (< j (n)))
           (equal (comp-perm (comp-perm (transpose (1- j) j (n))
                                        (transpose i (1- j) (n))
			                (n))
		             (transpose (1- j) j (n))
		             (n))
		  (transpose i j (n))))
  :hints (("Goal" :use ((:instance permp-transpose (n (n)))
		        (:instance permp-transpose (n (n)) (i (1- j)))
		        (:instance permp-transpose (n (n)) (j (1- j)))
			(:instance nth-diff-perm (n (n))
                                                 (x (comp-perm (comp-perm (transpose (1- j) j (n))
                                                                          (transpose i (1- j) (n))
									  (n))
		                                               (transpose (1- j) j (n))
			                                       (n)))
						 (y (transpose i j (n))))
			(:instance nth-conj-adjacent-transpose-rmat
			  (k (nth-diff (comp-perm (comp-perm (transpose (1- j) j (n))
                                                             (transpose i (1- j) (n))
					                     (n))
		                                  (transpose (1- j) j (n))
			                          (n))
				       (transpose i j (n)))))))))

;; The claim follows by induction:

;; We need rmatp versions of permute-comp-perm and nth-permut:

(local-defthm permute-comp-perm-reverse
  (implies (and (rmatp a n n) (posp n)
		(in x (sym n))
		(in y (sym n)))
	   (equal (permute a (comp-perm x y n))
	          (permute (permute a x) y)))
  :hints (("Goal" :in-theory (enable rmatp)
                  :use ((:instance permute-comp-perm (l a))))))

(local-in-theory (disable permute-comp-perm))

(local-defthm nth-permute-rmatp
  (implies (and (rmatp a m n) (posp m) (posp n)
                (in p (sym m))
		(natp k)
		(< k m))
	   (equal (nth k (permute a p))
	          (nth (nth k p) a)))
  :hints (("Goal" :use (len-rmatp (:instance nth-permute (l a)))
                  :in-theory (disable len-rmatp))))

(local-defthm permute-e-rmatp
  (implies (and (rmatp a m n) (posp m) (posp n))
	   (equal (permute a (ninit m))
	          a))
  :hints (("Goal" :use (len-rmatp (:instance permute-e (l a)))
                  :in-theory (disable len-rmatp))))

	         
(local-defthmd rdetn-permute-transpose-step
  (let ((a1 (permute a (transpose (1- j) j (n)))))
    (implies (and (rmatp a (n) (n))
                  (natp i) (natp j) (< i (1- j)) (< j (n))
                  (equal (rdetn (permute a1 (transpose i (1- j) (n))))
                         (r- (rdetn a1))))
	   (equal (rdetn (permute a (transpose i j (n))))
                  (r- (rdetn a)))))
  :hints (("Goal" :use (conj-adjacent-transpose-rmat
                        (:instance permp-transpose (n (n)))
		        (:instance permp-transpose (n (n)) (i (1- j)))
		        (:instance permp-transpose (n (n)) (j (1- j)))			
			(:instance rdetn-permute-adjacent-transpose (i (1- j)))
			(:instance rdetn-permute-adjacent-transpose (i (1- j))
			                                           (a (permute a
								               (comp-perm (transpose (1- j) j (n))
                                                                                          (transpose i (1- j) (n))
			                                                                  (n)))))))))

(local-defun rdetn-permute-transpose-induct (i j a)
  (if (and (natp i) (natp j) (< i (1- j)) (< j (n)))
      (list (rdetn-permute-transpose-induct i (1- j) (permute a (transpose (1- j) j (n)))))
    (list a)))      

(defthmd rdetn-permute-transpose
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< i j) (< j (n)))
	   (equal (rdetn (permute a (transpose i j (n))))
                  (r- (rdetn a))))
  :hints (("Goal" :induct (rdetn-permute-transpose-induct i j a))
          ("Subgoal *1/2" :use (rdetn-permute-adjacent-transpose))
          ("Subgoal *1/1" :use (rdetn-permute-transpose-step
	                        (:instance rmatp-permute (p (TRANSPOSE (+ -1 J) J (N))) (m (n)) (n (n)))
	                        (:instance permp-transpose (n (n)) (i (1- j)))))))
       
;; Now suppose (row i a) = (row j a), where 0 <= i < j < (n).  We would like to show that 
;; (rdetn a) = (r0).  If j = i + 1 ,then apply rdetn-adjacent-equal.  Otherwise, let
;; a' = (permute (transpose (1+ i) j (n)) a).  By nth-permute,

;;   (nth i a') = (nth (nth i (transpose (1+ i) j (n))) a) = (nth i a)

;; and

;;   (nth (1+ i) a') = (nth (nth (1+ i) (transpose (1+ i) j (n))) a) = (nth j a) = (nth i a)

;; and by rdetn-adjacent-equal, (rdetn a') = (r0).  By rdetn-transpose-rows,

;;   (rdetn a) = (r- (rdetn a') = (r- (r0)) = (r0).

;; Thus, rdetn is an alternating function:

(local-defthmd rdetn-alternating-1
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< (1+ i) j) (< j (n)) (= (row i a) (row j a)))
           (equal (rdetn a) (r0)))
  :hints (("Goal" :in-theory (e/d (transpose-vals) (r-r-))
                  :use ((:instance permp-transpose (i (1+ i)) (n (n)))
		        (:instance rdetn-adjacent-equal (a (permute a (transpose (1+ i) j (n)))))
			(:instance rdetn-permute-transpose (i (1+ i)))
			(:instance r-r- (x (rdetn a)))))))

(local-defthmd rdetn-alternating-2
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< i j) (< j (n)) (= (row i a) (row j a)))
           (equal (rdetn a) (r0)))
  :hints (("Goal" :cases ((= j (1+ i)))
                  :use (rdetn-adjacent-equal rdetn-alternating-1))))

(defthmd rdetn-alternating
  (implies (and (rmatp a (n) (n))
                (natp i) (natp j) (< i (n)) (< j (n)) (not (= i j)) (= (row i a) (row j a)))
	   (equal (rdetn a) (r0)))
  :hints (("Goal" :use (rdetn-alternating-2 (:instance rdetn-alternating-2 (i j) (j i))))))

;; We shall require a generalization of rdetn-transpose-rows to arbitrary permutations.
;; First note that rdetn-permute-transpose may be restated as follows:

(local-defthmd rdetn-permute-transp
  (implies (and (rmatp a (n) (n))
                (transp p (n)))
	   (equal (rdetn (permute a p))
	          (r- (rdetn a))))
  :hints (("Goal" :in-theory (enable transp)
                  :use ((:instance rdetn-permute-transpose (i (least-moved p)) (j (nth (least-moved p) p)))
		        (:instance least-moved-transpose (n (n)) (i (least-moved p)) (j (nth (least-moved p) p)))))))

(include-book "arithmetic-5/top" :dir :system)

(local-defun rdetn-permute-trans-list-p-induct (a l)
  (if (consp l)
      (list (rdetn-permute-trans-list-p-induct (permute a (car l)) (cdr l)))
    (list a l)))

(local-defthmd rdetn-permute-trans-list-p
  (implies (and (rmatp a (n) (n))
                (trans-list-p l (n)))
	   (equal (rdetn (permute a (comp-perm-list l (n))))
	          (if (evenp (len l))
		      (rdetn a)
		    (r- (rdetn a)))))
  :hints (("Goal" :induct (rdetn-permute-trans-list-p-induct a l))
          ("Subgoal *1/1" :use ((:instance permp-transp (n (n)) (p (car l)))
                                (:instance permp-trans-list (n (n)) (l (cdr l)))
				(:instance rdetn-permute-transp (p (car l)))))))

(defthmd rdetn-permute-rows
  (implies (and (rmatp a (n) (n))
                (in p (sym (n))))
	   (equal (rdetn (permute a p))
	          (if (even-perm-p p (n))
		      (rdetn a)
		    (r- (rdetn a)))))
  :hints (("Goal" :in-theory (enable even-perm-p)
                  :use ((:instance parity-0-1 (n (n)))
		        (:instance parity-len-trans-list (n (n)))
			(:instance trans-list-p-trans-list (n (n)))
			(:instance perm-prod-trans (n (n)))
			(:instance rdetn-permute-trans-list-p (l (trans-list p (n))))))))

;; Since rdet satisfies the constraints on rdetn, this applies to rdet by functional
;; instantiation:

(local-defthmd rdet-permute-rows-n
  (implies (and (rmatp a (n) (n))
                (in p (sym (n))))
	   (equal (rdet (permute a p) (n))
	          (if (even-perm-p p (n))
		      (rdet a (n))
		    (r- (rdet a (n))))))
  :hints (("Goal" :use ((:functional-instance rdetn-permute-rows
			  (rdetn (lambda (a) (if (and (rmatp a (n) (n)) (in p (sym (n)))) (rdet a (n)) (rdetn a)))))))
	  ("Subgoal 3" :use (rdetn-adjacent-equal (:instance rdet-alternating (j (1+ i)) (n (n)))))
	  ("Subgoal 2" :use (rdetn-n-linear (:instance rdet-n-linear (n (n)))))))

(defthmd rdet-permute-rows
  (implies (and (rmatp a n n) (posp n)
                (in p (sym n)))
	   (equal (rdet (permute a p) n)
	          (if (even-perm-p p n)
		      (rdet a n)
		    (r- (rdet a n)))))
  :hints (("Goal" :use ((:functional-instance rdet-permute-rows-n
                          (n (lambda () (if (posp n) n (n)))))))))

;; The proof of rdet-unique is based on lists of k-tuples of natural numbers less than (n),
;; where k <= (n):

(defun tuplep (x k)
  (if (zp k)
      (null x)
    (and (consp x)
         (natp (car x))
         (< (car x) (n))
	 (tuplep (cdr x) (1- k)))))

(local-defthm true-listp-tuplep
  (implies (tuplep x k)
           (true-listp x)))

(local-defthm len-tuplep
  (implies (and (natp k) (tuplep x k))
           (equal (len x) k)))

(defun tuple-list-p (l k)
  (if (consp l)
      (and (tuplep (car l) k)
           (tuple-list-p (cdr l) k))
    (null l)))

(local-defthm member-tuple-list-p
  (implies (and (tuple-list-p l k) (member x l))
           (tuplep x k)))

;; We recursively define a dlist containing all such k-tuples:

(defun extend-tuple-aux (x m) 
  (if (consp m)
      (cons (append x (list (car m)))
            (extend-tuple-aux x (cdr m)))
    ()))

(defund extend-tuple (x)
  (extend-tuple-aux x (ninit (n))))

(defun extend-tuples (l)
  (if (consp l)
      (append (extend-tuple (car l))
              (extend-tuples (cdr l)))
    ()))

(local-defun tuplep-append-induct (x k)
  (if (zp k)
      (list x k)
    (list (tuplep-append-induct (cdr x) (1- k)))))

(local-defthm tuplep-append
  (implies (and (posp k) (tuplep x (1- k)) (member j (ninit (n))))
           (tuplep (append x (list j)) k))
  :hints (("Goal" :induct (tuplep-append-induct x k))
          ("Subgoal *1/2" :use ((:instance member-ninit (n (n)) (x j))))))

(local-defthm tuple-list-p-extend-tuple-aux
  (implies (and (posp k) (tuplep x (1- k)) (sublistp m (ninit (n))))
           (tuple-list-p (extend-tuple-aux x m) k)))

(local-defthm tuple-list-p-extend-tuple
  (implies (and (posp k) (tuplep x (1- k)))
           (tuple-list-p (extend-tuple x) k))
  :hints (("Goal" :in-theory (enable extend-tuple))))

(local-defthm tuple-list-p-append
  (implies (and (natp k) (tuple-list-p l k) (tuple-list-p m k))
           (tuple-list-p (append l m) k)))

(local-defthm tuple-list-p-extend-tuples
  (implies (and (posp k) (tuple-list-p l (1- k)))
           (tuple-list-p (extend-tuples l) k)))

(defun all-tuples (k)
  (if (zp k)
      (list ())
    (extend-tuples (all-tuples (1- k)))))

(local-defthm tuple-list-p-all-tuples
  (implies (and (natp k) (<= k (n)))
           (tuple-list-p (all-tuples k) k)))

(local-defun equal-append-list-induct (x y)
  (if (consp x)
      (list (equal-append-list-induct (cdr x) (cdr y)))
    (list x y)))

(local-defthm equal-append-list
  (implies (and (true-listp x) (true-listp y))
           (iff (equal (append x (list i)) (append y (list j)))
	        (and (equal x y) (equal i j))))
  :hints (("Goal" :induct (equal-append-list-induct x y))))

(local-defthm member-append-extend-tuple-aux
  (implies (and (true-listp x) (true-listp y))
           (iff (member (append x (list j)) (extend-tuple-aux y l))
                (and (equal x y) (member j l))))
  :hints (("Goal" :induct (len l))))

(local-defthm dlistp-extend-tuple-aux
  (implies (and (true-listp x) (dlistp m))
           (dlistp (extend-tuple-aux x m))))

(local-defthm dlistp-extend-tuple
  (implies (and (posp k) (tuplep x (1- k)))
           (dlistp (extend-tuple x)))
  :hints (("Goal" :in-theory (enable extend-tuple))))

(local-defthm member-append-extend-tuple
 (implies (and (true-listp x) (true-listp y))
           (iff (member (append x (list j)) (extend-tuple y))
                (and (equal x y) (member j (ninit (n))))))
  :hints (("Goal" :in-theory (enable extend-tuple))))

(local-defthm member-append-extend-tuples
 (implies (and (true-listp x) (tuple-list-p l k))
           (iff (member (append x (list j)) (extend-tuples l))
                (and (member x l) (member j (ninit (n)))))))

(local-defthm disjointp-extend-tuple-aux
  (implies (and (true-listp x) (tuple-list-p l k) (not (member x l)))
           (disjointp (extend-tuple-aux x m) (extend-tuples l)))
  :hints (("Goal" :induct (len m))))

(local-defthm disjointp-extend-tuple
  (implies (and (true-listp x) (tuple-list-p l k) (not (member x l)))
           (disjointp (extend-tuple x) (extend-tuples l)))
  :hints (("Goal" :in-theory (enable extend-tuple))))

(local-defthm dlistp-extend-tuples
  (implies (and (posp k) (tuple-list-p l (1- k)) (dlistp l))
           (dlistp (extend-tuples l)))
  :hints (("Subgoal *1/3" :use ((:instance dlistp-append (l (EXTEND-TUPLE (CAR L)))
                                                         (m (EXTEND-TUPLES (CDR L))))))))

(defthm dlistp-all-tuples
  (implies (and (natp k) (<= k (n)))
           (dlistp (all-tuples k))))

(local-defun firstn (n x)
  (if (zp n)
      ()
    (cons (car x) (firstn (1- n) (cdr x)))))

(local-defthmd tuplep-decomp
  (implies (and (posp k) (tuplep x k))
           (and (equal (append (firstn (1- k) x) (last x)) x)
	        (tuplep (firstn (1- k) x) (1- k))
		(member (car (last x)) (ninit (n))))))

(local-defun tuplep-member-all-tuples-induct (x k)
  (if (zp k)
      (list x k)
    (list (tuplep-member-all-tuples-induct (firstn (1- k) x) (1- k)))))

(local-defthmd list-car-last
  (implies (and (consp x) (true-listp x))
           (equal (list (car (last x)))
	          (last x))))

(local-defthm tuplep-member-all-tuples
  (implies (and (natp k) (<= k (n)) (tuplep x k))
           (member x (all-tuples k)))
  :hints (("Goal" :induct (tuplep-member-all-tuples-induct x k))
          ("Subgoal *1/2" :use (tuplep-decomp list-car-last
	                        (:instance member-append-extend-tuples (x (firstn (1- k) x))
				                                       (k (1- k))
				                                       (j (car (last x)))
								       (l (all-tuples (1- k))))))))

(defthmd member-all-tuples
  (implies (and (natp k) (<= k (n)))
           (iff (member x (all-tuples k))
	        (tuplep x k)))
  :hints (("Goal" :use (tuplep-member-all-tuples
                        (:instance member-tuple-list-p (l (all-tuples k)))))))

;; Let a be a fixed (n)x(n) matrix.  We associate a value with a k-tuple x as follows:

(defun extract-entries (x a)
  (if (consp x)
      (cons (nth (car x) (car a))
            (extract-entries (cdr x) (cdr a)))
    ()))

(local-defun extract-entries-induct (x k a m)
  (if (consp x)
      (list (extract-entries-induct (cdr x) (1- k) (cdr a) (1- m)))
    (list x k a m)))

(local-defthm rlistnp-extract-entries
  (implies (and (natp k) (tuplep x k)
                (natp m) (<= k m) (<= m (n)) (rmatp a m (n)))
           (rlistnp (extract-entries x a) k))
  :hints (("Goal" :induct (extract-entries-induct x k a m) :in-theory (enable rmatp))))

(defun runits (x)
  (if (consp x)
      (cons (runit (car x) (n))
            (runits (cdr x)))
    ()))

(local-defthm len-runits
  (equal (len (runits x))
         (len x)))

(defun reval-tuple (x k a)
  (r* (rlist-prod (extract-entries x a))
      (rdetn (append (runits x) (nthcdr k a)))))

(local-defthm rmatp-nthcdr
  (implies (and (rmatp a m n) (natp k) (<= k m))
           (rmatp (nthcdr k a) (- m k) n))
  :hints (("Goal" :in-theory (enable rmatp))))

(local-defthm rmatp-append-runits-nthcdr-1
  (implies (and (rmatp a (n) (n)) (natp k) (<= k (n))
                (natp j) (tuplep x j))
	   (rmatp (append (runits x) (nthcdr k a)) (+ j (- (n) k)) (n)))
  :hints (("Goal" :induct (tuplep x j) :in-theory (enable rmatp))))

(local-defthm rmatp-append-runits-nthcdr
  (implies (and (rmatp a (n) (n)) (natp k) (<= k (n))
                (tuplep x k))
	   (rmatp (append (runits x) (nthcdr k a)) (n) (n)))
  :hints (("Goal" :use ((:instance rmatp-append-runits-nthcdr-1 (j k))))))

(defthm rp-reval-tuple
  (implies (and (rmatp a (n) (n)) (natp k) (<= k (n)) (tuplep x k))
           (rp (reval-tuple x k a)))
  :hints (("Goal" :use (rmatp-append-runits-nthcdr (:instance rlistnp-extract-entries (m (n)))))))

;; The sum of the values of a list of k-tuples: 

(defun rsum-tuples (l k a)
  (if (consp l)
      (r+ (reval-tuple (car l) k a)
	  (rsum-tuples (cdr l) k a))
    (r0)))

(defthm fp-rsum-tuples
  (implies (and (rmatp a (n) (n)) (natp k) (<= k (n)) (tuple-list-p l k))
           (rp (rsum-tuples l k a)))
  :hints (("Goal" :in-theory (disable reval-tuple))))

;; We would like to compute (rsum-tuples (all-tuples k) k a).  The case k = 0 is trivial:

(defthmd reval-tuple-nil
  (implies (rmatp a (n) (n))
           (equal (reval-tuple () 0 a)
	          (rdetn a))))

(defthm rsum-0-tuples
  (implies (rmatp a (n) (n))
           (equal (rsum-tuples (all-tuples 0) 0 a)
	          (rdetn a))))

;; We shall prove, as a consequence of n-linearity of rdetn, that incrementing k does not change the value of the sum.

;; If (rlistnp r (n)), We may think of r as a sum of multiples of unit vectors.  Given a sublist l of (ninit (n)),
;; (rsum-select l n) is the sum of the subset of these multiples corresponding to the members of l:

(defun rsum-select (l r)
  (if (consp l)
      (rlist-add (rlist-scalar-mul (nth (car l) r) (runit (car l) (n)))
                 (rsum-select (cdr l) r))
    (rlistn0 (n))))

(local-defthm rlistnp-rsum-select
  (implies (and (rlistnp r (n)) (sublistp l (ninit (n))))
           (rlistnp (rsum-select l r) (n)))
  :hints (("Subgoal *1/2" :use ((:instance member-ninit (x (car l)) (n (n)))))))

(local-defthm nth-rsum-select
  (implies (and (rlistnp r (n))
                (sublistp l (ninit (n)))
		(dlistp l)
		(natp k)
		(< k (n)))
	   (equal (nth k (rsum-select l r))
	          (if (member k l) (nth k r) (r0))))
  :hints (("Goal" :induct (len l)) 
          ("Subgoal *1/1" :use ((:instance member-ninit (n (n)) (x (car l)))
			        (:instance nth-rlist-add (i (car l)) (n (n))
				                         (x (RLIST-SCALAR-MUL (NTH k R) (RUNIT k (N))))
							 (y (RSUM-SELECT (CDR L) R)))
			        (:instance nth-rlist-scalar-mul (i (car l)) (n (n))
				                                (c (NTH (CAR L) R))
                                                                (x  (RUNIT (CAR L) (N))))
				(:instance nth-rlist-add (i k) (n (n))
				                         (x (RLIST-SCALAR-MUL (NTH (car l) R) (RUNIT (car l) (N))))
							 (y (RSUM-SELECT (CDR L) R)))							   
				(:instance nth-rlist-scalar-mul (i k) (n (n))
				                                (c (NTH (CAR L) R))
                                                                (x  (RUNIT (CAR L) (N))))))))

(local-defthm nth-rsum-select-ninit
  (implies (and (rlistnp r (n))
		(natp k)
		(< k (n)))
	   (equal (nth k (rsum-select (ninit (n)) r))
	          (nth k r)))
  :hints (("Goal" :use ((:instance nth-rsum-select (l (ninit (n))))
                        (:instance member-ninit (x k) (n (n)))))))		

(defthm rsum-select-ninit
  (implies (rlistnp r (n))
           (equal (rsum-select (ninit (n)) r)
	          r))
  :hints (("Goal" :in-theory (disable len-rlist rlistnp-rsum-select)
                  :use ((:instance nth-diff-diff (x (rsum-select (ninit (n)) r)) (y r))
                        (:instance nth-rsum-select-ninit (k (nth-diff (rsum-select (ninit (n)) r) r)))
			(:instance rlistnp-rsum-select (l (ninit (n))))
			(:instance len-rlist (n (n)) (x r))
			(:instance len-rlist (n (n)) (x (rsum-select (ninit (n)) r)))))))

(local-defthmd rsum-tuples-extend-tuple-1
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(sublistp l (ninit (n)))
		(consp l))
	   (equal (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
                  (r+ (reval-tuple (append x (list (car l))) (1+ k) a)
		      (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)))))

(local-defthmd rsum-tuples-extend-tuple-2
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n)) (tuplep x k)
		(natp i) (< i (n)))
	   (equal (reval-tuple (append x (list i)) (1+ k) a)
                  (r* (rlist-prod (extract-entries (append x (list i)) a))
		      (rdetn (append (runits (append x (list i))) (nthcdr (1+ k) a)))))))

(local-defthmd rsum-tuples-extend-tuple-3
  (implies (and (natp k) (natp m) (< k m) (<= m (n))
                (tuplep x k) (rmatp a m (n))
		(natp i) (< i (n)))
	   (equal (rlist-prod (extract-entries (append x (list i)) a))
	          (r* (rlist-prod (extract-entries x a))
		      (nth i (nth k a)))))
  :hints (("Goal" :induct (extract-entries-induct x k a m))
          ("Subgoal *1/2" :in-theory (enable rmatp)
	                  :expand ((nth 0 a))
			  :use ((:instance rp-entry (n (n)) (i 0) (j i))))
	  ("Subgoal *1/1" :expand ((nth 0 a))
	                  :in-theory (e/d (rmatp) (rlistnp-extract-entries))
	                  :use ((:instance rp-entry (n (n)) (i k) (j i))
	                        (:instance rp-entry (n (n)) (i 0) (j (car x)))
				(:instance nth (n k) (l a))
				(:instance rlistnp-extract-entries (x (cdr x)) (k (1- k)) (a (cdr a)) (m (1- m)))
				(:instance r*assoc (x (NTH (CAR X) (CAR A)))
                                                   (y (RLIST-PROD (EXTRACT-ENTRIES (CDR X) (CDR A))))
						   (z (NTH I (NTH K A))))))))

(local-defthmd rsum-tuples-extend-tuple-4
  (implies (and (natp k) (< k (n))
                (tuplep x k) (rmatp a (n) (n))
		(natp i) (< i (n)))
	   (equal (rlist-prod (extract-entries (append x (list i)) a))
	          (r* (rlist-prod (extract-entries x a))
		      (nth i (nth k a)))))
  :hints (("Goal" :use ((:instance rsum-tuples-extend-tuple-3 (m (n)))))))

(local-defthmd rsum-tuples-extend-tuple-5
  (implies (and (natp k) (<= k (n)) (tuplep x k)
		(natp i) (< i (n)))
	   (equal (runits (append x (list i)))
	          (append (runits x) (list (runit i (n)))))))

(local-defthm nth-append
  (implies (natp j)
           (equal (nth j (append l m))
	          (if (< j (len l))
		      (nth j l)
		    (nth (- j (len l)) m))))
  :hints (("Goal" :in-theory (enable nth))))

(local-defthm len-nthcdr
  (implies (and (natp j) (<= j (len l)))
           (equal (len (nthcdr j l))
	          (- (len l) j))))

(local-defthmd len-append-runits
  (implies (and (natp k) (< k (n))
                (tuplep x k) (rmatp a (n) (n))
		(natp i) (< i (n)))
	   (equal (len (append (runits x) (nthcdr k a)))
	          (n))))

(local-defthmd cdr-nthcdr
  (implies (natp j)
           (equal (nthcdr k (cdr a))
	          (cdr (nthcdr k a)))))

(local-defthmd rsum-tuples-extend-tuple-6
  (implies (and (natp k) (< k (n))
                (tuplep x k) (rmatp a (n) (n))
		(natp i) (< i (n))
		(natp j) (< j (n)))
	   (equal (nth j (append (append (runits x) (list (runit i (n))))
	                         (nthcdr (1+ k) a)))
		  (nth j (replace-row (append (runits x) (nthcdr k a)) k (runit i (n))))))
  :hints (("Goal" :cases ((= j k))
                  :expand ((NTH (+ J (- K)) (NTHCDR K A)))
                  :use (cdr-nthcdr len-append-runits))))

(local-defthmd true-listp-nthcdr
  (implies (true-listp l)
           (true-listp (nthcdr j l))))

(local-defthm true-listp-append
  (implies (true-listp m)
           (true-listp (append l m))))

(local-defthmd rsum-tuples-extend-tuple-7
  (implies (and (natp k) (< k (n))
                (tuplep x k) (rmatp a (n) (n))
		(natp i) (< i (n)))
           (TRUE-LISTP (APPEND (APPEND (RUNITS X) (LIST (RUNIT I (N))))
                               (NTHCDR K (CDR A)))))
  :hints (("Goal" :expand ((rmatp a (n) (n)))
                  :use ((:instance true-listp-nthcdr (j k) (l (cdr a)))))))

(local-defthm true-listp-replace-row
  (implies (true-listp a)
           (true-listp (replace-row a j r)))
  :hints (("Goal" :in-theory (enable replace-row))))

(local-defthmd rsum-tuples-extend-tuple-8
  (implies (and (natp k) (< k (n))
                (rmatp a (n) (n)))
           (TRUE-LISTP (REPLACE-ROW (APPEND (RUNITS X) (NTHCDR K A)) K (RUNIT I (N)))))
  :hints (("Goal" :in-theory (disable true-listp-nthcdr true-listp-replace-row)
                  :use ((:instance true-listp-replace-row (a (APPEND (RUNITS X) (NTHCDR K A))) (j k) (r (RUNIT I (N))))
		        (:instance true-listp-nthcdr (j k) (l a))))))

(local-defthmd rsum-tuples-extend-tuple-9
  (implies (and (natp k) (< k (n))
                (tuplep x k) (rmatp a (n) (n))
		(natp i) (< i (n)))
           (equal (append (append (runits x) (list (runit i (n))))
	                  (nthcdr (1+ k) a))
		  (replace-row (append (runits x) (nthcdr k a)) k (runit i (n)))))
  :hints (("Goal" :in-theory (disable len-rmatp)
                  :use (rsum-tuples-extend-tuple-7 rsum-tuples-extend-tuple-8 len-append-runits
		        (:instance len-rmatp (m (n)) (n (n)))
		        (:instance nth-diff-diff (x (append (append (runits x) (list (runit i (n)))) (nthcdr (1+ k) a)))
                                                 (y (replace-row (append (runits x) (nthcdr k a)) k (runit i (n)))))
			(:instance rsum-tuples-extend-tuple-6
			  (j (nth-diff (append (append (runits x) (list (runit i (n)))) (nthcdr (1+ k) a))
			               (replace-row (append (runits x) (nthcdr k a)) k (runit i (n))))))))))

(local-defthmd rsum-tuples-extend-tuple-10
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n)) (tuplep x k)
		(natp i) (< i (n)))
	   (equal (reval-tuple (append x (list i)) (1+ k) a)
                  (r* (r* (rlist-prod (extract-entries x a))
		          (nth i (nth k a)))
		      (rdetn (replace-row (append (runits x) (nthcdr k a)) k (runit i (n)))))))
  :hints (("Goal" :use (rsum-tuples-extend-tuple-2 rsum-tuples-extend-tuple-4
                        rsum-tuples-extend-tuple-5 rsum-tuples-extend-tuple-9))))

(local-defthmd rsum-tuples-extend-tuple-11
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n)) (tuplep x k)
		(natp i) (< i (n)))
	   (equal (reval-tuple (append x (list i)) (1+ k) a)
                  (r* (rlist-prod (extract-entries x a))
		      (r* (nth i (nth k a))
		          (rdetn (replace-row (append (runits x) (nthcdr k a)) k (runit i (n))))))))
  :hints (("Goal" :in-theory (disable rlistnp-extract-entries)
                  :use (rsum-tuples-extend-tuple-10
                        (:instance rlistnp-extract-entries (m (n)))
			(:instance rp-entry (m (n)) (n (n)) (i k) (j i))
                        (:instance r*assoc (x (rlist-prod (extract-entries x a)))
			                   (y (nth i (nth k a)))
					   (z (rdetn (replace-row (append (runits x) (nthcdr k a)) k (runit i (n))))))))))

(local-defthmd rsum-tuples-extend-tuple-12
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(sublistp l (ninit (n))))
	   (equal (reval-tuple x k (replace-row a k (rsum-select l (nth k a))))
	          (r* (rlist-prod (extract-entries x (replace-row a k (rsum-select l (nth k a)))))
		      (rdetn (append (runits x) (nthcdr k (replace-row a k (rsum-select l (nth k a))))))))))

(local-defthmd rsum-tuples-extend-tuple-13
  (implies (and (rmatp a m (n)) (natp m) (<= m (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (extract-entries x (replace-row a k r))
	          (extract-entries x a)))
  :hints (("Goal" :induct (extract-entries-induct x k a m) :in-theory (enable rmatp replace-row))))

(local-defthmd rsum-tuples-extend-tuple-14
  (implies (and (rmatp a m (n)) (natp m) (<= m (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (reval-tuple x k (replace-row a k (rsum-select l (nth k a))))
	          (r* (rlist-prod (extract-entries x a))
		      (rdetn (append (runits x) (nthcdr k (replace-row a k (rsum-select l (nth k a)))))))))
  :hints (("Goal" :use (rsum-tuples-extend-tuple-12
                        (:instance rsum-tuples-extend-tuple-13 (r (rsum-select l (nth k a))))))))

(local-defthm car-nthcdr
  (implies (< k (len l))
           (equal (CAR (NTHCDR K L)) (NTH K L)))
  :hints (("Goal" :in-theory (enable nth))))

(local-defthm consp-nthcdr
  (implies (and (natp k) (< k (len l)))
           (consp (nthcdr k l))))

(local-defun nth-nthcdr-induct (j k)
  (if (zp j)
      (list j k)
    (nth-nthcdr-induct (1- j) (1+ k))))

(local-defthm nth-nthcdr
  (implies (and (natp j) (natp k) (< (+ j k) (len l)))
           (equal (nth j (nthcdr k l))
	          (nth (+ j k) l)))
  :hints (("Goal" :induct (nth-nthcdr-induct j k))
          ("Subgoal *1/2" :in-theory (e/d (cdr-nthcdr) (len-nthcdr))
	                  :use ((:instance len-nthcdr (j k)))
	                  :expand ((NTH J (NTHCDR K L))))
	  ("Subgoal *1/1" :expand ((NTH 0 (NTHCDR K L))))))

(local-defthmd rsum-tuples-extend-tuple-15
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(natp j) (< j (n)))
	   (equal (nth j (append (runits x) (nthcdr k (replace-row a k r))))
	          (nth j (replace-row (append (runits x) (nthcdr k a)) k r))))
  :hints (("Goal" :cases ((= k j))
                  :in-theory (disable len-rmatp rmatp-append-runits-nthcdr)
                  :use (rmatp-append-runits-nthcdr
		        (:instance len-rmatp (m (n)) (n (n)))
		        (:instance len-rmatp (m (n)) (n (n)) (a (APPEND (RUNITS X) (NTHCDR K A))))))))

(local-defthmd rsum-tuples-extend-tuple-16
  (implies (and (natp k) (< k (n))
                (rmatp a (n) (n)))
           (TRUE-LISTP (REPLACE-ROW (APPEND (RUNITS X) (NTHCDR K A)) K r)))
  :hints (("Goal" :in-theory (disable true-listp-nthcdr true-listp-replace-row)
                  :use ((:instance true-listp-replace-row (a (APPEND (RUNITS X) (NTHCDR K A))) (j k))
		        (:instance true-listp-nthcdr (j k) (l a))))))

(local-defthmd rsum-tuples-extend-tuple-17
  (implies (and (natp k) (< k (n))
                (rmatp a (n) (n)))
           (TRUE-LISTP (APPEND (RUNITS X) (NTHCDR K (replace-row a k r)))))
  :hints (("Goal" :in-theory (disable true-listp-nthcdr true-listp-replace-row)
                  :use ((:instance true-listp-replace-row (j k))
		        (:instance true-listp-nthcdr (j k) (l (replace-row a k r)))))))

(local-defthmd rsum-tuples-extend-tuple-18
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
           (equal (len (append (runits x) (nthcdr k (replace-row a k r))))
	          (n)))
  :hints (("Goal" :in-theory (enable len-append-runits))))

(local-defthmd rsum-tuples-extend-tuple-19
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
           (equal (len (replace-row (append (runits x) (nthcdr k a)) k r))
	          (n)))
  :hints (("Goal" :in-theory (enable len-append-runits))))

(local-defthmd rsum-tuples-extend-tuple-20
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
          (equal (append (runits x) (nthcdr k (replace-row a k r)))
	         (replace-row (append (runits x) (nthcdr k a)) k r)))
  :hints (("Goal" :use (rsum-tuples-extend-tuple-16 rsum-tuples-extend-tuple-17 rsum-tuples-extend-tuple-18
		        rsum-tuples-extend-tuple-19
                        (:instance nth-diff-diff (x (append (runits x) (nthcdr k (replace-row a k r))))
                                                 (y (replace-row (append (runits x) (nthcdr k a)) k r)))
			(:instance rsum-tuples-extend-tuple-15
			   (j (nth-diff (append (runits x) (nthcdr k (replace-row a k r)))
			                (replace-row (append (runits x) (nthcdr k a)) k r))))))))

(local-defthmd rsum-tuples-extend-tuple-21
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (reval-tuple x k (replace-row a k (rsum-select l (nth k a))))
	          (r* (rlist-prod (extract-entries x a))
		      (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select l (nth k a)))))))
  :hints (("Goal" :use ((:instance rsum-tuples-extend-tuple-14 (m (n)))
                        (:instance rsum-tuples-extend-tuple-20 (r (rsum-select l (nth k a))))))))

(local-defthmd rsum-tuples-extend-tuple-22
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n))))
           (equal (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
                  (r+ (reval-tuple (append x (list (car l))) (1+ k) a)
		      (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)))))

(local-defthmd rsum-tuples-extend-tuple-23
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n)))
	        (equal (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
		       (reval-tuple x k (replace-row a k (rsum-select (cdr l) (nth k a))))))
	   (equal (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (r+ (r* (rlist-prod (extract-entries x a))
		          (r* (nth (car l) (nth k a))
		              (rdetn (replace-row (append (runits x) (nthcdr k a)) k (runit (car l) (n))))))
		      (r* (rlist-prod (extract-entries x a))
		          (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select (cdr l) (nth k a))))))))
  :hints (("Goal" :use (rsum-tuples-extend-tuple-22
                        (:instance rsum-tuples-extend-tuple-21 (l (cdr l)))
                        (:instance rsum-tuples-extend-tuple-11 (i (car l)))
			(:instance member-ninit (x (car l)) (n (n)))))))

(local-defthmd rsum-tuples-extend-tuple-24
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n))))
	   (equal (r+ (r* (rlist-prod (extract-entries x a))
		          (r* (nth (car l) (nth k a))
		              (rdetn (replace-row (append (runits x) (nthcdr k a)) k (runit (car l) (n))))))
		      (r* (rlist-prod (extract-entries x a))
		          (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select (cdr l) (nth k a))))))
		  (r* (rlist-prod (extract-entries x a))
		      (r+ (r* (nth (car l) (nth k a))
		              (rdetn (replace-row (append (runits x) (nthcdr k a)) k (runit (car l) (n)))))
			  (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select (cdr l) (nth k a))))))))
  :hints (("Goal" :in-theory (disable rlistnp-extract-entries rmatp-append-runits-nthcdr)
                  :use (rmatp-append-runits-nthcdr
                        (:instance member-ninit (x (car l)) (n (n)))
			(:instance rlistnp-row (i k) (m (n)) (n (n)))
			(:instance rp-entry (m (n)) (n (n)) (i k) (j (car l)))
			(:instance rlistnp-extract-entries (m (n)))
                        (:instance rdist (x (rlist-prod (extract-entries x a)))
			                 (y (r* (nth (car l) (nth k a))
		                                (rdetn (replace-row (append (runits x) (nthcdr k a)) k (runit (car l) (n))))))
					 (z (rdetn (replace-row (append (runits x) (nthcdr k a)) k
								(rsum-select (cdr l) (nth k a))))))))))

(local-defthmd rsum-tuples-extend-tuple-25
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n))))
	   (equal (r+ (r* (nth (car l) (nth k a))
		          (rdetn (replace-row (append (runits x) (nthcdr k a)) k (runit (car l) (n)))))
		      (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select (cdr l) (nth k a)))))
		  (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select l (nth k a))))))
  :hints (("Goal" :in-theory (disable rlistnp-extract-entries rmatp-append-runits-nthcdr)
                  :use (rmatp-append-runits-nthcdr
                        (:instance member-ninit (x (car l)) (n (n)))
			(:instance rlistnp-row (i k) (m (n)) (n (n)))
			(:instance rp-entry (m (n)) (n (n)) (i k) (j (car l)))
			(:instance rdetn-n-linear (a (append (runits x) (nthcdr k a))) (i k) (c (nth (car l) (nth k a)))
			                         (x (runit (car l) (n)))
						 (y (rsum-select (cdr l) (nth k a))))))))

(local-defthmd rsum-tuples-extend-tuple-26
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n)))
	        (equal (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
		       (reval-tuple x k (replace-row a k (rsum-select (cdr l) (nth k a))))))
	   (equal (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (r* (rlist-prod (extract-entries x a))
		      (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select l (nth k a)))))))
  :hints (("Goal" :use (rsum-tuples-extend-tuple-23 rsum-tuples-extend-tuple-24 rsum-tuples-extend-tuple-25))))

(local-defthmd rsum-tuples-extend-tuple-27
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n)))
	        (equal (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
		       (reval-tuple x k (replace-row a k (rsum-select (cdr l) (nth k a))))))
	   (equal (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (r* (rlist-prod (extract-entries x a))
		      (rdetn (append (runits x) (nthcdr k (replace-row a k (rsum-select l (nth k a)))))))))
  :hints (("Goal" :use (rsum-tuples-extend-tuple-26
                        (:instance rsum-tuples-extend-tuple-20 (r (rsum-select l (nth k a))))))))

(local-defthmd rsum-tuples-extend-tuple-28
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n)))
	        (equal (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
		       (reval-tuple x k (replace-row a k (rsum-select (cdr l) (nth k a))))))
	   (equal (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (reval-tuple x k (replace-row a k (rsum-select l (nth k a))))))
  :hints (("Goal" :in-theory (enable rsum-tuples-extend-tuple-13)
                  :use (rsum-tuples-extend-tuple-27))))

;; We need this basic result:

(local-defthmd rdetn-replace-0-1
  (implies (and (rmatp a (n) (n)) (natp k) (< k (n)))
           (equal (r+ (rdetn (replace-row a k (rlistn0 (n))))
	              (rdetn (replace-row a k (rlistn0 (n)))))
		  (rdetn (replace-row a k (rlistn0 (n))))))
  :hints (("Goal" :in-theory (disable rlist-scalar-mul-r1)
                  :use ((:instance rdetn-n-linear (i k) (c (r1)) (x (rlistn0 (n))) (y (rlistn0 (n))))
                        (:instance rlist-scalar-mul-r1 (n (n)) (x (rlistn0 (n))))))))

(local-defthmd rdetn-replace-0
  (implies (and (rmatp a (n) (n)) (natp k) (< k (n)))
           (equal (rdetn (replace-row a k (rlistn0 (n))))
	          (r0)))
  :hints (("Goal" :use (rdetn-replace-0-1 (:instance r+left-cancel (x (rdetn (replace-row a k (rlistn0 (n)))))
                                                           (z (rdetn (replace-row a k (rlistn0 (n)))))
							   (y (r0)))))))

;; Prove by induction on l, using rdetn-replace-0 and rsum-tuples-extend-tuple-26:

(local-defthmd rsum-tuples-extend-tuple-29
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(sublistp l (ninit (n))))
	   (equal (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (reval-tuple x k (replace-row a k (rsum-select l (nth k a))))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/2" :in-theory (enable rsum-tuples-extend-tuple-20)
	                  :use ((:instance rdetn-replace-0 (a (APPEND (RUNITS X) (NTHCDR K A))))
			        (:instance rlistnp-extract-entries (m (n)) (a (REPLACE-ROW A K (RLISTN0 (N)))))))
	  ("Subgoal *1/1" :use (rsum-tuples-extend-tuple-28))))


(local-defthm rsum-select-ninit
  (implies (rlistnp r (n))
           (equal (rsum-select (ninit (n)) r)
	          r)))

;; Substitute (ninit (n)) for l:

(local-defthmd rsum-tuples-extend-tuple-30
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (rsum-tuples (extend-tuple-aux x (ninit (n))) (1+ k) a)
		  (reval-tuple x k (replace-row a k (nth k a)))))
  :hints (("Goal" :in-theory (disable rsum-tuples reval-tuple)
                  :use ((:instance rsum-tuples-extend-tuple-29 (l (ninit (n))))
                        (:instance rlistnp-row (n (n)) (m (n)) (i k))))))

;; We shall derive a formula for (rsum-tuples (extend-tuple x) (1+ k) a).

;; Let l be a sublist of (ninit (n)).  According to the definitions of rsum-tuples and extend-tuple-aux,

;;   (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
;;     = (r+ (reval-tuple (append x (list (car l))) (1+ k) a)
;;             (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)),

;; where
  
;;   (reval-tuple (append x (list i)) (1+ k) a)
;;     = (r* (rlist-prod (extract-entries (append x (list i)) a))
;;           (rdetn (append (runits (append x (list i))) (nthcdr (1+ k) a))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (r* (nth i (nth k a))
;;               (rdetn (append (append (runits x) (list (unit i (n)))) (nthcdr (1+ k) a)))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (r* (nth i (nth k a))
;;	         (rdetn (replace-row (append (runits x) (nthcdr k a) k (unit i (n)))))))

;; and

;;   (rsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
;;     = (reval-tuple x k (replace-row a k (rsum-select (cdr l) (nth k a))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (rdetn (append (runits x) (nthcdr k (replace-row a k (rsum-select (cdr l) (nth k a)))))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select (cdr l) (nth k a))))).

;; Thus, by rdetn-n-linear,

;;   (rsum-tuples (extend-tuple-aux x l) (1+ k) a)
;;     = (r* (rlist-prod (extract-entries x a))
;;           (rdetn (replace-row (append (runits x) (nthcdr k a)) k (rsum-select l (nth k a)))))
;;     = (r* (rlist-prod (extract-entries x a))
;;           (rdetn (append (runits x) (nthcdr k (replace-row a k (rsum-select l (nth k a)))))))
;;     = (reval-tuple x k (replace-row a k (rsum-select l (nth k a)))).

;; Substitute (ninit (n)) for l:

;;   (rsum-tuples (extend-tuple x) (1+ k) a)
;;     = (reval-tuple x k (replace-row a k (rsum-select (ninit (n)) (nth k a))))
;;     = (reval-tuple x k (replace-row a k (nth k a)))
;;     = (reval-tuple x k a):

(defthm rsum-tuples-extend-tuple
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (rsum-tuples (extend-tuple x) (1+ k) a)
		  (reval-tuple x k a)))
  :hints (("Goal" :in-theory (enable extend-tuple)
                  :use (rsum-tuples-extend-tuple-30
                        (:instance replace-rmat-row-self (m (n)) (n (n)) (i k))))))

;; This leads to the recurrence formula

;;    (rsum-tuples (all-tuples k) k a) = (rsum-tuples (all-tuples (1- k)) (1- k) a):

(defthm rsum-tuples-append
  (implies (and (rmatp a (n) (n)) (natp k) (<= k (n)) (tuple-list-p l k) (tuple-list-p m k))
           (equal (rsum-tuples (append l m) k a)
	          (r+ (rsum-tuples l k a) (rsum-tuples m k a))))
  :hints (("Goal" :in-theory (disable reval-tuple))
          ("Subgoal *1/2" :use ((:instance r+assoc (x (reval-tuple (car l) k a))
					           (y (RSUM-TUPLES (CDR L) K A))
					           (z (RSUM-TUPLES M K A)))))))
                        
(defthmd rsum-tuples-extend-tuples
  (implies (and (rmatp a (n) (n))
                (natp k) (< k (n))
		(tuple-list-p l k))
	   (equal (rsum-tuples (extend-tuples l) (1+ k) a)
	          (rsum-tuples l k a)))
  :hints (("Goal" :in-theory (disable reval-tuple))))

(defthm rsum-tuples-extend-all-tuples
  (implies (and (rmatp a (n) (n))
                (posp k) (<= k (n)))
	   (equal (rsum-tuples (all-tuples k) k a)
	          (rsum-tuples (all-tuples (1- k)) (1- k) a)))
  :hints (("Goal" :use ((:instance rsum-tuples-extend-tuples (l (all-tuples (1- k))) (k (1- k)))))))

;; By induction, (rsum-tuples (all-tuples (n)) (n) a) = (rdetn a):

(local-defthmd rsum-tuples-induction
  (implies (and (rmatp a (n) (n))
                (natp k) (<= k (n)))
	   (equal (rsum-tuples (all-tuples k) k a)
	          (rdetn a)))
  :hints (("Goal" :induct (fact k) :in-theory (disable all-tuples))))

(defthmd rsum-tuples-rdetn
  (implies (rmatp a (n) (n))
	   (equal (rsum-tuples (all-tuples (n)) (n) a)
	          (rdetn a)))
  :hints (("Goal" :use ((:instance rsum-tuples-induction (k (n)))))))

(local-in-theory (disable rsum-tuples-induction rsum-tuples-extend-all-tuples))

;; If x is an (n)-tuple, then (reval-tuple x (n) a) = (rdetn (runits x)).  Since rdetn
;; is alternating, this value is (r0) unless x is a dlist:

(local-defthmd nthcdr-nil
  (implies (true-listp l)
           (equal (nthcdr (len l) l) ())))

(local-defthmd append-nil
  (implies (true-listp l)
           (equal (append l ()) l)))

(local-defthm reval-tuple-n
  (implies (and (rmatp a (n) (n))
                (tuplep x (n)))
	   (equal (reval-tuple x (n) a)
	          (r* (rlist-prod (extract-entries x a))
		      (rdetn (runits x)))))
  :hints (("Goal" :in-theory (disable len-rmatp)
                  :use ((:instance nthcdr-nil (l a))
                        (:instance append-nil (l (runits x)))
			(:instance len-rmatp (m (n)) (n (n)))))))

(local-defthm member-runits
  (implies (member z l)
           (member (runit z (n))
	           (runits l))))

(local-defthmd dlistp-runits-1
  (implies (and (true-listp x) (dlistp (runits x)))
           (dlistp x)))

(local-defthmd dlistp-runits
  (implies (and (tuplep x (n)) (dlistp (runits x)))
           (dlistp x))
  :hints (("Goal" :use (dlistp-runits-1))))

(local-defthmd rmatp-runits
  (implies (tuplep x k)
           (rmatp (runits x) k (n)))
  :hints (("Goal" :in-theory (enable rmatp))))

(defthm rdetn-runits-0
  (implies (and (tuplep x (n)) (not (dlistp x)))
           (equal (rdetn (runits x))
	          (r0)))
  :hints (("Goal" :in-theory (disable len-tuplep dcex-lemma)
                  :use (dlistp-runits
                        (:instance rmatp-runits (k (n)))
			(:instance len-tuplep (k (n)))
                        (:instance rdetn-alternating (a (runits x)) (i (dcex1 (runits x))) (j (dcex2 (runits x))))
			(:instance dcex-lemma (l (runits x)))))))

(defthm reval-tuple-r0
  (implies (and (rmatp a (n) (n))
                (tuplep x (n))
		(not (dlistp x)))
	   (equal (reval-tuple x (n) a)
	          (r0)))		  
  :hints (("Goal" :in-theory (disable rlistnp-extract-entries)
                  :use ((:instance rlistnp-extract-entries (m (n)) (k (n)))))))


(local-defun select-dlists (l)
  (if (consp l)
      (if (dlistp (car l))
          (cons (car l) (select-dlists (cdr l)))
	(select-dlists (cdr l)))
    ()))

(local-defthmd dlistp-select-dlists
  (implies (dlistp l)
           (and (sublistp (select-dlists l) l)
                (dlistp (select-dlists l))))
  :hints (("Goal" :induct (len l))))

(local-defthmd rsum-tuples-dlists
  (implies (and (rmatp a (n) (n))
                (tuple-list-p l (n)))
	   (equal (rsum-tuples l (n) a)
	          (rsum-tuples (select-dlists l) (n) a))))

;; But (select-dlists (all-tuples (n))) = (slist (n)), and therefore (rsum-tuples (slist (n)) (n) a) = (rdetn a).
;; However, that first equation looks like it would be hard to prove, so we shall instead prove
;; (permp (select-dlists (all-tuples (n))) (slist (n)) and derive the second equation from that.

(local-defthmd member-select-dlists
  (iff (member x (select-dlists l))
       (and (member x l)
            (dlistp x)))
  :hints (("Goal" :induct (len l))))

(local-defthmd member-select-dlists-all-tuples
  (iff (member x (select-dlists (all-tuples (n))))
       (and (tuplep x (n))
            (dlistp x)))
  :hints (("Goal" :use ((:instance member-select-dlists (l (all-tuples (n))))
                        (:instance member-all-tuples (k (n)))))))

(local-defthmd tuplep-sublistp-ninit
  (implies (natp k)
           (iff (tuplep x k)
	        (and (sublistp x (ninit (n)))
		     (equal (len x) k)
		     (true-listp x))))		     
  :hints (("Subgoal *1/2" :use ((:instance member-ninit (x (car x)) (n (n)))))
          ("Subgoal *1/1" :use ((:instance member-ninit (x (car x)) (n (n)))))))

(local-defthmd member-select-dlists-all-tuples-permp
  (iff (member x (select-dlists (all-tuples (n))))
       (permp x (ninit (n))))
  :hints (("Goal" :in-theory (enable permp)
                  :use (member-select-dlists-all-tuples
                        (:instance tuplep-sublistp-ninit (k (n)))
                        (:instance permp-eq-len (l x) (m (ninit (n))))
                        (:instance eq-len-permp (l x) (m (ninit (n))))))))

(local-defthmd member-select-dlists-slist
  (iff (member x (select-dlists (all-tuples (n))))
       (member x (slist (n))))
  :hints (("Goal" :in-theory (enable permp-slist)
                  :use (member-select-dlists-all-tuples-permp))))

(local-defthmd permp-select-dlists-all-tuples
  (permp (select-dlists (all-tuples (n)))
         (slist (n)))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance dlistp-select-dlists (l (all-tuples (n))))
		        (:instance scex1-lemma (l (select-dlists (all-tuples (n)))) (m (slist (n))))
		        (:instance scex1-lemma (m (select-dlists (all-tuples (n)))) (l (slist (n))))
			(:instance member-select-dlists-slist (x (scex1 (select-dlists (all-tuples (n))) (slist (n)))))
			(:instance member-select-dlists-slist (x (scex1 (slist (n)) (select-dlists (all-tuples (n))))))))))

(local-defun tuple-list-p-hack (l k)
  (if (consp l)
      (and (tuplep (car l) k)
           (tuple-list-p-hack (cdr l) k))
    t))

(local-defthm tuple-list-p-hack-lemma
  (implies (tuple-list-p l k)
           (tuple-list-p-hack l k)))
	
(local-defthmd permp-rsum-tuples-hack
  (implies (and (rmatp a (n) (n)) (true-listp l)
                (dlistp l) (tuple-list-p-hack l (n))
		(dlistp m) (tuple-list-p-hack m (n))
		(permp l m))
	   (equal (rsum-tuples l (n) a)
	          (rsum-tuples m (n) a)))		      
  :hints (("Goal" :in-theory (disable reval-tuple reval-tuple-n)
                  :use ((:functional-instance rval-sum-permp
                          (rargp (lambda (x) (if (rmatp a (n) (n)) (tuplep x (n)) (rargp x))))
                          (rval (lambda (x) (if (rmatp a (n) (n)) (reval-tuple x (n) a) (rval x))))
                          (rarg-listp (lambda (x) (if (rmatp a (n) (n)) (tuple-list-p-hack x (n)) (rarg-listp x))))
			  (rval-sum (lambda (x) (if (rmatp a (n) (n)) (rsum-tuples x (n) a) (rval-sum x)))))))))

(local-defthmd permp-rsum-tuples
  (implies (and (rmatp a (n) (n)) (true-listp l)
                (dlistp l) (tuple-list-p l (n))
		(dlistp m) (tuple-list-p m (n))
		(permp l m))
	   (equal (rsum-tuples l (n) a)
	          (rsum-tuples m (n) a)))		      
  :hints (("Goal" :use (permp-rsum-tuples-hack))))

;; To apply permp-rsum-tuples, we must show (tuple-list-p (slist (n))):

(local-defthm tuple-list-p-sublistp
  (implies (and (tuple-list-p l k) (true-listp m) (sublistp m l))
           (tuple-list-p m k)))

(local-defthm tuple-list-p-slist
  (and (tuple-list-p (slist (n)) (n))
       (tuple-list-p (select-dlists (all-tuples (n))) (n)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (permp-select-dlists-all-tuples
		        (:instance dlistp-select-dlists (l (all-tuples (n))))
                        (:instance tuple-list-p-sublistp (k (n)) (l (all-tuples (n))) (m (select-dlists (all-tuples (n)))))
                        (:instance tuple-list-p-sublistp (k (n)) (m (slist (n))) (l (select-dlists (all-tuples (n)))))))))
                        
;; Combine these results with rsum-tuples-dlists and rsum-tuples-rdetn:

(defthmd rsum-tuples-n
  (implies (rmatp a (n) (n))
	   (equal (rsum-tuples (slist (n)) (n) a)
	          (rdetn a)))
  :hints (("Goal" :use (permp-select-dlists-all-tuples rsum-tuples-rdetn
                        (:instance permp-rsum-tuples (l (select-dlists (all-tuples (n)))) (m (slist (n))))
			(:instance dlistp-select-dlists (l (all-tuples (n))))
			(:instance rsum-tuples-dlists (l (all-tuples (n))))))))
			
;; For p in (slist (n)),

;;   (reval-tuple p (n) a) = (r* (rlist-prod (extract-entries p a))
;;                              (rdetn (runits p))),
				
;; where (rlist-prod (extract-entries p a)) = (rdet-prod a p (n)).

(local-defun extract-entries (x a)
  (if (consp x)
      (cons (nth (car x) (car a))
            (extract-entries (cdr x) (cdr a)))
    ()))

(local-defthm len-extract-entries
  (equal (len (extract-entries p a))
         (len p)))

(local-defthmd nth-extract-entries
  (implies (and (natp i) (< i (len p)) (= (len p) (len a)))
	   (equal (nth i (extract-entries p a))
		  (entry i (nth i p) a)))
  :hints (("Goal" :in-theory (enable nth))))

(local-defun rdet-entries (p a n)
  (if (zp n)
      ()
    (append (rdet-entries p a (1- n))
	    (list (entry (1- n) (nth (1- n) p) a)))))

(local-defthm len-rdet-entries
  (implies (natp n)
	   (equal (len (rdet-entries p a n))
		  n)))

(local-defthmd nth-rdet-entries
  (implies (and (natp i) (natp k) (< i k) (<= k (n)) (member p (slist (n))) (rmatp a (n) (n)))
	   (equal (nth i (rdet-entries p a k))
		  (entry i (nth i p) a)))
  :hints (("Goal" :in-theory (enable nth) :induct (fact k))))

(local-defthmd equal-rdet-entries-extract-entries
  (implies (and (rmatp a (n) (n)) (member p (slist (n))))
	   (equal (rdet-entries p a (n))
		  (extract-entries p a)))
  :hints (("Goal" :in-theory (e/d (len-perm) (len-rmatp entry))
                  :use ((:instance len-rmatp (m (n)) (n (n)))
		        (:instance nth-diff-diff (x (rdet-entries p a (n))) (y (extract-entries p a)))
                        (:instance nth-rdet-entries (k (n)) (i (nth-diff (rdet-entries p a (n)) (extract-entries p a))))
			(:instance nth-extract-entries (i (nth-diff (rdet-entries p a (n)) (extract-entries p a))))))))

(local-defun rdet-prod (a p n)
  (if (zp n)
      (r1)
    (r* (rdet-prod a p (1- n))
        (entry (1- n) (nth (1- n) p) a))))

(local-defthm rlistp-append
  (implies (and (rlistp l) (rlistp m))
           (rlistp (append l m))))

(local-defthm rlist-prod-append
  (implies (and (rlistp l) (rlistp m))
           (equal (rlist-prod (append l m))
	          (r* (rlist-prod l) (rlist-prod m))))
  :hints (("Subgoal *1/3" :use ((:instance r*assoc (x (car l)) (y (rlist-prod (cdr l))) (z (rlist-prod m)))))
          ("Subgoal *1/2" :use ((:instance r*assoc (x (car l)) (y (rlist-prod (cdr l))) (z (rlist-prod m)))))))

(local-defthm rlistp-rdet-entries
  (implies (and (natp k) (<= k (n)) (member p (slist (n))) (rmatp a (n) (n)))
           (rlistp (rdet-entries p a k)))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :use ((:instance rp-entry (m (n)) (n (n)) (i (1- k)) (j (nth (1- k) p)))
	                        (:instance nth-perm-ninit (n (n)) (x p) (k (1- k)))))))


(local-defthmd rlist-prod-rdet-entries
  (implies (and (natp k) (<= k (n)) (member p (slist (n))) (rmatp a (n) (n)))
           (equal (rlist-prod (rdet-entries p a k))
	          (rdet-prod a p k)))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :use ((:instance rp-entry (m (n)) (n (n)) (i (1- k)) (j (nth (1- k) p)))
	                        (:instance nth-perm-ninit (n (n)) (x p) (k (1- k)))))))

(local-defthmd rlist-prod-extract-entries
  (implies (and (rmatp a (n) (n))
                (member p (slist (n))))
           (equal (rlist-prod (extract-entries p a))
	          (rdet-prod a p (n))))
  :hints (("Goal" :use (equal-rdet-entries-extract-entries
                        (:instance rlist-prod-rdet-entries (k (n)))))))

(local-defthmd reval-tuple-rdet-prod
  (implies (and (rmatp a (n) (n))
                (member p (slist (n))))
	   (equal (reval-tuple p (n) a)
	          (r* (rdet-prod a p (n))
		      (rdetn (runits p)))))
  :hints (("Goal" :use (rlist-prod-extract-entries
                        (:instance reval-tuple-n (x p))
			(:instance member-select-dlists-all-tuples (x p))
                        (:instance member-select-dlists-slist (x p))))))

;; But

;;   (rdetn (runits p)) = (rdetn (permute (id-rmat (n)) p))
;;                     = (r* (if (even-perm-p p (n)) (r1) (r- (r1)))
;;                           (rdetn (id-rmat (n)))).

(local-defthmd nth-runits
  (implies (and (natp k) (< k (len x)))
           (equal (nth k (runits x))
	          (runit (nth k x) (n))))
  :hints (("Goal" :in-theory (enable nth))))

(local-defthmd nth-permute-id-rmat
  (implies (and (natp k) (< k (n)) (in p (sym (n))))
           (equal (nth k (permute (id-rmat (n)) p))
	          (runit (nth k p) (n))))
  :hints (("Goal" :in-theory (disable nth-id-rmat len-rmatp)
                  :use ((:instance len-rmatp (a (id-rmat (n))) (m (n)) (n (n)))
		        (:instance nth-permute (l (id-rmat (n))))
			(:instance nth-id-rmat (i (nth k p)) (n (n)))
			(:instance member-perm (x p) (k (nth k p)) (n (n)))))))

(defthmd runits-permute-id-mat
  (implies (member p (slist (n)))
           (equal (runits p)
	          (permute (id-rmat (n)) p)))
  :hints (("Goal" :use ((:instance nth-diff-diff (x (runits p)) (y (permute (id-rmat (n)) p)))
                        (:instance nth-permute-id-rmat (k (nth-diff (runits p) (permute (id-rmat (n)) p))))
                        (:instance nth-runits (x p) (k (nth-diff (runits p) (permute (id-rmat (n)) p))))
			(:instance len-perm (x p) (n (n)))))))

(defthmd reval-tuple-rdet-prod
  (implies (and (rmatp a (n) (n))
                (member p (slist (n))))
	   (equal (reval-tuple p (n) a)
	          (r* (rdet-prod a p (n))
		      (rdetn (runits p))))))

(defthmd rdetn-permute-rows
  (implies (and (rmatp a (n) (n))
                (in p (sym (n))))
	   (equal (rdetn (permute a p))
	          (if (even-perm-p p (n))
		      (rdetn a)
		    (r- (rdetn a))))))
		    
;; Thus, we have

(defthmd reval-tuple-perm
  (implies (and (rmatp a (n) (n))
                (member p (slist (n))))
	   (equal (reval-tuple p (n) a)
	          (r* (rdet-term a p (n))
		      (rdetn (id-rmat (n))))))
  :hints (("Goal" :in-theory (e/d (rdet-term) (reval-tuple reval-tuple-n))
                  :use (reval-tuple-rdet-prod runits-permute-id-mat
                        (:instance rdetn-permute-rows (a (id-rmat (n))))
			(:instance r-r* (x (RDET-PROD A P (N))) (y (RDETN (ID-RMAT (N)))))
			(:instance r-r* (y (RDET-PROD A P (N))) (x (RDETN (ID-RMAT (N)))))
			(:instance r*comm (x (RDET-PROD A P (N))) (y (RDETN (ID-RMAT (N)))))
			(:instance r*comm (x (R- (RDET-PROD A P (N)))) (y (RDETN (ID-RMAT (N)))))))))

;; The desired result follows by summing over (slist (n)):

(local-defthmd rsum-tuples-sublist-slist
  (implies (and (rmatp a (n) (n)) (sublistp l (slist (n))))
	   (equal (rsum-tuples l (n) a)
	          (r* (rdet-sum a l (n))
		      (rdetn (id-rmat (n))))))
  :hints (("Goal" :in-theory (e/d (reval-tuple-perm) (reval-tuple reval-tuple-n)))))

(defthmd rsum-tuples-slist
  (implies (rmatp a (n) (n))
	   (equal (rsum-tuples (slist (n)) (n) a)
	          (r* (rdet a (n))
		      (rdetn (id-rmat (n))))))
  :hints (("Goal" :in-theory (enable rdet)
                  :use ((:instance rsum-tuples-sublist-slist (l (slist (n))))))))
	          
(defthmd rdet-unique
  (implies (rmatp a (n) (n))
           (equal (rdetn a)
                  (r* (rdet a (n))
                      (rdetn (id-rmat (n))))))
  :hints (("Goal" :use (rsum-tuples-n rsum-tuples-slist))))


;;-------------------------------------------------------------------------------------------------------
;;   Multiplicativity of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; As an application of rdet-unique, we shall prove that for nxn matrices a and b,

;;   (rdet (rmat* a b) n) = (r* (rdet a n) (rdet b n).

;; To this end, we shall show that the following is a determinant function of its first
;; argument, i.e., it satisfies the constraints on rdetn:

(defun rdet-rmat* (a b n)
  (rdet (rmat* a b) n))



(local-defthm rmat*-replace-row
  (implies (and (rmatp a m n) (rmatp b n p) (natp m) (natp n) (natp p)
                (natp k) (< k m) (rlistnp x n))
	   (equal (rmat* (replace-row a k x) b)
	          (replace-row (rmat* a b) k (rdot-list x (transpose-mat b)))))
  :hints (("Goal" :in-theory (enable rmatp rmat* replace-row))))

(local-defthm rdot-list-rlist-add
  (implies (and (rlistnp x n) (rlistnp y n) (rmatp b m n) (natp m))
           (equal (rdot-list (rlist-add x y) b)
	          (rlist-add (rdot-list x b) (rdot-list y b))))
  :hints (("Goal" :in-theory (enable rmatp rdot-rlist-add))))

(local-defthm rdot-list-rlist-scalar-mul
  (implies (and (rlistnp x n) (rp c) (rmatp b m n) (natp m))
           (equal (rdot-list (rlist-scalar-mul c x) b)
	          (rlist-scalar-mul c (rdot-list x b))))
  :hints (("Goal" :in-theory (enable rmatp rdot-rlist-scalar-mul))))

;; Firsat show that rdet-rmat* is n-linear:

;;   (rdet-rmat* (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) b n)
;;      = (rdet (rmat* (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) b) n)
;;      = (rdet (replace-row (rmat* a b)
;;                           k
;;     		             (rdot-list (rlist-add (rlist-scalar-mul c x) y) (transpose-mat b)))
;;     	        n)
;;      = (rdet (replace-row (rmat* a b)
;;                           k
;;     		             (rlist-add (rlist-scalar-mul c (rdot-list x (transpose-mat b)))
;;     		                        (rdot-list y (transpose-mat b))))
;;              n)
;;      = (r+ (r* c (rdet (replace-row (rmat* a b) k (rdot-list x (transpose-mat b))) n)
;;            (rdet (replace-row (rmat* a b) k (rdot-list y (transpose-mat b))) n)
;;      = (r+ (r* c (rdet (rmat* (replace-row a k x) b) n))
;;            (rdet (rmat* (replace-row a y x) b) n))
;;      = (r+ (r* c (rdet-rmat* (replace-row a k x) b n))
;;            (rdet-rmat* (replace-row a k y) b n))

(defthmd rdet-rmat*-n-linear
  (implies (and (rmatp a n n) (rmatp b n n) (posp n) (natp k) (< k n)
                (rlistnp x n) (rlistnp y n) (rp c))
           (equal (rdet-rmat* (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) b n)
                  (r+ (r* c (rdet-rmat* (replace-row a k x) b n))
                      (rdet-rmat* (replace-row a k y) b n))))
  :hints (("Goal" :use ((:instance rmatp-transpose (a b) (m n))
                        (:instance rdot-list-rlist-add (m n) (x (RLIST-SCALAR-MUL C X)) (b (transpose-mat b)))))))

;; The proof of the alternating property is easier:

(defthm rmat*-row
  (implies (and (natp m) (natp n) (rmatp a m n) (rmatp b n n) (natp k) (< k m))
           (equal (nth k (rmat* a b))
	          (rdot-list (nth k a) (transpose-mat b))))
  :hints (("Goal" :in-theory (enable nth rmat* rmatp))))
		      
(defthmd rdet-rmat*-adjacent-equal
  (implies (and (rmatp a n n) (rmatp b n n) (posp n)
		(natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (rdet-rmat* a b n) (r0)))
  :hints (("Goal" :use ((:instance rdet-alternating (i k) (j (1+ k)) (a (rmat* a b)))
                        (:instance rmatp-rmat* (m n) (p n))))))

;; Now apply functional instantiation:

(defthmd rdet-rmat*-val-n
  (implies (and (rmatp a (n) (n)) (rmatp b (n) (n)))
           (equal (rdet-rmat* a b (n))
	          (r* (rdet a (n))
		      (rdet-rmat* (id-rmat (n)) b (n)))))
  :hints (("Goal" :use ((:functional-instance rdet-unique
			  (rdetn (lambda (a) (if (and (rmatp a (n) (n)) (rmatp b (n) (n))) (rdet-rmat* a b (n)) (rdetn a)))))))	  
          ("Subgoal 3" :use (rdetn-adjacent-equal (:instance rdet-rmat*-adjacent-equal (n (n)) (k i))))
          ("Subgoal 2" :use (rdetn-n-linear (:instance rdet-rmat*-n-linear (n (n)) (k i))))))

(defthmd rdet-multiplicative
  (implies (and (rmatp a n n) (rmatp b n n) (posp n))
           (equal (rdet (rmat* a b) n)
	          (r* (rdet a n) (rdet b n))))
  :hints (("Goal" :in-theory (enable id-rmat-left)
                  :use ((:functional-instance rdet-rmat*-val-n
                          (n (lambda () (if (and (rmatp a n n) (rmatp b n n) (posp n)) n (n)))))))))
		  

;;-------------------------------------------------------------------------------------------------------
;;   Cofactor Expansion
;;-------------------------------------------------------------------------------------------------------

;; Given an nxn matrix a, we define the submatrix (minor i j a) to be the result of deleting
;; the ith row and the jth column of a:

(defun delete-row (k a)
  (if (zp k)
      (cdr a)
    (cons (car a) (delete-row (1- k) (cdr a)))))

(defund delete-col (k a)
  (transpose-mat (delete-row k (transpose-mat a))))

(defund minor (i j a)
  (delete-col j (delete-row i a)))

(defthmd rmatp-delete-row
  (implies (and (rmatp a m n) (natp m) (natp k) (< k m))
           (rmatp (delete-row k a) (1- m) n))
  :hints (("Goal" :in-theory (enable rmatp))))

(defthmd rmatp-delete-col
  (implies (and (rmatp a m n) (posp m) (natp n) (> n 1) (natp k) (< k n))
           (rmatp (delete-col k a) m (1- n)))
  :hints (("Goal" :in-theory (enable delete-col)
                  :use (rmatp-transpose
                        (:instance rmatp-delete-row (a (transpose-mat a)) (m n) (n m))
			(:instance rmatp-transpose (a (delete-row k (transpose-mat a))) (m (1- n)) (n m))))))

(defthmd rmatp-minor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
	   (rmatp (minor i j a) (1- n) (1- n)))
  :hints (("Goal" :in-theory (enable minor)
                  :use ((:instance rmatp-delete-row (k i) (m n))
		        (:instance rmatp-delete-col (k j) (a (delete-row i a)) (m (1- n)))))))

(local-in-theory (enable nth rmatp))

(local-defun entry-delete-row-induct (a i r m)
  (if (or (zp i) (zp r))
      (list a i r m)
    (list (entry-delete-row-induct (cdr a) (1- i) (1- r) (1- m)))))
    
(local-defthm row-delete-row
  (implies (and (rmatp a m n) (natp m) (> m 1) (posp n) (natp i) (< i m)
                (natp r) (< r (1- m)))
	   (equal (nth r (delete-row i a))
	          (nth (if (>= r i) (1+ r) r) a)))
  :hints (("Goal" :induct (entry-delete-row-induct a i r m))
          ("Subgoal *1/1" :expand ((DELETE-ROW I A)))))

(local-defthmd entry-delete-row
  (implies (and (rmatp a m n) (natp m) (> m 1) (posp n) (natp i) (< i m)
                (natp r) (< r (1- m)) (natp s) (< s n))
	   (equal (entry r s (delete-row i a))
	          (entry (if (>= r i) (1+ r) r) s a))))

(local-defthmd entry-delete-col
  (implies (and (rmatp a m n) (posp m) (natp n) (> n 1) (natp j) (< j n)
                (natp r) (< r m) (natp s) (< s (1- n)))
	   (equal (entry r s (delete-col j a))
	          (entry r (if (>= s j) (1+ s) s) a)))
  :hints (("Goal" :in-theory (e/d (delete-col) (nth-transpose-rmat))
                  :use (rmatp-transpose
                        (:instance rmatp-delete-row (a (transpose-mat a)) (m n) (n m) (k j))
			(:instance rmatp-transpose (a (delete-row j (transpose-mat a))) (m (1- n)) (n m))
                        (:instance transpose-rmat-entry (a (delete-row j (transpose-mat a))) (m (1- n)) (n m) (j r) (i s))
			(:instance entry-delete-row (a (transpose-mat a)) (m n) (n m) (i j) (s r) (r s))
			(:instance transpose-rmat-entry (i r) (j (if (>= s j) (1+ s) s)))))))

;; We derive an expression for an entry of (minor i j a):

(defthmd entry-rmat-minor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (natp s) (< r (1- n)) (< s (1- n)))
	   (equal (entry r s (minor i j a))
	          (entry (if (>= r i) (1+ r) r)
		         (if (>= s j) (1+ s) s)
			 a)))
  :hints (("Goal" :in-theory (e/d (minor) (entry delete-row row-delete-row rmatp))
                  :use ((:instance rmatp-delete-row (m n) (k i))
		        (:instance entry-delete-col (a (delete-row i a)) (m (1- n)))
		        (:instance entry-delete-row (m n) (s (if (>= s j) (1+ s) s)))))))

;; We shall also require an expression for the rth row of (minor i j a).  This is based on the
;; following function, which deletes the jth member of a list l:

(defun delete-nth (j l)
  (if (zp j)
      (cdr l)
    (cons (car l) (delete-nth (1- j) (cdr l)))))

(local-defthm nth-delete-nth
  (implies (and (natp j) (< j (len l)) (natp k) (< (1+ k) (len l)))
           (equal (nth k (delete-nth j l))
	          (if (< k j)
		      (nth k l)
		    (nth (1+ k) l)))))

(local-defthm len-delete-nth
  (implies (and (natp j) (< j (len l)))
           (equal (len (delete-nth j l))
	          (1- (len l)))))

(local-defthm true-listp-delete-nth
  (implies (and (natp j) (< j (len l)) (true-listp l))
           (true-listp (delete-nth j l))))

(local-defthmd nth-nth-minor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (< r (1- n)) (natp s) (< s (1- n)))
	   (equal (nth s (delete-nth j (nth (if (< r i) r (1+ r)) a)))
	          (nth s (nth r (minor i j a)))))
  :hints (("Goal" :in-theory (disable nth rmatp)
                  :use (entry-rmat-minor))))

(defthmd row-rmat-minor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (< r (1- n)))
	   (equal (nth r (minor i j a))
	          (delete-nth j (nth (if (< r i) r (1+ r)) a))))
  :hints (("Goal" :in-theory (disable rlistnp-nth len-rmat-row len-rlist MEMBER-RMATP-RLISTNP nth rmatp delete-nth rlistnp-row)
                  :use (rmatp-minor
                        (:instance nth-diff-diff (x (nth r (minor i j a)))
                                                 (y (delete-nth j (nth (if (< r i) r (1+ r)) a))))
			(:instance nth-nth-minor
			            (s (nth-diff (nth r (minor i j a)) (delete-nth j (nth (if (< r i) r (1+ r)) a)))))
			(:instance len-rlist (x (nth r a)))
			(:instance len-rlist (x (nth (1+ r) a)))
			(:instance len-rlist (x (nth r (minor i j a))) (n (1- n)))
			(:instance rlistnp-row (m n) (i r))
			(:instance rlistnp-row (m n) (i (1+ r)))
			(:instance rlistnp-row (a (minor i j a)) (m (1- n)) (n (1- n)) (i r))))))

;; minor commutes with transpose-mat:

(local-defthmd entry-transpose-minor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (natp s) (< r (1- n)) (< s (1- n)))
           (equal (entry r s (transpose-mat (minor i j a)))
	          (entry (if (>= s i) (1+ s) s)
		         (if (>= r j) (1+ r) r)
			 a)))
  :hints (("Goal" :in-theory (disable nth rmatp nth-transpose-rmat)
                  :use (rmatp-minor
                        (:instance transpose-rmat-entry (a (minor i j a)) (m (1- n)) (n (1- n)) (j r) (i s))
                        (:instance entry-rmat-minor (r s) (s r))))))

(local-defthmd entry-rmat-minor-transpose
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (natp s) (< r (1- n)) (< s (1- n)))
           (equal (entry r s (minor j i (transpose-mat a)))
	          (entry (if (>= s i) (1+ s) s)
		         (if (>= r j) (1+ r) r)
			 a)))
  :hints (("Goal" :in-theory (disable nth rmatp nth-transpose-rmat)
                  :use ((:instance rmatp-transpose (m n))
                        (:instance entry-rmat-minor (a (transpose-mat a)) (i j) (j i))
                        (:instance transpose-rmat-entry (m n) (j (if (>= r j) (1+ r) r)) (i (if (>= s i) (1+ s) s)))))))

(defthmd transpose-minor-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
	   (and (rmatp (transpose-mat (minor i j a)) (1- n) (1- n))
	        (equal (transpose-mat (minor i j a))
	               (minor j i (transpose-mat a)))))
  :hints (("Goal" :in-theory (disable entry nth rmatp nth-transpose-rmat)
                  :use (rmatp-minor
                        (:instance rmatp-transpose (m n))
                        (:instance rmatp-minor (a (transpose-mat a)) (i j) (j i))
                        (:instance rmatp-transpose (m (1- n)) (n (1- n)) (a (minor i j a)))
			(:instance rmat-entry-diff-lemma (m (1- n)) (n (1- n))
			                            (a (transpose-mat (minor i j a)))
			                            (b (minor j i (transpose-mat a))))
			(:instance entry-transpose-minor
			            (r (car (entry-diff (transpose-mat (minor i j a)) (minor j i (transpose-mat a)))))
			            (s (cdr (entry-diff (transpose-mat (minor i j a)) (minor j i (transpose-mat a))))))
			(:instance entry-rmat-minor-transpose
			            (r (car (entry-diff (transpose-mat (minor i j a)) (minor j i (transpose-mat a)))))
			            (s (cdr (entry-diff (transpose-mat (minor i j a)) (minor j i (transpose-mat a))))))))))

;; Next, we define the cofactor of an entry of a:

(defund rdet-cofactor (i j a n)
  (if (evenp (+ i j))
      (rdet (minor i j a) (1- n))
    (r- (rdet (minor i j a) (1- n)))))

;; Cofactor expansion of the determinant of a by column j:

(defun expand-rdet-col-aux (a i j n)
  (if (zp i)
      (r0)
    (r+ (r* (entry (1- i) j a)
            (rdet-cofactor (1- i) j a n))
	(expand-rdet-col-aux a (1- i) j n))))

(defund expand-rdet-col (a j n)
  (expand-rdet-col-aux a n j n))

;; Cofactor expansion of the determinant of a by row i:

(defun expand-rdet-row-aux (a i j n)
  (if (zp j)
      (r0)
    (r+ (r* (entry i (1- j) a)
            (rdet-cofactor i (1- j) a n))
	(expand-rdet-row-aux a i (1- j) n))))

(defund expand-rdet-row (a i n)
  (expand-rdet-row-aux a i n n))

;; Cofactor expansion by column i is equivalent to expansion of the transpose by row i:

(defthm rdet-cofactor-transpose
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (< i n) (natp j) (< j n))
	   (equal (rdet-cofactor j i (transpose-mat a) n)
	          (rdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable rdet-cofactor)
                  :use (rmatp-minor transpose-minor-rmat
		        (:instance rdet-transpose (a (minor i j a)) (n (1- n)))))))

(local-defthmd expand-rdet-row-aux-transpose
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (< i n) (natp j) (< j n))
           (equal (expand-rdet-row-aux (transpose-mat a) j i n)
	          (expand-rdet-col-aux a i j n))))

(defthmd expand-rdet-row-transpose
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (< i n))
           (equal (expand-rdet-row (transpose-mat a) i n)
	          (expand-rdet-col a i n)))
  :hints (("Goal" :in-theory (enable expand-rdet-row expand-rdet-col expand-rdet-row-aux-transpose))))

;; We shall prove, by functional instantiation of rdet-unique,  that the result of cofactor
;; expansion by a column has the same value as the determinant, and it will follow that the
;; same is true for expansion by a row.  The requires proving analogs of the constraints on
;; rdetn.

(defthm rp-rdet-cofactor
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
           (rp (rdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable rdet-cofactor)
                  :use (rmatp-minor rp-entry))))

(local-defthmd rp-expand-rdet-col-aux
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (natp i) (<= i n) (natp j) (< j n))
           (rp (expand-rdet-col-aux a i j n)))
  :hints (("Subgoal *1/5" :use ((:instance rp-entry (m n) (i (1- i)))))))

(defthm rp-expand-rdet-col
  (implies (and (rmatp a n n) (> n 1) (natp j) (< j n))
           (rp (expand-rdet-col a j n)))
  :hints (("Goal" :in-theory (enable expand-rdet-col)
                  :use ((:instance rp-expand-rdet-col-aux (i n))))))

(local-defthmd rlistnp-delete-nth
  (implies (and (rlistnp x n) (posp n) (natp k) (< k n))
           (rlistnp (delete-nth k x) (1- n))))

(local-defthmd row-rmat-minor-replace-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (rlistnp x n)
		(natp r) (< r (1- n)))
	   (equal (nth r (minor i j (replace-row a k x)))
	          (nth r (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x)))))
  :hints (("Goal" :in-theory (e/d (row-rmat-minor) (nth rmatp rmatp-replace-row nth-replace-row len-rmatp))
                  :use (rmatp-minor rlistnp-delete-nth
		        (:instance rlistnp-delete-nth (k j))
                        (:instance len-rmatp (m n))
                        (:instance len-rmatp (a (minor i j a)) (m (1- n)) (n (1- n)))
			(:instance rmatp-replace-row (m n) (r x))
			(:instance nth-replace-row (r x) (j r))
			(:instance nth-replace-row (r x) (j (1+ r)))
			(:instance nth-replace-row (a (minor i j a)) (j r) (k (if (< k i) k (1- k))) (r (delete-nth j x)))
                        (:instance rmatp-minor (a (replace-row a k x)))))))

(local-defthmd minor-replace-rmat-row-1
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (rlistnp x n))
	   (and (true-listp (minor i j (replace-row a k x)))
	        (equal (len (minor i j (replace-row a k x))) (1- n))
		(true-listp (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x)))
		(equal (len (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x))) (1- n))))
  :hints (("Goal" :in-theory (disable nth rmatp rmatp-replace-row len-rmatp)
                  :use (rmatp-minor rlistnp-delete-nth
		        (:instance rlistnp-delete-nth (k j))
                        (:instance len-rmatp (m n))
                        (:instance len-rmatp (a (minor i j a)) (m (1- n)) (n (1- n)))
                        (:instance len-rmatp (a (minor i j (replace-row a k x))) (m (1- n)) (n (1- n)))
			(:instance rmatp-replace-row (m n) (r x))
                        (:instance rmatp-minor (a (replace-row a k x)))))))

;; The effect on (minor i j a) of replacing a row of a other than row i:

(defthmd minor-replace-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (rlistnp x n))
	   (equal (minor i j (replace-row a k x))
	          (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x))))
  :hints (("Goal" :in-theory (disable nth rmatp rmatp-replace-row len-rmatp)
                  :use (minor-replace-rmat-row-1
		        (:instance nth-diff-diff (x (minor i j (replace-row a k x)))
			                         (y (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x))))
                        (:instance row-rmat-minor-replace-rmat-row
			             (r (nth-diff (minor i j (replace-row a k x))
				                  (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x)))))))))

(local-defthmd row-rmat-minor-replace-rmat-row-i
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (rlistnp x n)
		(natp r) (< r (1- n)))
	   (equal (nth r (minor i j (replace-row a i x)))
	          (nth r (minor i j a))))
  :hints (("Goal" :in-theory (e/d (row-rmat-minor) (nth rmatp rmatp-replace-row nth-replace-row len-rmatp))
                  :use (rmatp-minor
                        (:instance len-rmatp (m n))
                        (:instance len-rmatp (a (minor i j a)) (m (1- n)) (n (1- n)))
			(:instance rmatp-replace-row (m n) (r x) (k i))
			(:instance nth-replace-row (r x) (j r) (k i))
			(:instance nth-replace-row (r x) (j (1+ r)) (k i))
                        (:instance rmatp-minor (a (replace-row a i x)))))))

(local-defthmd minor-replace-rmat-row-i-1
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (rlistnp x n))
	   (and (true-listp (minor i j (replace-row a i x)))
	        (equal (len (minor i j (replace-row a i x))) (1- n))
		(true-listp (minor i j a))
		(equal (len (minor i j a)) (1- n))))
  :hints (("Goal" :in-theory (disable nth rmatp rmatp-replace-row len-rmatp)
                  :use (rmatp-minor
                        (:instance len-rmatp (m n))
                        (:instance len-rmatp (a (minor i j a)) (m (1- n)) (n (1- n)))
                        (:instance len-rmatp (a (minor i j (replace-row a i x))) (m (1- n)) (n (1- n)))
			(:instance rmatp-replace-row (m n) (r x) (k i))
                        (:instance rmatp-minor (a (replace-row a i x)))))))

;; Replacing row i of a does not alter (minor i j a):

(defthmd minor-replace-rmat-row-i
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (rlistnp x n))
	   (equal (minor i j (replace-row a i x))
	          (minor i j a)))
  :hints (("Goal" :in-theory (disable nth rmatp rmatp-replace-row len-rmatp)
                  :use (minor-replace-rmat-row-i-1
		        (:instance nth-diff-diff (x (minor i j (replace-row a i x)))
			                         (y (minor i j a)))
                        (:instance row-rmat-minor-replace-rmat-row-i
			             (r (nth-diff (minor i j (replace-row a i x))
				                  (minor i j a))))))))

(defthmd cofactor-replace-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (rlistnp x n))
	   (equal (rdet-cofactor i j (replace-row a i x) n)
	          (rdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable rdet-cofactor)
                  :use (minor-replace-rmat-row-i))))

(local-defthmd delete-nth-rlist-add-scalar-mul
  (implies (and (rlistnp x n) (rlistnp y n) (rp c) (posp n) (natp k) (< k n))
           (equal (delete-nth k (rlist-add (rlist-scalar-mul c x) y))
	          (rlist-add (rlist-scalar-mul c (delete-nth k x)) (delete-nth k y)))))

(local-defthmd rdet-minor-n-linear
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (rdet (minor i j (replace-row a k (rlist-add (rlist-scalar-mul c x) y))) (+ -1 n))
	          (r+ (r* c (rdet (minor i j (replace-row a k x)) (1- n)))
		      (rdet (minor i j (replace-row a k y)) (1- n)))))
  :hints (("Goal" :in-theory (e/d (delete-nth-rlist-add-scalar-mul minor-replace-rmat-row)
                                  (rmatp rdet-n-linear))
                  :use (rmatp-minor
		        (:instance rlistnp-delete-nth (k j))
		        (:instance rlistnp-delete-nth (k j) (x y))
		        (:instance rdet-n-linear (a (minor i j a))
			                         (n (1- n))
			                         (i (if (< k i) k (1- k)))
						 (x (delete-nth j x))
						 (y (delete-nth j y)))))))

(local-defthmd rdet-cofactor-n-linear
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (rdet-cofactor i j (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) n)
	          (r+ (r* c (rdet-cofactor i j (replace-row a k x) n))
		      (rdet-cofactor i j (replace-row a k y) n))))
  :hints (("Goal" :in-theory (e/d (r-r+ r-r* rdet-cofactor rdet-minor-n-linear)
                                  (rmatp rmatp-minor rlistnp rlist-add rlist-scalar-mul))
                  :use ((:instance rmatp-minor (a (replace-row a k x)))
		        (:instance rmatp-minor (a (replace-row a k y)))))))

(local-defthmd rdet-cofactor-i
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (rlistnp x n) (rlistnp y n) (rp c))
	   (and (equal (rdet-cofactor i j (replace-row a i (rlist-add (rlist-scalar-mul c x) y)) n)
	               (rdet-cofactor i j a n))
		(equal (rdet-cofactor i j (replace-row a i y) n)
	               (rdet-cofactor i j a n))
	        (equal (rdet-cofactor i j (replace-row a i x) n)
		       (rdet-cofactor i j a n))))
  :hints (("Goal" :in-theory (e/d (r-r+ r-r* rdet-cofactor minor-replace-rmat-row-i)
                                  (rmatp rmatp-minor rlistnp rlist-add rlist-scalar-mul)))))

(local-defund expand-rdet-col-aux-term (i j a n)
  (r* (entry i j a)
      (rdet-cofactor i j a n)))

(local-defun expand-rdet-col-aux-alt (a i j n)
  (if (zp i)
      (r0)
    (r+ (expand-rdet-col-aux-term (1- i) j a n)
	(expand-rdet-col-aux-alt a (1- i) j n))))

(local-defthmd expand-rdet-col-aux-alt-rewrite
  (equal (expand-rdet-col-aux-alt a i j n)
         (expand-rdet-col-aux a i j n))
  :hints (("Goal" :in-theory (enable expand-rdet-col-aux-term))))

(local-defthmd expand-rdet-col-aux-term-expand
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (expand-rdet-col-aux-term i j (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) n)
	          (r+ (r* c (expand-rdet-col-aux-term i j (replace-row a k x) n))
		      (expand-rdet-col-aux-term i j (replace-row a k y) n))))
  :hints (("Goal" :in-theory (e/d (r-r+ r-r* expand-rdet-col-aux-term rdet-cofactor-n-linear)
                                  (nth rmatp rmatp-minor rlistnp rlist-add rlist-scalar-mul))
		  :use ((:instance rp-entry (m n))
		        (:instance r*assoc (x c) (y (entry i j a)) (z (RDET-COFACTOR I J (REPLACE-ROW A K X) n)))
			(:instance r*comm (x c) (y (entry i j a)))
		        (:instance r*assoc (y c) (x (entry i j a)) (z (RDET-COFACTOR I J (REPLACE-ROW A K X) n)))))))

(local-defthmd expand-rdet-col-aux-term-expand-i
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (expand-rdet-col-aux-term i j (replace-row a i (rlist-add (rlist-scalar-mul c x) y)) n)
	          (r+ (r* c (expand-rdet-col-aux-term i j (replace-row a i x) n))
		      (expand-rdet-col-aux-term i j (replace-row a i y) n))))
  :hints (("Goal" :in-theory (e/d (r-r+ r-r* expand-rdet-col-aux-term rdet-cofactor-i)
                                  (rlistnp-rlist-scalar-mul nth rmatp rmatp-minor rlistnp rlist-add rlist-scalar-mul))
		  :use (rlistnp-rlist-scalar-mul
		        (:instance r*assoc (x c) (y (nth j x)) (z (RDET-COFACTOR I J A N)))))))

(local-defthmd expand-rdet-col-aux-term-expand-all
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (expand-rdet-col-aux-term i j (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) n)
	          (r+ (r* c (expand-rdet-col-aux-term i j (replace-row a k x) n))
		      (expand-rdet-col-aux-term i j (replace-row a k y) n))))
  :hints (("Goal" :use (expand-rdet-col-aux-term-expand expand-rdet-col-aux-term-expand-i))))

(local-defthm rp-rdet-col-aux-term
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (rp (expand-rdet-col-aux-term i j a n)))
  :hints (("Goal" :in-theory (enable expand-rdet-col-aux-term)
                  :use ((:instance rp-entry (m n))))))

(local-defthm rp-rdet-col-aux-alt
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (<= i n) (natp j) (< j n))
           (rp (expand-rdet-col-aux-alt a i j n))))

(local-defthmd hack-5
  (implies (and (rp x) (rp y) (rp c) (rp xt) (rp yt))
           (equal (r+ (r+ (r* c xt) yt) (r+ (r* c x) y))
	          (r+ (r+ (r* c xt) (r* c x)) (r+ yt y))))
  :hints (("Goal" :use ((:instance r+assoc (x (r+ (r* c xt) yt)) (y (r* c x)) (z y))
                        (:instance r+assoc (x (r* c xt)) (y yt) (z (r* c x)))
			(:instance r+comm (x yt) (y (r* c x)))
			(:instance r+assoc (x (r* c xt)) (y (r* c x)) (z yt))
			(:instance r+assoc (x (r+ (r* c xt) (r* c x))) (y yt) (z y))))))

(local-defthmd expand-rdet-col-aux-alt-n-linear
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (<= i n) (natp j) (< j n)
                (natp k) (< k n) (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (expand-rdet-col-aux-alt (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) i j n)
		  (r+ (r* c (expand-rdet-col-aux-alt (replace-row a k x) i j n))
		      (expand-rdet-col-aux-alt (replace-row a k y) i j n))))
  :hints (("Goal" :in-theory (e/d (r-r+ r-r* expand-rdet-col-aux-term-expand-all)
                                  (entry expand-rdet-col-aux-alt-rewrite rlistnp-rlist-scalar-mul nth rmatp rmatp-minor
				   rlistnp rlist-add rlist-scalar-mul)))				   
	  ("Subgoal *1/5" :use ((:instance hack-5 (x (EXPAND-RDET-COL-AUX-ALT (REPLACE-ROW A K X) (+ -1 I) J N))
		                                  (y (EXPAND-RDET-COL-AUX-ALT (REPLACE-ROW A K Y) (+ -1 I) J N))
				         	  (xt (EXPAND-RDET-COL-AUX-TERM (+ -1 I) J (REPLACE-ROW A K X) N))
					          (yt (EXPAND-RDET-COL-AUX-TERM (+ -1 I) J (REPLACE-ROW A K Y) N)))))))

(local-defthmd expand-rdet-col-aux-n-linear
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (<= i n) (natp j) (< j n)
                (natp k) (< k n) (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (expand-rdet-col-aux (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) i j n)
		  (r+ (r* c (expand-rdet-col-aux (replace-row a k x) i j n))
		      (expand-rdet-col-aux (replace-row a k y) i j n))))
  :hints (("Goal" :in-theory (enable expand-rdet-col-aux-alt-rewrite)
                  :use (expand-rdet-col-aux-alt-n-linear))))

;; It follows that cofactor expansion by column j is n-linear:

(defthmd expand-rdet-col-n-linear
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k n) (rlistnp x n) (rlistnp y n) (rp c))
	   (equal (expand-rdet-col (replace-row a k (rlist-add (rlist-scalar-mul c x) y)) j n)
		  (r+ (r* c (expand-rdet-col (replace-row a k x) j n))
		      (expand-rdet-col (replace-row a k y) j n))))
  :hints (("Goal" :in-theory (enable expand-rdet-col)
                  :use ((:instance expand-rdet-col-aux-n-linear (i n))))))

;; Now suppose adjacent rows k and k+1 of a are equal.  Then for any i other than k and k+1, (minor i j a)
;; has 2 adjacent rows,and therefore (rdet-cofactor i j a n) = (r0).  Meanwhile, (minor k j) = (minor (1+ k) j)
;; and (entry k j a) = (entry (1+ k) j a), but k + j and (k + 1) + j have opposite parities, and therefore
;; (rdet-cofactor k j a n) + (rdet-cofactor (1+ k) j a n) = (r0).  Thus, (expand-rdet-col a j n) = r0:

(local-defthmd minor-equal-rows-1
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (< i k))
	   (equal (nth (1- k) (minor i j a))
	          (nth k (minor i j a))))
  :hints (("Goal" :use ((:instance row-rmat-minor (r (1- k)))
                        (:instance row-rmat-minor (r k))))))

(local-defthmd minor-equal-rows-2
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (> i (1+ k)) (< i n))
	   (equal (nth k (minor i j a))
	          (nth (1+ k) (minor i j a))))
  :hints (("Goal" :use ((:instance row-rmat-minor (r (1+ k)))
                        (:instance row-rmat-minor (r k))))))

(local-defthmd minor-equal-rows-0-1
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (< i k))
	   (equal (rdet (minor i j a) (+ -1 n))
	          (r0)))
  :hints (("Goal" :use (minor-equal-rows-1 rmatp-minor
                        (:instance rdet-alternating (a (minor i j a)) (n (1- n)) (i (1- k)) (j k))))))

(local-defthmd minor-equal-rows-0-2
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (> i (1+ k)) (< i n))
	   (equal (rdet (minor i j a) (+ -1 n))
	          (r0)))
  :hints (("Goal" :use (minor-equal-rows-2 rmatp-minor
                        (:instance rdet-alternating (a (minor i j a)) (n (1- n)) (i (1+ k)) (j k))))))
			
(local-defthmd cofactor-equal-rows
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (< i n) (not (= i k)) (not (= i (1+ k))))
	   (equal (rdet-cofactor i j a n)
	          (r0)))
  :hints (("Goal" :in-theory (enable rdet-cofactor)
                  :use (minor-equal-rows-0-1 minor-equal-rows-0-2))))


(local-defthm nth-minor-equal-rows
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp r) (< r (1- n)))
	   (equal (nth r (minor k j a))
	          (nth r (minor (1+ k) j a))))
  :hints (("Goal" :use ((:instance row-rmat-minor (i k))
                        (:instance row-rmat-minor (i (1+ k)))))))

(local-defthmd minor-equal-rows
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (minor k j a)
	          (minor (1+ k) j a)))
  :hints (("Goal" :in-theory (disable len-rmatp)
                  :use ((:instance rmatp-minor (i k))
                        (:instance rmatp-minor (i (1+ k)))
			(:instance len-rmatp (a (minor k j a)) (m (1- n)) (n (1- n)))
			(:instance len-rmatp (a (minor (1+ k) j a)) (m (1- n)) (n (1- n)))
			(:instance nth-diff-diff (x (minor k j a)) (y (minor (1+ k) j a)))
			(:instance nth-minor-equal-rows (r (nth-diff (minor k j a) (minor (1+ k) j a))))))))

(local-defthmd cofactor-sum-0
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (r+ (rdet-cofactor (1+ k) j a n)
	              (rdet-cofactor k j a n))
	          (r0)))
  :hints (("Goal" :in-theory (e/d (rdet-cofactor) (nth rmatp))
                  :use (minor-equal-rows
		        (:instance rmatp-minor (i k))))))
		
(local-defthmd expand-rdet-col-aux-0-1
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (<= i k))
	   (equal (expand-rdet-col-aux a i j n)
	          (r0)))		  
  :hints (("Subgoal *1/2" :in-theory (enable cofactor-equal-rows)
                          :use ((:instance rp-entry (m n) (i (1- i)))))))

(local-defthmd expand-rdet-col-aux-0-2
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (expand-rdet-col-aux a (+ 2 k) j n)
	          (r0)))		  
  :hints (("Goal" :in-theory (disable rdist)
                  :use (cofactor-sum-0
                        (:instance rp-entry (m n) (i k))
                        (:instance expand-rdet-col-aux-0-1 (i k))
			(:instance rdist (x (entry k j a)) (y (rdet-cofactor (1+ k) j a n)) (z (rdet-cofactor k j a n)))))))

(local-defthmd expand-rdet-col-aux-0-3
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (> i (1+ k)) (<= i n))
	   (equal (expand-rdet-col-aux a i j n)
	          (r0)))		  
  :hints (("Subgoal *1/2" :in-theory (e/d (rp-expand-rdet-col-aux) (rmatp nth))
                          :use (expand-rdet-col-aux-0-2
			        (:instance cofactor-equal-rows (i (1- i)))
			        (:instance rp-entry (m n) (i (1- i)))))))

(defthmd expand-rdet-col-adjacent-equal
  (implies (and (rmatp a n n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (expand-rdet-col a j n)
	          (r0)))
  :hints (("Goal" :in-theory (enable expand-rdet-col)
                  :use ((:instance expand-rdet-col-aux-0-3 (i n))))))

;; By functional instantiation of rdet-unique,we have the following:

(local-defthmd expand-rdet-col-val-n
  (implies (and (rmatp a (n) (n)) (> (n) 1) (natp k) (< k (n)))
           (equal (expand-rdet-col a k (n))
	          (r* (rdet a (n))
		      (expand-rdet-col (id-rmat (n)) k (n)))))
  :hints (("Goal" :use ((:functional-instance rdet-unique
			  (rdetn (lambda (a)
			                (if (and (rmatp a (n) (n)) (> (n) 1) (natp k) (< k (n)))
					    (expand-rdet-col a k (n))
					  (rdetn a)))))))
	  ("Subgoal 3" :use (rdetn-adjacent-equal (:instance expand-rdet-col-adjacent-equal (k i) (j k) (n (n)))))
          ("Subgoal 2" :use (rdetn-n-linear (:instance expand-rdet-col-n-linear (k i) (j k) (n (n)))))))

(defthmd expand-rdet-col-val
  (implies (and (rmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-rdet-col a k n)
	          (r* (rdet a n)
		      (expand-rdet-col (id-rmat n) k n))))
  :hints (("Goal" :use ((:functional-instance expand-rdet-col-val-n
			  (n (lambda () (if (and (posp n) (> n 1)) n (n)))))))))

;; It remains to show that (expand-rdet-col (id-rmat n) k n) = (r1).
;; By row-rmat-minor, we habe the following expression for the rth row of (minor i j (id-rmat n)):

(defthmd nth-minor-id-rmat
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp r) (< r (1- n)))
	   (equal (nth r (minor i j (id-rmat n)))
	          (delete-nth j (runit (if (< r i) r (1+ r)) n))))
  :hints (("Goal" :in-theory (e/d (nth-id-rmat) (rmatp-id-rmat))
                  :use (rmatp-id-rmat
		        (:instance row-rmat-minor (a (id-rmat n)))))))

;; The following is a consequence of the definirtions of runit and delete-nth:

(local-defun delete-nth-runit-induct (j k n)
  (if (zp j)
      (list j k n)
    (list (delete-nth-runit-induct (1- j) (1- k) (1- n)))))

(local-defun delete-nth-rlistn0-induct (j n)
  (if (zp j)
      (list j n)
    (delete-nth-rlistn0-induct (1- j) (1- n))))

(local-defthm delete-nth-rlistn0
  (implies (and (natp j) (< j n) (posp n))
           (equal (delete-nth j (rlistn0 n))
	          (rlistn0 (1- n))))
  :hints (("Goal" :induct (delete-nth-rlistn0-induct j n))))

(defthmd delete-nth-runit
  (implies (and (posp n) (natp j) (< j n) (natp k) (< k n))
           (equal (delete-nth j (runit k n))
	          (if (< j k)
		      (runit (1- k) (1- n))
		    (if (> j k)
		        (runit k (1- n))
		      (rlistn0 (1- n))))))
  :hints (("Goal" :induct (delete-nth-runit-induct j k n))
          ("Subgoal *1/2" :expand ((DELETE-NTH J (LIST* (R1) (R0) (RLISTN0 (+ -2 N))))
	                           (DELETE-NTH (+ -1 J) (CONS (R0) (RLISTN0 (+ -2 N))))))))

;; Consequently, if i <> j, then we find a zero row of (minor i j (id-rmat n)), which implies that
;; its determinant is (r0):

(defthmd nth-minor-id-rmat-0
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (equal (nth (if (< j i) j (1- j)) (minor i j (id-rmat n)))
	          (rlistn0 (1- n))))
  :hints (("Goal" :in-theory (enable nth-minor-id-rmat delete-nth-runit))))

(defthmd rdet-minor-id-rmat-0
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (equal (rdet (minor i j (id-rmat n)) (1- n))
	          (r0)))
  :hints (("Goal" :use (nth-minor-id-rmat-0
                        (:instance rdet-row-0 (a (minor i j (id-rmat n))) (n (1- n)) (k (if (< j i) j (1- j))))
			(:instance rmatp-minor (a (id-rmat n)))))))

;; On the other hand, (minor j j (id-rmat n)) = (id-rmat (1- n)):

(defthmd nth-minor-id-rmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n) (natp r) (< r (1- n)))
	   (equal (nth r (minor j j (id-rmat n)))
	          (nth r (id-rmat (1- n)))))
  :hints (("Goal" :in-theory (enable nth-minor-id-rmat delete-nth-runit))))

(defthmd minor-id-rmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n))
	   (equal (minor j j (id-rmat n))
	          (id-rmat (1- n))))
  :hints (("Goal" :use ((:instance rmat-entry-diff-lemma (m (1- n)) (n (1- n)) (a (minor j j (id-rmat n))) (b (id-rmat (1- n))))
                        (:instance nth-minor-id-rmat-diagonal (r (car (entry-diff (minor j j (id-rmat n)) (id-rmat (1- n))))))
			(:instance rmatp-minor (i j) (a (id-rmat n)))))))

;; Thus, the corresponding cofactor is (r1), as is the cofactor expansion:

(local-defthmd rdet-minor-id-rmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n))
	   (equal (rdet (minor j j (id-rmat n)) (1- n))
	          (r1)))
  :hints (("Goal" :use (minor-id-rmat-diagonal))))

(local-defthmd expand-rdet-col-aux-id-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n) (natp i) (<= i n))
           (equal (expand-rdet-col-aux (id-rmat n) i j n)
	          (if (> i j) (r1) (r0))))
  :hints (("Subgoal *1/2" :in-theory (enable rdet-cofactor)
                          :use (rdet-minor-id-rmat-diagonal
			        (:instance rdet-minor-id-rmat-0 (i (1- i)))))))

(defthmd expand-rdet-col-id-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n))
           (equal (expand-rdet-col (id-rmat n) j n)
	          (r1)))
  :hints (("Goal" :in-theory (enable expand-rdet-col-aux-id-rmat expand-rdet-col))))

;; Combine this with expand-rdet-col-val:

(defthmd expand-rdet-col-rdet
  (implies (and (rmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-rdet-col a k n)
	          (rdet a n)))
  :hints (("Goal" :use (expand-rdet-col-val (:instance expand-rdet-col-id-rmat (j k))))))

;; It follows from rdet-transpose, expand-rdet-row-transpose, and transpose-rmat-2 that the same holds
;; for row expansion:

(defthmd expand-rdet-row-rdet
  (implies (and (rmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-rdet-row a k n)
	          (rdet a n)))
  :hints (("Goal" :use (rdet-transpose
                        (:instance expand-rdet-row-transpose (i k) (a (transpose-mat a)))
                        (:instance expand-rdet-col-rdet (a (transpose-mat a)))
			(:instance rmatp-transpose (m n))
			(:instance transpose-rmat-2 (m n))))))


;;---------------------------------------------------------------------------------------------------------

;; As a consequence of expand-rdet-row-rdet, we have a recursive version of rdet, based on cofactor
;; expansion with respect to row 0:

(encapsulate ()

(local (include-book "ordinals/lexicographic-book" :dir :system))

(set-well-founded-relation acl2::l<)

(mutual-recursion

  (defund rdet-rec-cofactor (j a n)
    (declare (xargs :measure (list (nfix n) 0 0)))
    (if (zp n)
        ()
      (if (evenp j)
          (rdet-rec (minor 0 j a) (1- n))
        (r- (rdet-rec (minor 0 j a) (1- n))))))

  (defun expand-rdet-rec-aux (a j n)
    (declare (xargs :measure (list (nfix n) 1 (nfix j))))
    (if (zp j)
        (r0)
      (r+ (r* (entry 0 (1- j) a)
              (rdet-rec-cofactor (1- j) a n))
	  (expand-rdet-rec-aux a (1- j) n))))

  (defund expand-rdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 2 0)))
    (expand-rdet-rec-aux a n n))

  (defun rdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 3 0)))
    (if (zp n)
        (r0)
      (if (= n 1)
          (entry 0 0 a)
        (expand-rdet-rec a n))))

))

(local-defun minors (a k)
  (if (zp k)
      ()
    (cons (minor 0 (1- k) a)
          (minors a (1- k)))))

(local (encapsulate ()

  (local (include-book "ordinals/lexicographic-book" :dir :system))

  (set-well-founded-relation acl2::l<)

  (defun rdet-rec-rdet-induct (flg a n)
    (declare (xargs :measure (list (nfix n) (acl2-count a))))
    (if (zp n)
        (list a n)
      (if flg
          (if (consp a)
	      (and (rdet-rec-rdet-induct () (car a) n)
	           (rdet-rec-rdet-induct t (cdr a) n))
            t)
        (if (> n 1)
            (rdet-rec-rdet-induct t (minors a n) (1- n))
	  t))))
))

(local-defun rmat-listp (l n)
  (if (consp l)
      (and (rmatp (car l) n n)
	   (rmat-listp (cdr l) n))
    t))

(local-defun rdet-rec-equal-rdet-listp (l n)
  (if (consp l)
      (and (equal (rdet-rec (car l) n)
	          (rdet (car l) n))
	   (rdet-rec-equal-rdet-listp (cdr l) n))
    t))

(local-defthm rdet-1
  (implies (rmatp a 1 1)
           (equal (rdet a 1)
	          (entry 0 0 a)))
  :hints (("Goal" :in-theory (enable rdet-term rdet)
                  :expand ((rdet-prod a '(0) 1)))))

(local-defthm rmat-listp-minors
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp k) (<= k n))
           (rmat-listp (minors a k) (1- n)))
  :hints (("Subgoal *1/5" :use ((:instance rmatp-minor (i 0) (j (1- k)))))))

(local-defthmd expand-rdet-rec-aux-rewrite
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (<= j n)
                (rdet-rec-equal-rdet-listp (minors a j) (1- n)))
           (equal (expand-rdet-rec-aux a j n)
	          (expand-rdet-row-aux a 0 j n)))
  :hints (("Goal" :in-theory (enable rdet-cofactor rdet-rec-cofactor))))

(local-defthm rdet-rec-rewrite
  (implies (and (rmatp a n n) (natp n) (> n 1)
                (rdet-rec-equal-rdet-listp (minors a n) (1- n)))
	   (equal (rdet-rec a n) (rdet a n)))
  :hints (("Goal" :in-theory (e/d (expand-rdet-rec expand-rdet-row) (expand-rdet-rec-aux expand-rdet-row-aux))
                  :use ((:instance expand-rdet-rec-aux-rewrite (j n))
		        (:instance expand-rdet-row-rdet (k 0))))))

(local-defthm rdet-rec-rdet-lemma
  (implies (posp n)
           (if flg
               (implies (rmat-listp x n)
	                (rdet-rec-equal-rdet-listp x n))
	     (implies (rmatp x n n)
	              (equal (rdet-rec x n) (rdet x n)))))
  :rule-classes ()
  :hints (("Goal" :induct (rdet-rec-rdet-induct flg x n))
          ("Subgoal *1/5" :use ((:instance rmat-listp-minors (a x) (k n))))))

(defthmd rdet-rec-rdet
  (implies (and (rmatp a n n) (posp n))
           (equal (rdet-rec a n)
	          (rdet a n)))
  :hints (("Goal" :use ((:instance rdet-rec-rdet-lemma (flg ()) (x a))))))


;;---------------------------------------------------------------------------------------------------------
;;    Classical Adjoint
;;---------------------------------------------------------------------------------------------------------

;; Given an nxn matrix a, we shall define its cofactor matrix (cofactor-rmat a n) to be the nxn
;; matrix with entries

;;    (entry i j (cofactor-rmat a n)) = (rdet-cofactor i j a n).

;; We begin by defining the ith row of the cofactor matrix:

(defun cofactor-rmat-row-aux (i j a n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp n) (> n 1) (natp j) (< j n))
      (cons (rdet-cofactor i j a n)
            (cofactor-rmat-row-aux i (1+ j) a n))
    ()))

(defund cofactor-rmat-row (i a n)
  (cofactor-rmat-row-aux i 0 a n))

(local-defthmd rlistnp-cofactor-rmat-row-aux
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (<= j n))
           (rlistnp (cofactor-rmat-row-aux i j a n)
	            (- n j))))

(defthm rlistnp-cofactor-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (rlistnp (cofactor-rmat-row i a n) n))
  :hints (("Goal" :in-theory (enable cofactor-rmat-row)
                  :use ((:instance rlistnp-cofactor-rmat-row-aux (j 0))))))

(local-defun nth-cofactor-rmat-row-aux-induct (j k n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp n) (natp j) (< j n))
      (list (nth-cofactor-rmat-row-aux-induct (1+ j) (1- k) n))
    (list j k n)))

(local-defthmd nth-cofactor-rmat-row-aux
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (<= j n)
                (natp k) (< k (- n j)))
           (equal (nth k (cofactor-rmat-row-aux i j a n))
	          (rdet-cofactor i (+ j k) a n)))
  :hints (("Goal" :induct (nth-cofactor-rmat-row-aux-induct j k n))))

(defthmd nth-cofactor-rmat-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (nth j (cofactor-rmat-row i a n))
	          (rdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable cofactor-rmat-row)
                  :use ((:instance nth-cofactor-rmat-row-aux (j 0) (k j))))))

;; The cofactor matrix may now be defined:

(defun cofactor-rmat-aux (i a n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp n) (natp i) (< i n))
      (cons (cofactor-rmat-row i a n)
            (cofactor-rmat-aux (1+ i) a n))
    ()))

(defund cofactor-rmat (a n)
  (cofactor-rmat-aux 0 a n))

(local-defthmd rmatp-cofactor-rmat-aux
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (<= i n))
           (rmatp (cofactor-rmat-aux i a n) (- n i) n)))

(defthm rmatp-cofactor-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (rmatp (cofactor-rmat a n) n n))
  :hints (("Goal" :in-theory (enable cofactor-rmat)
                  :use ((:instance rmatp-cofactor-rmat-aux (i 0))))))

(local-defthmd nth-cofactor-rmat-aux
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (<= i n) (natp k) (< k (- n i)))
           (equal (nth k (cofactor-rmat-aux i a n))
	          (cofactor-rmat-row (+ i k) a n)))
  :hints (("Goal" :induct (nth-cofactor-rmat-row-aux-induct i k n))))

(defthmd nth-cofactor-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (nth i (cofactor-rmat a n))
	          (cofactor-rmat-row i a n)))
  :hints (("Goal" :in-theory (enable cofactor-rmat)
                  :use ((:instance nth-cofactor-rmat-aux (i 0) (k i))))))

(defthmd cofactor-rmat-entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (cofactor-rmat a n))
	          (rdet-cofactor i j a n)))
  :hints (("Goal" :use (nth-cofactor-rmat nth-cofactor-rmat-row))))

;; The classsical adjoint of a is the transpose of its cofactor matrix:

(defund adjoint-rmat (a n)
  (transpose-mat (cofactor-rmat a n)))

(defthm rmatp-adjoint
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (rmatp (adjoint-rmat a n) n n))
  :hints (("Goal" :in-theory (enable adjoint-rmat)
                  :use (rmatp-cofactor-rmat
		        (:instance rmatp-transpose (a (cofactor-rmat a n)) (m n))))))

(defthmd adjoint-rmat-entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (adjoint-rmat a n))
	          (rdet-cofactor j i a n)))
  :hints (("Goal" :in-theory (enable adjoint-rmat)
                  :use ((:instance cofactor-rmat-entry (i j) (j i))
		        (:instance transpose-rmat-entry (a (cofactor-rmat a n)) (m n) (i j) (j i))))))

;; By cofactor-rmat-entry and rdet-cofactor-transpose,

;;    (entry i j (cofactor-rmat (transpose-mat a) n))
;;      = (rdet-cofactor i j (transpose-mat a) n)
;;      = (rdet-cofactor j i a n))
;;      = (entry j i (cofactor-fmat a n))
;;      = (entry i j (transpose-mat (cofactor-rmat a n)))
;;      = (entry i j (adjoint-rmat a n))

(defthmd cofactor-rmat--entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (cofactor-rmat (transpose-mat a) n))
                  (entry i j (adjoint-rmat a n))))
  :hints (("Goal" :use (adjoint-rmat-entry
                        (:instance rmatp-transpose (m n))
                        (:instance cofactor-rmat-entry (a (transpose-mat a)))
                        (:instance transpose-rmat-entry (m n) (i j) (j i))
			(:instance cofactor-rmat-entry (i j) (j i))))))

;; Therefore,

(defthmd cofactor-rmat-transpose
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (equal (cofactor-rmat (transpose-mat a) n)
	          (adjoint-rmat a n)))
  :hints (("Goal" :use ((:instance rmat-entry-diff-lemma (a (cofactor-rmat (transpose-mat a) n))
                                                         (b (adjoint-rmat a n))
							 (m n))
                        (:instance rmatp-transpose (m n))
			(:instance cofactor-rmat--entry
			             (i (car (entry-diff (cofactor-rmat (transpose-mat a) n) (adjoint-rmat a n))))
			             (j (cdr (entry-diff (cofactor-rmat (transpose-mat a) n) (adjoint-rmat a n)))))))))

;; Note that the the dot product of (row i a) and (cofactor-rmat-row i a n) is a rearrangemnt of
;; the sum (expand-rdet-row a i n):

(local-defund co-prod (i j a n)
  (r* (entry i j a)
      (rdet-cofactor i j a n)))

(local-defthm rp-coprod
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n) (natp i) (< i n))
           (rp (co-prod i j a n)))
  :hints (("Goal" :in-theory (e/d (co-prod) (rp-rdet-cofactor))
                  :use (rp-rdet-cofactor (:instance rp-entry (m n))))))

(local-defun nlistp (l n)
  (if (consp l)
      (and (natp (car l)) (< (car l) n)
           (nlistp (cdr l) n))
    t))

(local-defun co-prod-sum (i l a n)
  (if (consp l)
      (r+ (co-prod i (car l) a n)
          (co-prod-sum i (cdr l) a n))
    (r0)))

(local-defun nlist (n)
  (if (zp n)
      ()
    (cons (1- n) (nlist (1- n)))))

(local-defthm nlistp-nlist
  (implies (and (natp n) (natp m) (<= m n))
           (nlistp (nlist m) n)))

(local-defthmd expand-rdet-row-aux-rewrite
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (<= j n) (natp i) (< i n))
           (equal (expand-rdet-row-aux a i j n)
	          (co-prod-sum i (nlist j) a n)))
  :hints (("Subgoal *1/5" :in-theory (e/d (co-prod) (nth rmatp)))))

(local-defthmd expand-rdet-row-rewrite
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (expand-rdet-row a i n)
	          (co-prod-sum i (nlist n) a n)))
  :hints (("Goal" :in-theory (enable expand-rdet-row)
                  :use ((:instance expand-rdet-row-aux-rewrite (j n))))))



(local-defthmd cofactor-rmat-row-aux-replace-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (<= j n)
                (rlistnp x n))
	   (equal (cofactor-rmat-row-aux i j (replace-row a i x) n)
                  (cofactor-rmat-row-aux i j a n)))
  :hints (("Subgoal *1/4" :in-theory (enable cofactor-replace-rmat-row))))

(defthm cofactor-rmat-row-replace-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n)
                (rlistnp x n))
	   (equal (cofactor-rmat-row i (replace-row a i x) n)
                  (cofactor-rmat-row i a n)))
  :hints (("Goal" :in-theory (enable cofactor-rmat-row-aux-replace-row cofactor-rmat-row))))

(local-defun nlistr (j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (posp n) (natp j) (< j n))
      (cons j (nlistr (1+ j) n))
    ()))

(local-defthm nlistp-nlistr
  (implies (and (natp n) (natp j) (<= j n))
           (nlistp (nlistr j n) n)))

(local-defun a-row (i j a n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (posp n) (natp j) (< j n))
      (cons (entry i j a) (a-row i (1+ j) a n))
    ()))

(local-defthmd cons-nth-nthcdr
  (implies (and (natp j) (< j (len l)))
           (equal (CONS (NTH J l) (CDR (NTHCDR J l)))
	          (nthcdr j l))))

(local-defthmd nthcdr-len
  (implies (true-listp l)
           (null (nthcdr (len l) l))))

(local-defthmd a-row-nthcdr
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (<= j n) (natp i) (< i n))
           (equal (a-row i j a n) (nthcdr j (row i a))))
  :hints (("Goal" :in-theory (e/d (cdr-nthcdr) (rmatp)))
          ("Subgoal *1/4" :use ((:instance cons-nth-nthcdr (l (row i a)))))
	  ("Subgoal *1/5" :in-theory (disable RLISTNP-NTH MEMBER-RMATP-RLISTNP rlistnp-row)
	                  :use ((:instance nthcdr-len (l (row i a)))
	                        (:instance rlistnp-row (m n))))))

(local-defthmd rdot-cofactor-rmat-row-aux-rewrite
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp j) (< j n) (natp i) (< i n))
           (equal (rdot (a-row i j a n) (cofactor-rmat-row-aux i j a n))
	          (co-prod-sum i (nlistr j n) a n)))
  :hints (("Goal" :in-theory (enable co-prod))))

(local-defthmd rdot-cofactor-rmat-row-rewrite
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (rdot (row i a) (cofactor-rmat-row i a n))
	          (co-prod-sum i (nlistr 0 n) a n)))
  :hints (("Goal" :in-theory (enable cofactor-rmat-row)
                  :use ((:instance a-row-nthcdr (j 0))
		        (:instance rdot-cofactor-rmat-row-aux-rewrite (j 0))))))

(local-defthmd member-nlist
  (implies (natp n)
           (iff (member x (nlist n))
	        (and (natp x) (< x n)))))

(local-defthmd dlistp-nlist
  (implies (natp n)
           (dlistp (nlist n)))
  :hints (("Subgoal *1/4" :use ((:instance member-nlist (x (1- n)) (n (1- n)))))))

(local-defthmd member-nlistr
  (implies (and (natp n) (natp j) (<= j n))
           (iff (member x (nlistr j n))
	        (and (natp x) (>= x j) (< x n)))))

(local-defthmd member-nlist-nlistr
  (implies (natp n)
           (iff (member x (nlist n))
	        (member x (nlistr 0 n))))
  :hints (("Goal" :use (member-nlist (:instance member-nlistr (j 0))))))

(local-defthmd dlistp-nlistr
  (implies (and (natp n) (natp j) (<= j n))
           (dlistp (nlistr j n)))
  :hints (("Subgoal *1/4" :use ((:instance member-nlistr (x j) (j (1+ j)))))))

(local-defthmd permp-nlist-nlistr
  (implies (natp n)
           (permp (nlist n) (nlistr 0 n)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (dlistp-nlist
		        (:instance dlistp-nlistr (j 0))
			(:instance scex1-lemma (l (nlist n)) (m (nlistr 0 n)))
			(:instance scex1-lemma (m (nlist n)) (l (nlistr 0 n)))
			(:instance member-nlist-nlistr (x (scex1 (nlist n) (nlistr 0 n))))
			(:instance member-nlist-nlistr (x (scex1 (nlistr 0 n) (nlist n))))))))

(local-defthmd co-prod-sum-permp
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n)
                (dlistp l) (dlistp m) (nlistp l n) (nlistp m n) (permp l m))
	   (equal (co-prod-sum i l a n)
	          (co-prod-sum i m a n)))
  :hints (("Goal" :use ((:functional-instance rval-sum-permp
                          (rargp (lambda (x) (if (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
			                         (member x (nlist n)) (rargp x))))
			  (rval (lambda (x) (if (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
			                        (co-prod i x a n) (rval x))))
			  (rarg-listp (lambda (x) (if (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
			                              (nlistp x n) (rarg-listp x))))
			  (rval-sum (lambda (x) (if (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
			                            (co-prod-sum i x a n) (rval-sum x)))))))
	  ("Subgoal 2" :use (member-nlist))
	  ("Subgoal 1" :use ((:instance member-nlist (x (car l)))))))

(defthmd rdot-cofactor-rmat-row-expand-rdet-row
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (rdot (row i a) (cofactor-rmat-row i a n))
                  (expand-rdet-row a i n)))
  :hints (("Goal" :use (expand-rdet-row-rewrite rdot-cofactor-rmat-row-rewrite dlistp-nlist permp-nlist-nlistr
                        (:instance dlistp-nlistr (j 0))
                        (:instance co-prod-sum-permp (l (nlist n)) (m (nlistr 0 n)))))))

;; Combining this with expand-rdet-row-rdet, we have the following expression for the determinant:

(defthmd rdot-cofactor-rmat-row-rdet
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (rdot (row i a) (cofactor-rmat-row i a n))
                  (rdet a n)))
  :hints (("Goal" :use (rdot-cofactor-rmat-row-expand-rdet-row
                        (:instance expand-rdet-row-rdet (k i))))))

;; Next we substitute (replace-row a i (row k a)) for a in rdot-cofactor-rmat-row-rdet, where k <> i.
;; Since this matrix has 2 identical rows, its determinant is (r0) by rdet-alternating, and we have

(defthmd rdot-cofactor-rmat-row-rdet-0
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp k) (< k n) (not (= k i)))
           (equal (rdot (row k a) (cofactor-rmat-row i a n))
                  (r0)))
  :hints (("Goal" :use ((:instance rdot-cofactor-rmat-row-rdet (a (replace-row a i (row k a))))
		        (:instance rlistnp-row (m n) (i k))
			(:instance rdet-alternating (a (replace-row a i (row k a))) (j k))))))

;; Thus, we have the following for general k:

(defthmd rdot-cofactor-rmat-row-rdelta
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp k) (< k n))
           (equal (rdot (row k a) (cofactor-rmat-row i a n))
                  (r* (rdelta i k) (rdet a n))))
  :hints (("Goal" :use (rdot-cofactor-rmat-row-rdet rdot-cofactor-rmat-row-rdet-0))))

;; This yields an expression for the nxn matrix product of a and its adjoint:

(defthmd rmatp-rmat*-adjoint
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (rmatp (rmat* a (adjoint-rmat a n)) n n))
  :hints (("Goal" :use ((:instance rmatp-rmat* (b (adjoint-rmat a n)) (m n) (p n))))))

(defthmd rmat*-adjoint-entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (rmat* a (adjoint-rmat a n)))
	          (r* (rdelta i j) (rdet a n))))
  :hints (("Goal" :in-theory (enable adjoint-rmat)
                  :use (rmatp-adjoint
		        (:instance rmat*-entry (m n) (p n) (b (adjoint-rmat a n)))
                        (:instance col-transpose-rmat (m n) (a (cofactor-rmat a n)))
                        (:instance nth-cofactor-rmat (i j))
			(:instance rdot-cofactor-rmat-row-rdelta (k i) (i j))))))

(defthm rmatp-rmat-scalar-mul-rdet-id-mat
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (rmatp (rmat-scalar-mul (rdet a n) (id-rmat n)) n n))
  :hints (("Goal" :in-theory (enable rmatp-rmat-scalar-mul))))

(defthmd rmat-scalar-mul-rdet-id-mat-entry
  (implies (and (rmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (rmat-scalar-mul (rdet a n) (id-rmat n)))
	          (r* (rdelta i j) (rdet a n))))
  :hints (("Goal" :in-theory (enable entry-id-rmat)
                  :use ((:instance rmat-scalar-mul-entry (c (rdet a n)) (a (id-rmat n)) (m n))))))

(defthmd rmat*-adjoint-rmat
  (implies (and (rmatp a n n) (natp n) (> n 1))
           (equal (rmat* a (adjoint-rmat a n))
	          (rmat-scalar-mul (rdet a n) (id-rmat n))))
  :hints (("Goal" :use (rmatp-rmat*-adjoint rmatp-rmat-scalar-mul-rdet-id-mat
                        (:instance rmat-entry-diff-lemma (m n)
			                            (a (rmat* a (adjoint-rmat a n)))
						    (b (rmat-scalar-mul (rdet a n) (id-rmat n))))
                        (:instance rmat*-adjoint-entry
			             (i (car (entry-diff (rmat* a (adjoint-rmat a n))
				                         (rmat-scalar-mul (rdet a n) (id-rmat n)))))
			             (j (cdr (entry-diff (rmat* a (adjoint-rmat a n))
				                         (rmat-scalar-mul (rdet a n) (id-rmat n))))))
                        (:instance rmat-scalar-mul-rdet-id-mat-entry
			             (i (car (entry-diff (rmat* a (adjoint-rmat a n))
				                         (rmat-scalar-mul (rdet a n) (id-rmat n)))))
			             (j (cdr (entry-diff (rmat* a (adjoint-rmat a n))
				                         (rmat-scalar-mul (rdet a n) (id-rmat n))))))))))
