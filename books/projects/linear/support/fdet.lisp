(in-package "DM")

(include-book "fmat")
(include-book "projects/groups/symmetric" :dir :system)

;; The term contributed by a permutation p in (sym n) to the determinant of an nxn
;;  matrix a is computed as follows:
;;   (1) select an entry from each row of a, the selection from row i being the one
;;       in column (nth i p), i.e., (entry i (nth i p) a);
;;   (2) compute the product of these n entries;
;;   (3) negate the product if p is an odd permutation.

(defun fdet-prod (a p n)
  (if (zp n)
      (f1)
    (f* (fdet-prod a p (1- n))
        (entry (1- n) (nth (1- n) p) a))))

(defund fdet-term (a p n)
  (if (even-perm-p p n)
      (fdet-prod a p n)
    (f- (fdet-prod a p n))))

;; The determinant of a is the sum over (slist n) of these signed products:

(defun fdet-sum (a l n)
  (if (consp l)
      (f+ (fdet-term a (car l) n)
	  (fdet-sum a (cdr l) n))
    (f0)))

(defund fdet (a n)
  (fdet-sum a (slist n) n))

;; We shall derive an equivalent definition of fdet-prod that allows us to apply the results of
;; "ring.lisp" by functional instantiation.

;; First we define a predicate that recognizes a pair of natural numbers that determine an entry of a:

(local-defund pairp (x n)
  (and (consp x)
       (natp (car x)) (< (car x) n)
       (natp (cdr x)) (< (cdr x) n)))

(local-defund pair-val (x a)
  (entry (car x) (cdr x) a))

;; Under suitable constraints on n and a, pairp and pair-val satisfy the constraint on fargp and fval
;; (see ring.lisp):

(local-defthm fp-pair-val
  (implies (and (pairp x n) (posp n) (fmatp a n n))
           (fp (pair-val x a)))
  :hints (("Goal" :in-theory (enable pair-val pairp)
                  :use ((:instance fp-entry (m n) (i (car x)) (j (cdr x)))))))

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
      (f* (pair-val (car l) a)
          (pairs-prod (cdr l) a))
    (f1)))

(local-defthm fp-pairs-prod
  (implies (and (posp n) (fmatp a n n)
                (pair-listp l n))
           (fp (pairs-prod l a))))

(local-defthm pairs-prod-append
  (implies (and (fmatp a n n) (posp n)
                (pair-listp l n)
		(pairp x n))
           (equal (pairs-prod (append l (list x)) a)
                  (f* (pairs-prod l a)
		      (pair-val x a))))
  :hints (("Subgoal *1/2" :use ((:instance f*assoc (x (PAIR-VAL (CAR L) A)) (y (PAIRS-PROD (CDR L) A)) (z (PAIR-VAL X A)))))))

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
  
;; We have the following equivalent formulation of fdet-prod:

(local-defthmd fdet-prod-rewrite
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(natp k) (<= k n))
           (equal (fdet-prod a p k)
	          (pairs-prod (perm-pairs k p) a)))		  
  :hints (("Subgoal *1/5'" :in-theory (enable pair-val perm-pair))))

;; The determinant is a ring element:

;; By pair-listp-perm-pairs and fp-pairs-prod, fdet-prod and fdet-term return ring elements:

(defthm fp-fdet-prod
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(natp k) (<= k n))
           (fp (fdet-prod a p k)))
  :hints (("Goal" :in-theory (enable fdet-prod-rewrite))))

(defthm fp-fdet-term
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n)))
           (fp (fdet-term a p n)))
  :hints (("Goal" :in-theory (enable fdet-term))))

;; The following result, which will be used in the next section, is derived by functional instantiation
;; of fval-prod-permp:

(local-defthmd pairs-prod-permp
  (implies (and (posp n) (fmatp a n n)
                (dlistp l) (pair-listp l n)
		(dlistp m) (pair-listp m n)
		(permp l m))
           (equal (pairs-prod l a)
	          (pairs-prod m a)))
  :hints (("Goal" :use ((:functional-instance fval-prod-permp
                          (fargp (lambda (x) (if (and (posp n) (fmatp a n n)) (pairp x n) (fargp x))))
                          (fval (lambda (x) (if (and (posp n) (fmatp a n n)) (pair-val x a) (fval x))))
                          (farg-listp (lambda (x) (if (and (posp n) (fmatp a n n)) (pair-listp x n) (farg-listp x))))
			  (fval-prod (lambda (x) (if (and (posp n) (fmatp a n n)) (pairs-prod x a) (fval-prod x)))))))))

;; We similarly derive the following functional instances of fp-fval-sum, fval-sum-append, and
;; fval-sum-permp:

(local-defthm fp-fdet-sum
  (implies (and (fmatp a n n) (posp n)
                (sublistp l (slist n)))
	   (fp (fdet-sum a l n))))

(defthm fp-fdet
  (implies (and (fmatp a n n) (posp n))
	   (fp (fdet a n)))
  :hints (("Goal" :in-theory (enable fdet))))

(local-defthmd fdet-sum-append
  (implies (and (fmatp a n n) (posp n)
                (sublistp l (slist n))
		(sublistp m (slist n)))
	   (equal (fdet-sum a (append l m) n)
	          (f+ (fdet-sum a l n)
		      (fdet-sum a m n))))
  :hints (("Subgoal *1/2" :use ((:instance f+assoc (x (FDET-TERM A (CAR L) N)) (y (FDET-SUM A (CDR L) N)) (z (FDET-SUM A M N)))))))

(local-defthmd fdet-sum-permp
  (implies (and (fmatp a n n) (posp n)
                (dlistp l) (sublistp l (slist n))
		(dlistp m) (sublistp m (slist n))
		(permp l m))
	   (equal (fdet-sum a l n)
	          (fdet-sum a m n)))		      
  :hints (("Goal" :use ((:functional-instance fval-sum-permp
                          (fargp (lambda (x) (if (and (posp n) (fmatp a n n)) (member x (slist n)) (fargp x))))
                          (fval (lambda (x) (if (and (posp n) (fmatp a n n)) (fdet-term a x n) (fval x))))
                          (farg-listp (lambda (x) (if (and (posp n) (fmatp a n n)) (sublistp x (slist n)) (farg-listp x))))
			  (fval-sum (lambda (x) (if (and (posp n) (fmatp a n n)) (fdet-sum a x n) (fval-sum x)))))))))


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
           (equal (pairs-prod l (id-fmat n))
	          (f0)))
  :hints (("Subgoal *1/2" :in-theory (enable perm-pair pair-val)
                          :use (least-moved-perm
			        (:instance len-perm (x p))
				(:instance member-perm (x p) (k (nth (least-moved p) p)))
			        (:instance entry-id-fmat (i (least-moved p))
				                         (j (nth (least-moved p) p)))))))

(local-defthmd fdet-term-id-fmat
  (implies (and (posp n) (member p (slist n)) (not (= p (ninit n))))
           (equal (fdet-term (id-fmat n) p n)
	          (f0)))
  :hints (("Goal" :in-theory (enable fdet-prod-rewrite fdet-term)
                  :use (least-moved-perm
		        (:instance member-least-moved-pairs (k n))
			(:instance fdet-prod-rewrite (a (id-fmat n)) (k n))
			(:instance pairs-prod-r0 (l (perm-pairs n p)))))))

(local-defthmd pairs-prod-ninit
  (implies (and (posp n) (natp k) (<= k n))
           (equal (pairs-prod (perm-pairs k (ninit n)) (id-fmat n))
	          (f1)))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :in-theory (e/d (pairp pair-val perm-pair)
	                                  (pair-listp-perm-pairs pairs-prod-append))
	                  :use ((:instance pairs-prod-append (l (perm-pairs (1- k) (ninit n)))
	                                                     (a (id-fmat n))
							     (x (perm-pair (1- k) (ninit n))))
				(:instance pair-listp-perm-pairs (p (ninit n)) (k (1- k)))))))

(local-defthmd fdet-term-id-fmat-ninit
  (implies (posp n)
           (equal (fdet-term (id-fmat n) (ninit n) n)
	          (f1)))
  :hints (("Goal" :in-theory (enable fdet-term)
                  :use ((:instance pairs-prod-ninit (k n))
			(:instance fdet-prod-rewrite (a (id-fmat n)) (p (ninit n)) (k n))))))
			

(local-defthmd fdet-sum-id-fmat
  (implies (and (posp n) (dlistp l) (sublistp l (slist n)))
           (equal (fdet-sum (id-fmat n) l n)
	          (if (member (ninit n) l)
		      (f1) (f0))))		      
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use (fdet-term-id-fmat-ninit (:instance fdet-term-id-fmat (p (car l)))))))

;; To compute (fdet (id-fmat n) n), note that if p is any permutation other than (ninit n), we can find
;; i < n such that (nth i p) <> i, and hence (entry i (nth i p) (id-fmat n)) = (f0), which implies
;; (fdet-term (id-fmat p n)) = (f0).  On the other hand, (nth i (ninit n)) = i for all i, which implies
;; (fdet-term (id-fmat (ninit n) n)) = (f1).   Thus,

(defthm fdet-id-fmat
  (implies (posp n)
           (equal (fdet (id-fmat n) n)
	          (f1)))
  :hints (("Goal" :in-theory (enable fdet)
                  :use ((:instance fdet-sum-id-fmat (l (slist n)))))))


;;-------------------------------------------------------------------------------------------------------

;; fdet is invariant under transpose-mat.  This follows from the observation that the term contributed
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
  (implies (and (fmatp a n n) (posp n) (member p (slist n)))
           (equal (pairs-prod (flip-perm-pairs n p) a)
	          (pairs-prod (perm-pairs n (inv-perm p n)) a)))
  :hints (("Goal" :in-theory (enable pair-listp-flip-perm-pairs)
                  :use (permp-flip-perm-pairs
                        (:instance pairs-prod-permp (l (flip-perm-pairs n p)) (m (perm-pairs n (inv-perm p n))))))))

(local-defthmd pairs-prod-perm-pairs-transpose
  (implies (and (fmatp a n n) (posp n) (member p (slist n))
                (natp k) (<= k n))
           (equal (pairs-prod (flip-perm-pairs k p) a)
	          (pairs-prod (perm-pairs k p) (transpose-mat a))))
  :hints (("Subgoal *1/5" :in-theory (enable pair-listp-perm-pairs pair-listp-flip-perm-pairs)
                          :use ((:instance fmatp-transpose (m n))))
	  ("Subgoal *1/5''" :in-theory (e/d (pair-val perm-pair flip-perm-pair) (entry))
	                    :use ((:instance transpose-fmat-entry (m n) (i (1- k)) (j (nth (1- k) p)))
			          (:instance nth-perm (i (1- k)))))))

(local-defthmd pairs-prod-inv-perm-pairs-transpose
  (implies (and (fmatp a n n) (posp n) (member p (slist n)))
           (equal (pairs-prod (perm-pairs n (inv-perm p n)) a)
	          (pairs-prod (perm-pairs n p) (transpose-mat a))))
  :hints (("Goal" :use (pairs-prod-flip-perm-pairs
                        (:instance pairs-prod-perm-pairs-transpose (k n))))))
  
(defthmd fdet-term-transpose
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n)))
           (equal (fdet-term (transpose-mat a) p n)
	          (fdet-term a (inv-perm p n) n)))
  :hints (("Goal" :in-theory (enable even-perm-p fdet-prod-rewrite fdet-term)  
                  :use (pairs-prod-inv-perm-pairs-transpose parity-inv
		        (:instance fmatp-transpose (m n))))))

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

(local-defthmd fdet-sum-inv-perms
  (implies (and (posp n) (fmatp a n n))
           (equal (fdet-sum a (inv-perms (slist n) n) n)
	          (fdet-sum a (slist n) n)))
  :hints (("Goal" :use (permp-inv-perms sublistp-inv-perms-slist
                        (:instance fdet-sum-permp (l (inv-perms (slist n) n)) (m (slist n)))))))

(local-defthmd fdet-sum-transpose
  (implies (and (posp n) (fmatp a n n) (sublistp l (slist n)))
           (equal (fdet-sum a (inv-perms l n) n)
	          (fdet-sum (transpose-mat a) l n)))
  :hints (("Subgoal *1/2" :use ((:instance fdet-term-transpose (p (car l)))))))

(defthmd fdet-transpose
  (implies (and (posp n) (fmatp a n n))
           (equal (fdet (transpose-mat a) n)
	          (fdet a n)))
  :hints (("Goal" :in-theory (enable fdet)
                  :use (fdet-sum-inv-perms
		        (:instance fdet-sum-transpose (l (slist n)))))))


;;-------------------------------------------------------------------------------------------------------

;; fdet is alternating, i.e., if 2 rows of a are equal, then its determinant is (f0).

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
  (implies (and (fmatp a n n) (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
           (equal (pair-val (perm-pair i (comp-perm p (transpose i j n) n))  a)
                  (pair-val (perm-pair j p) a)))
  :hints (("Goal" :in-theory (enable pair-val perm-pair transpose-vals)
                  :use ((:instance nth-comp-perm (x p) (y (transpose i j n)) (k i))))))

(local-defthmd pair-val-perm-pair-comp-perm-2
  (implies (and (fmatp a n n) (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
           (equal (pair-val (perm-pair j (comp-perm p (transpose i j n) n))  a)
                  (pair-val (perm-pair i p) a)))
  :hints (("Goal" :in-theory (enable pair-val perm-pair transpose-vals)
                  :use ((:instance nth-comp-perm (x p) (y (transpose i j n)) (k i))))))

(local-defthmd pair-val-perm-pair-comp-perm-3
  (implies (and (fmatp a n n) (posp n) (member p (slist n))
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(posp k) (<= k n) (not (= (1- k) i)) (not (= (1- k) j))
		(member p (slist n)))
           (equal (pair-val (perm-pair (1- k) (comp-perm p (transpose i j n) n))  a)
                  (pair-val (perm-pair (1- k) p) a)))
  :hints (("Goal" :in-theory (e/d (pair-val perm-pair transpose-vals) (nth-comp-perm))
                  :use ((:instance nth-comp-perm (x p) (y (transpose i j n)) (k (1- k)))))))

(local-defthmd pairs-prod-perm-pairs-alt-comp-perm
  (implies (and (fmatp a n n) (posp n) (member p (slist n))
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
  (implies (and (fmatp a n n) (posp n) 
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
;; p' = (comp-perm p (transpose i j n) n).  Then the factors of (fdet-prod a p' n) are the same as
;; those of (fdet-prod a p n):

(defthmd fdet-prod-comp-perm
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (fdet-prod a (comp-perm p (transpose i j n) n) n)
	          (fdet-prod a p n)))
  :hints (("Goal" :in-theory (e/d (fdet-prod-rewrite) (sym-closed))
                  :use (pairs-prod-perm-pairs-comp-perm permp-transpose
			(:instance sym-closed (x p) (y (transpose i j n)))))))

;; If p is even, then p' is odd, and therefore (fdet-term a p' n) is the negative of (fdet-term a p n):

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

(defthmd fdet-term-comp-perm
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(member p (slist n)))
	   (equal (f+ (fdet-term a (comp-perm p (transpose i j n) n) n)
	              (fdet-term a p n))
		  (f0)))
  :hints (("Goal" :in-theory (enable fdet-prod-comp-perm fdet-term))))

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

(local-defthmd fp-comp-perm-transpose-list
  (implies (and (posp n) (sublistp l (slist n)) (fmatp a n n)
		(natp i) (< i n) (natp j) (< j n) (not (= i j)))                
           (fp (fdet-sum a (comp-perm-transpose-list l n i j) n))))

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
  (implies (and (fmatp a n n) (posp n) 
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
  (implies (and (fp a) (fp d) (fp at) (fp td)
                (= (f+ at a) (f0))
		(= (f+ td d) (f0)))
	   (equal (f+ (f+ at td) (f+ a d)) (f0)))
  :hints (("Goal" :use ((:instance f+assoc (x at) (y td) (z (f+ a d)))
                        (:instance f+assoc (x td) (y a) (z d))
			(:instance f+comm (x a) (y td))
			(:instance f+assoc (x a) (y td) (z d))))))

(local-defthmd fdet-sum-comp-perm-transpose-list
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(sublistp l (slist n)))
	   (equal (f+ (fdet-sum a (comp-perm-transpose-list l n i j) n)
	              (fdet-sum a l n))
		  (f0)))
  :hints (("Subgoal *1/2" :use ((:instance hack-1 (at (FDET-TERM A (COMP-PERM (CAR L) (TRANSPOSE I J N) N) N))
                                                  (td (FDET-SUM A (COMP-PERM-TRANSPOSE-LIST (CDR L) N I J) N))
						  (a (FDET-TERM A (CAR L) N))
						  (d (FDET-SUM A (CDR L) N)))
				(:instance fdet-term-comp-perm (p (car l)))
				(:instance fp-comp-perm-transpose-list (l (cdr l)))))))

(local-defthmd member-comp-perm-transpose-list-even-perms
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a))
		(sublistp l (even-perms n))
		(member x (comp-perm-transpose-list l n i j)))
	   (not (even-perm-p x n)))	   
  :hints (("Subgoal *1/2" :use ((:instance even-perms-even (p (car l)))))))


(local-defthmd disjointp-comp-perm-transpose-list
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (disjointp (comp-perm-transpose-list (even-perms n) n i j)
	              (even-perms n)))
  :hints (("Goal" :use ((:instance common-member-shared (l (comp-perm-transpose-list (even-perms n) n i j)) (m (even-perms n)))
                        (:instance member-comp-perm-transpose-list-even-perms
				     (l (even-perms n))
			             (x (common-member (comp-perm-transpose-list (even-perms n) n i j)
						       (even-perms n))))
			(:instance even-perms-even (p (common-member (comp-perm-transpose-list (even-perms n) n i j)
								     (even-perms n))))))))

(local-defthmd dlistp-append-comp-perm-transpose-list
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (dlistp (append (comp-perm-transpose-list (even-perms n) n i j)
	                   (even-perms n))))
  :hints (("Goal" :use (disjointp-comp-perm-transpose-list
                        (:instance dlistp-comp-perm-transpose-list (l (even-perms n)))))))

(local-defthm len-append
  (equal (len (append l m))
         (+ (len l) (len m))))

(local-defthmd len-append-comp-perm-transpose-list
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (equal (len (append (comp-perm-transpose-list (even-perms n) n i j)
	                       (even-perms n)))
		  (fact n)))
  :hints (("Goal" :in-theory (enable order)
                  :use (order-alt))))

(local-defthmd sublistp-append-comp-perm-transpose-list
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (sublistp (append (comp-perm-transpose-list (even-perms n) n i j)
	                     (even-perms n))
		     (slist n)))
  :hints (("Goal" :use ((:instance sublistp-comp-perm-transpose-list-slist (l (even-perms n)))))))

(local-defthmd permp--append-comp-perm-transpose-list
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (permp (append (comp-perm-transpose-list (even-perms n) n i j)
	                  (even-perms n))
		  (slist n)))
  :hints (("Goal" :use (sublistp-append-comp-perm-transpose-list dlistp-append-comp-perm-transpose-list
                        len-append-comp-perm-transpose-list len-slist
                        (:instance permp-eq-len (l (append (comp-perm-transpose-list (even-perms n) n i j) (even-perms n)))
                                                (m (slist n)))))))

(defthmd fdet-alternating
  (implies (and (fmatp a n n) (posp n) 
		(natp i) (< i n) (natp j) (< j n) (not (= i j)) (= (row i a) (row j a)))
	   (equal (fdet a n) (f0)))
  :hints (("Goal" :in-theory (enable fdet)
                  :use (permp--append-comp-perm-transpose-list sublistp-append-comp-perm-transpose-list
		        dlistp-append-comp-perm-transpose-list
			(:instance sublistp-comp-perm-transpose-list-slist (l (even-perms n)))
			(:instance fdet-sum-comp-perm-transpose-list (l (even-perms n)))
			(:instance fdet-sum-append (l (comp-perm-transpose-list (even-perms n) n i j)) (m (even-perms n)))
			(:instance fdet-sum-permp (l (append (comp-perm-transpose-list (even-perms n) n i j) (even-perms n)))
			                          (m (slist n)))))))
		        

;;-------------------------------------------------------------------------------------------------------

;; fdet is n-linear, i.e, linear as a function of each row.  This property is
;; specified in terms of the basic operation of replacing a row of a with a given list.
;; For a given row i and permutation p, the term contributed by p to the determinant of
;; (replace-row a i x) by each permutation is a linear function of x:

(local-defthm pairs-prod-extend
  (implies (and (member p (slist n))
                (posp n) (fmatp a n n)                 
		(posp k) (<= k n))
           (equal (pairs-prod (perm-pairs k p) a)
                  (f* (pairs-prod (perm-pairs (1- k) p) a)
		      (pair-val (perm-pair (1- k) p) a)))))

(local-defthm pairs-prod-nil
  (equal (pairs-prod () a)
         (f1)))

(local-defthm perm-pairs-0
  (equal (perm-pairs 0 p)
         ()))

(local-in-theory (disable pairs-prod perm-pairs))

(local-defthm pair-val-perm-pair-replace-row
   (implies (and (fmatp a n n) (posp n)
                 (member p (slist n))
		 (natp i) (< i n)
		 (natp k) (< k n)
  		 (flistnp x n))
            (equal (PAIR-VAL (PERM-PAIR k P)
                             (REPLACE-ROW A I X))
	           (if (= i k)
		       (nth (nth k p) x)
		     (entry k (nth k p) a))))
  :hints (("Goal" :in-theory (enable pair-val perm-pair))))

(local-defthmd pairs-prod-replace-row-1
    (implies (and (fmatp a n n) (posp n)
                  (member p (slist n))
  		  (flistnp x n) (flistnp y n) (fp c)
		  (natp i) (< i n) (natp k) (<= k i) (<= k n))
             (let ((a1 (replace-row a i x))
                   (a2 (replace-row a i y))
                   (a3 (replace-row a i (flist-add (flist-scalar-mul c x) y))))
               (and (equal (pairs-prod (perm-pairs k p) a1)
	                   (pairs-prod (perm-pairs k p) a3))
	            (equal (pairs-prod (perm-pairs k p) a2)
	                   (pairs-prod (perm-pairs k p) a3)))))
  :hints (("Goal" :induct (fact k))))

(local-defthmd hack-2
  (implies (and (fp p) (fp c) (fp x) (fp y))
           (equal (f* p (f+ (f* c x) y))
	          (f+ (f* c (f* p x)) (f* p y))))
  :hints (("Goal" :use ((:instance fdist (x p) (y (f* c x)) (z y))
                        (:instance f*assoc (x p) (y c) (z x))
			(:instance f*comm (x p) (y c))
			(:instance f*assoc (x c) (y p) (z x))))))

(local-defthmd pairs-prod-replace-row-2
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(flistnp x n) (flistnp y n) (fp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (flist-add (flist-scalar-mul c x) y))))
             (equal (pairs-prod (perm-pairs (1+ i) p) a3)
  		    (f+ (f* c (pairs-prod (perm-pairs (1+ i) p) a1))
		  	(pairs-prod (perm-pairs (1+ i) p) a2)))))
  :hints (("Goal" :in-theory (disable nth-flist-scalar-mul nth-flist-add)
	          :use (nth-perm
		        (:instance pairs-prod-replace-row-1 (k i))
			(:instance nth-flist-scalar-mul (i (nth i p)))
	                (:instance nth-flist-add (i (nth i p)) (x (flist-scalar-mul c x)))
			(:instance hack-2 (p (PAIRS-PROD (PERM-PAIRS I P) (REPLACE-ROW A I X)))
			                  (x (NTH (NTH I P) X))
					  (y (nth (nth i p) y)))))))

(local-defthmd hack-3
  (implies (and (fp x) (fp y) (fp a) (fp c))
           (equal (f* (f+ (f* c x) y) a)
	          (f+ (f* c (f* x a)) (f* y a))))
  :hints (("Goal" :use ((:instance fdist-comm (x (f* c x)) (z a))
                        (:instance f*assoc (x c) (y x) (z a))))))

(local-defthmd pairs-prod-replace-row-3
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(flistnp x n) (flistnp y n) (fp c)
                (natp i) (< i n) (natp k) (> k i) (<= k n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (flist-add (flist-scalar-mul c x) y))))
             (equal (pairs-prod (perm-pairs k p) a3)
  		    (f+ (f* c (pairs-prod (perm-pairs k p) a1))
		  	(pairs-prod (perm-pairs k p) a2)))))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :in-theory (disable nth-flist-scalar-mul nth-flist-add)
	                  :use (pairs-prod-replace-row-2
			        (:instance nth-perm (i (1- k)))
			        (:instance nth-flist-scalar-mul (i (nth (1- k) p)))
	                        (:instance nth-flist-add (i (nth (1- k) p)) (x (flist-scalar-mul c x)))))
	  ("Subgoal *1/2.1" :in-theory (disable pairs-prod-extend)
	                    :use ((:instance fp-entry (m n) (i (1- k)) (j (nth (1- k) p)))
	                          (:instance hack-3 (x (PAIRS-PROD (PERM-PAIRS (+ -1 K) P) (REPLACE-ROW A I x)))
				                    (y (PAIRS-PROD (PERM-PAIRS (+ -1 K) P) (REPLACE-ROW A I Y)))
						    (a (NTH (NTH (+ -1 K) P) (NTH (+ -1 K) A))))))))

(local-defthmd pairs-prod-replace-row
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(flistnp x n) (flistnp y n) (fp c)
                (natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (flist-add (flist-scalar-mul c x) y))))
             (equal (pairs-prod (perm-pairs n p) a3)
  		    (f+ (f* c (pairs-prod (perm-pairs n p) a1))
		  	(pairs-prod (perm-pairs n p) a2)))))
  :hints (("Goal" :use ((:instance pairs-prod-replace-row-3 (k n))))))

(local-defthmd fdet-prod-replace-row
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(flistnp x n) (flistnp y n) (fp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (flist-add (flist-scalar-mul c x) y))))
             (equal (fdet-prod a3 p n)
	            (f+ (f* c (fdet-prod a1 p n))
			(fdet-prod a2 p n)))))
  :hints (("Goal" :in-theory (disable pairs-prod-extend)
                  :use (pairs-prod-replace-row
                        (:instance fdet-prod-rewrite (k n) (a (replace-row a i x)))
                        (:instance fdet-prod-rewrite (k n) (a (replace-row a i y)))
                        (:instance fdet-prod-rewrite (k n) (a (replace-row a i (flist-add (flist-scalar-mul c x) y))))))))

(defthm fdet-term-replace-row
  (implies (and (fmatp a n n) (posp n)
                (member p (slist n))
		(flistnp x n) (flistnp y n) (fp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (flist-add (flist-scalar-mul c x) y))))
             (equal (fdet-term a3 p n)
	            (f+ (f* c (fdet-term a1 p n))
			(fdet-term a2 p n)))))
  :hints (("Goal" :in-theory (e/d (fdet-term fdet-prod-replace-row) (fp-fdet-prod))
                  :use ((:instance f-f+ (x (F* C (FDET-PROD (REPLACE-ROW A I X) P N)))
		                        (y (FDET-PROD (REPLACE-ROW A I Y) P N)))
			(:instance f-f* (x c) (y (FDET-PROD (REPLACE-ROW A I X) P N)))
			(:instance fp-fdet-prod (a (replace-row a i x)) (k n))
			(:instance fp-fdet-prod (a (replace-row a i y)) (k n))))))

(local-defthmd hack-4
  (implies (and (fp x1) (fp x2) (fp y1) (fp y2) (fp c))
           (equal (f+ (f+ (f* c x1) y1) (f+ (f* c x2) y2))
	          (f+ (f+ (f* c x1) (f* c x2)) (f+ y1 y2))))
  :hints (("Goal" :use ((:instance f+assoc (x (f+ (f* c x1) y1)) (y (f* c x2)) (z y2))
                        (:instance f+assoc (x (f* c x1)) (y y1) (z (f* c x2)))
			(:instance f+comm (x y1) (y (f* c x2)))
			(:instance f+assoc (x (f* c x1)) (y (f* c x2)) (z y1))
			(:instance f+assoc (x (f+ (f* c x1) (f* c x2))) (y y1) (z y2))))))

(local-defthmd fdet-sum-replace-row
  (implies (and (fmatp a n n) (posp n)
                (sublistp l (slist n))
		(flistnp x n) (flistnp y n) (fp c)
		(natp i) (< i n))
	   (let ((a1 (replace-row a i x))
	         (a2 (replace-row a i y))
	         (a3 (replace-row a i (flist-add (flist-scalar-mul c x) y))))
             (equal (fdet-sum a3 l n)
	            (f+ (f* c (fdet-sum a1 l n))
			(fdet-sum a2 l n)))))
  :hints (("Subgoal *1/2" :use ((:instance hack-4 (x1 (FDET-TERM (REPLACE-ROW A I X) (car l) n))
                                                  (y1 (FDET-TERM (REPLACE-ROW A I y) (car l) n))
						  (x2 (FDET-sum (REPLACE-ROW A I X) (cdr l) n))
						  (y2 (FDET-sum (REPLACE-ROW A I y) (cdr l) n)))))))

;; The desired result follows by summing over all permutations:
	          
(defthm fdet-n-linear
  (implies (and (fmatp a n n) (posp n) (natp i) (< i n)
		(flistnp x n) (flistnp y n) (fp c))
	   (equal (fdet (replace-row a i (flist-add (flist-scalar-mul c x) y)) n)
		  (f+ (f* c (fdet (replace-row a i x) n))
		      (fdet (replace-row a i y) n))))
  :hints (("Goal" :in-theory (enable fdet)
                  :use ((:instance fdet-sum-replace-row (l (slist n)))))))

;; As a consequence of fdet-n-linear, if a has a zero row, then its deteminant is (f0).
;; To prove this, we instantiate fdet-n-linear with c = (f1) and x = y = (flistn0 n):

(defthmd fdet-replace-0-1
  (implies (and (fmatp a n n) (posp n) (natp k) (< k n))
           (equal (f+ (fdet (replace-row a k (flistn0 n)) n)
	              (fdet (replace-row a k (flistn0 n)) n))
		  (fdet (replace-row a k (flistn0 n)) n)))
  :hints (("Goal" :in-theory (disable flist-scalar-mul-f1)
                  :use ((:instance fdet-n-linear (i k) (c (f1)) (x (flistn0 n)) (y (flistn0 n)))
                        (:instance flist-scalar-mul-f1 (x (flistn0 n)))))))

;; It follows that (fdet (replace-row a k (flistn0 n)) n) = (f0).  But if (row k a) = (flistn0 n),
;; then (replace-row a k (flistn0 n)) = a:

(local-defthmd fdet-replace-0
  (implies (and (fmatp a n n) (posp n) (natp k) (< k n))
           (equal (fdet (replace-row a k (flistn0 n)) n)
	          (f0)))
  :hints (("Goal" :use (fdet-replace-0-1 (:instance f+left-cancel (x (fdet (replace-row a k (flistn0 n)) n))
                                                                  (z (fdet (replace-row a k (flistn0 n)) n))
							          (y (f0)))))))

(defthmd fdet-row-0
  (implies (and (fmatp a n n) (posp n) (natp k) (< k n) (= (nth k a) (flistn0 n)))
           (equal (fdet a n)
	          (f0)))
  :hints (("Goal" :use (fdet-replace-0 (:instance replace-fmat-row-self (m n) (i k))))))


;;-------------------------------------------------------------------------------------------------------
;;   Uniqueness of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; We shall show that for given n, fdet is the unique n-linear alternating function on
;; nxn matrices such that (fdet (id-fmat n) n) = (f1).  To that end, we constrain the
;; function fdetn as follows:

(encapsulate (((n) => *))
  (local (defun n () 2))
  (defthm posp-n
    (posp (n))
    :rule-classes (:type-prescription :rewrite)))

(encapsulate (((fdetn *) => *))
  (local (defun fdetn (a) (fdet a (n))))
  (defthm fp-fdetn
    (implies (fmatp a (n) (n))
             (fp (fdetn a))))
  (defthmd fdetn-n-linear
    (implies (and (fmatp a (n) (n)) (natp i) (< i (n))
		  (flistnp x (n)) (flistnp y (n)) (fp c))
	     (equal (fdetn (replace-row a i (flist-add (flist-scalar-mul c x) y)))
		    (f+ (f* c (fdetn (replace-row a i x)))
		        (fdetn (replace-row a i y))))))
  (defthmd fdetn-adjacent-equal
    (implies (and (fmatp a (n) (n))
		  (natp i) (< i (1- (n))) (= (row i a) (row (1+ i) a)))
	     (equal (fdetn a) (f0)))
    :hints (("Goal" :use ((:instance fdet-alternating (n (n)) (j (1+ i))))))))

;; Our objective is to prove that (fdetn a) = (f* (fdet a (n)) (fdetn (id-fmat (n)))):

;; (defthmd fdet-unique
;;   (implies (fmatp a (n) (n))
;;            (equal (fdetn a)
;;                   (f* (fdet a (n))
;;                       (fdetn (id-fmat (n)))))))

;; If we also prove that for a given function f, (f a n) satisfies the constraints on (fdetn a),
;; we may conclude by functional instantiation that (f a n) = (f* (fdet a n) (f (id-fmat n))).
;; From this it follows that if f has the additional property (f (id-fmat n)) = (f1), then
;; (f a) = (fdet a (n)).

;; Note that we have replaced the property that fdetn is alternating with the weaker property
;; fdetn-adjacent-equal, which says that the value is (f0) if 2 adjacent rows are equal.  This
;; relaxes the proof obligations for functional instantiation, which will be critical for the
;; proof of correctness of cofactor expansion.  We shall show that this property together with
;; n-linearity implies that the same holds for 2 non-adjacent rows.

;; It follows from fdetn-n-linear and fdetn-adjacent-equal that transposing 2 adjacent rows negates
;; the value of fdetn:

(local-in-theory (disable nth fmatp replace-row))

(local-defthmd replace-adjacent-rows-same
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n)))
		(flistnp x (n)))
           (equal (fdetn (replace-row (replace-row a i x) (1+ i) x))
		  (f0)))
  :hints (("Goal" :in-theory (disable len-fmatp)
                  :use ((:instance len-fmatp (m (n)) (n (n)))
                        (:instance fdetn-adjacent-equal (a (replace-row (replace-row a i x) (1+ i) x)))))))

(local-defthm flistnp-nth
  (implies (and (natp m) (natp n) (fmatp a m n)
	        (natp i) (< i m))
           (flistnp (nth i a) n))
  :hints (("Goal" :use (flistnp-row))))

(local-defthmd fdetn-adjacent-alternating-1
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (f+ (fdetn (replace-row (replace-row a i (flist-add (row i a) (row (1+ i) a)))
	                                 (1+ i)
		                         (row i a)))
	              (fdetn (replace-row (replace-row a i (flist-add (row i a) (row (1+ i) a)))
	                                 (1+ i)
				         (row (1+ i) a))))
		  (f0)))
  :hints (("Goal" :in-theory (disable len-fmatp flist-scalar-mul-f1)
                  :use ((:instance len-fmatp (m (n)) (n (n)))
		        (:instance flist-scalar-mul-f1 (n (n)) (x (nth i a)))
			(:instance replace-adjacent-rows-same (x (flist-add (row i a) (row (1+ i) a))))
		        (:instance fdetn-n-linear (a (replace-row a i (flist-add (row i a) (row (1+ i) a))))
			                         (i (1+ i)) (c (f1)) (x (row i a)) (y (row (1+ i) a)))))))

(local-defthmd fdetn-adjacent-alternating-2
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (fdetn (replace-row (replace-row a i (flist-add (row i a) (row (1+ i) a)))
	                             (1+ i)
		                     (row i a)))
		  (fdetn (replace-row (replace-row a (1+ i) (row i a))
		                     i
				     (flist-add (row i a) (row (1+ i) a))))))
  :hints (("Goal" :in-theory (disable len-fmatp)
                  :use ((:instance len-fmatp (m (n)) (n (n)))
			(:instance replace-2-fmat-rows (m (n)) (n (n))
			                          (x (flist-add (row i a) (row (1+ i) a))) (j (1+ i)) (y (row i a)))))))

(local-defthmd fdetn-adjacent-alternating-3
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (fdetn (replace-row (replace-row a (1+ i) (row i a))
		                     i
				     (flist-add (row i a) (row (1+ i) a))))
		  (fdetn (replace-row (replace-row a (1+ i) (row i a))
		                     i
				     (row (1+ i) a)))))
  :hints (("Goal" :in-theory (disable flist-scalar-mul-f1 len-fmatp)
                  :use ((:instance len-fmatp (m (n)) (n (n)))
		        (:instance flist-scalar-mul-f1 (n (n)) (x (nth i a)))
			(:instance fdetn-n-linear (a (replace-row a (1+ i) (row i a)))
			                         (c (f1)) (x (row i a)) (y (row (1+ i) a)))
			(:instance fdetn-adjacent-equal (a (replace-row (replace-row a (1+ i) (row i a))
			                                               i (row i a))))))))

(local-defthmd fdetn-adjacent-alternating-4
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (fdetn (replace-row (replace-row a i (flist-add (row i a) (row (1+ i) a)))
	                             (1+ i)
		                     (row (1+ i) a)))
		  (fdetn (replace-row a i (flist-add (row i a) (row (1+ i) a))))))
  :hints (("Goal" :in-theory (disable len-fmatp flist-scalar-mul-f1)
                  :use ((:instance len-fmatp (m (n)) (n (n)))
		        (:instance replace-fmat-row-self (m (n)) (n (n)) (i (1+ i))
			                            (a (replace-row a i (flist-add (row i a) (row (1+ i) a)))))))))

(local-defthmd fdetn-adjacent-alternating-5
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (fdetn (replace-row a i (flist-add (row i a) (row (1+ i) a))))
		  (fdetn a)))
  :hints (("Goal" :in-theory (disable len-fmatp flist-scalar-mul-f1)
                  :use ((:instance len-fmatp (m (n)) (n (n)))
		        (:instance flist-scalar-mul-f1 (n (n)) (x (nth i a)))
			(:instance fdetn-n-linear (c (f1)) (x (row i a)) (y (row (1+ i) a)))
			(:instance fdetn-adjacent-equal (a (replace-row a i (row (1+ i) a))))
			(:instance replace-fmat-row-self (m (n)) (n (n)))))))

(local-defthmd fdetn-adjacent-alternating-6
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (f+ (fdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))
	              (fdetn a))
		  (f0)))
  :hints (("Goal" :use (fdetn-adjacent-alternating-1 fdetn-adjacent-alternating-2 fdetn-adjacent-alternating-3
                        fdetn-adjacent-alternating-4 fdetn-adjacent-alternating-5))))

(defthmd fdetn-interchange-adjacent
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (fdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))
	          (f- (fdetn a))))
  :hints (("Goal" :use (fdetn-adjacent-alternating-6
                        (:instance flistnp-row (n (n)) (m (n)) (i (1+ i)))
                        (:instance f-unique (x (fdetn a))
			                    (y (fdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))))
			(:instance f+comm (x (fdetn a))
			                  (y (fdetn (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))))
		        (:instance fmatp-replace-row (m (n)) (n (n)) (k (1+ i)) (r (row i a)))
                        (:instance fmatp-replace-row (m (n)) (n (n)) (a (replace-row a (1+ i) (row i a)))
			                             (k i) (r (row (1+ i) a)))))))

;; Interchanging adjacent rows may be expressed as a permutation:

(local-defthmd fdetn-adjacent-alternating-7
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n)))
		(natp k) (< k (n)))
           (equal (nth k (replace-row (replace-row a (1+ i) (row i a))
		                      i
		                      (row (1+ i) a)))
	          (nth k (permute a (transpose i (1+ i) (n))))))
  :hints (("Goal" :in-theory (e/d (transpose-vals) (len-fmatp nth-permute len-replace-row fmatp-replace-row))
                  :use ((:instance len-fmatp (m (n)) (n (n)))
		        (:instance nth-permute (l a) (p (TRANSPOSE I (+ 1 I) (N))))
		        (:instance nth-permute (l a) (p (TRANSPOSE I (+ 1 I) (N))) (k i))
		        (:instance fmatp-replace-row (m (n)) (n (n)) (k (1+ i)) (r (row i a)))
                        (:instance fmatp-replace-row (m (n)) (n (n)) (a (replace-row a (1+ i) (row i a)))
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

(defthmd interchange-adjacent-fmat-permute
  (implies (and (fmatp a (n) (n))
		(natp i) (< i (1- (n))))
           (equal (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a))
	          (permute a (transpose i (1+ i) (n)))))
  :hints (("Goal" :in-theory (disable len-fmatp nth-permute len-replace-row fmatp-replace-row)
                  :use ((:instance len-fmatp (m (n)) (n (n)))
		        (:instance fmatp-replace-row (m (n)) (n (n)) (k (1+ i)) (r (row i a)))
                        (:instance fmatp-replace-row (m (n)) (n (n)) (a (replace-row a (1+ i) (row i a)))
			                             (k i) (r (row (1+ i) a)))
			(:instance len-replace-row (k (1+ i)) (r (row i a)))
                        (:instance len-replace-row (a (replace-row a (1+ i) (row i a)))
			                           (k i) (r (row (1+ i) a)))
			(:instance permp-transpose (n (n)) (j (1+ i)))
			(:instance len-perm (n (n)) (x (transpose i (1+ i) (n))))
			(:instance nth-diff-diff (x (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a)))
			                         (y (permute a (transpose i (1+ i) (n)))))
			(:instance fdetn-adjacent-alternating-7
			  (k (nth-diff (replace-row (replace-row a (1+ i) (row i a)) i (row (1+ i) a))
			               (permute a (transpose i (1+ i) (n))))))))))

(defthmd fdetn-permute-adjacent-transpose
  (implies (and (fmatp a (n) (n))
                (natp i) (< i (1- (n))))
           (equal (fdetn (permute a (transpose i (1+ i) (n))))
                  (f- (fdetn a))))
  :hints (("Goal" :use (fdetn-interchange-adjacent interchange-adjacent-fmat-permute))))

;; Note that applying any permutation to the rows of a produces a matrix of the
;; same dimensions:

(local-defthm fmatp-remove1
  (implies (and (fmatp a m n) (natp m) (member r a))
           (fmatp (remove1 r a) (1- m) n))	   
  :hints (("Goal" :in-theory (enable fmatp))))

(local-defthm member-fmatp-flistnp
  (implies (and (fmatp a m n) (member r a))
           (flistnp r n))
  :hints (("Goal" :in-theory (enable fmatp))))

(local-defthmd fmatp-perm
  (implies (and (fmatp a m n) (natp m) (natp n)
                (true-listp b) (permutationp b a))
	   (fmatp b m n))
  :hints (("Goal" :in-theory (enable fmatp))))

(local-defthm true-listp-permute
  (true-listp (permute l p)))

(defthm fmatp-permute
  (implies (and (fmatp a m n) (posp m) (posp n)
                (in p (sym m)))
	   (fmatp (permute a p) m n))
  :hints (("Goal" :in-theory (enable fmatp)
                  :use ((:instance permutationp-permute (l a))
                        (:instance permutationp-symmetric (l a) (m (permute a p)))
			(:instance fmatp-perm (b (permute a p)))))))

;; Next we show that fdetn-permute-adjacent-transpose applies to a transposition of any
;; 2 rows.  First note that for 0 <= i and i - 1 < j < n, (transpose i j (n)) is the
;; result of conjugating (transpose i (1- j) (n)) by (transpose (1- j) j (n)):


(local-defthmd nth-conj-adjacent-transpose-fmat
  (implies (and (fmatp a (n) (n))
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

(defthmd conj-adjacent-transpose-fmat
  (implies (and (fmatp a (n) (n))
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
			(:instance nth-conj-adjacent-transpose-fmat
			  (k (nth-diff (comp-perm (comp-perm (transpose (1- j) j (n))
                                                             (transpose i (1- j) (n))
					                     (n))
		                                  (transpose (1- j) j (n))
			                          (n))
				       (transpose i j (n)))))))))

;; The claim follows by induction:

;; We need fmatp versions of permute-comp-perm and nth-permut:

(local-defthm permute-comp-perm-reverse
  (implies (and (fmatp a n n) (posp n)
		(in x (sym n))
		(in y (sym n)))
	   (equal (permute a (comp-perm x y n))
	          (permute (permute a x) y)))
  :hints (("Goal" :in-theory (enable fmatp)
                  :use ((:instance permute-comp-perm (l a))))))

(local-in-theory (disable permute-comp-perm))

(local-defthm nth-permute-fmatp
  (implies (and (fmatp a m n) (posp m) (posp n)
                (in p (sym m))
		(natp k)
		(< k m))
	   (equal (nth k (permute a p))
	          (nth (nth k p) a)))
  :hints (("Goal" :use (len-fmatp (:instance nth-permute (l a)))
                  :in-theory (disable len-fmatp))))

(local-defthm permute-e-fmatp
  (implies (and (fmatp a m n) (posp m) (posp n))
	   (equal (permute a (ninit m))
	          a))
  :hints (("Goal" :use (len-fmatp (:instance permute-e (l a)))
                  :in-theory (disable len-fmatp))))

	         
(local-defthmd fdetn-permute-transpose-step
  (let ((a1 (permute a (transpose (1- j) j (n)))))
    (implies (and (fmatp a (n) (n))
                  (natp i) (natp j) (< i (1- j)) (< j (n))
                  (equal (fdetn (permute a1 (transpose i (1- j) (n))))
                         (f- (fdetn a1))))
	   (equal (fdetn (permute a (transpose i j (n))))
                  (f- (fdetn a)))))
  :hints (("Goal" :use (conj-adjacent-transpose-fmat
                        (:instance permp-transpose (n (n)))
		        (:instance permp-transpose (n (n)) (i (1- j)))
		        (:instance permp-transpose (n (n)) (j (1- j)))			
			(:instance fdetn-permute-adjacent-transpose (i (1- j)))
			(:instance fdetn-permute-adjacent-transpose (i (1- j))
			                                           (a (permute a
								               (comp-perm (transpose (1- j) j (n))
                                                                                          (transpose i (1- j) (n))
			                                                                  (n)))))))))

(local-defun fdetn-permute-transpose-induct (i j a)
  (if (and (natp i) (natp j) (< i (1- j)) (< j (n)))
      (list (fdetn-permute-transpose-induct i (1- j) (permute a (transpose (1- j) j (n)))))
    (list a)))      

(defthmd fdetn-permute-transpose
  (implies (and (fmatp a (n) (n))
                (natp i) (natp j) (< i j) (< j (n)))
	   (equal (fdetn (permute a (transpose i j (n))))
                  (f- (fdetn a))))
  :hints (("Goal" :induct (fdetn-permute-transpose-induct i j a))
          ("Subgoal *1/2" :use (fdetn-permute-adjacent-transpose))
          ("Subgoal *1/1" :use (fdetn-permute-transpose-step
	                        (:instance fmatp-permute (p (TRANSPOSE (+ -1 J) J (N))) (m (n)) (n (n)))
	                        (:instance permp-transpose (n (n)) (i (1- j)))))))
       
;; Now suppose (row i a) = (row j a), where 0 <= i < j < (n).  We would like to show that 
;; (fdetn a) = (f0).  If j = i + 1 ,then apply fdetn-adjacent-equal.  Otherwise, let
;; a' = (permute (transpose (1+ i) j (n)) a).  By nth-permute,

;;   (nth i a') = (nth (nth i (transpose (1+ i) j (n))) a) = (nth i a)

;; and

;;   (nth (1+ i) a') = (nth (nth (1+ i) (transpose (1+ i) j (n))) a) = (nth j a) = (nth i a)

;; and by fdetn-adjacent-equal, (fdetn a') = (f0).  By fdetn-transpose-rows,

;;   (fdetn a) = (f- (fdetn a') = (f- (f0)) = (f0).

;; Thus, fdetn is an alternating function:

(local-defthmd fdetn-alternating-1
  (implies (and (fmatp a (n) (n))
                (natp i) (natp j) (< (1+ i) j) (< j (n)) (= (row i a) (row j a)))
           (equal (fdetn a) (f0)))
  :hints (("Goal" :in-theory (e/d (transpose-vals) (f-f-))
                  :use ((:instance permp-transpose (i (1+ i)) (n (n)))
		        (:instance fdetn-adjacent-equal (a (permute a (transpose (1+ i) j (n)))))
			(:instance fdetn-permute-transpose (i (1+ i)))
			(:instance f-f- (x (fdetn a)))))))

(local-defthmd fdetn-alternating-2
  (implies (and (fmatp a (n) (n))
                (natp i) (natp j) (< i j) (< j (n)) (= (row i a) (row j a)))
           (equal (fdetn a) (f0)))
  :hints (("Goal" :cases ((= j (1+ i)))
                  :use (fdetn-adjacent-equal fdetn-alternating-1))))

(defthmd fdetn-alternating
  (implies (and (fmatp a (n) (n))
                (natp i) (natp j) (< i (n)) (< j (n)) (not (= i j)) (= (row i a) (row j a)))
	   (equal (fdetn a) (f0)))
  :hints (("Goal" :use (fdetn-alternating-2 (:instance fdetn-alternating-2 (i j) (j i))))))

;; We shall require a generalization of fdetn-transpose-rows to arbitrary permutations.
;; First note that fdetn-permute-transpose may be restated as follows:

(local-defthmd fdetn-permute-transp
  (implies (and (fmatp a (n) (n))
                (transp p (n)))
	   (equal (fdetn (permute a p))
	          (f- (fdetn a))))
  :hints (("Goal" :in-theory (enable transp)
                  :use ((:instance fdetn-permute-transpose (i (least-moved p)) (j (nth (least-moved p) p)))
		        (:instance least-moved-transpose (n (n)) (i (least-moved p)) (j (nth (least-moved p) p)))))))

(include-book "arithmetic-5/top" :dir :system)

(local-defun fdetn-permute-trans-list-p-induct (a l)
  (if (consp l)
      (list (fdetn-permute-trans-list-p-induct (permute a (car l)) (cdr l)))
    (list a l)))

(local-defthmd fdetn-permute-trans-list-p
  (implies (and (fmatp a (n) (n))
                (trans-list-p l (n)))
	   (equal (fdetn (permute a (comp-perm-list l (n))))
	          (if (evenp (len l))
		      (fdetn a)
		    (f- (fdetn a)))))
  :hints (("Goal" :induct (fdetn-permute-trans-list-p-induct a l))
          ("Subgoal *1/1" :use ((:instance permp-transp (n (n)) (p (car l)))
                                (:instance permp-trans-list (n (n)) (l (cdr l)))
				(:instance fdetn-permute-transp (p (car l)))))))

(defthmd fdetn-permute-rows
  (implies (and (fmatp a (n) (n))
                (in p (sym (n))))
	   (equal (fdetn (permute a p))
	          (if (even-perm-p p (n))
		      (fdetn a)
		    (f- (fdetn a)))))
  :hints (("Goal" :in-theory (enable even-perm-p)
                  :use ((:instance parity-0-1 (n (n)))
		        (:instance parity-len-trans-list (n (n)))
			(:instance trans-list-p-trans-list (n (n)))
			(:instance perm-prod-trans (n (n)))
			(:instance fdetn-permute-trans-list-p (l (trans-list p (n))))))))

;; Since fdet satisfies the constraints on fdetn, this applies to fdet by functional
;; instantiation:

(local-defthmd fdet-permute-rows-n
  (implies (and (fmatp a (n) (n))
                (in p (sym (n))))
	   (equal (fdet (permute a p) (n))
	          (if (even-perm-p p (n))
		      (fdet a (n))
		    (f- (fdet a (n))))))
  :hints (("Goal" :use ((:functional-instance fdetn-permute-rows
			  (fdetn (lambda (a) (if (and (fmatp a (n) (n)) (in p (sym (n)))) (fdet a (n)) (fdetn a)))))))
	  ("Subgoal 3" :use (fdetn-adjacent-equal (:instance fdet-alternating (j (1+ i)) (n (n)))))
	  ("Subgoal 2" :use (fdetn-n-linear (:instance fdet-n-linear (n (n)))))))

(defthmd fdet-permute-rows
  (implies (and (fmatp a n n) (posp n)
                (in p (sym n)))
	   (equal (fdet (permute a p) n)
	          (if (even-perm-p p n)
		      (fdet a n)
		    (f- (fdet a n)))))
  :hints (("Goal" :use ((:functional-instance fdet-permute-rows-n
                          (n (lambda () (if (posp n) n (n)))))))))

;; The proof of fdet-unique is based on lists of k-tuples of natural numbers less than (n),
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

(local-defthm flistnp-extract-entries
  (implies (and (natp k) (tuplep x k)
                (natp m) (<= k m) (<= m (n)) (fmatp a m (n)))
           (flistnp (extract-entries x a) k))
  :hints (("Goal" :induct (extract-entries-induct x k a m) :in-theory (enable fmatp))))

(defun funits (x)
  (if (consp x)
      (cons (funit (car x) (n))
            (funits (cdr x)))
    ()))

(local-defthm len-funits
  (equal (len (funits x))
         (len x)))

(defun feval-tuple (x k a)
  (f* (flist-prod (extract-entries x a))
      (fdetn (append (funits x) (nthcdr k a)))))

(local-defthm fmatp-nthcdr
  (implies (and (fmatp a m n) (natp k) (<= k m))
           (fmatp (nthcdr k a) (- m k) n))
  :hints (("Goal" :in-theory (enable fmatp))))

(local-defthm fmatp-append-funits-nthcdr-1
  (implies (and (fmatp a (n) (n)) (natp k) (<= k (n))
                (natp j) (tuplep x j))
	   (fmatp (append (funits x) (nthcdr k a)) (+ j (- (n) k)) (n)))
  :hints (("Goal" :induct (tuplep x j) :in-theory (enable fmatp))))

(local-defthm fmatp-append-funits-nthcdr
  (implies (and (fmatp a (n) (n)) (natp k) (<= k (n))
                (tuplep x k))
	   (fmatp (append (funits x) (nthcdr k a)) (n) (n)))
  :hints (("Goal" :use ((:instance fmatp-append-funits-nthcdr-1 (j k))))))

(defthm fp-feval-tuple
  (implies (and (fmatp a (n) (n)) (natp k) (<= k (n)) (tuplep x k))
           (fp (feval-tuple x k a)))
  :hints (("Goal" :use (fmatp-append-funits-nthcdr (:instance flistnp-extract-entries (m (n)))))))

;; The sum of the values of a list of k-tuples: 

(defun fsum-tuples (l k a)
  (if (consp l)
      (f+ (feval-tuple (car l) k a)
	  (fsum-tuples (cdr l) k a))
    (f0)))

(defthm fp-fsum-tuples
  (implies (and (fmatp a (n) (n)) (natp k) (<= k (n)) (tuple-list-p l k))
           (fp (fsum-tuples l k a)))
  :hints (("Goal" :in-theory (disable feval-tuple))))

;; We would like to compute (fsum-tuples (all-tuples k) k a).  The case k = 0 is trivial:

(defthmd feval-tuple-nil
  (implies (fmatp a (n) (n))
           (equal (feval-tuple () 0 a)
	          (fdetn a))))

(defthm fsum-0-tuples
  (implies (fmatp a (n) (n))
           (equal (fsum-tuples (all-tuples 0) 0 a)
	          (fdetn a))))

;; We shall prove, as a consequence of n-linearity of fdetn, that incrementing k does not change the value of the sum.

;; If (flistnp r (n)), We may think of r as a sum of multiples of unit vectors.  Given a sublist l of (ninit (n)),
;; (fsum-select l n) is the sum of the subset of these multiples corresponding to the members of l:

(defun fsum-select (l r)
  (if (consp l)
      (flist-add (flist-scalar-mul (nth (car l) r) (funit (car l) (n)))
                 (fsum-select (cdr l) r))
    (flistn0 (n))))

(local-defthm flistnp-fsum-select
  (implies (and (flistnp r (n)) (sublistp l (ninit (n))))
           (flistnp (fsum-select l r) (n)))
  :hints (("Subgoal *1/2" :use ((:instance member-ninit (x (car l)) (n (n)))))))

(local-defthm nth-fsum-select
  (implies (and (flistnp r (n))
                (sublistp l (ninit (n)))
		(dlistp l)
		(natp k)
		(< k (n)))
	   (equal (nth k (fsum-select l r))
	          (if (member k l) (nth k r) (f0))))
  :hints (("Goal" :induct (len l)) 
          ("Subgoal *1/1" :use ((:instance member-ninit (n (n)) (x (car l)))
			        (:instance nth-flist-add (i (car l)) (n (n))
				                         (x (FLIST-SCALAR-MUL (NTH k R) (FUNIT k (N))))
							 (y (FSUM-SELECT (CDR L) R)))
			        (:instance nth-flist-scalar-mul (i (car l)) (n (n))
				                                (c (NTH (CAR L) R))
                                                                (x  (FUNIT (CAR L) (N))))
				(:instance nth-flist-add (i k) (n (n))
				                         (x (FLIST-SCALAR-MUL (NTH (car l) R) (FUNIT (car l) (N))))
							 (y (FSUM-SELECT (CDR L) R)))							   
				(:instance nth-flist-scalar-mul (i k) (n (n))
				                                (c (NTH (CAR L) R))
                                                                (x  (FUNIT (CAR L) (N))))))))

(local-defthm nth-fsum-select-ninit
  (implies (and (flistnp r (n))
		(natp k)
		(< k (n)))
	   (equal (nth k (fsum-select (ninit (n)) r))
	          (nth k r)))
  :hints (("Goal" :use ((:instance nth-fsum-select (l (ninit (n))))
                        (:instance member-ninit (x k) (n (n)))))))		

(defthm fsum-select-ninit
  (implies (flistnp r (n))
           (equal (fsum-select (ninit (n)) r)
	          r))
  :hints (("Goal" :in-theory (disable len-flist flistnp-fsum-select)
                  :use ((:instance nth-diff-diff (x (fsum-select (ninit (n)) r)) (y r))
                        (:instance nth-fsum-select-ninit (k (nth-diff (fsum-select (ninit (n)) r) r)))
			(:instance flistnp-fsum-select (l (ninit (n))))
			(:instance len-flist (n (n)) (x r))
			(:instance len-flist (n (n)) (x (fsum-select (ninit (n)) r)))))))

(local-defthmd fsum-tuples-extend-tuple-1
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(sublistp l (ninit (n)))
		(consp l))
	   (equal (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
                  (f+ (feval-tuple (append x (list (car l))) (1+ k) a)
		      (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)))))

(local-defthmd fsum-tuples-extend-tuple-2
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n)) (tuplep x k)
		(natp i) (< i (n)))
	   (equal (feval-tuple (append x (list i)) (1+ k) a)
                  (f* (flist-prod (extract-entries (append x (list i)) a))
		      (fdetn (append (funits (append x (list i))) (nthcdr (1+ k) a)))))))

(local-defthmd fsum-tuples-extend-tuple-3
  (implies (and (natp k) (natp m) (< k m) (<= m (n))
                (tuplep x k) (fmatp a m (n))
		(natp i) (< i (n)))
	   (equal (flist-prod (extract-entries (append x (list i)) a))
	          (f* (flist-prod (extract-entries x a))
		      (nth i (nth k a)))))
  :hints (("Goal" :induct (extract-entries-induct x k a m))
          ("Subgoal *1/2" :in-theory (enable fmatp)
	                  :expand ((nth 0 a))
			  :use ((:instance fp-entry (n (n)) (i 0) (j i))))
	  ("Subgoal *1/1" :expand ((nth 0 a))
	                  :in-theory (e/d (fmatp) (flistnp-extract-entries))
	                  :use ((:instance fp-entry (n (n)) (i k) (j i))
	                        (:instance fp-entry (n (n)) (i 0) (j (car x)))
				(:instance nth (n k) (l a))
				(:instance flistnp-extract-entries (x (cdr x)) (k (1- k)) (a (cdr a)) (m (1- m)))
				(:instance f*assoc (x (NTH (CAR X) (CAR A)))
                                                   (y (FLIST-PROD (EXTRACT-ENTRIES (CDR X) (CDR A))))
						   (z (NTH I (NTH K A))))))))

(local-defthmd fsum-tuples-extend-tuple-4
  (implies (and (natp k) (< k (n))
                (tuplep x k) (fmatp a (n) (n))
		(natp i) (< i (n)))
	   (equal (flist-prod (extract-entries (append x (list i)) a))
	          (f* (flist-prod (extract-entries x a))
		      (nth i (nth k a)))))
  :hints (("Goal" :use ((:instance fsum-tuples-extend-tuple-3 (m (n)))))))

(local-defthmd fsum-tuples-extend-tuple-5
  (implies (and (natp k) (<= k (n)) (tuplep x k)
		(natp i) (< i (n)))
	   (equal (funits (append x (list i)))
	          (append (funits x) (list (funit i (n)))))))

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

(local-defthmd len-append-funits
  (implies (and (natp k) (< k (n))
                (tuplep x k) (fmatp a (n) (n))
		(natp i) (< i (n)))
	   (equal (len (append (funits x) (nthcdr k a)))
	          (n))))

(local-defthmd cdr-nthcdr
  (implies (natp j)
           (equal (nthcdr k (cdr a))
	          (cdr (nthcdr k a)))))

(local-defthmd fsum-tuples-extend-tuple-6
  (implies (and (natp k) (< k (n))
                (tuplep x k) (fmatp a (n) (n))
		(natp i) (< i (n))
		(natp j) (< j (n)))
	   (equal (nth j (append (append (funits x) (list (funit i (n))))
	                         (nthcdr (1+ k) a)))
		  (nth j (replace-row (append (funits x) (nthcdr k a)) k (funit i (n))))))
  :hints (("Goal" :cases ((= j k))
                  :expand ((NTH (+ J (- K)) (NTHCDR K A)))
                  :use (cdr-nthcdr len-append-funits))))

(local-defthmd true-listp-nthcdr
  (implies (true-listp l)
           (true-listp (nthcdr j l))))

(local-defthm true-listp-append
  (implies (true-listp m)
           (true-listp (append l m))))

(local-defthmd fsum-tuples-extend-tuple-7
  (implies (and (natp k) (< k (n))
                (tuplep x k) (fmatp a (n) (n))
		(natp i) (< i (n)))
           (TRUE-LISTP (APPEND (APPEND (FUNITS X) (LIST (FUNIT I (N))))
                               (NTHCDR K (CDR A)))))
  :hints (("Goal" :expand ((fmatp a (n) (n)))
                  :use ((:instance true-listp-nthcdr (j k) (l (cdr a)))))))

(local-defthm true-listp-replace-row
  (implies (true-listp a)
           (true-listp (replace-row a j r)))
  :hints (("Goal" :in-theory (enable replace-row))))

(local-defthmd fsum-tuples-extend-tuple-8
  (implies (and (natp k) (< k (n))
                (fmatp a (n) (n)))
           (TRUE-LISTP (REPLACE-ROW (APPEND (FUNITS X) (NTHCDR K A)) K (FUNIT I (N)))))
  :hints (("Goal" :in-theory (disable true-listp-nthcdr true-listp-replace-row)
                  :use ((:instance true-listp-replace-row (a (APPEND (FUNITS X) (NTHCDR K A))) (j k) (r (FUNIT I (N))))
		        (:instance true-listp-nthcdr (j k) (l a))))))

(local-defthmd fsum-tuples-extend-tuple-9
  (implies (and (natp k) (< k (n))
                (tuplep x k) (fmatp a (n) (n))
		(natp i) (< i (n)))
           (equal (append (append (funits x) (list (funit i (n))))
	                  (nthcdr (1+ k) a))
		  (replace-row (append (funits x) (nthcdr k a)) k (funit i (n)))))
  :hints (("Goal" :in-theory (disable len-fmatp)
                  :use (fsum-tuples-extend-tuple-7 fsum-tuples-extend-tuple-8 len-append-funits
		        (:instance len-fmatp (m (n)) (n (n)))
		        (:instance nth-diff-diff (x (append (append (funits x) (list (funit i (n)))) (nthcdr (1+ k) a)))
                                                 (y (replace-row (append (funits x) (nthcdr k a)) k (funit i (n)))))
			(:instance fsum-tuples-extend-tuple-6
			  (j (nth-diff (append (append (funits x) (list (funit i (n)))) (nthcdr (1+ k) a))
			               (replace-row (append (funits x) (nthcdr k a)) k (funit i (n))))))))))

(local-defthmd fsum-tuples-extend-tuple-10
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n)) (tuplep x k)
		(natp i) (< i (n)))
	   (equal (feval-tuple (append x (list i)) (1+ k) a)
                  (f* (f* (flist-prod (extract-entries x a))
		          (nth i (nth k a)))
		      (fdetn (replace-row (append (funits x) (nthcdr k a)) k (funit i (n)))))))
  :hints (("Goal" :use (fsum-tuples-extend-tuple-2 fsum-tuples-extend-tuple-4
                        fsum-tuples-extend-tuple-5 fsum-tuples-extend-tuple-9))))

(local-defthmd fsum-tuples-extend-tuple-11
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n)) (tuplep x k)
		(natp i) (< i (n)))
	   (equal (feval-tuple (append x (list i)) (1+ k) a)
                  (f* (flist-prod (extract-entries x a))
		      (f* (nth i (nth k a))
		          (fdetn (replace-row (append (funits x) (nthcdr k a)) k (funit i (n))))))))
  :hints (("Goal" :in-theory (disable flistnp-extract-entries)
                  :use (fsum-tuples-extend-tuple-10
                        (:instance flistnp-extract-entries (m (n)))
			(:instance fp-entry (m (n)) (n (n)) (i k) (j i))
                        (:instance f*assoc (x (flist-prod (extract-entries x a)))
			                   (y (nth i (nth k a)))
					   (z (fdetn (replace-row (append (funits x) (nthcdr k a)) k (funit i (n))))))))))

(local-defthmd fsum-tuples-extend-tuple-12
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(sublistp l (ninit (n))))
	   (equal (feval-tuple x k (replace-row a k (fsum-select l (nth k a))))
	          (f* (flist-prod (extract-entries x (replace-row a k (fsum-select l (nth k a)))))
		      (fdetn (append (funits x) (nthcdr k (replace-row a k (fsum-select l (nth k a))))))))))

(local-defthmd fsum-tuples-extend-tuple-13
  (implies (and (fmatp a m (n)) (natp m) (<= m (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (extract-entries x (replace-row a k r))
	          (extract-entries x a)))
  :hints (("Goal" :induct (extract-entries-induct x k a m) :in-theory (enable fmatp replace-row))))

(local-defthmd fsum-tuples-extend-tuple-14
  (implies (and (fmatp a m (n)) (natp m) (<= m (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (feval-tuple x k (replace-row a k (fsum-select l (nth k a))))
	          (f* (flist-prod (extract-entries x a))
		      (fdetn (append (funits x) (nthcdr k (replace-row a k (fsum-select l (nth k a)))))))))
  :hints (("Goal" :use (fsum-tuples-extend-tuple-12
                        (:instance fsum-tuples-extend-tuple-13 (r (fsum-select l (nth k a))))))))

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

(local-defthmd fsum-tuples-extend-tuple-15
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(natp j) (< j (n)))
	   (equal (nth j (append (funits x) (nthcdr k (replace-row a k r))))
	          (nth j (replace-row (append (funits x) (nthcdr k a)) k r))))
  :hints (("Goal" :cases ((= k j))
                  :in-theory (disable len-fmatp fmatp-append-funits-nthcdr)
                  :use (fmatp-append-funits-nthcdr
		        (:instance len-fmatp (m (n)) (n (n)))
		        (:instance len-fmatp (m (n)) (n (n)) (a (APPEND (FUNITS X) (NTHCDR K A))))))))

(local-defthmd fsum-tuples-extend-tuple-16
  (implies (and (natp k) (< k (n))
                (fmatp a (n) (n)))
           (TRUE-LISTP (REPLACE-ROW (APPEND (FUNITS X) (NTHCDR K A)) K r)))
  :hints (("Goal" :in-theory (disable true-listp-nthcdr true-listp-replace-row)
                  :use ((:instance true-listp-replace-row (a (APPEND (FUNITS X) (NTHCDR K A))) (j k))
		        (:instance true-listp-nthcdr (j k) (l a))))))

(local-defthmd fsum-tuples-extend-tuple-17
  (implies (and (natp k) (< k (n))
                (fmatp a (n) (n)))
           (TRUE-LISTP (APPEND (FUNITS X) (NTHCDR K (replace-row a k r)))))
  :hints (("Goal" :in-theory (disable true-listp-nthcdr true-listp-replace-row)
                  :use ((:instance true-listp-replace-row (j k))
		        (:instance true-listp-nthcdr (j k) (l (replace-row a k r)))))))

(local-defthmd fsum-tuples-extend-tuple-18
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
           (equal (len (append (funits x) (nthcdr k (replace-row a k r))))
	          (n)))
  :hints (("Goal" :in-theory (enable len-append-funits))))

(local-defthmd fsum-tuples-extend-tuple-19
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
           (equal (len (replace-row (append (funits x) (nthcdr k a)) k r))
	          (n)))
  :hints (("Goal" :in-theory (enable len-append-funits))))

(local-defthmd fsum-tuples-extend-tuple-20
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
          (equal (append (funits x) (nthcdr k (replace-row a k r)))
	         (replace-row (append (funits x) (nthcdr k a)) k r)))
  :hints (("Goal" :use (fsum-tuples-extend-tuple-16 fsum-tuples-extend-tuple-17 fsum-tuples-extend-tuple-18
		        fsum-tuples-extend-tuple-19
                        (:instance nth-diff-diff (x (append (funits x) (nthcdr k (replace-row a k r))))
                                                 (y (replace-row (append (funits x) (nthcdr k a)) k r)))
			(:instance fsum-tuples-extend-tuple-15
			   (j (nth-diff (append (funits x) (nthcdr k (replace-row a k r)))
			                (replace-row (append (funits x) (nthcdr k a)) k r))))))))

(local-defthmd fsum-tuples-extend-tuple-21
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (feval-tuple x k (replace-row a k (fsum-select l (nth k a))))
	          (f* (flist-prod (extract-entries x a))
		      (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select l (nth k a)))))))
  :hints (("Goal" :use ((:instance fsum-tuples-extend-tuple-14 (m (n)))
                        (:instance fsum-tuples-extend-tuple-20 (r (fsum-select l (nth k a))))))))

(local-defthmd fsum-tuples-extend-tuple-22
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n))))
           (equal (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
                  (f+ (feval-tuple (append x (list (car l))) (1+ k) a)
		      (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)))))

(local-defthmd fsum-tuples-extend-tuple-23
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n)))
	        (equal (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
		       (feval-tuple x k (replace-row a k (fsum-select (cdr l) (nth k a))))))
	   (equal (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (f+ (f* (flist-prod (extract-entries x a))
		          (f* (nth (car l) (nth k a))
		              (fdetn (replace-row (append (funits x) (nthcdr k a)) k (funit (car l) (n))))))
		      (f* (flist-prod (extract-entries x a))
		          (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select (cdr l) (nth k a))))))))
  :hints (("Goal" :use (fsum-tuples-extend-tuple-22
                        (:instance fsum-tuples-extend-tuple-21 (l (cdr l)))
                        (:instance fsum-tuples-extend-tuple-11 (i (car l)))
			(:instance member-ninit (x (car l)) (n (n)))))))

(local-defthmd fsum-tuples-extend-tuple-24
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n))))
	   (equal (f+ (f* (flist-prod (extract-entries x a))
		          (f* (nth (car l) (nth k a))
		              (fdetn (replace-row (append (funits x) (nthcdr k a)) k (funit (car l) (n))))))
		      (f* (flist-prod (extract-entries x a))
		          (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select (cdr l) (nth k a))))))
		  (f* (flist-prod (extract-entries x a))
		      (f+ (f* (nth (car l) (nth k a))
		              (fdetn (replace-row (append (funits x) (nthcdr k a)) k (funit (car l) (n)))))
			  (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select (cdr l) (nth k a))))))))
  :hints (("Goal" :in-theory (disable flistnp-extract-entries fmatp-append-funits-nthcdr)
                  :use (fmatp-append-funits-nthcdr
                        (:instance member-ninit (x (car l)) (n (n)))
			(:instance flistnp-row (i k) (m (n)) (n (n)))
			(:instance fp-entry (m (n)) (n (n)) (i k) (j (car l)))
			(:instance flistnp-extract-entries (m (n)))
                        (:instance fdist (x (flist-prod (extract-entries x a)))
			                 (y (f* (nth (car l) (nth k a))
		                                (fdetn (replace-row (append (funits x) (nthcdr k a)) k (funit (car l) (n))))))
					 (z (fdetn (replace-row (append (funits x) (nthcdr k a)) k
								(fsum-select (cdr l) (nth k a))))))))))

(local-defthmd fsum-tuples-extend-tuple-25
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n))))
	   (equal (f+ (f* (nth (car l) (nth k a))
		          (fdetn (replace-row (append (funits x) (nthcdr k a)) k (funit (car l) (n)))))
		      (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select (cdr l) (nth k a)))))
		  (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select l (nth k a))))))
  :hints (("Goal" :in-theory (disable flistnp-extract-entries fmatp-append-funits-nthcdr)
                  :use (fmatp-append-funits-nthcdr
                        (:instance member-ninit (x (car l)) (n (n)))
			(:instance flistnp-row (i k) (m (n)) (n (n)))
			(:instance fp-entry (m (n)) (n (n)) (i k) (j (car l)))
			(:instance fdetn-n-linear (a (append (funits x) (nthcdr k a))) (i k) (c (nth (car l) (nth k a)))
			                         (x (funit (car l) (n)))
						 (y (fsum-select (cdr l) (nth k a))))))))

(local-defthmd fsum-tuples-extend-tuple-26
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n)))
	        (equal (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
		       (feval-tuple x k (replace-row a k (fsum-select (cdr l) (nth k a))))))
	   (equal (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (f* (flist-prod (extract-entries x a))
		      (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select l (nth k a)))))))
  :hints (("Goal" :use (fsum-tuples-extend-tuple-23 fsum-tuples-extend-tuple-24 fsum-tuples-extend-tuple-25))))

(local-defthmd fsum-tuples-extend-tuple-27
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n)))
	        (equal (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
		       (feval-tuple x k (replace-row a k (fsum-select (cdr l) (nth k a))))))
	   (equal (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (f* (flist-prod (extract-entries x a))
		      (fdetn (append (funits x) (nthcdr k (replace-row a k (fsum-select l (nth k a)))))))))
  :hints (("Goal" :use (fsum-tuples-extend-tuple-26
                        (:instance fsum-tuples-extend-tuple-20 (r (fsum-select l (nth k a))))))))

(local-defthmd fsum-tuples-extend-tuple-28
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(consp l)
		(sublistp l (ninit (n)))
	        (equal (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
		       (feval-tuple x k (replace-row a k (fsum-select (cdr l) (nth k a))))))
	   (equal (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (feval-tuple x k (replace-row a k (fsum-select l (nth k a))))))
  :hints (("Goal" :in-theory (enable fsum-tuples-extend-tuple-13)
                  :use (fsum-tuples-extend-tuple-27))))

;; We need this basic result:

(local-defthmd fdetn-replace-0-1
  (implies (and (fmatp a (n) (n)) (natp k) (< k (n)))
           (equal (f+ (fdetn (replace-row a k (flistn0 (n))))
	              (fdetn (replace-row a k (flistn0 (n)))))
		  (fdetn (replace-row a k (flistn0 (n))))))
  :hints (("Goal" :in-theory (disable flist-scalar-mul-f1)
                  :use ((:instance fdetn-n-linear (i k) (c (f1)) (x (flistn0 (n))) (y (flistn0 (n))))
                        (:instance flist-scalar-mul-f1 (n (n)) (x (flistn0 (n))))))))

(local-defthmd fdetn-replace-0
  (implies (and (fmatp a (n) (n)) (natp k) (< k (n)))
           (equal (fdetn (replace-row a k (flistn0 (n))))
	          (f0)))
  :hints (("Goal" :use (fdetn-replace-0-1 (:instance f+left-cancel (x (fdetn (replace-row a k (flistn0 (n)))))
                                                           (z (fdetn (replace-row a k (flistn0 (n)))))
							   (y (f0)))))))

;; Prove by induction on l, using fdetn-replace-0 and fsum-tuples-extend-tuple-26:

(local-defthmd fsum-tuples-extend-tuple-29
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k)
		(sublistp l (ninit (n))))
	   (equal (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
		  (feval-tuple x k (replace-row a k (fsum-select l (nth k a))))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/2" :in-theory (enable fsum-tuples-extend-tuple-20)
	                  :use ((:instance fdetn-replace-0 (a (APPEND (FUNITS X) (NTHCDR K A))))
			        (:instance flistnp-extract-entries (m (n)) (a (REPLACE-ROW A K (FLISTN0 (N)))))))
	  ("Subgoal *1/1" :use (fsum-tuples-extend-tuple-28))))


(local-defthm fsum-select-ninit
  (implies (flistnp r (n))
           (equal (fsum-select (ninit (n)) r)
	          r)))

;; Substitute (ninit (n)) for l:

(local-defthmd fsum-tuples-extend-tuple-30
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (fsum-tuples (extend-tuple-aux x (ninit (n))) (1+ k) a)
		  (feval-tuple x k (replace-row a k (nth k a)))))
  :hints (("Goal" :in-theory (disable fsum-tuples feval-tuple)
                  :use ((:instance fsum-tuples-extend-tuple-29 (l (ninit (n))))
                        (:instance flistnp-row (n (n)) (m (n)) (i k))))))

;; We shall derive a formula for (fsum-tuples (extend-tuple x) (1+ k) a).

;; Let l be a sublist of (ninit (n)).  According to the definitions of fsum-tuples and extend-tuple-aux,

;;   (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
;;     = (f+ (feval-tuple (append x (list (car l))) (1+ k) a)
;;             (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)),

;; where
  
;;   (feval-tuple (append x (list i)) (1+ k) a)
;;     = (f* (flist-prod (extract-entries (append x (list i)) a))
;;           (fdetn (append (funits (append x (list i))) (nthcdr (1+ k) a))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (f* (nth i (nth k a))
;;               (fdetn (append (append (funits x) (list (unit i (n)))) (nthcdr (1+ k) a)))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (f* (nth i (nth k a))
;;	         (fdetn (replace-row (append (funits x) (nthcdr k a) k (unit i (n)))))))

;; and

;;   (fsum-tuples (extend-tuple-aux x (cdr l)) (1+ k) a)
;;     = (feval-tuple x k (replace-row a k (fsum-select (cdr l) (nth k a))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (fdetn (append (funits x) (nthcdr k (replace-row a k (fsum-select (cdr l) (nth k a)))))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select (cdr l) (nth k a))))).

;; Thus, by fdetn-n-linear,

;;   (fsum-tuples (extend-tuple-aux x l) (1+ k) a)
;;     = (f* (flist-prod (extract-entries x a))
;;           (fdetn (replace-row (append (funits x) (nthcdr k a)) k (fsum-select l (nth k a)))))
;;     = (f* (flist-prod (extract-entries x a))
;;           (fdetn (append (funits x) (nthcdr k (replace-row a k (fsum-select l (nth k a)))))))
;;     = (feval-tuple x k (replace-row a k (fsum-select l (nth k a)))).

;; Substitute (ninit (n)) for l:

;;   (fsum-tuples (extend-tuple x) (1+ k) a)
;;     = (feval-tuple x k (replace-row a k (fsum-select (ninit (n)) (nth k a))))
;;     = (feval-tuple x k (replace-row a k (nth k a)))
;;     = (feval-tuple x k a):

(defthm fsum-tuples-extend-tuple
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
                (tuplep x k))
	   (equal (fsum-tuples (extend-tuple x) (1+ k) a)
		  (feval-tuple x k a)))
  :hints (("Goal" :in-theory (enable extend-tuple)
                  :use (fsum-tuples-extend-tuple-30
                        (:instance replace-fmat-row-self (m (n)) (n (n)) (i k))))))

;; This leads to the recurrence formula

;;    (fsum-tuples (all-tuples k) k a) = (fsum-tuples (all-tuples (1- k)) (1- k) a):

(defthm fsum-tuples-append
  (implies (and (fmatp a (n) (n)) (natp k) (<= k (n)) (tuple-list-p l k) (tuple-list-p m k))
           (equal (fsum-tuples (append l m) k a)
	          (f+ (fsum-tuples l k a) (fsum-tuples m k a))))
  :hints (("Goal" :in-theory (disable feval-tuple))
          ("Subgoal *1/2" :use ((:instance f+assoc (x (feval-tuple (car l) k a))
					           (y (FSUM-TUPLES (CDR L) K A))
					           (z (FSUM-TUPLES M K A)))))))
                        
(defthmd fsum-tuples-extend-tuples
  (implies (and (fmatp a (n) (n))
                (natp k) (< k (n))
		(tuple-list-p l k))
	   (equal (fsum-tuples (extend-tuples l) (1+ k) a)
	          (fsum-tuples l k a)))
  :hints (("Goal" :in-theory (disable feval-tuple))))

(defthm fsum-tuples-extend-all-tuples
  (implies (and (fmatp a (n) (n))
                (posp k) (<= k (n)))
	   (equal (fsum-tuples (all-tuples k) k a)
	          (fsum-tuples (all-tuples (1- k)) (1- k) a)))
  :hints (("Goal" :use ((:instance fsum-tuples-extend-tuples (l (all-tuples (1- k))) (k (1- k)))))))

;; By induction, (fsum-tuples (all-tuples (n)) (n) a) = (fdetn a):

(local-defthmd fsum-tuples-induction
  (implies (and (fmatp a (n) (n))
                (natp k) (<= k (n)))
	   (equal (fsum-tuples (all-tuples k) k a)
	          (fdetn a)))
  :hints (("Goal" :induct (fact k) :in-theory (disable all-tuples))))

(defthmd fsum-tuples-fdetn
  (implies (fmatp a (n) (n))
	   (equal (fsum-tuples (all-tuples (n)) (n) a)
	          (fdetn a)))
  :hints (("Goal" :use ((:instance fsum-tuples-induction (k (n)))))))

(local-in-theory (disable fsum-tuples-induction fsum-tuples-extend-all-tuples))

;; If x is an (n)-tuple, then (feval-tuple x (n) a) = (fdetn (funits x)).  Since fdetn
;; is alternating, this value is (f0) unless x is a dlist:

(local-defthmd nthcdr-nil
  (implies (true-listp l)
           (equal (nthcdr (len l) l) ())))

(local-defthmd append-nil
  (implies (true-listp l)
           (equal (append l ()) l)))

(local-defthm feval-tuple-n
  (implies (and (fmatp a (n) (n))
                (tuplep x (n)))
	   (equal (feval-tuple x (n) a)
	          (f* (flist-prod (extract-entries x a))
		      (fdetn (funits x)))))
  :hints (("Goal" :in-theory (disable len-fmatp)
                  :use ((:instance nthcdr-nil (l a))
                        (:instance append-nil (l (funits x)))
			(:instance len-fmatp (m (n)) (n (n)))))))

(local-defthm member-funits
  (implies (member z l)
           (member (funit z (n))
	           (funits l))))

(local-defthmd dlistp-funits-1
  (implies (and (true-listp x) (dlistp (funits x)))
           (dlistp x)))

(local-defthmd dlistp-funits
  (implies (and (tuplep x (n)) (dlistp (funits x)))
           (dlistp x))
  :hints (("Goal" :use (dlistp-funits-1))))

(local-defthmd fmatp-funits
  (implies (tuplep x k)
           (fmatp (funits x) k (n)))
  :hints (("Goal" :in-theory (enable fmatp))))

(defthm fdetn-funits-0
  (implies (and (tuplep x (n)) (not (dlistp x)))
           (equal (fdetn (funits x))
	          (f0)))
  :hints (("Goal" :in-theory (disable len-tuplep dcex-lemma)
                  :use (dlistp-funits
                        (:instance fmatp-funits (k (n)))
			(:instance len-tuplep (k (n)))
                        (:instance fdetn-alternating (a (funits x)) (i (dcex1 (funits x))) (j (dcex2 (funits x))))
			(:instance dcex-lemma (l (funits x)))))))

(defthm feval-tuple-r0
  (implies (and (fmatp a (n) (n))
                (tuplep x (n))
		(not (dlistp x)))
	   (equal (feval-tuple x (n) a)
	          (f0)))		  
  :hints (("Goal" :in-theory (disable flistnp-extract-entries)
                  :use ((:instance flistnp-extract-entries (m (n)) (k (n)))))))


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

(local-defthmd fsum-tuples-dlists
  (implies (and (fmatp a (n) (n))
                (tuple-list-p l (n)))
	   (equal (fsum-tuples l (n) a)
	          (fsum-tuples (select-dlists l) (n) a))))

;; But (select-dlists (all-tuples (n))) = (slist (n)), and therefore (fsum-tuples (slist (n)) (n) a) = (fdetn a).
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
	
(local-defthmd permp-fsum-tuples-hack
  (implies (and (fmatp a (n) (n)) (true-listp l)
                (dlistp l) (tuple-list-p-hack l (n))
		(dlistp m) (tuple-list-p-hack m (n))
		(permp l m))
	   (equal (fsum-tuples l (n) a)
	          (fsum-tuples m (n) a)))		      
  :hints (("Goal" :in-theory (disable feval-tuple feval-tuple-n)
                  :use ((:functional-instance fval-sum-permp
                          (fargp (lambda (x) (if (fmatp a (n) (n)) (tuplep x (n)) (fargp x))))
                          (fval (lambda (x) (if (fmatp a (n) (n)) (feval-tuple x (n) a) (fval x))))
                          (farg-listp (lambda (x) (if (fmatp a (n) (n)) (tuple-list-p-hack x (n)) (farg-listp x))))
			  (fval-sum (lambda (x) (if (fmatp a (n) (n)) (fsum-tuples x (n) a) (fval-sum x)))))))))

(local-defthmd permp-fsum-tuples
  (implies (and (fmatp a (n) (n)) (true-listp l)
                (dlistp l) (tuple-list-p l (n))
		(dlistp m) (tuple-list-p m (n))
		(permp l m))
	   (equal (fsum-tuples l (n) a)
	          (fsum-tuples m (n) a)))		      
  :hints (("Goal" :use (permp-fsum-tuples-hack))))

;; To apply permp-fsum-tuples, we must show (tuple-list-p (slist (n))):

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
                        
;; Combine these results with fsum-tuples-dlists and fsum-tuples-fdetn:

(defthmd fsum-tuples-n
  (implies (fmatp a (n) (n))
	   (equal (fsum-tuples (slist (n)) (n) a)
	          (fdetn a)))
  :hints (("Goal" :use (permp-select-dlists-all-tuples fsum-tuples-fdetn
                        (:instance permp-fsum-tuples (l (select-dlists (all-tuples (n)))) (m (slist (n))))
			(:instance dlistp-select-dlists (l (all-tuples (n))))
			(:instance fsum-tuples-dlists (l (all-tuples (n))))))))
			
;; For p in (slist (n)),

;;   (feval-tuple p (n) a) = (f* (flist-prod (extract-entries p a))
;;                              (fdetn (funits p))),
				
;; where (flist-prod (extract-entries p a)) = (fdet-prod a p (n)).

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

(local-defun fdet-entries (p a n)
  (if (zp n)
      ()
    (append (fdet-entries p a (1- n))
	    (list (entry (1- n) (nth (1- n) p) a)))))

(local-defthm len-fdet-entries
  (implies (natp n)
	   (equal (len (fdet-entries p a n))
		  n)))

(local-defthmd nth-fdet-entries
  (implies (and (natp i) (natp k) (< i k) (<= k (n)) (member p (slist (n))) (fmatp a (n) (n)))
	   (equal (nth i (fdet-entries p a k))
		  (entry i (nth i p) a)))
  :hints (("Goal" :in-theory (enable nth) :induct (fact k))))

(local-defthmd equal-fdet-entries-extract-entries
  (implies (and (fmatp a (n) (n)) (member p (slist (n))))
	   (equal (fdet-entries p a (n))
		  (extract-entries p a)))
  :hints (("Goal" :in-theory (e/d (len-perm) (len-fmatp entry))
                  :use ((:instance len-fmatp (m (n)) (n (n)))
		        (:instance nth-diff-diff (x (fdet-entries p a (n))) (y (extract-entries p a)))
                        (:instance nth-fdet-entries (k (n)) (i (nth-diff (fdet-entries p a (n)) (extract-entries p a))))
			(:instance nth-extract-entries (i (nth-diff (fdet-entries p a (n)) (extract-entries p a))))))))

(local-defun fdet-prod (a p n)
  (if (zp n)
      (f1)
    (f* (fdet-prod a p (1- n))
        (entry (1- n) (nth (1- n) p) a))))

(local-defthm flistp-append
  (implies (and (flistp l) (flistp m))
           (flistp (append l m))))

(local-defthm flist-prod-append
  (implies (and (flistp l) (flistp m))
           (equal (flist-prod (append l m))
	          (f* (flist-prod l) (flist-prod m))))
  :hints (("Subgoal *1/3" :use ((:instance f*assoc (x (car l)) (y (flist-prod (cdr l))) (z (flist-prod m)))))
          ("Subgoal *1/2" :use ((:instance f*assoc (x (car l)) (y (flist-prod (cdr l))) (z (flist-prod m)))))))

(local-defthm flistp-fdet-entries
  (implies (and (natp k) (<= k (n)) (member p (slist (n))) (fmatp a (n) (n)))
           (flistp (fdet-entries p a k)))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :use ((:instance fp-entry (m (n)) (n (n)) (i (1- k)) (j (nth (1- k) p)))
	                        (:instance nth-perm-ninit (n (n)) (x p) (k (1- k)))))))


(local-defthmd flist-prod-fdet-entries
  (implies (and (natp k) (<= k (n)) (member p (slist (n))) (fmatp a (n) (n)))
           (equal (flist-prod (fdet-entries p a k))
	          (fdet-prod a p k)))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :use ((:instance fp-entry (m (n)) (n (n)) (i (1- k)) (j (nth (1- k) p)))
	                        (:instance nth-perm-ninit (n (n)) (x p) (k (1- k)))))))

(local-defthmd flist-prod-extract-entries
  (implies (and (fmatp a (n) (n))
                (member p (slist (n))))
           (equal (flist-prod (extract-entries p a))
	          (fdet-prod a p (n))))
  :hints (("Goal" :use (equal-fdet-entries-extract-entries
                        (:instance flist-prod-fdet-entries (k (n)))))))

(local-defthmd feval-tuple-fdet-prod
  (implies (and (fmatp a (n) (n))
                (member p (slist (n))))
	   (equal (feval-tuple p (n) a)
	          (f* (fdet-prod a p (n))
		      (fdetn (funits p)))))
  :hints (("Goal" :use (flist-prod-extract-entries
                        (:instance feval-tuple-n (x p))
			(:instance member-select-dlists-all-tuples (x p))
                        (:instance member-select-dlists-slist (x p))))))

;; But

;;   (fdetn (funits p)) = (fdetn (permute (id-fmat (n)) p))
;;                     = (f* (if (even-perm-p p (n)) (f1) (f- (f1)))
;;                           (fdetn (id-fmat (n)))).

(local-defthmd nth-funits
  (implies (and (natp k) (< k (len x)))
           (equal (nth k (funits x))
	          (funit (nth k x) (n))))
  :hints (("Goal" :in-theory (enable nth))))

(local-defthmd nth-permute-id-fmat
  (implies (and (natp k) (< k (n)) (in p (sym (n))))
           (equal (nth k (permute (id-fmat (n)) p))
	          (funit (nth k p) (n))))
  :hints (("Goal" :in-theory (disable nth-id-fmat len-fmatp)
                  :use ((:instance len-fmatp (a (id-fmat (n))) (m (n)) (n (n)))
		        (:instance nth-permute (l (id-fmat (n))))
			(:instance nth-id-fmat (i (nth k p)) (n (n)))
			(:instance member-perm (x p) (k (nth k p)) (n (n)))))))

(defthmd funits-permute-id-mat
  (implies (member p (slist (n)))
           (equal (funits p)
	          (permute (id-fmat (n)) p)))
  :hints (("Goal" :use ((:instance nth-diff-diff (x (funits p)) (y (permute (id-fmat (n)) p)))
                        (:instance nth-permute-id-fmat (k (nth-diff (funits p) (permute (id-fmat (n)) p))))
                        (:instance nth-funits (x p) (k (nth-diff (funits p) (permute (id-fmat (n)) p))))
			(:instance len-perm (x p) (n (n)))))))

(defthmd feval-tuple-fdet-prod
  (implies (and (fmatp a (n) (n))
                (member p (slist (n))))
	   (equal (feval-tuple p (n) a)
	          (f* (fdet-prod a p (n))
		      (fdetn (funits p))))))

(defthmd fdetn-permute-rows
  (implies (and (fmatp a (n) (n))
                (in p (sym (n))))
	   (equal (fdetn (permute a p))
	          (if (even-perm-p p (n))
		      (fdetn a)
		    (f- (fdetn a))))))
		    
;; Thus, we have

(defthmd feval-tuple-perm
  (implies (and (fmatp a (n) (n))
                (member p (slist (n))))
	   (equal (feval-tuple p (n) a)
	          (f* (fdet-term a p (n))
		      (fdetn (id-fmat (n))))))
  :hints (("Goal" :in-theory (e/d (fdet-term) (feval-tuple feval-tuple-n))
                  :use (feval-tuple-fdet-prod funits-permute-id-mat
                        (:instance fdetn-permute-rows (a (id-fmat (n))))
			(:instance f-f* (x (FDET-PROD A P (N))) (y (FDETN (ID-FMAT (N)))))
			(:instance f-f* (y (FDET-PROD A P (N))) (x (FDETN (ID-FMAT (N)))))
			(:instance f*comm (x (FDET-PROD A P (N))) (y (FDETN (ID-FMAT (N)))))
			(:instance f*comm (x (f- (FDET-PROD A P (N)))) (y (FDETN (ID-FMAT (N)))))))))

;; The desired result follows by summing over (slist (n)):

(local-defthmd fsum-tuples-sublist-slist
  (implies (and (fmatp a (n) (n)) (sublistp l (slist (n))))
	   (equal (fsum-tuples l (n) a)
	          (f* (fdet-sum a l (n))
		      (fdetn (id-fmat (n))))))
  :hints (("Goal" :in-theory (e/d (feval-tuple-perm) (feval-tuple feval-tuple-n)))))

(defthmd fsum-tuples-slist
  (implies (fmatp a (n) (n))
	   (equal (fsum-tuples (slist (n)) (n) a)
	          (f* (fdet a (n))
		      (fdetn (id-fmat (n))))))
  :hints (("Goal" :in-theory (enable fdet)
                  :use ((:instance fsum-tuples-sublist-slist (l (slist (n))))))))
	          
(defthmd fdet-unique
  (implies (fmatp a (n) (n))
           (equal (fdetn a)
                  (f* (fdet a (n))
                      (fdetn (id-fmat (n))))))
  :hints (("Goal" :use (fsum-tuples-n fsum-tuples-slist))))


;;-------------------------------------------------------------------------------------------------------
;;   Multiplicativity of the Determinant
;;-------------------------------------------------------------------------------------------------------

;; As an application of fdet-unique, we shall prove that for nxn matrices a and b,

;;   (fdet (fmat* a b) n) = (f* (fdet a n) (fdet b n).

;; To this end, we shall show that the following is a determinant function of its first
;; argument, i.e., it satisfies the constraints on fdetn:

(defun fdet-fmat* (a b n)
  (fdet (fmat* a b) n))



(local-defthm fmat*-replace-row
  (implies (and (fmatp a m n) (fmatp b n p) (natp m) (natp n) (natp p)
                (natp k) (< k m) (flistnp x n))
	   (equal (fmat* (replace-row a k x) b)
	          (replace-row (fmat* a b) k (fdot-list x (transpose-mat b)))))
  :hints (("Goal" :in-theory (enable fmatp fmat* replace-row))))

(local-defthm fdot-list-flist-add
  (implies (and (flistnp x n) (flistnp y n) (fmatp b m n) (natp m))
           (equal (fdot-list (flist-add x y) b)
	          (flist-add (fdot-list x b) (fdot-list y b))))
  :hints (("Goal" :in-theory (enable fmatp fdot-flist-add))))

(local-defthm fdot-list-flist-scalar-mul
  (implies (and (flistnp x n) (fp c) (fmatp b m n) (natp m))
           (equal (fdot-list (flist-scalar-mul c x) b)
	          (flist-scalar-mul c (fdot-list x b))))
  :hints (("Goal" :in-theory (enable fmatp fdot-flist-scalar-mul))))

;; Firsat show that fdet-fmat* is n-linear:

;;   (fdet-fmat* (replace-row a k (flist-add (flist-scalar-mul c x) y)) b n)
;;      = (fdet (fmat* (replace-row a k (flist-add (flist-scalar-mul c x) y)) b) n)
;;      = (fdet (replace-row (fmat* a b)
;;                           k
;;     		             (fdot-list (flist-add (flist-scalar-mul c x) y) (transpose-mat b)))
;;     	        n)
;;      = (fdet (replace-row (fmat* a b)
;;                           k
;;     		             (flist-add (flist-scalar-mul c (fdot-list x (transpose-mat b)))
;;     		                        (fdot-list y (transpose-mat b))))
;;              n)
;;      = (f+ (f* c (fdet (replace-row (fmat* a b) k (fdot-list x (transpose-mat b))) n)
;;            (fdet (replace-row (fmat* a b) k (fdot-list y (transpose-mat b))) n)
;;      = (f+ (f* c (fdet (fmat* (replace-row a k x) b) n))
;;            (fdet (fmat* (replace-row a y x) b) n))
;;      = (f+ (f* c (fdet-fmat* (replace-row a k x) b n))
;;            (fdet-fmat* (replace-row a k y) b n))

(defthmd fdet-fmat*-n-linear
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (natp k) (< k n)
                (flistnp x n) (flistnp y n) (fp c))
           (equal (fdet-fmat* (replace-row a k (flist-add (flist-scalar-mul c x) y)) b n)
                  (f+ (f* c (fdet-fmat* (replace-row a k x) b n))
                      (fdet-fmat* (replace-row a k y) b n))))
  :hints (("Goal" :use ((:instance fmatp-transpose (a b) (m n))
                        (:instance fdot-list-flist-add (m n) (x (FLIST-SCALAR-MUL C X)) (b (transpose-mat b)))))))

;; The proof of the alternating property is easier:

(defthm fmat*-row
  (implies (and (natp m) (natp n) (fmatp a m n) (fmatp b n n) (natp k) (< k m))
           (equal (nth k (fmat* a b))
	          (fdot-list (nth k a) (transpose-mat b))))
  :hints (("Goal" :in-theory (enable nth fmat* fmatp))))
		      
(defthmd fdet-fmat*-adjacent-equal
  (implies (and (fmatp a n n) (fmatp b n n) (posp n)
		(natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (fdet-fmat* a b n) (f0)))
  :hints (("Goal" :use ((:instance fdet-alternating (i k) (j (1+ k)) (a (fmat* a b)))
                        (:instance fmatp-fmat* (m n) (p n))))))

;; Now apply functional instantiation:

(defthmd fdet-fmat*-val-n
  (implies (and (fmatp a (n) (n)) (fmatp b (n) (n)))
           (equal (fdet-fmat* a b (n))
	          (f* (fdet a (n))
		      (fdet-fmat* (id-fmat (n)) b (n)))))
  :hints (("Goal" :use ((:functional-instance fdet-unique
			  (fdetn (lambda (a) (if (and (fmatp a (n) (n)) (fmatp b (n) (n))) (fdet-fmat* a b (n)) (fdetn a)))))))	  
          ("Subgoal 3" :use (fdetn-adjacent-equal (:instance fdet-fmat*-adjacent-equal (n (n)) (k i))))
          ("Subgoal 2" :use (fdetn-n-linear (:instance fdet-fmat*-n-linear (n (n)) (k i))))))

(defthmd fdet-multiplicative
  (implies (and (fmatp a n n) (fmatp b n n) (posp n))
           (equal (fdet (fmat* a b) n)
	          (f* (fdet a n) (fdet b n))))
  :hints (("Goal" :in-theory (enable id-fmat-left)
                  :use ((:functional-instance fdet-fmat*-val-n
                          (n (lambda () (if (and (fmatp a n n) (fmatp b n n) (posp n)) n (n)))))))))
		  

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

(defthmd fmatp-delete-row
  (implies (and (fmatp a m n) (natp m) (natp k) (< k m))
           (fmatp (delete-row k a) (1- m) n))
  :hints (("Goal" :in-theory (enable fmatp))))

(defthmd fmatp-delete-col
  (implies (and (fmatp a m n) (posp m) (natp n) (> n 1) (natp k) (< k n))
           (fmatp (delete-col k a) m (1- n)))
  :hints (("Goal" :in-theory (enable delete-col)
                  :use (fmatp-transpose
                        (:instance fmatp-delete-row (a (transpose-mat a)) (m n) (n m))
			(:instance fmatp-transpose (a (delete-row k (transpose-mat a))) (m (1- n)) (n m))))))

(defthmd fmatp-minor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
	   (fmatp (minor i j a) (1- n) (1- n)))
  :hints (("Goal" :in-theory (enable minor)
                  :use ((:instance fmatp-delete-row (k i) (m n))
		        (:instance fmatp-delete-col (k j) (a (delete-row i a)) (m (1- n)))))))

(local-in-theory (enable nth fmatp))

(local-defun entry-delete-row-induct (a i r m)
  (if (or (zp i) (zp r))
      (list a i r m)
    (list (entry-delete-row-induct (cdr a) (1- i) (1- r) (1- m)))))
    
(local-defthm row-delete-row
  (implies (and (fmatp a m n) (natp m) (> m 1) (posp n) (natp i) (< i m)
                (natp r) (< r (1- m)))
	   (equal (nth r (delete-row i a))
	          (nth (if (>= r i) (1+ r) r) a)))
  :hints (("Goal" :induct (entry-delete-row-induct a i r m))
          ("Subgoal *1/1" :expand ((DELETE-ROW I A)))))

(local-defthmd entry-delete-row
  (implies (and (fmatp a m n) (natp m) (> m 1) (posp n) (natp i) (< i m)
                (natp r) (< r (1- m)) (natp s) (< s n))
	   (equal (entry r s (delete-row i a))
	          (entry (if (>= r i) (1+ r) r) s a))))

(local-defthmd entry-delete-col
  (implies (and (fmatp a m n) (posp m) (natp n) (> n 1) (natp j) (< j n)
                (natp r) (< r m) (natp s) (< s (1- n)))
	   (equal (entry r s (delete-col j a))
	          (entry r (if (>= s j) (1+ s) s) a)))
  :hints (("Goal" :in-theory (e/d (delete-col) (nth-transpose-fmat))
                  :use (fmatp-transpose
                        (:instance fmatp-delete-row (a (transpose-mat a)) (m n) (n m) (k j))
			(:instance fmatp-transpose (a (delete-row j (transpose-mat a))) (m (1- n)) (n m))
                        (:instance transpose-fmat-entry (a (delete-row j (transpose-mat a))) (m (1- n)) (n m) (j r) (i s))
			(:instance entry-delete-row (a (transpose-mat a)) (m n) (n m) (i j) (s r) (r s))
			(:instance transpose-fmat-entry (i r) (j (if (>= s j) (1+ s) s)))))))

;; We derive an expression for an entry of (minor i j a):

(defthmd entry-fmat-minor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (natp s) (< r (1- n)) (< s (1- n)))
	   (equal (entry r s (minor i j a))
	          (entry (if (>= r i) (1+ r) r)
		         (if (>= s j) (1+ s) s)
			 a)))
  :hints (("Goal" :in-theory (e/d (minor) (entry delete-row row-delete-row fmatp))
                  :use ((:instance fmatp-delete-row (m n) (k i))
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
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (< r (1- n)) (natp s) (< s (1- n)))
	   (equal (nth s (delete-nth j (nth (if (< r i) r (1+ r)) a)))
	          (nth s (nth r (minor i j a)))))
  :hints (("Goal" :in-theory (disable nth fmatp)
                  :use (entry-fmat-minor))))

(defthmd row-fmat-minor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (< r (1- n)))
	   (equal (nth r (minor i j a))
	          (delete-nth j (nth (if (< r i) r (1+ r)) a))))
  :hints (("Goal" :in-theory (disable flistnp-nth len-fmat-row len-flist MEMBER-FMATP-FLISTNP nth fmatp delete-nth flistnp-row)
                  :use (fmatp-minor
                        (:instance nth-diff-diff (x (nth r (minor i j a)))
                                                 (y (delete-nth j (nth (if (< r i) r (1+ r)) a))))
			(:instance nth-nth-minor
			            (s (nth-diff (nth r (minor i j a)) (delete-nth j (nth (if (< r i) r (1+ r)) a)))))
			(:instance len-flist (x (nth r a)))
			(:instance len-flist (x (nth (1+ r) a)))
			(:instance len-flist (x (nth r (minor i j a))) (n (1- n)))
			(:instance flistnp-row (m n) (i r))
			(:instance flistnp-row (m n) (i (1+ r)))
			(:instance flistnp-row (a (minor i j a)) (m (1- n)) (n (1- n)) (i r))))))

;; minor commutes with transpose-mat:

(local-defthmd entry-transpose-minor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (natp s) (< r (1- n)) (< s (1- n)))
           (equal (entry r s (transpose-mat (minor i j a)))
	          (entry (if (>= s i) (1+ s) s)
		         (if (>= r j) (1+ r) r)
			 a)))
  :hints (("Goal" :in-theory (disable nth fmatp nth-transpose-fmat)
                  :use (fmatp-minor
                        (:instance transpose-fmat-entry (a (minor i j a)) (m (1- n)) (n (1- n)) (j r) (i s))
                        (:instance entry-fmat-minor (r s) (s r))))))

(local-defthmd entry-fmat-minor-transpose
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n)
                (natp r) (natp s) (< r (1- n)) (< s (1- n)))
           (equal (entry r s (minor j i (transpose-mat a)))
	          (entry (if (>= s i) (1+ s) s)
		         (if (>= r j) (1+ r) r)
			 a)))
  :hints (("Goal" :in-theory (disable nth fmatp nth-transpose-fmat)
                  :use ((:instance fmatp-transpose (m n))
                        (:instance entry-fmat-minor (a (transpose-mat a)) (i j) (j i))
                        (:instance transpose-fmat-entry (m n) (j (if (>= r j) (1+ r) r)) (i (if (>= s i) (1+ s) s)))))))

(defthmd transpose-minor-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
	   (and (fmatp (transpose-mat (minor i j a)) (1- n) (1- n))
	        (equal (transpose-mat (minor i j a))
	               (minor j i (transpose-mat a)))))
  :hints (("Goal" :in-theory (disable entry nth fmatp nth-transpose-fmat)
                  :use (fmatp-minor
                        (:instance fmatp-transpose (m n))
                        (:instance fmatp-minor (a (transpose-mat a)) (i j) (j i))
                        (:instance fmatp-transpose (m (1- n)) (n (1- n)) (a (minor i j a)))
			(:instance fmat-entry-diff-lemma (m (1- n)) (n (1- n))
			                            (a (transpose-mat (minor i j a)))
			                            (b (minor j i (transpose-mat a))))
			(:instance entry-transpose-minor
			            (r (car (entry-diff (transpose-mat (minor i j a)) (minor j i (transpose-mat a)))))
			            (s (cdr (entry-diff (transpose-mat (minor i j a)) (minor j i (transpose-mat a))))))
			(:instance entry-fmat-minor-transpose
			            (r (car (entry-diff (transpose-mat (minor i j a)) (minor j i (transpose-mat a)))))
			            (s (cdr (entry-diff (transpose-mat (minor i j a)) (minor j i (transpose-mat a))))))))))

;; Next, we define the cofactor of an entry of a:

(defund fdet-cofactor (i j a n)
  (if (evenp (+ i j))
      (fdet (minor i j a) (1- n))
    (f- (fdet (minor i j a) (1- n)))))

;; Cofactor expansion of the determinant of a by column j:

(defun expand-fdet-col-aux (a i j n)
  (if (zp i)
      (f0)
    (f+ (f* (entry (1- i) j a)
            (fdet-cofactor (1- i) j a n))
	(expand-fdet-col-aux a (1- i) j n))))

(defund expand-fdet-col (a j n)
  (expand-fdet-col-aux a n j n))

;; Cofactor expansion of the determinant of a by row i:

(defun expand-fdet-row-aux (a i j n)
  (if (zp j)
      (f0)
    (f+ (f* (entry i (1- j) a)
            (fdet-cofactor i (1- j) a n))
	(expand-fdet-row-aux a i (1- j) n))))

(defund expand-fdet-row (a i n)
  (expand-fdet-row-aux a i n n))

;; Cofactor expansion by column i is equivalent to expansion of the transpose by row i:

(defthm fdet-cofactor-transpose
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (< i n) (natp j) (< j n))
	   (equal (fdet-cofactor j i (transpose-mat a) n)
	          (fdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable fdet-cofactor)
                  :use (fmatp-minor transpose-minor-fmat
		        (:instance fdet-transpose (a (minor i j a)) (n (1- n)))))))

(local-defthmd expand-fdet-row-aux-transpose
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (< i n) (natp j) (< j n))
           (equal (expand-fdet-row-aux (transpose-mat a) j i n)
	          (expand-fdet-col-aux a i j n))))

(defthmd expand-fdet-row-transpose
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (< i n))
           (equal (expand-fdet-row (transpose-mat a) i n)
	          (expand-fdet-col a i n)))
  :hints (("Goal" :in-theory (enable expand-fdet-row expand-fdet-col expand-fdet-row-aux-transpose))))

;; We shall prove, by functional instantiation of fdet-unique,  that the result of cofactor
;; expansion by a column has the same value as the determinant, and it will follow that the
;; same is true for expansion by a row.  The requires proving analogs of the constraints on
;; fdetn.

(defthm fp-fdet-cofactor
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (natp j) (< i n) (< j n))
           (fp (fdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable fdet-cofactor)
                  :use (fmatp-minor fp-entry))))

(local-defthmd fp-expand-fdet-col-aux
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (natp i) (<= i n) (natp j) (< j n))
           (fp (expand-fdet-col-aux a i j n)))
  :hints (("Subgoal *1/5" :use ((:instance fp-entry (m n) (i (1- i)))))))

(defthm fp-expand-fdet-col
  (implies (and (fmatp a n n) (> n 1) (natp j) (< j n))
           (fp (expand-fdet-col a j n)))
  :hints (("Goal" :in-theory (enable expand-fdet-col)
                  :use ((:instance fp-expand-fdet-col-aux (i n))))))

(local-defthmd flistnp-delete-nth
  (implies (and (flistnp x n) (posp n) (natp k) (< k n))
           (flistnp (delete-nth k x) (1- n))))

(local-defthmd row-fmat-minor-replace-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (flistnp x n)
		(natp r) (< r (1- n)))
	   (equal (nth r (minor i j (replace-row a k x)))
	          (nth r (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x)))))
  :hints (("Goal" :in-theory (e/d (row-fmat-minor) (nth fmatp fmatp-replace-row nth-replace-row len-fmatp))
                  :use (fmatp-minor flistnp-delete-nth
		        (:instance flistnp-delete-nth (k j))
                        (:instance len-fmatp (m n))
                        (:instance len-fmatp (a (minor i j a)) (m (1- n)) (n (1- n)))
			(:instance fmatp-replace-row (m n) (r x))
			(:instance nth-replace-row (r x) (j r))
			(:instance nth-replace-row (r x) (j (1+ r)))
			(:instance nth-replace-row (a (minor i j a)) (j r) (k (if (< k i) k (1- k))) (r (delete-nth j x)))
                        (:instance fmatp-minor (a (replace-row a k x)))))))

(local-defthmd minor-replace-fmat-row-1
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (flistnp x n))
	   (and (true-listp (minor i j (replace-row a k x)))
	        (equal (len (minor i j (replace-row a k x))) (1- n))
		(true-listp (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x)))
		(equal (len (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x))) (1- n))))
  :hints (("Goal" :in-theory (disable nth fmatp fmatp-replace-row len-fmatp)
                  :use (fmatp-minor flistnp-delete-nth
		        (:instance flistnp-delete-nth (k j))
                        (:instance len-fmatp (m n))
                        (:instance len-fmatp (a (minor i j a)) (m (1- n)) (n (1- n)))
                        (:instance len-fmatp (a (minor i j (replace-row a k x))) (m (1- n)) (n (1- n)))
			(:instance fmatp-replace-row (m n) (r x))
                        (:instance fmatp-minor (a (replace-row a k x)))))))

;; The effect on (minor i j a) of replacing a row of a other than row i:

(defthmd minor-replace-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (flistnp x n))
	   (equal (minor i j (replace-row a k x))
	          (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x))))
  :hints (("Goal" :in-theory (disable nth fmatp fmatp-replace-row len-fmatp)
                  :use (minor-replace-fmat-row-1
		        (:instance nth-diff-diff (x (minor i j (replace-row a k x)))
			                         (y (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x))))
                        (:instance row-fmat-minor-replace-fmat-row
			             (r (nth-diff (minor i j (replace-row a k x))
				                  (replace-row (minor i j a) (if (< k i) k (1- k)) (delete-nth j x)))))))))

(local-defthmd row-fmat-minor-replace-fmat-row-i
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (flistnp x n)
		(natp r) (< r (1- n)))
	   (equal (nth r (minor i j (replace-row a i x)))
	          (nth r (minor i j a))))
  :hints (("Goal" :in-theory (e/d (row-fmat-minor) (nth fmatp fmatp-replace-row nth-replace-row len-fmatp))
                  :use (fmatp-minor
                        (:instance len-fmatp (m n))
                        (:instance len-fmatp (a (minor i j a)) (m (1- n)) (n (1- n)))
			(:instance fmatp-replace-row (m n) (r x) (k i))
			(:instance nth-replace-row (r x) (j r) (k i))
			(:instance nth-replace-row (r x) (j (1+ r)) (k i))
                        (:instance fmatp-minor (a (replace-row a i x)))))))

(local-defthmd minor-replace-fmat-row-i-1
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (flistnp x n))
	   (and (true-listp (minor i j (replace-row a i x)))
	        (equal (len (minor i j (replace-row a i x))) (1- n))
		(true-listp (minor i j a))
		(equal (len (minor i j a)) (1- n))))
  :hints (("Goal" :in-theory (disable nth fmatp fmatp-replace-row len-fmatp)
                  :use (fmatp-minor
                        (:instance len-fmatp (m n))
                        (:instance len-fmatp (a (minor i j a)) (m (1- n)) (n (1- n)))
                        (:instance len-fmatp (a (minor i j (replace-row a i x))) (m (1- n)) (n (1- n)))
			(:instance fmatp-replace-row (m n) (r x) (k i))
                        (:instance fmatp-minor (a (replace-row a i x)))))))

;; Replacing row i of a does not alter (minor i j a):

(defthmd minor-replace-fmat-row-i
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (flistnp x n))
	   (equal (minor i j (replace-row a i x))
	          (minor i j a)))
  :hints (("Goal" :in-theory (disable nth fmatp fmatp-replace-row len-fmatp)
                  :use (minor-replace-fmat-row-i-1
		        (:instance nth-diff-diff (x (minor i j (replace-row a i x)))
			                         (y (minor i j a)))
                        (:instance row-fmat-minor-replace-fmat-row-i
			             (r (nth-diff (minor i j (replace-row a i x))
				                  (minor i j a))))))))

(defthmd cofactor-replace-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (flistnp x n))
	   (equal (fdet-cofactor i j (replace-row a i x) n)
	          (fdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable fdet-cofactor)
                  :use (minor-replace-fmat-row-i))))

(local-defthmd delete-nth-flist-add-scalar-mul
  (implies (and (flistnp x n) (flistnp y n) (fp c) (posp n) (natp k) (< k n))
           (equal (delete-nth k (flist-add (flist-scalar-mul c x) y))
	          (flist-add (flist-scalar-mul c (delete-nth k x)) (delete-nth k y)))))

(local-defthmd fdet-minor-n-linear
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (flistnp x n) (flistnp y n) (fp c))
	   (equal (fdet (minor i j (replace-row a k (flist-add (flist-scalar-mul c x) y))) (+ -1 n))
	          (f+ (f* c (fdet (minor i j (replace-row a k x)) (1- n)))
		      (fdet (minor i j (replace-row a k y)) (1- n)))))
  :hints (("Goal" :in-theory (e/d (delete-nth-flist-add-scalar-mul minor-replace-fmat-row)
                                  (fmatp fdet-n-linear))
                  :use (fmatp-minor
		        (:instance flistnp-delete-nth (k j))
		        (:instance flistnp-delete-nth (k j) (x y))
		        (:instance fdet-n-linear (a (minor i j a))
			                         (n (1- n))
			                         (i (if (< k i) k (1- k)))
						 (x (delete-nth j x))
						 (y (delete-nth j y)))))))

(local-defthmd fdet-cofactor-n-linear
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (flistnp x n) (flistnp y n) (fp c))
	   (equal (fdet-cofactor i j (replace-row a k (flist-add (flist-scalar-mul c x) y)) n)
	          (f+ (f* c (fdet-cofactor i j (replace-row a k x) n))
		      (fdet-cofactor i j (replace-row a k y) n))))
  :hints (("Goal" :in-theory (e/d (f-f+ f-f* fdet-cofactor fdet-minor-n-linear)
                                  (fmatp fmatp-minor flistnp flist-add flist-scalar-mul))
                  :use ((:instance fmatp-minor (a (replace-row a k x)))
		        (:instance fmatp-minor (a (replace-row a k y)))))))

(local-defthmd fdet-cofactor-i
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (flistnp x n) (flistnp y n) (fp c))
	   (and (equal (fdet-cofactor i j (replace-row a i (flist-add (flist-scalar-mul c x) y)) n)
	               (fdet-cofactor i j a n))
		(equal (fdet-cofactor i j (replace-row a i y) n)
	               (fdet-cofactor i j a n))
	        (equal (fdet-cofactor i j (replace-row a i x) n)
		       (fdet-cofactor i j a n))))
  :hints (("Goal" :in-theory (e/d (f-f+ f-f* fdet-cofactor minor-replace-fmat-row-i)
                                  (fmatp fmatp-minor flistnp flist-add flist-scalar-mul)))))

(local-defund expand-fdet-col-aux-term (i j a n)
  (f* (entry i j a)
      (fdet-cofactor i j a n)))

(local-defun expand-fdet-col-aux-alt (a i j n)
  (if (zp i)
      (f0)
    (f+ (expand-fdet-col-aux-term (1- i) j a n)
	(expand-fdet-col-aux-alt a (1- i) j n))))

(local-defthmd expand-fdet-col-aux-alt-rewrite
  (equal (expand-fdet-col-aux-alt a i j n)
         (expand-fdet-col-aux a i j n))
  :hints (("Goal" :in-theory (enable expand-fdet-col-aux-term))))

(local-defthmd expand-fdet-col-aux-term-expand
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (not (= k i)) (flistnp x n) (flistnp y n) (fp c))
	   (equal (expand-fdet-col-aux-term i j (replace-row a k (flist-add (flist-scalar-mul c x) y)) n)
	          (f+ (f* c (expand-fdet-col-aux-term i j (replace-row a k x) n))
		      (expand-fdet-col-aux-term i j (replace-row a k y) n))))
  :hints (("Goal" :in-theory (e/d (f-f+ f-f* expand-fdet-col-aux-term fdet-cofactor-n-linear)
                                  (nth fmatp fmatp-minor flistnp flist-add flist-scalar-mul))
		  :use ((:instance fp-entry (m n))
		        (:instance f*assoc (x c) (y (entry i j a)) (z (FDET-COFACTOR I J (REPLACE-ROW A K X) n)))
			(:instance f*comm (x c) (y (entry i j a)))
		        (:instance f*assoc (y c) (x (entry i j a)) (z (FDET-COFACTOR I J (REPLACE-ROW A K X) n)))))))

(local-defthmd expand-fdet-col-aux-term-expand-i
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (flistnp x n) (flistnp y n) (fp c))
	   (equal (expand-fdet-col-aux-term i j (replace-row a i (flist-add (flist-scalar-mul c x) y)) n)
	          (f+ (f* c (expand-fdet-col-aux-term i j (replace-row a i x) n))
		      (expand-fdet-col-aux-term i j (replace-row a i y) n))))
  :hints (("Goal" :in-theory (e/d (f-f+ f-f* expand-fdet-col-aux-term fdet-cofactor-i)
                                  (flistnp-flist-scalar-mul nth fmatp fmatp-minor flistnp flist-add flist-scalar-mul))
		  :use (flistnp-flist-scalar-mul
		        (:instance f*assoc (x c) (y (nth j x)) (z (FDET-COFACTOR I J A N)))))))

(local-defthmd expand-fdet-col-aux-term-expand-all
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp k) (< k n) (flistnp x n) (flistnp y n) (fp c))
	   (equal (expand-fdet-col-aux-term i j (replace-row a k (flist-add (flist-scalar-mul c x) y)) n)
	          (f+ (f* c (expand-fdet-col-aux-term i j (replace-row a k x) n))
		      (expand-fdet-col-aux-term i j (replace-row a k y) n))))
  :hints (("Goal" :use (expand-fdet-col-aux-term-expand expand-fdet-col-aux-term-expand-i))))

(local-defthm fp-fdet-col-aux-term
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (fp (expand-fdet-col-aux-term i j a n)))
  :hints (("Goal" :in-theory (enable expand-fdet-col-aux-term)
                  :use ((:instance fp-entry (m n))))))

(local-defthm fp-fdet-col-aux-alt
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (<= i n) (natp j) (< j n))
           (fp (expand-fdet-col-aux-alt a i j n))))

(local-defthmd hack-5
  (implies (and (fp x) (fp y) (fp c) (fp xt) (fp yt))
           (equal (f+ (f+ (f* c xt) yt) (f+ (f* c x) y))
	          (f+ (f+ (f* c xt) (f* c x)) (f+ yt y))))
  :hints (("Goal" :use ((:instance f+assoc (x (f+ (f* c xt) yt)) (y (f* c x)) (z y))
                        (:instance f+assoc (x (f* c xt)) (y yt) (z (f* c x)))
			(:instance f+comm (x yt) (y (f* c x)))
			(:instance f+assoc (x (f* c xt)) (y (f* c x)) (z yt))
			(:instance f+assoc (x (f+ (f* c xt) (f* c x))) (y yt) (z y))))))

(local-defthmd expand-fdet-col-aux-alt-n-linear
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (<= i n) (natp j) (< j n)
                (natp k) (< k n) (flistnp x n) (flistnp y n) (fp c))
	   (equal (expand-fdet-col-aux-alt (replace-row a k (flist-add (flist-scalar-mul c x) y)) i j n)
		  (f+ (f* c (expand-fdet-col-aux-alt (replace-row a k x) i j n))
		      (expand-fdet-col-aux-alt (replace-row a k y) i j n))))
  :hints (("Goal" :in-theory (e/d (f-f+ f-f* expand-fdet-col-aux-term-expand-all)
                                  (entry expand-fdet-col-aux-alt-rewrite flistnp-flist-scalar-mul nth fmatp fmatp-minor
				   flistnp flist-add flist-scalar-mul)))				   
	  ("Subgoal *1/5" :use ((:instance hack-5 (x (EXPAND-FDET-COL-AUX-ALT (REPLACE-ROW A K X) (+ -1 I) J N))
		                                  (y (EXPAND-FDET-COL-AUX-ALT (REPLACE-ROW A K Y) (+ -1 I) J N))
				         	  (xt (EXPAND-FDET-COL-AUX-TERM (+ -1 I) J (REPLACE-ROW A K X) N))
					          (yt (EXPAND-FDET-COL-AUX-TERM (+ -1 I) J (REPLACE-ROW A K Y) N)))))))

(local-defthmd expand-fdet-col-aux-n-linear
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (<= i n) (natp j) (< j n)
                (natp k) (< k n) (flistnp x n) (flistnp y n) (fp c))
	   (equal (expand-fdet-col-aux (replace-row a k (flist-add (flist-scalar-mul c x) y)) i j n)
		  (f+ (f* c (expand-fdet-col-aux (replace-row a k x) i j n))
		      (expand-fdet-col-aux (replace-row a k y) i j n))))
  :hints (("Goal" :in-theory (enable expand-fdet-col-aux-alt-rewrite)
                  :use (expand-fdet-col-aux-alt-n-linear))))

;; It follows that cofactor expansion by column j is n-linear:

(defthmd expand-fdet-col-n-linear
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k n) (flistnp x n) (flistnp y n) (fp c))
	   (equal (expand-fdet-col (replace-row a k (flist-add (flist-scalar-mul c x) y)) j n)
		  (f+ (f* c (expand-fdet-col (replace-row a k x) j n))
		      (expand-fdet-col (replace-row a k y) j n))))
  :hints (("Goal" :in-theory (enable expand-fdet-col)
                  :use ((:instance expand-fdet-col-aux-n-linear (i n))))))

;; Now suppose adjacent rows k and k+1 of a are equal.  Then for any i other than k and k+1, (minor i j a)
;; has 2 adjacent rows,and therefore (fdet-cofactor i j a n) = (f0).  Meanwhile, (minor k j) = (minor (1+ k) j)
;; and (entry k j a) = (entry (1+ k) j a), but k + j and (k + 1) + j have opposite parities, and therefore
;; (fdet-cofactor k j a n) + (fdet-cofactor (1+ k) j a n) = (f0).  Thus, (expand-fdet-col a j n) = r0:

(local-defthmd minor-equal-rows-1
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (< i k))
	   (equal (nth (1- k) (minor i j a))
	          (nth k (minor i j a))))
  :hints (("Goal" :use ((:instance row-fmat-minor (r (1- k)))
                        (:instance row-fmat-minor (r k))))))

(local-defthmd minor-equal-rows-2
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (> i (1+ k)) (< i n))
	   (equal (nth k (minor i j a))
	          (nth (1+ k) (minor i j a))))
  :hints (("Goal" :use ((:instance row-fmat-minor (r (1+ k)))
                        (:instance row-fmat-minor (r k))))))

(local-defthmd minor-equal-rows-0-1
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (< i k))
	   (equal (fdet (minor i j a) (+ -1 n))
	          (f0)))
  :hints (("Goal" :use (minor-equal-rows-1 fmatp-minor
                        (:instance fdet-alternating (a (minor i j a)) (n (1- n)) (i (1- k)) (j k))))))

(local-defthmd minor-equal-rows-0-2
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (> i (1+ k)) (< i n))
	   (equal (fdet (minor i j a) (+ -1 n))
	          (f0)))
  :hints (("Goal" :use (minor-equal-rows-2 fmatp-minor
                        (:instance fdet-alternating (a (minor i j a)) (n (1- n)) (i (1+ k)) (j k))))))
			
(local-defthmd cofactor-equal-rows
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (< i n) (not (= i k)) (not (= i (1+ k))))
	   (equal (fdet-cofactor i j a n)
	          (f0)))
  :hints (("Goal" :in-theory (enable fdet-cofactor)
                  :use (minor-equal-rows-0-1 minor-equal-rows-0-2))))


(local-defthm nth-minor-equal-rows
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp r) (< r (1- n)))
	   (equal (nth r (minor k j a))
	          (nth r (minor (1+ k) j a))))
  :hints (("Goal" :use ((:instance row-fmat-minor (i k))
                        (:instance row-fmat-minor (i (1+ k)))))))

(local-defthmd minor-equal-rows
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (minor k j a)
	          (minor (1+ k) j a)))
  :hints (("Goal" :in-theory (disable len-fmatp)
                  :use ((:instance fmatp-minor (i k))
                        (:instance fmatp-minor (i (1+ k)))
			(:instance len-fmatp (a (minor k j a)) (m (1- n)) (n (1- n)))
			(:instance len-fmatp (a (minor (1+ k) j a)) (m (1- n)) (n (1- n)))
			(:instance nth-diff-diff (x (minor k j a)) (y (minor (1+ k) j a)))
			(:instance nth-minor-equal-rows (r (nth-diff (minor k j a) (minor (1+ k) j a))))))))

(local-defthmd cofactor-sum-0
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (f+ (fdet-cofactor (1+ k) j a n)
	              (fdet-cofactor k j a n))
	          (f0)))
  :hints (("Goal" :in-theory (e/d (fdet-cofactor) (nth fmatp))
                  :use (minor-equal-rows
		        (:instance fmatp-minor (i k))))))
		
(local-defthmd expand-fdet-col-aux-0-1
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (<= i k))
	   (equal (expand-fdet-col-aux a i j n)
	          (f0)))		  
  :hints (("Subgoal *1/2" :in-theory (enable cofactor-equal-rows)
                          :use ((:instance fp-entry (m n) (i (1- i)))))))

(local-defthmd expand-fdet-col-aux-0-2
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (expand-fdet-col-aux a (+ 2 k) j n)
	          (f0)))		  
  :hints (("Goal" :in-theory (disable fdist)
                  :use (cofactor-sum-0
                        (:instance fp-entry (m n) (i k))
                        (:instance expand-fdet-col-aux-0-1 (i k))
			(:instance fdist (x (entry k j a)) (y (fdet-cofactor (1+ k) j a n)) (z (fdet-cofactor k j a n)))))))

(local-defthmd expand-fdet-col-aux-0-3
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a))
		(natp i) (> i (1+ k)) (<= i n))
	   (equal (expand-fdet-col-aux a i j n)
	          (f0)))		  
  :hints (("Subgoal *1/2" :in-theory (e/d (fp-expand-fdet-col-aux) (fmatp nth))
                          :use (expand-fdet-col-aux-0-2
			        (:instance cofactor-equal-rows (i (1- i)))
			        (:instance fp-entry (m n) (i (1- i)))))))

(defthmd expand-fdet-col-adjacent-equal
  (implies (and (fmatp a n n) (> n 1) (natp j) (< j n)
                (natp k) (< k (1- n)) (= (row k a) (row (1+ k) a)))
	   (equal (expand-fdet-col a j n)
	          (f0)))
  :hints (("Goal" :in-theory (enable expand-fdet-col)
                  :use ((:instance expand-fdet-col-aux-0-3 (i n))))))

;; By functional instantiation of fdet-unique,we have the following:

(local-defthmd expand-fdet-col-val-n
  (implies (and (fmatp a (n) (n)) (> (n) 1) (natp k) (< k (n)))
           (equal (expand-fdet-col a k (n))
	          (f* (fdet a (n))
		      (expand-fdet-col (id-fmat (n)) k (n)))))
  :hints (("Goal" :use ((:functional-instance fdet-unique
			  (fdetn (lambda (a)
			                (if (and (fmatp a (n) (n)) (> (n) 1) (natp k) (< k (n)))
					    (expand-fdet-col a k (n))
					  (fdetn a)))))))
	  ("Subgoal 3" :use (fdetn-adjacent-equal (:instance expand-fdet-col-adjacent-equal (k i) (j k) (n (n)))))
          ("Subgoal 2" :use (fdetn-n-linear (:instance expand-fdet-col-n-linear (k i) (j k) (n (n)))))))

(defthmd expand-fdet-col-val
  (implies (and (fmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-fdet-col a k n)
	          (f* (fdet a n)
		      (expand-fdet-col (id-fmat n) k n))))
  :hints (("Goal" :use ((:functional-instance expand-fdet-col-val-n
			  (n (lambda () (if (and (posp n) (> n 1)) n (n)))))))))

;; It remains to show that (expand-fdet-col (id-fmat n) k n) = (f1).
;; By row-fmat-minor, we habe the following expression for the rth row of (minor i j (id-fmat n)):

(defthmd nth-minor-id-fmat
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n)
                (natp r) (< r (1- n)))
	   (equal (nth r (minor i j (id-fmat n)))
	          (delete-nth j (funit (if (< r i) r (1+ r)) n))))
  :hints (("Goal" :in-theory (e/d (nth-id-fmat) (fmatp-id-fmat))
                  :use (fmatp-id-fmat
		        (:instance row-fmat-minor (a (id-fmat n)))))))

;; The following is a consequence of the definirtions of funit and delete-nth:

(local-defun delete-nth-funit-induct (j k n)
  (if (zp j)
      (list j k n)
    (list (delete-nth-funit-induct (1- j) (1- k) (1- n)))))

(local-defun delete-nth-flistn0-induct (j n)
  (if (zp j)
      (list j n)
    (delete-nth-flistn0-induct (1- j) (1- n))))

(local-defthm delete-nth-flistn0
  (implies (and (natp j) (< j n) (posp n))
           (equal (delete-nth j (flistn0 n))
	          (flistn0 (1- n))))
  :hints (("Goal" :induct (delete-nth-flistn0-induct j n))))

(defthmd delete-nth-funit
  (implies (and (posp n) (natp j) (< j n) (natp k) (< k n))
           (equal (delete-nth j (funit k n))
	          (if (< j k)
		      (funit (1- k) (1- n))
		    (if (> j k)
		        (funit k (1- n))
		      (flistn0 (1- n))))))
  :hints (("Goal" :induct (delete-nth-funit-induct j k n))
          ("Subgoal *1/2" :expand ((DELETE-NTH J (LIST* (f1) (f0) (FLISTN0 (+ -2 N))))
	                           (DELETE-NTH (+ -1 J) (CONS (f0) (FLISTN0 (+ -2 N))))))))

;; Consequently, if i <> j, then we find a zero row of (minor i j (id-fmat n)), which implies that
;; its determinant is (f0):

(defthmd nth-minor-id-fmat-0
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (equal (nth (if (< j i) j (1- j)) (minor i j (id-fmat n)))
	          (flistn0 (1- n))))
  :hints (("Goal" :in-theory (enable nth-minor-id-fmat delete-nth-funit))))

(defthmd fdet-minor-id-fmat-0
  (implies (and (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n) (not (= i j)))
	   (equal (fdet (minor i j (id-fmat n)) (1- n))
	          (f0)))
  :hints (("Goal" :use (nth-minor-id-fmat-0
                        (:instance fdet-row-0 (a (minor i j (id-fmat n))) (n (1- n)) (k (if (< j i) j (1- j))))
			(:instance fmatp-minor (a (id-fmat n)))))))

;; On the other hand, (minor j j (id-fmat n)) = (id-fmat (1- n)):

(defthmd nth-minor-id-fmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n) (natp r) (< r (1- n)))
	   (equal (nth r (minor j j (id-fmat n)))
	          (nth r (id-fmat (1- n)))))
  :hints (("Goal" :in-theory (enable nth-minor-id-fmat delete-nth-funit))))

(defthmd minor-id-fmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n))
	   (equal (minor j j (id-fmat n))
	          (id-fmat (1- n))))
  :hints (("Goal" :use ((:instance fmat-entry-diff-lemma (m (1- n)) (n (1- n)) (a (minor j j (id-fmat n))) (b (id-fmat (1- n))))
                        (:instance nth-minor-id-fmat-diagonal (r (car (entry-diff (minor j j (id-fmat n)) (id-fmat (1- n))))))
			(:instance fmatp-minor (i j) (a (id-fmat n)))))))

;; Thus, the corresponding cofactor is (f1), as is the cofactor expansion:

(local-defthmd fdet-minor-id-fmat-diagonal
  (implies (and (natp n) (> n 1) (natp j) (< j n))
	   (equal (fdet (minor j j (id-fmat n)) (1- n))
	          (f1)))
  :hints (("Goal" :use (minor-id-fmat-diagonal))))

(local-defthmd expand-fdet-col-aux-id-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n) (natp i) (<= i n))
           (equal (expand-fdet-col-aux (id-fmat n) i j n)
	          (if (> i j) (f1) (f0))))
  :hints (("Subgoal *1/2" :in-theory (enable fdet-cofactor)
                          :use (fdet-minor-id-fmat-diagonal
			        (:instance fdet-minor-id-fmat-0 (i (1- i)))))))

(defthmd expand-fdet-col-id-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n))
           (equal (expand-fdet-col (id-fmat n) j n)
	          (f1)))
  :hints (("Goal" :in-theory (enable expand-fdet-col-aux-id-fmat expand-fdet-col))))

;; Combine this with expand-fdet-col-val:

(defthmd expand-fdet-col-fdet
  (implies (and (fmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-fdet-col a k n)
	          (fdet a n)))
  :hints (("Goal" :use (expand-fdet-col-val (:instance expand-fdet-col-id-fmat (j k))))))

;; It follows from fdet-transpose, expand-fdet-row-transpose, and transpose-fmat-2 that the same holds
;; for row expansion:

(defthmd expand-fdet-row-fdet
  (implies (and (fmatp a n n) (posp n) (> n 1) (natp k) (< k n))
           (equal (expand-fdet-row a k n)
	          (fdet a n)))
  :hints (("Goal" :use (fdet-transpose
                        (:instance expand-fdet-row-transpose (i k) (a (transpose-mat a)))
                        (:instance expand-fdet-col-fdet (a (transpose-mat a)))
			(:instance fmatp-transpose (m n))
			(:instance transpose-fmat-2 (m n))))))


;;---------------------------------------------------------------------------------------------------------

;; As a consequence of expand-fdet-row-fdet, we have a recursive version of fdet, based on cofactor
;; expansion with respect to row 0:

(encapsulate ()

(local (include-book "ordinals/lexicographic-book" :dir :system))

(set-well-founded-relation acl2::l<)

(mutual-recursion

  (defund fdet-rec-cofactor (j a n)
    (declare (xargs :measure (list (nfix n) 0 0)))
    (if (zp n)
        ()
      (if (evenp j)
          (fdet-rec (minor 0 j a) (1- n))
        (f- (fdet-rec (minor 0 j a) (1- n))))))

  (defun expand-fdet-rec-aux (a j n)
    (declare (xargs :measure (list (nfix n) 1 (nfix j))))
    (if (zp j)
        (f0)
      (f+ (f* (entry 0 (1- j) a)
              (fdet-rec-cofactor (1- j) a n))
	  (expand-fdet-rec-aux a (1- j) n))))

  (defund expand-fdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 2 0)))
    (expand-fdet-rec-aux a n n))

  (defun fdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 3 0)))
    (if (zp n)
        (f0)
      (if (= n 1)
          (entry 0 0 a)
        (expand-fdet-rec a n))))

))

(local-defun minors (a k)
  (if (zp k)
      ()
    (cons (minor 0 (1- k) a)
          (minors a (1- k)))))

(local (encapsulate ()

  (local (include-book "ordinals/lexicographic-book" :dir :system))

  (set-well-founded-relation acl2::l<)

  (defun fdet-rec-fdet-induct (flg a n)
    (declare (xargs :measure (list (nfix n) (acl2-count a))))
    (if (zp n)
        (list a n)
      (if flg
          (if (consp a)
	      (and (fdet-rec-fdet-induct () (car a) n)
	           (fdet-rec-fdet-induct t (cdr a) n))
            t)
        (if (> n 1)
            (fdet-rec-fdet-induct t (minors a n) (1- n))
	  t))))
))

(local-defun fmat-listp (l n)
  (if (consp l)
      (and (fmatp (car l) n n)
	   (fmat-listp (cdr l) n))
    t))

(local-defun fdet-rec-equal-fdet-listp (l n)
  (if (consp l)
      (and (equal (fdet-rec (car l) n)
	          (fdet (car l) n))
	   (fdet-rec-equal-fdet-listp (cdr l) n))
    t))

(local-defthm fdet-1
  (implies (fmatp a 1 1)
           (equal (fdet a 1)
	          (entry 0 0 a)))
  :hints (("Goal" :in-theory (enable fdet-term fdet)
                  :expand ((fdet-prod a '(0) 1)))))

(local-defthm fmat-listp-minors
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp k) (<= k n))
           (fmat-listp (minors a k) (1- n)))
  :hints (("Subgoal *1/5" :use ((:instance fmatp-minor (i 0) (j (1- k)))))))

(local-defthmd expand-fdet-rec-aux-rewrite
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (<= j n)
                (fdet-rec-equal-fdet-listp (minors a j) (1- n)))
           (equal (expand-fdet-rec-aux a j n)
	          (expand-fdet-row-aux a 0 j n)))
  :hints (("Goal" :in-theory (enable fdet-cofactor fdet-rec-cofactor))))

(local-defthm fdet-rec-rewrite
  (implies (and (fmatp a n n) (natp n) (> n 1)
                (fdet-rec-equal-fdet-listp (minors a n) (1- n)))
	   (equal (fdet-rec a n) (fdet a n)))
  :hints (("Goal" :in-theory (e/d (expand-fdet-rec expand-fdet-row) (expand-fdet-rec-aux expand-fdet-row-aux))
                  :use ((:instance expand-fdet-rec-aux-rewrite (j n))
		        (:instance expand-fdet-row-fdet (k 0))))))

(local-defthm fdet-rec-fdet-lemma
  (implies (posp n)
           (if flg
               (implies (fmat-listp x n)
	                (fdet-rec-equal-fdet-listp x n))
	     (implies (fmatp x n n)
	              (equal (fdet-rec x n) (fdet x n)))))
  :rule-classes ()
  :hints (("Goal" :induct (fdet-rec-fdet-induct flg x n))
          ("Subgoal *1/5" :use ((:instance fmat-listp-minors (a x) (k n))))))

(defthmd fdet-rec-fdet
  (implies (and (fmatp a n n) (posp n))
           (equal (fdet-rec a n)
	          (fdet a n)))
  :hints (("Goal" :use ((:instance fdet-rec-fdet-lemma (flg ()) (x a))))))


;;---------------------------------------------------------------------------------------------------------
;;    Classical Adjoint
;;---------------------------------------------------------------------------------------------------------

;; Given an nxn matrix a, we shall define its cofactor matrix (cofactor-fmat a n) to be the nxn
;; matrix with entries

;;    (entry i j (cofactor-fmat a n)) = (fdet-cofactor i j a n).

;; We begin by defining the ith row of the cofactor matrix:

(defun cofactor-fmat-row-aux (i j a n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp n) (> n 1) (natp j) (< j n))
      (cons (fdet-cofactor i j a n)
            (cofactor-fmat-row-aux i (1+ j) a n))
    ()))

(defund cofactor-fmat-row (i a n)
  (cofactor-fmat-row-aux i 0 a n))

(local-defthmd flistnp-cofactor-fmat-row-aux
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (<= j n))
           (flistnp (cofactor-fmat-row-aux i j a n)
	            (- n j))))

(defthm flistnp-cofactor-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (flistnp (cofactor-fmat-row i a n) n))
  :hints (("Goal" :in-theory (enable cofactor-fmat-row)
                  :use ((:instance flistnp-cofactor-fmat-row-aux (j 0))))))

(local-defun nth-cofactor-fmat-row-aux-induct (j k n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp n) (natp j) (< j n))
      (list (nth-cofactor-fmat-row-aux-induct (1+ j) (1- k) n))
    (list j k n)))

(local-defthmd nth-cofactor-fmat-row-aux
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (<= j n)
                (natp k) (< k (- n j)))
           (equal (nth k (cofactor-fmat-row-aux i j a n))
	          (fdet-cofactor i (+ j k) a n)))
  :hints (("Goal" :induct (nth-cofactor-fmat-row-aux-induct j k n))))

(defthmd nth-cofactor-fmat-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (nth j (cofactor-fmat-row i a n))
	          (fdet-cofactor i j a n)))
  :hints (("Goal" :in-theory (enable cofactor-fmat-row)
                  :use ((:instance nth-cofactor-fmat-row-aux (j 0) (k j))))))

;; The cofactor matrix may now be defined:

(defun cofactor-fmat-aux (i a n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp n) (natp i) (< i n))
      (cons (cofactor-fmat-row i a n)
            (cofactor-fmat-aux (1+ i) a n))
    ()))

(defund cofactor-fmat (a n)
  (cofactor-fmat-aux 0 a n))

(local-defthmd fmatp-cofactor-fmat-aux
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (<= i n))
           (fmatp (cofactor-fmat-aux i a n) (- n i) n)))

(defthm fmatp-cofactor-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (fmatp (cofactor-fmat a n) n n))
  :hints (("Goal" :in-theory (enable cofactor-fmat)
                  :use ((:instance fmatp-cofactor-fmat-aux (i 0))))))

(local-defthmd nth-cofactor-fmat-aux
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (<= i n) (natp k) (< k (- n i)))
           (equal (nth k (cofactor-fmat-aux i a n))
	          (cofactor-fmat-row (+ i k) a n)))
  :hints (("Goal" :induct (nth-cofactor-fmat-row-aux-induct i k n))))

(defthmd nth-cofactor-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (nth i (cofactor-fmat a n))
	          (cofactor-fmat-row i a n)))
  :hints (("Goal" :in-theory (enable cofactor-fmat)
                  :use ((:instance nth-cofactor-fmat-aux (i 0) (k i))))))

(defthmd cofactor-fmat-entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (cofactor-fmat a n))
	          (fdet-cofactor i j a n)))
  :hints (("Goal" :use (nth-cofactor-fmat nth-cofactor-fmat-row))))

;; The classsical adjoint of a is the transpose of its cofactor matrix:

(defund adjoint-fmat (a n)
  (transpose-mat (cofactor-fmat a n)))

(defthm fmatp-adjoint
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (fmatp (adjoint-fmat a n) n n))
  :hints (("Goal" :in-theory (enable adjoint-fmat)
                  :use (fmatp-cofactor-fmat
		        (:instance fmatp-transpose (a (cofactor-fmat a n)) (m n))))))

(defthmd adjoint-fmat-entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (adjoint-fmat a n))
	          (fdet-cofactor j i a n)))
  :hints (("Goal" :in-theory (enable adjoint-fmat)
                  :use ((:instance cofactor-fmat-entry (i j) (j i))
		        (:instance transpose-fmat-entry (a (cofactor-fmat a n)) (m n) (i j) (j i))))))

;; By cofactor-fmat-entry and fdet-cofactor-transpose,

;;    (entry i j (cofactor-fmat (transpose-mat a) n))
;;      = (fdet-cofactor i j (transpose-mat a) n)
;;      = (fdet-cofactor j i a n))
;;      = (entry j i (cofactor-fmat a n))
;;      = (entry i j (transpose-mat (cofactor-fmat a n)))
;;      = (entry i j (adjoint-fmat a n))

(defthmd cofactor-fmat--entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (cofactor-fmat (transpose-mat a) n))
                  (entry i j (adjoint-fmat a n))))
  :hints (("Goal" :use (adjoint-fmat-entry
                        (:instance fmatp-transpose (m n))
                        (:instance cofactor-fmat-entry (a (transpose-mat a)))
                        (:instance transpose-fmat-entry (m n) (i j) (j i))
			(:instance cofactor-fmat-entry (i j) (j i))))))

;; Therefore,

(defthmd cofactor-fmat-transpose
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (equal (cofactor-fmat (transpose-mat a) n)
	          (adjoint-fmat a n)))
  :hints (("Goal" :use ((:instance fmat-entry-diff-lemma (a (cofactor-fmat (transpose-mat a) n))
                                                         (b (adjoint-fmat a n))
							 (m n))
                        (:instance fmatp-transpose (m n))
			(:instance cofactor-fmat--entry
			             (i (car (entry-diff (cofactor-fmat (transpose-mat a) n) (adjoint-fmat a n))))
			             (j (cdr (entry-diff (cofactor-fmat (transpose-mat a) n) (adjoint-fmat a n)))))))))

;; Note that the the dot product of (row i a) and (cofactor-fmat-row i a n) is a rearrangemnt of
;; the sum (expand-fdet-row a i n):

(local-defund co-prod (i j a n)
  (f* (entry i j a)
      (fdet-cofactor i j a n)))

(local-defthm fp-coprod
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n) (natp i) (< i n))
           (fp (co-prod i j a n)))
  :hints (("Goal" :in-theory (e/d (co-prod) (fp-fdet-cofactor))
                  :use (fp-fdet-cofactor (:instance fp-entry (m n))))))

(local-defun nlistp (l n)
  (if (consp l)
      (and (natp (car l)) (< (car l) n)
           (nlistp (cdr l) n))
    t))

(local-defun co-prod-sum (i l a n)
  (if (consp l)
      (f+ (co-prod i (car l) a n)
          (co-prod-sum i (cdr l) a n))
    (f0)))

(local-defun nlist (n)
  (if (zp n)
      ()
    (cons (1- n) (nlist (1- n)))))

(local-defthm nlistp-nlist
  (implies (and (natp n) (natp m) (<= m n))
           (nlistp (nlist m) n)))

(local-defthmd expand-fdet-row-aux-rewrite
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (<= j n) (natp i) (< i n))
           (equal (expand-fdet-row-aux a i j n)
	          (co-prod-sum i (nlist j) a n)))
  :hints (("Subgoal *1/5" :in-theory (e/d (co-prod) (nth fmatp)))))

(local-defthmd expand-fdet-row-rewrite
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (expand-fdet-row a i n)
	          (co-prod-sum i (nlist n) a n)))
  :hints (("Goal" :in-theory (enable expand-fdet-row)
                  :use ((:instance expand-fdet-row-aux-rewrite (j n))))))



(local-defthmd cofactor-fmat-row-aux-replace-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (<= j n)
                (flistnp x n))
	   (equal (cofactor-fmat-row-aux i j (replace-row a i x) n)
                  (cofactor-fmat-row-aux i j a n)))
  :hints (("Subgoal *1/4" :in-theory (enable cofactor-replace-fmat-row))))

(defthm cofactor-fmat-row-replace-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n)
                (flistnp x n))
	   (equal (cofactor-fmat-row i (replace-row a i x) n)
                  (cofactor-fmat-row i a n)))
  :hints (("Goal" :in-theory (enable cofactor-fmat-row-aux-replace-row cofactor-fmat-row))))

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
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (<= j n) (natp i) (< i n))
           (equal (a-row i j a n) (nthcdr j (row i a))))
  :hints (("Goal" :in-theory (e/d (cdr-nthcdr) (fmatp)))
          ("Subgoal *1/4" :use ((:instance cons-nth-nthcdr (l (row i a)))))
	  ("Subgoal *1/5" :in-theory (disable FLISTNP-NTH MEMBER-FMATP-FLISTNP flistnp-row)
	                  :use ((:instance nthcdr-len (l (row i a)))
	                        (:instance flistnp-row (m n))))))

(local-defthmd fdot-cofactor-fmat-row-aux-rewrite
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp j) (< j n) (natp i) (< i n))
           (equal (fdot (a-row i j a n) (cofactor-fmat-row-aux i j a n))
	          (co-prod-sum i (nlistr j n) a n)))
  :hints (("Goal" :in-theory (enable co-prod))))

(local-defthmd fdot-cofactor-fmat-row-rewrite
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (fdot (row i a) (cofactor-fmat-row i a n))
	          (co-prod-sum i (nlistr 0 n) a n)))
  :hints (("Goal" :in-theory (enable cofactor-fmat-row)
                  :use ((:instance a-row-nthcdr (j 0))
		        (:instance fdot-cofactor-fmat-row-aux-rewrite (j 0))))))

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
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n)
                (dlistp l) (dlistp m) (nlistp l n) (nlistp m n) (permp l m))
	   (equal (co-prod-sum i l a n)
	          (co-prod-sum i m a n)))
  :hints (("Goal" :use ((:functional-instance fval-sum-permp
                          (fargp (lambda (x) (if (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
			                         (member x (nlist n)) (fargp x))))
			  (fval (lambda (x) (if (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
			                        (co-prod i x a n) (fval x))))
			  (farg-listp (lambda (x) (if (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
			                              (nlistp x n) (farg-listp x))))
			  (fval-sum (lambda (x) (if (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
			                            (co-prod-sum i x a n) (fval-sum x)))))))
	  ("Subgoal 2" :use (member-nlist))
	  ("Subgoal 1" :use ((:instance member-nlist (x (car l)))))))

(defthmd fdot-cofactor-fmat-row-expand-fdet-row
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (fdot (row i a) (cofactor-fmat-row i a n))
                  (expand-fdet-row a i n)))
  :hints (("Goal" :use (expand-fdet-row-rewrite fdot-cofactor-fmat-row-rewrite dlistp-nlist permp-nlist-nlistr
                        (:instance dlistp-nlistr (j 0))
                        (:instance co-prod-sum-permp (l (nlist n)) (m (nlistr 0 n)))))))

;; Combining this with expand-fdet-row-fdet, we have the following expression for the determinant:

(defthmd fdot-cofactor-fmat-row-fdet
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n))
           (equal (fdot (row i a) (cofactor-fmat-row i a n))
                  (fdet a n)))
  :hints (("Goal" :use (fdot-cofactor-fmat-row-expand-fdet-row
                        (:instance expand-fdet-row-fdet (k i))))))

;; Next we substitute (replace-row a i (row k a)) for a in fdot-cofactor-fmat-row-fdet, where k <> i.
;; Since this matrix has 2 identical rows, its determinant is (f0) by fdet-alternating, and we have

(defthmd fdot-cofactor-fmat-row-fdet-0
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp k) (< k n) (not (= k i)))
           (equal (fdot (row k a) (cofactor-fmat-row i a n))
                  (f0)))
  :hints (("Goal" :use ((:instance fdot-cofactor-fmat-row-fdet (a (replace-row a i (row k a))))
		        (:instance flistnp-row (m n) (i k))
			(:instance fdet-alternating (a (replace-row a i (row k a))) (j k))))))

;; Thus, we have the following for general k:

(defthmd fdot-cofactor-fmat-row-fdelta
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp k) (< k n))
           (equal (fdot (row k a) (cofactor-fmat-row i a n))
                  (f* (fdelta i k) (fdet a n))))
  :hints (("Goal" :use (fdot-cofactor-fmat-row-fdet fdot-cofactor-fmat-row-fdet-0))))

;; This yields an expression for the nxn matrix product of a and its adjoint:

(defthmd fmatp-fmat*-adjoint
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (fmatp (fmat* a (adjoint-fmat a n)) n n))
  :hints (("Goal" :use ((:instance fmatp-fmat* (b (adjoint-fmat a n)) (m n) (p n))))))

(defthmd fmat*-adjoint-entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (fmat* a (adjoint-fmat a n)))
	          (f* (fdelta i j) (fdet a n))))
  :hints (("Goal" :in-theory (enable adjoint-fmat)
                  :use (fmatp-adjoint
		        (:instance fmat*-entry (m n) (p n) (b (adjoint-fmat a n)))
                        (:instance col-transpose-fmat (m n) (a (cofactor-fmat a n)))
                        (:instance nth-cofactor-fmat (i j))
			(:instance fdot-cofactor-fmat-row-fdelta (k i) (i j))))))

(defthm fmatp-fmat-scalar-mul-fdet-id-mat
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (fmatp (fmat-scalar-mul (fdet a n) (id-fmat n)) n n))
  :hints (("Goal" :in-theory (enable fmatp-fmat-scalar-mul))))

(defthmd fmat-scalar-mul-fdet-id-mat-entry
  (implies (and (fmatp a n n) (natp n) (> n 1) (natp i) (< i n) (natp j) (< j n))
           (equal (entry i j (fmat-scalar-mul (fdet a n) (id-fmat n)))
	          (f* (fdelta i j) (fdet a n))))
  :hints (("Goal" :in-theory (enable entry-id-fmat)
                  :use ((:instance fmat-scalar-mul-entry (c (fdet a n)) (a (id-fmat n)) (m n))))))

(defthmd fmat*-adjoint-fmat
  (implies (and (fmatp a n n) (natp n) (> n 1))
           (equal (fmat* a (adjoint-fmat a n))
	          (fmat-scalar-mul (fdet a n) (id-fmat n))))
  :hints (("Goal" :use (fmatp-fmat*-adjoint fmatp-fmat-scalar-mul-fdet-id-mat
                        (:instance fmat-entry-diff-lemma (m n)
			                            (a (fmat* a (adjoint-fmat a n)))
						    (b (fmat-scalar-mul (fdet a n) (id-fmat n))))
                        (:instance fmat*-adjoint-entry
			             (i (car (entry-diff (fmat* a (adjoint-fmat a n))
				                         (fmat-scalar-mul (fdet a n) (id-fmat n)))))
			             (j (cdr (entry-diff (fmat* a (adjoint-fmat a n))
				                         (fmat-scalar-mul (fdet a n) (id-fmat n))))))
                        (:instance fmat-scalar-mul-fdet-id-mat-entry
			             (i (car (entry-diff (fmat* a (adjoint-fmat a n))
				                         (fmat-scalar-mul (fdet a n) (id-fmat n)))))
			             (j (cdr (entry-diff (fmat* a (adjoint-fmat a n))
				                         (fmat-scalar-mul (fdet a n) (id-fmat n))))))))))
