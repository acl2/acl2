(in-package "DM")

(include-book "transpositions")
(local (include-book "rtl/rel11/lib/top" :dir :system))

(in-theory (enable dlistp-perm))

;; Given naturals j <= k, compute the list of all pairs (i . k) with 0 <= i < j:

(defun pairs-aux (j k)
  (if (zp j)
      ()
    (cons (cons (1- j) k)
          (pairs-aux (1- j) k))))

(local-defthmd member-pairs-aux
  (implies (and (natp j)
                (natp k)
		(<= j k))
	   (iff (member-equal x (pairs-aux j k))
	        (and (consp x)
		     (natp (car x))
		     (< (car x) j)
		     (equal (cdr x) k)))))

(local-defthm dlistp-pairs-aux
  (implies (and (natp j)
                (natp k)
		(<= j k))
           (dlistp (pairs-aux j k)))	   
  :hints (("Subgoal *1/5" :use ((:instance member-pairs-aux (j (1- j)) (x (cons (1- j) k)))))))
	   
;; The list of all pairs (i . j) with 0 <= i < j < n:

(defund pairs (n)
  (if (zp n)
      ()
    (append (pairs-aux (1- n) (1- n))
            (pairs (1- n)))))
            

(defthmd member-pairs
  (implies (natp n)
           (iff (member-equal x (pairs n))
	        (and (consp x)
		     (natp (car x))
		     (natp (cdr x))
		     (< (car x) (cdr x))
		     (< (cdr x) n))))
  :hints (("Goal" :in-theory (enable pairs))
          ("Subgoal *1/2" :use ((:instance member-pairs-aux (j (1- n)) (k (1- n)))))))

(local-defthm disjointp-pairs-aux-pairs
  (implies (and (natp j) (natp k) (<= j k))
           (disjointp (pairs-aux j k) (pairs k)))
  :hints (("Goal" :in-theory (enable pairs))  
          ("Subgoal *1/5" :use ((:instance member-pairs (n k) (x (cons (1- j) k)))))))

(defthm dlistp-pairs
  (implies (natp n)
           (dlistp (pairs n)))
  :hints (("Goal" :in-theory (enable pairs))))

;; Given a permutation p, extract the list of pairs (i . j) with p(i) > p(j): 

(defun invs-aux (p pairs)
  (if (consp pairs)
      (if (> (nth (caar pairs) p) (nth (cdar pairs) p))
          (cons (car pairs) (invs-aux p (cdr pairs)))
	(invs-aux p (cdr pairs)))
    ()))

(local-defthm sublistp-invs-aux-pairs
  (sublistp (invs-aux p pairs) pairs))

(local-defthm member-invs-aux
  (implies (dlistp pairs)
           (iff (member-equal x (invs-aux p pairs))
                (and (member-equal x pairs)
                     (> (nth (car x) p) (nth (cdr x) p))))))

(local-defthm dlistp-invs-aux
  (implies (dlistp pairs)
           (dlistp (invs-aux p pairs))))

;; The list of inversions of p:

(defund invs (p n)
  (invs-aux p (pairs n)))

(defthm sublistp-invs-pairs
  (sublistp (invs p n) (pairs n))
  :hints (("Goal" :in-theory (enable invs))))

(defthmd member-invs
  (implies (natp n)
           (iff (member x (invs p n))
	        (and (consp x)
		     (natp (car x))
		     (natp (cdr x))
		     (< (car x) (cdr x))
		     (< (cdr x) n)
                     (> (nth (car x) p) (nth (cdr x) p)))))
  :hints (("Goal" :in-theory (enable invs member-invs-aux member-pairs))))

(defthm dlistp-invs
  (implies (natp n)
           (dlistp (invs p n)))
  :hints (("Goal" :in-theory (enable invs))))

;; The list of pairs whose ordering is preserved by p (complement of the list of inversions):

(defun pres-aux (p pairs)
  (if (consp pairs)
      (if (< (nth (caar pairs) p) (nth (cdar pairs) p))
          (cons (car pairs) (pres-aux p (cdr pairs)))
	(pres-aux p (cdr pairs)))
    ()))

(local-defthm sublistp-pres-aux-pairs
  (sublistp (pres-aux p pairs) pairs))

(local-defthm member-pres-aux
  (implies (dlistp pairs)
           (iff (member-equal x (pres-aux p pairs))
                (and (member-equal x pairs)
                     (< (nth (car x) p) (nth (cdr x) p))))))

(local-defthm dlistp-pres-aux
  (implies (dlistp pairs)
           (dlistp (pres-aux p pairs))))

(defund pres (p n)
  (pres-aux p (pairs n)))

(defthm sublistp-pres-pairs
  (sublistp (pres p n) (pairs n))
  :hints (("Goal" :in-theory (enable pres))))

(defthmd member-pres
  (implies (natp n)
           (iff (member x (pres p n))
	        (and (consp x)
		     (natp (car x))
		     (natp (cdr x))
		     (< (car x) (cdr x))
		     (< (cdr x) n)
                     (< (nth (car x) p) (nth (cdr x) p)))))
  :hints (("Goal" :in-theory (enable pres member-pres-aux member-pairs))))

(defthm dlistp-pres
  (implies (natp n)
           (dlistp (pres p n)))
  :hints (("Goal" :in-theory (enable pres))))

(local-defthm disjointp-invs-pres-1
  (implies (and (natp n)
                (sublistp l (invs p n)))
	   (disjointp l (pres p n)))
  :hints (("Goal" :in-theory (enable member-invs member-pres))))

(defthm disjointp-invs-pres
  (implies (natp n)
	   (disjointp (invs p n) (pres p n))))

(defthm disjointp-pres-invs
  (implies (natp n)
	   (disjointp (pres p n) (invs p n)))
  :hints (("Goal" :use ((:instance disjointp-symmetric (l (invs p n)) (m (pres p n)))))))

(local-defthm sublistp-pairs-invs-perms-1
  (implies (and (natp n)
                (in p (sym n))
		(sublistp l (pairs n)))
	   (sublistp l (append(invs p n) (pres p n))))
  :hints (("Goal" :in-theory (enable member-invs member-pres))
          ("Subgoal *1/3" :use ((:instance member-pairs (x (car l)))
	                        (:instance nth-perm-ninit (k (caar l)) (x p))
	                        (:instance nth-perm-ninit (k (cdar l)) (x p))
	                        (:instance nth-perm-distinct (i (caar l)) (j (cdar l)) (x p))))))

(defthm sublistp-pairs-invs-perms
  (implies (and (natp n)
                (in p (sym n)))
	   (sublistp (pairs n) (append(invs p n) (pres p n)))))

(local-defthm sublistp-pairs-perms-invs-1
  (implies (and (natp n)
                (in p (sym n))
		(sublistp l (pairs n)))
	   (sublistp l (append(pres p n) (invs p n))))
  :hints (("Goal" :in-theory (enable member-invs member-pres))
          ("Subgoal *1/3" :use ((:instance member-pairs (x (car l)))
	                        (:instance nth-perm-ninit (k (caar l)) (x p))
	                        (:instance nth-perm-ninit (k (cdar l)) (x p))
	                        (:instance nth-perm-distinct (i (caar l)) (j (cdar l)) (x p))))))

(defthm sublistp-pairs-perms-invs
  (implies (and (natp n)
                (in p (sym n)))
	   (sublistp (pairs n) (append(pres p n) (invs p n)))))

;; The parity of p:

(defund parity (p n)
  (mod (len (invs p n)) 2))

(defthmd parity-0-1
  (member (parity p n) '(0 1))
  :hints (("Goal" :in-theory (enable parity))))

(defund even-perm-p (p n)
  (equal (parity p n) 0))

(defund odd-perm-p (p n)
  (equal (parity p n) 1))

;; (ninit n) is an even permutation:

(local-defthm invs-aux-ninit
  (implies (sublistp l (pairs n))
           (equal (invs-aux (ninit n) l)
	          ()))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance member-pairs (x (car l)))
	                        (:instance nth-ninit (k (caar l)))
	                        (:instance nth-ninit (k (cdar l)))))))

(defthm invs-ninit
  (equal (invs (ninit n) n) ())
  :hints (("Goal" :in-theory (enable invs))))

(defthm evenp-ninit
  (even-perm-p (ninit n) n)
  :hints (("Goal" :in-theory (enable parity even-perm-p))))
  

;;---------------------------------------------------------------------------------------------------------------

;; A permutation and its inverse have the same parity:

(encapsulate ()

;; We define a bijection from (invs p n) to (invs (inv-perm p n) n), which implies that they have the same length:

(local-defund f1 (x p) (cons (nth (cdr x) p) (nth (car x) p)))

;; The inverse of f:

(local-defund g1 (x p) (cons (index (cdr x) p) (index (car x) p)))

;; We must prove the following 2 lemmas:

(local-defthmd g1-f1-id
  (implies (and (posp n) (in p (sym n)) (member-equal x (invs p n)))
           (and (member-equal (f1 x p) (invs (inv-perm p n) n))
	        (equal (g1 (f1 x p) p) x)))
  :hints (("Goal" :in-theory (enable len-perm f1 g1 member-invs)
                  :use ((:instance nth-perm-ninit (k (car x)) (x p))
                        (:instance nth-perm-ninit (k (cdr x)) (x p))))))

(local-defthmd f1-g1-id
  (implies (and (posp n) (in p (sym n)) (member-equal x (invs (inv-perm p n) n)))
           (and (member-equal (g1 x p) (invs p n))
	        (equal (f1 (g1 x p) p) x)))
  :hints (("Goal" :in-theory (enable len-perm f1 g1 member-perm member-invs)
                  :use ((:instance nth-perm-ninit (k (car x)) (x (inv-perm p n)))
                        (:instance nth-perm-ninit (k (cdr x)) (x (inv-perm p n)))
			(:instance nth-inv-perm (k (car x)) (x p))
			(:instance nth-inv-perm (k (cdr x)) (x p))))))

;; By functional instantiation of len-1-1-equal, we conclude the following:

(defthmd len-invs-inv
  (implies (and (posp n) (in p (sym n)))
           (equal (len (invs (inv-perm p n) n))
	          (len (invs p n))))
  :hints (("Goal" :use ((:functional-instance len-1-1-equal
                         (x (lambda () (if (and (posp n) (in p (sym n))) (invs p n) (x))))
                         (y (lambda () (if (and (posp n) (in p (sym n))) (invs (inv-perm p n) n) (y))))
			 (xy (lambda (x) (if (and (posp n) (in p (sym n))) (f1 x p) (xy x))))
			 (yx (lambda (x) (if (and (posp n) (in p (sym n))) (g1 x p) (yx x)))))))
	 ("Subgoal 1" :use ((:instance g1-f1-id (x a))))
	 ("Subgoal 2" :use ((:instance f1-g1-id (x a))))))
)

;; Thus, p and (inv-perm p n) have the same parity:

(defthmd parity-inv
  (implies (and (posp n) (in p (sym n)))
           (equal (parity (inv-perm p n) n)
	          (parity p n)))
  :hints (("Goal" :in-theory (enable parity len-invs-inv))))


;;---------------------------------------------------------------------------------------------------------------

;; We shall prove that parity is a homomorphism from (sym n) into Z/2Z:

;; (defthmd parity-comp-perm
;;   (implies (and (posp n)
;;                 (in p (sym n))
;; 	           (in r (sym n)))
;; 	   (equal (parity (comp-perm p r n) n)
;; 	          (mod (+ (parity p n) (parity r n)) 2))))

;; Our proof of parity-comp-perm is based on the following 3 sublists of (pairs (ninit n)):

(defund invs-pres (p r n)
  (intersection-equal (invs (inv-perm p n) n) (pres r n)))

(defund pres-invs (p r n)
  (intersection-equal (pres (inv-perm p n) n) (invs r n)))

(defund invs-invs (p r n)
  (intersection-equal (invs (inv-perm p n) n) (invs r n)))

(defthmd dinjointp-invs-pres-pres-invs
  (implies (and (posp n)
                (member-equal p (slist n))
                (member-equal r (slist n)))
           (disjointp (invs-pres p r n)
                      (pres-invs p r n)))
  :hints (("Goal" :in-theory (enable invs-pres pres-invs)
                  :use ((:instance sublistp-intersection (l (invs (inv-perm p n) n)) (m (pres r n)))
		        (:instance sublistp-intersection (l (pres (inv-perm p n) n)) (m (invs r n)))
			(:instance sublistp-sublistp-disjointp (l1 (invs-pres p r n)) (l2 (pres r n))
			                                       (m1 (pres-invs p r n)) (m2 (invs r n)))
			(:instance disjointp-symmetric (l (invs r n)) (m (pres r n)))))))

(defthmd dlistp-invs-pres-pres-invs
  (implies (and (posp n)
                (member-equal p (slist n))
                (member-equal r (slist n)))
           (and (dlistp (invs-pres p r n))
	        (dlistp (pres-invs p r n))))
  :hints (("Goal" :in-theory (enable invs-pres pres-invs)
                  :use ((:instance dlistp-intersection (l (invs (inv-perm p n) n)) (m (pres r n)))
                        (:instance dlistp-intersection (l (pres (inv-perm p n) n)) (m (invs r n)))
			(:instance dlistp-invs (p (inv-perm p n)))
			(:instance dlistp-pres (p (inv-perm p n)))))))

(defthmd dlistp-append-invs-pres-pres-invs
  (implies (and (posp n)
                (member-equal p (slist n))
                (member-equal r (slist n)))
           (dlistp (append (invs-pres p r n)
                           (pres-invs p r n))))
  :hints (("Goal" :in-theory (disable dlistp-intersection dlistp-invs dlistp-pres)
                  :use (dinjointp-invs-pres-pres-invs dlistp-invs-pres-pres-invs))))

(defthmd len-invs-r
  (implies (and (posp n) (in p (sym n)) (in r (sym n)))
           (equal (len (invs r n))
	          (+ (len (pres-invs p r n)) (len (invs-invs p r n)))))
  :hints (("Goal" :in-theory (enable invs-invs pres-invs)
                  :use ((:instance len-append-intersection-1 (l1 (pres (inv-perm p n) n))
                                                             (l2 (invs (inv-perm p n) n))
							     (m (invs r n)))
			(:instance sublistp-sublistp (l (invs r n))
			                             (m (pairs n))
						     (n (append (pres (inv-perm p n) n) (invs (inv-perm p n) n))))))))

(defthmd len-invs-p
  (implies (and (posp n) (in p (sym n)) (in r (sym n)))
           (equal (len (invs p n))
	          (+ (len (invs-pres p r n)) (len (invs-invs p r n)))))
  :hints (("Goal" :in-theory (enable invs-invs invs-pres)
                  :use (len-invs-inv
		        (:instance len-append-intersection-2 (m1 (pres r n))
                                                             (m2 (invs r n))
							     (l (invs (inv-perm p n) n)))
			(:instance sublistp-sublistp (l (invs (inv-perm p n) n))
			                             (m (pairs n))
						     (n (append (pres r n) (invs r n))))))))

(encapsulate ()

;; We define a bijection from
;;   (invs (comp-perm r p n) n)
;; to
;;   (append (invs-pres p r n) (pres-invs p r n)) 
;; which will allow us to conclude that the 2 lists have the same length:

(local-defun f1 (pair p)
  (if (< (nth (car pair) p) (nth (cdr pair) p))
      (cons (nth (car pair) p) (nth (cdr pair) p))
    (cons (nth (cdr pair) p) (nth (car pair) p))))

;; The inverse of f:

(local-defun g1 (pair p)
  (if (< (index (car pair) p) (index (cdr pair) p))
      (cons (index (car pair) p) (index (cdr pair) p))
    (cons (index (cdr pair) p) (index (car pair) p))))

(local-defthm g1-f1-1
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (invs (comp-perm r p n) n))
                (< (nth (car x) p) (nth (cdr x) p)))
	   (and (member-equal (f1 x p) (pres-invs p r n))
	        (equal (g1 (f1 x p) p) x)))
  :hints (("Goal" :in-theory (enable len-perm pres-invs)
                  :use ((:instance member-invs (p (comp-perm r p n)))
			(:instance member-invs (p r) (x (cons (nth (car x) p) (nth (cdr x) p))))
			(:instance member-pres (p (inv-perm p n)) (x (cons (nth (car x) p) (nth (cdr x) p))))
			(:instance nth-perm-ninit (k (car x)) (x p))
			(:instance nth-perm-ninit (k (cdr x)) (x p))
			(:instance nth-perm-ninit (k (nth (car x) p)) (x r))
			(:instance nth-perm-ninit (k (nth (cdr x) p)) (x r))))))

(local-defthm g1-f1-2
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (invs (comp-perm r p n) n))
                (> (nth (car x) p) (nth (cdr x) p)))
	   (and (member-equal (f1 x p) (invs-pres p r n))
	        (equal (g1 (f1 x p) p) x)))
  :hints (("Goal" :in-theory (enable len-perm invs-pres)
                  :use ((:instance member-invs (p (comp-perm r p n)))
			(:instance member-pres (p r) (x (cons (nth (cdr x) p) (nth (car x) p))))
			(:instance member-invs (p (inv-perm p n)) (x (cons (nth (cdr x) p) (nth (car x) p))))
			(:instance nth-perm-ninit (k (car x)) (x p))
			(:instance nth-perm-ninit (k (cdr x)) (x p))
			(:instance nth-perm-ninit (k (nth (car x) p)) (x r))
			(:instance nth-perm-ninit (k (nth (cdr x) p)) (x r))))))

(local-defthmd g1-f1-3
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (invs (comp-perm r p n) n)))
           (or (> (nth (car x) p) (nth (cdr x) p))
	       (< (nth (car x) p) (nth (cdr x) p))))
  :hints (("Goal" :in-theory (enable len-perm)
	          :use ((:instance member-invs (p (comp-perm r p n)))
                        (:instance nth-perm-distinct (i (car x)) (j (cdr x)) (x p))
			(:instance nth-perm-ninit (k (car x)) (x p))
			(:instance nth-perm-ninit (k (cdr x)) (x p))))))

(local-defthmd g1-f1-id
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (invs (comp-perm r p n) n)))
           (and (member-equal (f1 x p) (append (invs-pres p r n) (pres-invs p r n)))
	        (equal (g1 (f1 x p) p) x)))
  :hints (("Goal" :use (g1-f1-1 g1-f1-2 g1-f1-3))))

(local-defthmd f1-g1-1
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (invs-pres p r n)))
           (equal (f1 (g1 x p) p) x))
  :hints (("Goal" :in-theory (enable len-perm invs-pres)
                  :use ((:instance member-invs (p (inv-perm p n)))
			(:instance member-perm (k (car x)) (x p))
			(:instance member-perm (k (cdr x)) (x p))))))

(local-defthmd f1-g1-2
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (pres-invs p r n)))
           (equal (f1 (g1 x p) p) x))
  :hints (("Goal" :in-theory (enable len-perm pres-invs)
                  :use ((:instance member-pres (p (inv-perm p n)))
			(:instance member-perm (k (car x)) (x p))
			(:instance member-perm (k (cdr x)) (x p))))))

(local-defthmd f1-g1-3
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (invs-pres p r n)))
           (and (equal (g1 x p) (cons (index (cdr x) p) (index (car x) p)))
	        (natp (index (cdr x) p)) (natp (index (car x) p))
	        (< (index (cdr x) p) n) (< (index (car x) p) n)
		(< (index (cdr x) p) (index (car x) p))
		(> (nth (index (cdr x) p) (comp-perm r p n)) (nth (index (car x) p) (comp-perm r p n)))))
  :hints (("Goal" :in-theory (e/d (len-perm invs-pres) (ind<len))
                  :use ((:instance member-invs (p (inv-perm p n)))
		        (:instance member-pres (p r))
			(:instance ind<len (x (car x)) (l p))
			(:instance ind<len (x (cdr x)) (l p))
			(:instance member-perm (k (car x)) (x p))
			(:instance member-perm (k (cdr x)) (x p))))))

(local-defthmd f1-g1-4
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (invs-pres p r n)))
           (member (g1 x p) (invs (comp-perm r p n) n)))
  :hints (("Goal" :in-theory (e/d (len-perm invs-pres) (ind<len))
                  :use (f1-g1-3
			(:instance member-invs (p (comp-perm r p n)) (x (cons (index (cdr x) p) (index (car x) p))))))))

(local-defthmd f1-g1-5
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (pres-invs p r n)))
           (and (equal (g1 x p) (cons (index (car x) p) (index (cdr x) p)))
	        (natp (index (cdr x) p)) (natp (index (car x) p))
	        (< (index (cdr x) p) n) (< (index (car x) p) n)
		(< (index (car x) p) (index (cdr x) p))
		(> (nth (index (car x) p) (comp-perm r p n)) (nth (index (cdr x) p) (comp-perm r p n)))))
  :hints (("Goal" :in-theory (e/d (len-perm pres-invs) (ind<len))
                  :use ((:instance member-pres (p (inv-perm p n)))
		        (:instance member-invs (p r))
			(:instance ind<len (x (car x)) (l p))
			(:instance ind<len (x (cdr x)) (l p))
			(:instance member-perm (k (car x)) (x p))
			(:instance member-perm (k (cdr x)) (x p))))))

(local-defthmd f1-g1-6
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (pres-invs p r n)))
           (member (g1 x p) (invs (comp-perm r p n) n)))
  :hints (("Goal" :in-theory (e/d (len-perm invs-pres) (ind<len))
                  :use (f1-g1-5
			(:instance member-invs (p (comp-perm r p n)) (x (cons (index (car x) p) (index (cdr x) p))))))))

(local-defthmd f1-g1-id
  (implies (and (posp n) (in p (sym n)) (in r (sym n)) (member-equal x (append (invs-pres p r n) (pres-invs p r n))))
           (and (member-equal (g1 x p) (invs (comp-perm r p n) n))
	        (equal (f1 (g1 x p) p) x)))
  :hints (("Goal" :use (f1-g1-1 f1-g1-2 f1-g1-4 f1-g1-6))))

(local-in-theory (disable f1 g1))

(defthmd len-invs-comp-perm-append
  (implies (and (posp n) (in p (sym n)) (in r (sym n)))
           (equal (len (append (invs-pres p r n) (pres-invs p r n)))
	          (len (invs (comp-perm r p n) n))))
  :hints (("Goal" :use ((:functional-instance len-1-1-equal
                         (x (lambda () (if (and (posp n) (in p (sym n)) (in r (sym n))) (invs (comp-perm r p n) n) (x))))
                         (y (lambda () (if (and (posp n) (in p (sym n)) (in r (sym n))) (append (invs-pres p r n) (pres-invs p r n)) (y))))
			 (xy (lambda (x) (if (and (posp n) (in p (sym n)) (in r (sym n))) (f1 x p) (xy x))))
			 (yx (lambda (x) (if (and (posp n) (in p (sym n)) (in r (sym n))) (g1 x p) (yx x)))))))
	 ("Subgoal 1" :use (dlistp-append-invs-pres-pres-invs))
	 ("Subgoal 2" :use ((:instance g1-f1-id (x a))))
	 ("Subgoal 3" :use ((:instance f1-g1-id (x a))))))
)
                         
(defthmd len-invs-comp-perm
  (implies (and (posp n) (in p (sym n)) (in r (sym n)))
           (equal (len (invs (comp-perm r p n) n))
	          (+ (len (invs-pres p r n)) (len (pres-invs p r n)))))
  :hints (("Goal" :use (len-invs-comp-perm-append))))

;; Combine len-invs-comp-perm, len-invs-r. and len-invs-p:

(local-defthmd len-invs-sum
  (implies (and (posp n) (in p (sym n)) (in r (sym n)))
           (equal (+ (len (invs r n)) (len (invs p n)))
	          (+ (len (invs (comp-perm r p n) n))
		     (* 2 (len (invs-invs p r n))))))
  :hints (("Goal" :use (len-invs-comp-perm len-invs-r len-invs-p))))

;; The main result follows:

(defthmd parity-comp-perm
  (implies (and (posp n)
                (in p (sym n))
	        (in r (sym n)))
	   (equal (parity (comp-perm r p n) n)
	          (mod (+ (parity p n) (parity r n)) 2)))
  :hints (("Goal" :in-theory (enable parity)
                  :use (len-invs-sum
		        (:instance rtl::mod-mult (m (len (invs (comp-perm r p n) n))) (a (len (invs-invs p r n))) (n 2))))))


;;-----------------------------------------------------------------------------------------------------------------------------------

;; All transpositions are odd.  First we show that a transposition of adjacent elements performs a single
;; inversion and therefore has odd parity:

(local-defthmd transpose-adjacent-invs-aux
  (implies (and (sublistp l (pairs n))
                (dlistp l)
		(trans-args-p i (1+ i) n))
	   (equal (invs-aux (transpose i (1+ i) n) l)
	          (if (member-equal (cons i (1+ i)) l)
		      (list (cons i (1+ i)))
		    ())))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable transpose-vals)
                          :use ((:instance member-pairs (x (car l)))))))
			  
(local-defthmd transpose-adjacent-invs
  (implies (trans-args-p i (1+ i) n)
           (equal (invs (transpose i (1+ i) n) n)
	          (list (cons i (1+ i)))))
  :hints (("Goal" :in-theory (enable invs)
                  :use ((:instance member-pairs (x (cons i (1+ i))))
		        (:instance transpose-adjacent-invs-aux (l (pairs n)))))))

(defthmd transpose-adjacent-odd
  (implies (trans-args-p i (1+ i) n)
           (equal (parity (transpose i (1+ i) n) n)
	          1))
  :hints (("Goal" :in-theory (enable parity)
                  :use (transpose-adjacent-invs))))

;; Every transposition is a conjugate of an adjacent transposition:

(defthmd transpose-conjugate
  (implies (and (trans-args-p i j n) (< (1+ i) j))
           (equal (transpose i j n)
	          (comp-perm (transpose (1+ i) j n)
		             (comp-perm (transpose i (1+ i) n)
			                (transpose (1+ i) j n)
					n)
			     n)))
  :hints (("Goal" :in-theory (enable transpose-vals)
                  :use (permp-transpose
		        (:instance nth-diff-perm (x (comp-perm (transpose (1+ i) j n)
		                                               (comp-perm (transpose i (1+ i) n)
			                                                  (transpose (1+ i) j n)
									  n)
							       n))
						 (y (transpose i j n)))						 
			(:instance permp-transpose (i (1+ i)))
			(:instance permp-transpose (j (1+ i)))))))

(local-defthmd transpose-non-adjacent-odd
  (implies (and (trans-args-p i j n) (< (1+ i) j))
           (equal (parity (transpose i j n) n) 1))
  :hints (("Goal" :in-theory (enable parity-comp-perm)
                  :use (transpose-conjugate transpose-adjacent-odd permp-transpose 
		        (:instance permp-transpose (i (1+ i)))
		        (:instance permp-transpose (j (1+ i)))
                        (:instance parity-0-1 (p (transpose i (1+ i) n)))
			(:instance parity-0-1 (p (transpose (1+ i) j n)))
			(:instance parity-0-1 (p (transpose i j n)))))))

(local-defthmd transpose-odd-i<j
  (implies (and (trans-args-p i j n) (< i j))
           (odd-perm-p (transpose i j n) n))
  :hints (("Goal" :in-theory (enable odd-perm-p)
                  :use (transpose-non-adjacent-odd transpose-adjacent-odd))))

(defthmd transpose-odd
  (implies (trans-args-p i j n)
           (odd-perm-p (transpose i j n) n))
  :hints (("Goal" :use (transpose-odd-i<j transpose-transpose
                        (:instance transpose-odd-i<j (i j) (j i))))))

(defthmd transp-odd
  (implies (transp p n)
           (odd-perm-p p n))
  :hints (("Goal" :in-theory (enable transp)
                  :use ((:instance transpose-odd (i (least-moved p)) (j (nth (least-moved p) p)))))))
			

;; It follows that the parity of a product of a list of transpositions is that of the length of the list:

(defthmd parity-trans-list
  (implies (and (posp n) (trans-list-p l n))
           (equal (parity (comp-perm-list l n) n)
	          (mod (len l) 2)))
  :hints (("Subgoal *1/3" :in-theory (enable parity even-perm-p) :use (evenp-ninit))  
          ("Subgoal *1/1" :in-theory (enable odd-perm-p)
	                  :use ((:instance parity-comp-perm (r (car l)) (p (comp-perm-list (cdr l) n)))
	                        (:instance transp-odd (p (car l)))
	                        (:instance permp-transp (p (car l)))
	                        (:instance permp-trans-list (l (cdr l)))))))

;; In particular,

(defthmd parity-len-trans-list
  (implies (and (posp n) (in p (sym n)))
           (equal (parity p n)
	          (mod (len (trans-list p n)) 2)))
  :hints (("Goal" :use (trans-list-p-trans-list perm-prod-trans
                        (:instance parity-trans-list (l (trans-list p n)))))))

;;---------------------------------------------------------------------------------------------------------------

;; This is just an aside, but some day I hope to formalize basic linear algebra.

;; An mxn matrix is a list of m rows (of rationals, I suppose) of length n.
;; The entry in row i and column j:

(defun entry (i j mat)
  (nth j (nth i mat)))

;; The term contributed by a permutation p to the determinant of an nxn matrix:

(defun det-term-aux (mat p l)
  (if (consp l)
      (* (entry (car l) (nth (car l) p) mat)
	 (det-term-aux mat p (cdr l)))
    1))

(defun det-term (mat p n)
  (* (expt -1 (parity p n))
     (det-term-aux mat p (ninit n))))

;; The determinant of an nxn matrix:

(defun det-aux (mat l n)
  (if (consp l)
      (+ (det-term mat (car l) n)
	 (det-aux mat (cdr l) n))
    0))

(defun det (mat n)
  (det-aux mat (slist n) n))

;;---------------------------------------------------------------------------------------------------------------

;; The alternating group is the subgroup of the symmetric group comprising the even permutations:

(defun even-perms-aux (l n)
  (if (consp l)
      (if (even-perm-p (car l) n)
          (cons (car l) (even-perms-aux (cdr l) n))
	(even-perms-aux (cdr l) n))
    ()))

(defund even-perms (n)
  (even-perms-aux (slist n) n))

(local-defthm even-perms-aux-even
  (iff (member-equal p (even-perms-aux l n))
       (and (member-equal p l) (even-perm-p p n))))

(defthmd even-perms-even
  (implies (posp n) 
           (iff (member-equal p (even-perms n))
	        (and (in p (sym n)) (even-perm-p p n))))
  :hints (("Goal" :in-theory (enable even-perms))))

(local-defthm sublistp-even-perms-aux
  (sublistp (even-perms-aux l n) l))

(local-defthm dlistp-even-perms-aux
  (implies (dlistp l)
           (dlistp (even-perms-aux l n))))

(defthm sublistp-even-perms-slist
  (implies (posp n)
           (sublistp (even-perms n) (slist n)))
  :hints (("Goal" :in-theory (enable even-perms))))

(defthm dlistp-even-perms
  (implies (posp n)
           (dlistp (even-perms n)))
  :hints (("Goal" :in-theory (enable even-perms))))

(defthm car-even-perms
  (implies (posp n)
           (equal (car (even-perms n))
	          (ninit n)))
  :hints (("Goal" :in-theory (enable even-perms)
                  :expand ((even-perms-aux (slist n) n)))))

(defthm consp-even-perms
  (implies (posp n)
           (consp (even-perms n)))
  :hints (("Goal" :use (car-even-perms))))

(defthm comp-perm-even
  (implies (and (posp n)
                (in p (sym n))
	        (in r (sym n))
		(even-perm-p p n)
		(even-perm-p r n))
	   (even-perm-p (comp-perm r p n) n))
  :hints (("Goal" :in-theory (enable parity-comp-perm even-perm-p))))

(defthm even-perms-closed
  (implies (and (posp n)
                (member-equal x (even-perms n))
                (member-equal y (even-perms n)))
           (member-equal (comp-perm x y n) (even-perms n)))
  :hints (("Goal" :in-theory (enable even-perms-even))))

(defthm inv-perm-even
  (implies (and (posp n)
                (in p (sym n)))
	   (iff (even-perm-p (inv-perm p n) n)
		(even-perm-p p n)))
  :hints (("Goal" :in-theory (enable even-perm-p parity-inv))))

(defthm even-perms-inverse
  (implies (and (posp n)
                (member-equal x (even-perms n)))
	   (member-equal (inv-perm x n) (even-perms n)))
  :hints (("Goal" :in-theory (enable even-perms-even))))

(defsubgroup alt (n) (sym n)
  (posp n)
  (even-perms n))

;; It follows from parity-inv and parity-comp-perm that parity is preserved by conjugation,
;; and therefore (alt n) is a normal subgroup of (sym n):

(defthmd parity-conjugate
  (implies (and (posp n)
                (in p (sym n))
	        (in a (sym n)))
	   (equal (parity (conj p a (sym n)) n)
		  (parity p n)))
  :hints (("Goal" :in-theory (enable conj parity-inv parity-comp-perm)
	   :use (parity-0-1 (:instance parity-0-1 (p a))))))

(defthmd alt-normal
  (implies (posp n)
           (normalp (alt n) (sym n)))
  :hints (("Goal" :in-theory (enable even-perm-p)
                  :use ((:instance not-normalp-cex (h (alt n)) (g (sym n)))
		        (:instance conj-in-g (g (sym n))
			                     (x (car (normalp-cex (alt n) (sym n))))
			                     (a (cadr (normalp-cex (alt n) (sym n)))))
		        (:instance parity-conjugate (p (car (normalp-cex (alt n) (sym n))))
			                            (a (cadr (normalp-cex (alt n) (sym n)))))
                        (:instance even-perms-even (p (car (normalp-cex (alt n) (sym n)))))
                        (:instance even-perms-even (p (conj (car (normalp-cex (alt n) (sym n)))
			                                    (cadr (normalp-cex (alt n) (sym n)))
						            (sym n))))))))

;; If n > 1, then (sym n) has at least one odd element, e.g., (transpose 0 1 n), and therefore (alt n) is a proper subgroup.
;; Since every element of (sym n) is either odd or even, it follows from parity-comp-perm and parity-inv that for every p
;; in (sym n), either p or (comp-perm (inv-perm (transpose 0 1 n) n) p n) is in (alt n), and by member-lcoset-iff, p is in
;; either (lcoset (ninit) (alt n) (sym n)) or (lcoset (transpose 0 1 n) (alt n) (sym n)).  Therefore, these are the only
;; elements of (lcosets (alt n) (sym n)):

(local-defthmd members-lcosets-alt
  (implies (and (natp n)
		(> n 1))
	   (and (member-equal (lcoset (ninit n) (alt n) (sym n)) (lcosets (alt n) (sym n)))
		(member-equal (lcoset (transpose 0 1 n) (alt n) (sym n)) (lcosets (alt n) (sym n)))
		(not (equal (lcoset (ninit n) (alt n) (sym n))
			    (lcoset (transpose 0 1 n) (alt n) (sym n))))))
  :hints (("Goal" :in-theory (enable e even-perm-p odd-perm-p)
                  :use (evenp-ninit
		        (:instance inv-e (g (sym n)))
                        (:instance permp-transpose (i 0) (j 1))
                        (:instance transpose-odd (i 0) (j 1))
			(:instance member-lcoset-iff (x (ninit n)) (y (transpose 0 1 n)) (h (alt n)) (g (sym n)))
			(:instance even-perms-even (p (transpose 0 1 n)))))))

(local-defthmd only-members-lcosets-alt
  (implies (and (natp n)
		(> n 1)
		(member-equal c (lcosets (alt n) (sym n))))
	   (or (equal c (lcoset (ninit n) (alt n) (sym n)))
	       (equal c (lcoset (transpose 0 1 n) (alt n) (sym n)))))
  :hints (("Goal" :in-theory (enable e even-perm-p odd-perm-p)
                  :use (evenp-ninit
		        (:instance inv-e (g (sym n)))
                        (:instance permp-transpose (i 0) (j 1))
                        (:instance transpose-odd (i 0) (j 1))
			(:instance member-lcoset-iff (x (ninit n)) (y (transpose 0 1 n)) (h (alt n)) (g (sym n)))
			(:instance even-perms-even (p (transpose 0 1 n)))
			(:instance lcosets-cars (h (alt n)) (g (sym n)))
			(:instance equal-lcoset (h (alt n)) (g (sym n)) (y (car c)) (x (ninit n)))
			(:instance equal-lcoset (h (alt n)) (g (sym n)) (y (car c)) (x (transpose 0 1 n)))
			(:instance member-lcoset-iff (h (alt n)) (g (sym n)) (y (car c)) (x (ninit n)))
			(:instance member-lcoset-iff (h (alt n)) (g (sym n)) (y (car c)) (x (transpose 0 1 n)))
			(:instance even-perms-even (p (car c)))
			(:instance even-perms-even (p (comp-perm (inv-perm (transpose 0 1 n) n) (car c) n)))
			(:instance parity-inv (p (transpose 0 1 n)))
			(:instance parity-0-1 (p (car c)))
			(:instance parity-comp-perm (r (inv-perm (transpose 0 1 n) n)) (p (car c)))))))

(local-defun third-member (a b l)
  (if (or (equal (car l) a) (equal (car l) b))
      (if (or (equal (cadr l) a) (equal (cadr l) b))
          (caddr l)
	(cadr l))
    (car l)))

(local-defthmd third-member-exists
  (implies (and (dlistp l)
                (member-equal a l)
		(member-equal b l)
		(not (equal a b))
		(not (equal (len l) 2)))
	   (let ((m (third-member a b l)))
	     (and (member m l)
	          (not (equal m a))
		  (not (equal m b))))))

(defthmd subgroup-index-alt
  (implies (and (natp n) (> n 1))
           (equal (subgroup-index (alt n) (sym n))
	          2))
  :hints (("Goal" :in-theory '(posp natp subgroup-index)
                  :use (members-lcosets-alt subgroupp-alt
		        (:instance dlistp-lcosets (h (alt n)) (g (sym n)))
                        (:instance only-members-lcosets-alt (c (third-member (lcoset (ninit n) (alt n) (sym n))
			                                                     (lcoset (transpose 0 1 n) (alt n) (sym n))
									     (lcosets (alt n) (sym n)))))
		        (:instance third-member-exists (a (lcoset (ninit n) (alt n) (sym n)))
			                               (b (lcoset (transpose 0 1 n) (alt n) (sym n)))
						       (l (lcosets (alt n) (sym n))))))))

;; The order of (alt n) follows from Lagrange's Theorem:

(defthmd order-alt
  (implies (and (natp n) (> n 1))
           (equal (order (alt n))
	          (/ (fact n) 2)))
  :hints (("Goal" :use (subgroup-index-alt
                        (:instance lagrange (h (alt n)) (g (sym n)))))))

(in-theory (disable dlistp-perm))
