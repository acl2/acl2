(in-package "DM")

(include-book "projects/groups/symmetric" :dir :system)
(include-book "sylvester")
(local (include-book "support/derangements"))

;; Let n >= 1.  A permutation p in (slist n) fixes k, where 0 <= k < n, if
;; (nth k p) = k.  p is a derangement if p does not fix any member of (ninit n):

(defund fixes (p k)
  (equal (nth k p) k))

(defun derangementp (p n)
  (if (posp n)
      (and (not (fixes p (1- n)))
	   (derangementp p (1- n)))
    t))

;; The list of all derangements:

(defun derangements-aux (u n)
  (if (consp u)
      (if (derangementp (car u) n)
	  (cons (car u) (derangements-aux (cdr u) n))
	(derangements-aux (cdr u) n))
    ()))

(defund derangements (n)
  (derangements-aux (slist n) n))

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

(defthm subset-fixer
  (member-equal (fixer k n) (subsets (slist n))))

;; The list l of inclusion-exclusion-principle is the list of all such fixers:

(defun fixers-aux (k n)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (natp k) (natp n) (< k n))
      (cons (fixer k n)
	    (fixers-aux (1+ k) n))
    ()))

(defund fixers (n)
  (fixers-aux 0 n))

;; (fixers n) is a list of n subsets of (slist n):

(defthm sublistp-fixers
  (implies (posp n)
	   (sublistp (fixers n) (subsets (slist n)))))

(defthm len-fixers
  (implies (natp n)
	   (equal (len (fixers n))
		  n)))

;; To apply inclusion-exclusion-principle, we must show that (fixers n) is a dlist.
;; Let 0 <= j < k < n.  There exists an index i = (other-index j k) that is distinct
;; from both j and k (here we require the assumption that n >= 3):

(defun other-index (j k)
  (if (or (= j 0) (= k 0))
      (if (or (= j 1) (= k 1))
	  2
	1)
    0))

;; Consider the transposition of i and j:

(defund fixer-mover (j k n)
  (transpose j (other-index j k) n))

;; This transposition fixes k but not j, and therefore (fixer j n) and (fixer k n)
;; are distinct.  It follows that (fixers n) is a dlist:

(defthm dlistp-fixers
  (implies (and (posp n) (>= n 3))
	   (dlistp (fixers n))))

;; Thus, inclusion-exclusion-principle will provide the length of (union-list (fixers n)).
;; Note that a permutation p in (slist n) is a member of (union-list (fixers n)) iff p fixes
;; some member of (ninit n), which is true iff p is not a member of (derangements n).  It
;; follows that (append (derangements n) (union-list (fixers n))) is a permutation of (slist n),
;; and we have the following expression for the length of (derangements n):

(defthmd len-derangements
  (implies (posp n)
           (equal (len (derangements n))
	          (- (fact n) (len (union-list (fixers n)))))))

;; inclusion-exclusion-principle expresses the length of (union-list (fixers n)) in terms of the
;; lengths of the intersections of subsets of (fixers n).  Let s be a subset of (fixers n) of 
;; order k > 0.  We shall prove that (len (int-list s)) = (n - k)!.

;; First we define the list of indices of the members of s in the list (fixers n):

(defun fixed-indices (s n)
  (if (consp s)
      (cons (index (car s) (fixers n))
	    (fixed-indices (cdr s) n))
    ()))

(defthm len-fixed-indices
  (equal (len (fixed-indices s n))
         (len s)))

;; This list is a sublist of (ninit n) and a dlist:

(defthm sublistp-fixed-indices
  (implies (and (posp n) (>= n 3) (member-equal s (subsets (fixers n))))
	   (sublistp (fixed-indices s n) (ninit n))))

(defthm dlistp-fixed-indices
  (implies (and (posp n) (>= n 3) (member-equal s (subsets (fixers n))))
	   (dlistp (fixed-indices s n))))

;; A permutation p in (slist n) belongs to (int-list s) iff p fixes every member of
;; (fixed-indices s n):

(defun fixes-list (p l)
  (if (consp l)
      (and (fixes p (car l))
           (fixes-list p (cdr l)))
    t))

(defthmd member-int-list-subset-fixers
  (implies (and (posp n) (>= n 3) (consp s) (member-equal s (subsets (fixers n))))
	   (iff (member-equal p (int-list s))
		(and (member-equal p (slist n))
	             (fixes-list p (fixed-indices s n))))))

;; The complement of (fixed-indices s n):

(defund moved-indices (s n)
  (set-difference-equal (ninit n) (fixed-indices s n)))

;; (moved-indices s n) is a sublist of (ninit n) and a dlist:

(defthm sublistp-moved-indices
  (sublistp (moved-indices s n) (ninit n)))

(defthm dlistp-moved-indices
  (implies (posp n)
           (dlistp (moved-indices s n))))

(defthmd len-moved-indices
  (implies (and (posp n) (>= n 3) (member-equal s (subsets (fixers n))))
           (equal (len (moved-indices s n))
	          (- n (len (fixed-indices s n))))))

;; Let m = (moved-indices s n).  We define a bijection from (int-list s) to (perms m).  If p
;; is a member of (int-list s), then the image of p under this bijection is the restriction of
;; p to m:

(defun restrict-perm (p m)
  (if (consp m)
      (cons (nth (car m) p)
	    (restrict-perm p (cdr m)))
    ()))

;; The inverse bijection maps a member p of (perms m) to the extension of p that fixes the
;; members of (fixed-indices s n):

(defun extend-perm (p m n)
  (if (posp n)
      (append (extend-perm p m (1- n))
              (list (if (member-equal (1- n) m)
	                (nth (index (1- n) m) p)
	              (1- n))))
    ()))

;; The following 2 results establish the bijection:

(defthm extend-restrict-perms
  (let ((m (moved-indices s n)))
    (implies (and (posp n) (>= n 3)
                  (consp s)
                  (member-equal s (subsets (fixers n)))
		  (member-equal p (int-list s)))
	     (and (member-equal (restrict-perm p m) (perms m))
		  (equal (extend-perm (restrict-perm p m) m n)
		         p)))))

(defthm restrict-extend-perms
  (let ((m (moved-indices s n)))
    (implies (and (posp n) (>= n 3)
                  (consp s)
                  (member-equal s (subsets (fixers n)))
		  (member-equal p (perms m)))
	    (and (member-equal (extend-perm p m n) (int-list s))
		 (equal (restrict-perm (extend-perm p m n) m)
		        p)))))

;; By functional instantiation of len-1-1-equal, (int-list s) and (perms (moved-indices s n))
;; have the same length:

(defthmd len-int-list-perms
  (implies (and (posp n) (>= n 3)
                (consp s) (member-equal s (subsets (fixers n))))
	   (equal (len (int-list s))
	          (len (perms (moved-indices s n))))))

;; Combine len-int-list-perms with len-perms, len-moved-indices, and len-fixed-indices:

(defthmd len-int-list-subset-fixers
  (implies (and (posp n) (>= n 3)
                (consp s) (member-equal s (subsets (fixers n))))
	   (equal (len (int-list s))
	          (fact (- n (len s))))))

;; Let 0 < k <= n.  If s is a subset of (fixers n) of order k, then (len (int-list s)) = (n - k)!.
;; Since (len (fixers n)) = n, the number of such subsets is (choose n k) = n!/(k!(n - k)!).  Thus,
;; (sum-len-int (subsets-of-order k (fixers n)) is the product (n - k)!n!/(k!(n - k)!) = n!/k!:

(defthm sum-len-int-subsets-of-order
  (implies (and (posp n) (>= n 3)
		(posp k) (<= k n))
	   (equal (sum-len-int (subsets-of-order k (fixers n)))
	          (/ (fact n) (fact k)))))

;; Applying this to the definition of inc-exc-aux yields the following:

(defthmd num-derangements-inc-exc-aux
  (implies (and (posp n) (>= n 3)
		(posp k) (<= k n))
	   (equal (* (fact n) (num-derangements-aux k n))
	          (inc-exc-aux (fixers n) k))))

;; Instantiate with k = 1:

(defthmd num-derangements-inc-exc
  (implies (and (posp n) (>= n 3))
	   (equal (num-derangements n)
	          (- (fact n) (len (union-list (fixers n)))))))

;; Finally, combine this with len-derangements:

(defthm derangements-formula
  (implies (posp n)
           (equal (len (derangements n))
                  (num-derangements n))))
