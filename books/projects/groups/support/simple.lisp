(in-package "DM")

(include-book "alt5")
(include-book "products")
(include-book "sylow")

;;---------------------------------------------------------------------------------------------------
;; Groups of Order Less Than 60
;;---------------------------------------------------------------------------------------------------

(local-defthmd union-subgroups-1
  (implies (and (dlistp l) (dlistp m))
	   (dlistp (union-equal l m))))

(local-defthmd union-subgroups-2
  (implies (and (dlistp l)
                (dlistp m)
                (not (sublistp l m)))
	   (> (len (union-equal l m))
	      (len m))))

(local-defthmd union-subgroups-3
  (implies (member-equal x (union-equal l m))
           (or (member-equal x l)
	       (member-equal x m))))

(local-defthmd union-subgroups
  (implies (and (subgroupp h1 g)
                (subgroupp h2 g)
		(equal (order h1) n)
		(equal (order h2) n)
		(not (sublistp (elts h1) (elts h2))))
	   (let ((l (union-equal (elts h1) (elts h2))))
	     (and (dlistp l)
	          (> (len l) (order h2))
		  (implies (member-equal x l)
		           (divides (ord x g) n)))))
  :hints (("Goal" :use ((:instance union-subgroups-1 (l (elts h1)) (m (elts h2)))
                        (:instance union-subgroups-2 (l (elts h1)) (m (elts h2)))
			(:instance union-subgroups-3 (l (elts h1)) (m (elts h2)))
                        (:instance ord-divides-order (g h1))
			(:instance ord-divides-order (g h2))))))

(local-defthmd sublistp-union
  (implies (and (sublistp l1 m) (sublistp l2 m))
           (sublistp (union-equal l1 l2) m)))

(local-defthm conjs-sub-not-sublist
  (implies (and (subgroupp h g)
		(member-equal k1 (conjs-sub h g))
		(member-equal k2 (conjs-sub h g))
		(sublistp (elts k1) (elts k2)))
	   (equal k2 k1))
  :rule-classes ()
  :hints (("Goal" :use (conjs-sub-not-subgroup
                        (:instance subgroup-subgroup (h k1) (k k2))))))

(defthmd union-conjs
  (let ((h1 (car (conjs-sub h g)))
        (h2 (cadr (conjs-sub h g))))
    (implies (and (subgroupp h g)
                  (> (len (conjs-sub h g)) 1))
	     (let ((l (union-equal (elts h1) (elts h2))))
	       (and (sublistp l (elts g))
	            (dlistp l)
	            (> (len l) (order h))
		    (implies (member-equal x l)
		             (divides (ord x g) (order h)))))))
  :hints (("Goal" :in-theory (disable subgroupp-conjs-sub dlistp-conjs-sub)
                  :use (dlistp-conjs-sub
                        (:instance union-subgroups (n (order h))
			                           (h1 (car (conjs-sub h g)))
                                                   (h2 (cadr (conjs-sub h g))))
                        (:instance conjs-sub-not-sublist (k1 (car (conjs-sub h g)))
			                                 (k2 (cadr (conjs-sub h g))))
			(:instance subgroupp-conjs-sub (k (car (conjs-sub h g))))
			(:instance subgroupp-conjs-sub (k (cadr (conjs-sub h g))))
			(:instance sublistp-union (l1 (elts (car (conjs-sub h g))))
			                          (l2 (elts (cadr (conjs-sub h g))))
						  (m (elts g)))
			(:instance order-conjs-sub (k (car (conjs-sub h g))))
			(:instance order-conjs-sub (k (cadr (conjs-sub h g))))))))

(defthmd subgroupp-equal-order
  (implies (and (subgroupp h g)
                (equal (order h) (order g)))
	   (subgroupp g h))
  :hints (("Goal" :use ((:instance equal-len-sublistp (l (elts h)) (m (elts g)))
                        (:instance subgroup-subgroup (h g) (k h))))))

(local-defthmd order-group-intersection-less
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(not (subgroupp h k)))
	   (not (equal (order (group-intersection h k g))
	               (order h))))
  :hints (("Goal" :use ((:instance subgroupp-equal-order (h (group-intersection h k g)) (g h))
                        (:instance subgroupp-transitive (k (group-intersection h k g)) (g k))))))

(local-defthmd group-intersection-trivial
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(not (subgroupp h k))
		(primep (order h)))
	   (equal (group-intersection h k g)
	          (trivial-subgroup g)))
  :hints (("Goal" :use (order-group-intersection-less
                        (:instance order-subgroup-divides (h (group-intersection h k g)) (g h))
			(:instance primep-no-divisor (d (order (group-intersection h k g))) (p (order h)))
			(:instance iff-trivial-order-1 (h (group-intersection h k g)))))))

(local-defthmd ntecs-1
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(not (subgroupp h k))
		(primep (order h)))
	   (equal (elts (group-intersection h k g))
	          (list (e g))))
  :hints (("Goal" :use (group-intersection-trivial))))

(local-defthmd ntecs-2
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(not (subgroupp h k))
		(primep (order h)))
	   (equal (intersection-equal (elts h) (elts k))
	          (list (e g))))
  :hints (("Goal" :use (ntecs-1))))

(local-defthmd ntecs-3
  (implies (subgroupp h g)
           (not (member-equal (e g) (cdr (elts h)))))
  :hints (("Goal" :in-theory (e/d (e) (subgroup-e))
                  :use (subgroup-e (:instance dlistp (l (elts h)))))))

(local-defthmd ntecs-4
  (implies (and (member-equal x l) (member-equal x m))
           (member-equal x (intersection-equal l m))))

(local-defthmd ntecs-5
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(not (subgroupp h k))
		(primep (order h))
		(member-equal x (elts h))
		(member-equal x (elts k)))
	   (equal (e g) x))
  :hints (("Goal" :use (ntecs-2 (:instance ntecs-4 (l (elts h)) (m (elts k)))))))

(local-defthmd ntecs-6
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(not (subgroupp h k))
		(primep (order h)))
	   (disjointp (cdr (elts h)) (cdr (elts k))))
  :hints (("Goal" :use (ntecs-3
                        (:instance ntecs-5 (x (common-member (cdr (elts h)) (cdr (elts k)))))
			(:instance common-member-shared (l (cdr (elts h))) (m (cdr (elts k))))))))

(local-defthmd ntecs-7
  (implies (and (subgroupp h g)
                (primep (order h))
                (member-equal k1 (conjs-sub h g))
                (member-equal k2 (conjs-sub h g))
		(not (equal k1 k2)))
	   (disjointp (cdr (elts k1)) (cdr (elts k2))))
  :hints (("Goal" :use (conjs-sub-not-subgroup
                        (:instance ntecs-6 (h k1) (k k2))
                        (:instance order-conjs-sub (k k1))
			(:instance subgroupp-conjs-sub (k k1))
			(:instance subgroupp-conjs-sub (k k2))))))

(defun non-trivial-elts-list (l)
  (if (consp l)
      (cons (cdr (elts (car l)))
            (non-trivial-elts-list (cdr l)))
    ()))

(local-defthmd ntecs-8
  (implies (and (subgroupp h g)
                (primep (order h))
		(sublistp l (conjs-sub h g))
		(member-equal k (conjs-sub h g))
		(not (member-equal k l)))
	   (disjointp-list (cdr (elts k)) (non-trivial-elts-list l)))
  :hints (("Subgoal *1/3" :use ((:instance ntecs-7 (k1 k) (k2 (car l)))))))

(local-defthmd ntecs-9
  (implies (and (subgroupp h g)
                (primep (order h))
		(dlistp l)
		(sublistp l (conjs-sub h g)))
	   (disjointp-pairwise (non-trivial-elts-list l)))
  :hints (("Subgoal *1/1" :use ((:instance ntecs-8 (k (car l)) (l (cdr l)))))))

(local-defthmd ntecs-10
  (implies (and (subgroupp h g)
		(sublistp l (conjs-sub h g)))
	   (dlistp-list (non-trivial-elts-list l)))	   
  :hints (("Subgoal *1/2" :in-theory (disable subgroupp-conjs-sub)
                          :use ((:instance subgroupp-conjs-sub (k (car l)))
			        (:instance dlistp (l (caar l)))))))

(local-defthmd ntecs-11
  (implies (and (subgroupp h g)
                (primep (order h)))
	   (dlistp (append-list (non-trivial-elts-list (conjs-sub h g)))))
  :hints (("Goal" :use ((:instance ntecs-9 (l (conjs-sub h g)))
                        (:instance ntecs-10 (l (conjs-sub h g)))))))

(local-defthmd ntecs-12
  (implies (and (subgroupp h g)
                (primep (order h))
		(member-equal k (conjs-sub h g)))
	   (sublistp (elts k) (elts g))))

(local-defthmd ntecs-13
  (implies (and (subgroupp h g)
                (primep (order h))
		(member-equal k (conjs-sub h g)))
	   (sublistp (cdr (elts k)) (elts g)))	   
  :hints (("Goal" :in-theory (disable subgroupp-conjs-sub) :use (ntecs-12))))

(local-defthmd ntecs-14
  (implies (and (subgroupp h g)
                (primep (order h))
		(sublistp l (conjs-sub h g)))
	   (sublistp (append-list (non-trivial-elts-list l))
	             (elts g)))
  :hints (("Subgoal *1/1" :use ((:instance ntecs-13 (k (car l)))))))

(local-defthmd ntecs-15
  (implies (and (subgroupp h g)
                (primep (order h)))
	   (sublistp (append-list (non-trivial-elts-list (conjs-sub h g)))
	             (elts g)))
  :hints (("Goal" :use ((:instance ntecs-14 (l (conjs-sub h g)))))))

(local-defthmd ntecs-16
  (implies (and (subgroupp h g)
                (primep (order h))
		(member-equal x (cdr (elts h))))
	   (equal (ord x g) (order h)))
  :hints (("Goal" :use (ntecs-3
                        (:instance ord>1 (a x))
			(:instance ord-divides-order (g h))
			(:instance primep-no-divisor (p (order h)) (d (ord x g)))))))

(local-defthmd ntecs-17
  (implies (and (subgroupp h g)
                (primep (order h))
		(member-equal k (conjs-sub h g))
		(member-equal x (cdr (elts k))))
	   (equal (ord x g) (order h)))
  :hints (("Goal" :use (order-conjs-sub subgroupp-conjs-sub
                        (:instance ntecs-16 (h k))))))

(local-defthmd ntecs-18
  (implies (and (subgroupp h g)
                (primep (order h))
		(sublistp l (conjs-sub h g))
		(member x (append-list (non-trivial-elts-list l))))
	   (equal (ord x g) (order h)))	   
  :hints (("Subgoal *1/1" :use ((:instance ntecs-17 (k (car l)))))))

(local-defthmd ntecs-19
  (implies (and (subgroupp h g)
                (primep (order h))
		(member x (append-list (non-trivial-elts-list (conjs-sub h g)))))
	   (equal (ord x g) (order h)))	   
  :hints (("Goal" :use ((:instance ntecs-18 (l (conjs-sub h g)))))))

(local-defthmd ntecs-20
  (implies (and (subgroupp h g)
                (primep (order h))
		(member-equal k (conjs-sub h g)))
	   (equal (len (cdr (elts k))) (1- (order h))))
  :hints (("Goal" :use (order-conjs-sub))))

(local-defthmd ntecs-21
  (implies (and (subgroupp h g)
                (primep (order h))
		(sublistp l (conjs-sub h g)))
	   (equal (len (append-list (non-trivial-elts-list l)))
	          (* (len l) (1- (order h)))))
  :hints (("Subgoal *1/1" :use ((:instance ntecs-20 (k (car l)))))))

(local-defthmd ntecs-22
  (implies (and (subgroupp h g)
                (primep (order h)))
	   (equal (len (append-list (non-trivial-elts-list (conjs-sub h g))))
	          (* (len (conjs-sub h g))
		     (1- (order h)))))
  :hints (("Goal" :use ((:instance ntecs-21 (l (conjs-sub h g)))))))

(defthmd non-trivial-elts-conjs-sub
  (implies (and (subgroupp h g)
                (primep (order h)))
	   (let ((l (append-list (non-trivial-elts-list (conjs-sub h g)))))
	     (and (sublistp l (elts g))
	          (dlistp l)
	          (equal (len l)
		         (* (len (conjs-sub h g))
			    (1- (order h))))
		  (implies (member-equal x l)
		           (equal (ord x g) (order h))))))
  :hints (("Goal" :use (ntecs-11 ntecs-15 ntecs-19 ntecs-22))))
		
;; For every composite n < 60, we construct a proper normal subgroup of a given group g of order n.
;; The proof for a prime power is based on center-p-group; the other cases are based mainly on the
;; Sylow theorems.

;; Notation: If p is a prime dividing (order g), we shall denote (sylow-subgroup g p) as hp,
;; and (len (conjs-sub hp g)) as np.

;; We have the following cases.

;; n = p^k, where p is prime and k > 1: By center-p-group, (order (center g)) > 1.  If
;; (order (center g)) < (order g), then (center (g)) is a proper normal subgroup by normalp-center.
;; But in the remaining case, (center g) = g by ordp-subgroup-equal, and hence g is abelian by
;; abelianp-center.  By cauchy, g has an element of order p.  By order-ord, (cyclic (elt-of-ord p g) g) 
;; is a subgroup of order p, and by abelianp-normal, it is a proper normal subgroup.

(local-defthmd nspp-1
  (implies (groupp g) (posp (order (center g))))
  :hints (("Goal" :in-theory (disable consp-cent-elts)
                  :use (consp-cent-elts)
		  :expand ((len (cent-elts g))))))

(local-defthmd nspp-2
  (implies (and (p-groupp g p)
                (> (order g) 1)
                (< (order (center g)) (order g)))
	   (proper-normalp (center g) g))
  :hints (("Goal" :in-theory (enable primep p-groupp proper-normalp)
                  :use (nspp-1 center-p-group))))

(local-defthmd nspp-3
  (implies (and (p-groupp g p)
                (> (order g) 1)
                (equal (order (center g)) (order g)))
	   (abelianp g))
  :hints (("Goal" :in-theory (disable abelianp-center)
                  :use (abelianp-center (:instance ordp-subgroup-equal (h (center g)))))))

(local-defthmd nspp-4
  (implies (and (p-groupp g p)
                (> (order g) 1))
	   (and (in (elt-of-ord p g) g)
	        (equal (ord (elt-of-ord p g) g) p)))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (cauchy))))

(local-defthmd nspp-5
  (implies (and (p-groupp g p)
                (> (order g) 1))
	   (and (subgroupp (cyclic (elt-of-ord p g) g) g)
	        (equal (order (cyclic (elt-of-ord p g) g)) p)))
  :hints (("Goal" :in-theory (e/d (p-groupp) (elt-of-ord subgroupp-cyclic))
                  :use (nspp-4
		        (:instance subgroupp-cyclic (a (elt-of-ord p g)))))))

(local-defthmd nspp-6
  (implies (and (p-groupp g p)
                (> (order g) 1)
                (equal (order (center g)) (order g))
		(> (order g) p))
	   (proper-normalp (cyclic (elt-of-ord p g) g) g))
  :hints (("Goal" :in-theory (enable p-groupp proper-normalp)
                  :use (nspp-3 nspp-5
		        (:instance abelianp-normalp (h (cyclic (elt-of-ord p g) g)))))))

(local-defthmd nspp-7
  (implies (groupp g)
           (<= (order (center g)) (order g)))
  :hints (("Goal" :use ((:instance subgroup-order-<= (h (center g)))))))

(defund normal-subgroup-prime-power (p k g)
  (declare (ignore k))
  (if (< (order (center g)) (order g))
      (center g)
    (cyclic (elt-of-ord p g) g)))

(defthm proper-normalp-prime-power
  (implies (and (groupp g)
                (equal (order g) (expt p k))
		(primep p)
                (natp k)
		(> k 1))
	   (proper-normalp (normal-subgroup-prime-power p k g) g))
  :hints (("Goal" :in-theory (enable normal-subgroup-prime-power p-groupp)
                  :use (nspp-2 nspp-6 nspp-7))))

;; n = pq, where p and q are primes and p < q: By the Sylow theorems, nq divides p and (mod nq p) = 1.
;; It follows that np = 1, and by len-conjs-sub-normalp, (sylow-subgroup g q) is normal in g.

(in-theory (disable subgroup-index))

(defund normal-subgroup-pq (p q g)
  (declare (ignore p))
  (sylow-subgroup g q))

(local-defthmd mod>p
  (implies (and (primep p)
                (posp n)
		(not (equal n 1))
		(equal (mod n p) 1))
	   (> n p))
  :hints (("Goal" :nonlinearp t :use ((:instance rtl::mod-def (x n) (acl2::y p))))))

(local-defthm proper-normalp-pq-1
  (implies (and (groupp g)
                (equal (order g) (* p q))
		(primep p)
		(primep q)
		(< p q))
	   (equal (order (sylow-subgroup g q))
	          q))
  :hints (("Goal" :use ((:instance order-sylow-subgroup (p q))))))

(local-defthm proper-normalp-pq-2
  (implies (and (groupp g)
                (equal (order g) (* p q))
		(primep p)
		(primep q)
		(< p q))
	   (equal (subgroup-index (sylow-subgroup g q) g)
	          p))
  :hints (("Goal" :use (proper-normalp-pq-1 (:instance lagrange (h (sylow-subgroup g q)))))))

(local-defthm proper-normalp-pq-3
  (implies (and (groupp g)
                (equal (order g) (* p q))
		(primep p)
		(primep q)
		(< p q))
	   (equal (len (conjs-sub (sylow-subgroup g q) g))
	          1))
  :hints (("Goal" :use (proper-normalp-pq-2
                        (:instance sylow-1 (p q))
			(:instance sylow-2 (p q))
			(:instance mod>p (n (len (conjs-sub (sylow-subgroup g q) g))) (p q))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g q) g))) (y p))))))

(defthm proper-normalp-pq
  (implies (and (groupp g)
                (equal (order g) (* p q))
		(primep p)
		(primep q)
		(< p q))
	   (proper-normalp (normal-subgroup-pq p q g) g))
  :hints (("Goal" :in-theory (enable normal-subgroup-pq proper-normalp)
                  :use (proper-normalp-pq-1 proper-normalp-pq-3
		        (:instance len-conjs-sub-normalp (h (sylow-subgroup g q)))))))

;; n = ppq, where p and q are primes: We must show that either np = 1 or nq = 1.  Suppose not.  Since
;; np divides q and (mod np p) = 1, q > p.  Since nq divides p^2 and (mod nq q) = 1, nq = p^2 and q
;; divides p^2 - 1.  Thus, q divides either p - 1 or p + 1.  Since q > p, q = p + 1, which implies p = 2,
;; q = 3, and (order g) = 12. Since n3 = 4, g has 4*2 = 8 elements of order 3.  Since n2 > 1, g has more
;; than 4 elements of order dividing 4, a contradiction.

(defund normal-subgroup-ppq (p q g)
  (if (normalp (sylow-subgroup g p) g)
      (sylow-subgroup g p)
    (sylow-subgroup g q)))

(local-defthmd proper-normalp-ppq-1
  (implies (and (primep p)
		(primep q)
		(not (equal p q)))
	   (equal (log (* p p q) q) 1))
  :hints (("Goal" :use ((:instance euclid (p q) (a p) (b p))
                        (:instance primep-no-divisor (d q))))))

(local-defthmd proper-normalp-ppq-2
  (implies (and (primep p)
		(primep q)
		(not (equal p q)))
	   (equal (log (* p p q) p) 2))
  :hints (("Goal" :use ((:instance primep-no-divisor (p q) (d p))))))

(local-defthmd proper-normalp-ppq-3
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p)
		(primep q)
		(not (equal p q)))
	   (and (equal (order (sylow-subgroup g q)) q)
	        (equal (order (sylow-subgroup g p)) (* p p))))
  :hints (("Goal" :use (proper-normalp-ppq-1 proper-normalp-ppq-2 order-sylow-subgroup
                        (:instance order-sylow-subgroup (p q))))))

(local-defthmd proper-normalp-ppq-4
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p)
		(primep q)
		(not (equal p q)))
	   (and (equal (subgroup-index (sylow-subgroup g q) g) (* p p))
	        (equal (subgroup-index (sylow-subgroup g p) g) q)))
  :hints (("Goal" :use (proper-normalp-ppq-3
                        (:instance lagrange (h (sylow-subgroup g q)))
                        (:instance lagrange (h (sylow-subgroup g p)))))))

(local-defthmd proper-normalp-ppq-5
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p) (primep q)
		(not (equal p q))
		(> (len (conjs-sub (sylow-subgroup g p) g)) 1))
	   (< p q))
  :hints (("Goal" :use (proper-normalp-ppq-4 sylow-1 sylow-2
			(:instance mod>p (n (len (conjs-sub (sylow-subgroup g p) g))))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g p) g))) (y q))))))

(local-defthmd proper-normalp-ppq-6
  (implies (and (posp n) (primep p) (primep q) (equal (/ n p) q))
           (equal (* p q) n)))

(local-defthmd proper-normalp-ppq-7
  (implies (and (posp n) (primep p) (> n p) (divides n (* p p)))
           (equal (* p p) n))
  :hints (("Goal" :use ((:instance gcd-prime (a n))
                        (:instance divides-product-divides-factor (d n) (m p) (n p))
			(:instance proper-normalp-ppq-6 (q p))
			(:instance gcd-commutative (x n) (y p))
			(:instance primep-no-divisor (d (/ n p)))))))

(local-defthmd proper-normalp-ppq-8
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p) (primep q)
		(not (equal p q))
		(> (len (conjs-sub (sylow-subgroup g q) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g p) g)) 1))
	   (and (equal (len (conjs-sub (sylow-subgroup g q) g)) (* p p))
	        (equal (mod (* p p) q) 1)))
  :hints (("Goal" :use (proper-normalp-ppq-4 proper-normalp-ppq-5
                        (:instance sylow-1 (p q))
			(:instance sylow-2 (p q))
			(:instance mod>p (n (len (conjs-sub (sylow-subgroup g p) g))) (p q))
			(:instance proper-normalp-ppq-7 (n (len (conjs-sub (sylow-subgroup g q) g))))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g p) g))) (y q))))))

(local-defthmd proper-normalp-ppq-9
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p) (primep q)
		(not (equal p q))
		(> (len (conjs-sub (sylow-subgroup g q) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g p) g)) 1))
	   (divides q (1- (* p p))))
  :hints (("Goal" :use (proper-normalp-ppq-8
                        (:instance rtl::mod-def (x (* p p)) (acl2::y q))))))

(local-defthm proper-normalp-ppq-10
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p) (primep q)
		(not (equal p q))
		(> (len (conjs-sub (sylow-subgroup g q) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g p) g)) 1))
	   (equal q (1+ p)))
  :rule-classes ()
  :hints (("Goal" :use (proper-normalp-ppq-9 proper-normalp-ppq-5
                        (:instance euclid (p q) (a (1- p)) (b (1+ p)))
			(:instance divides-leq (x q) (y (1- p)))
			(:instance divides-leq (x q) (y (1+ p)))))))

(local-defthm proper-normalp-ppq-11
  (implies (natp n)
           (or (divides 2 n) (divides 2 (1+ n))))
  :rule-classes ())

(local-defthm proper-normalp-ppq-12
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p) (primep q)
		(not (equal p q))
		(> (len (conjs-sub (sylow-subgroup g q) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g p) g)) 1))
	   (and (equal p 2)
	        (equal q 3)))
  :rule-classes ()
  :hints (("Goal" :use (proper-normalp-ppq-10
                        (:instance proper-normalp-ppq-11 (n p))
                        (:instance primep-no-divisor (d 2))
                        (:instance primep-no-divisor (d 2) (p (1+ p)))))))

(local-defthm proper-normalp-ppq-13
  (implies (and (groupp g)
                (equal (order g) 12))
	   (equal (order (sylow-subgroup g 2)) 4))
  :hints (("Goal" :use ((:instance order-sylow-subgroup (p 2))))))

(local-defthm proper-normalp-ppq-14
  (implies (and (groupp g)
                (equal (order g) 12))
	   (subgroupp (sylow-subgroup g 2) g))
  :hints (("Goal" :use ((:instance order-sylow-subgroup (p 2))))))

(local-defthm proper-normalp-ppq-15
  (implies (and (groupp g)
                (equal (order g) 12)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1))
	   (let* ((h1 (car (conjs-sub (sylow-subgroup g 2) g)))
                  (h2 (cadr (conjs-sub (sylow-subgroup g 2) g)))
		  (l (union-equal (elts h1) (elts h2))))
	     (and (sublistp l (elts g))
	          (dlistp l)
	          (> (len l) 4)
		  (implies (member-equal x l)
		           (divides (ord x g) 4)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (proper-normalp-ppq-13 proper-normalp-ppq-14
			(:instance union-conjs (h (sylow-subgroup g 2)))))))

(local-defthm proper-normalp-ppq-16
  (implies (and (groupp g)
                (equal (order g) 12))
	   (and (primep 3)
	        (equal (order (sylow-subgroup g 3)) 3)))
  :hints (("Goal" :use ((:instance order-sylow-subgroup (p 3))))))

(local-defthm proper-normalp-ppq-17
  (implies (and (groupp g)
                (equal (order g) 12))
	   (subgroupp (sylow-subgroup g 3) g))
  :hints (("Goal" :use ((:instance order-sylow-subgroup (p 3))))))

(local-defthmd proper-normalp-ppq-18
  (implies (and (groupp g)
                (equal (order g) 12)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
	   (equal (len (conjs-sub (sylow-subgroup g 3) g)) 4))
  :hints (("Goal" :use ((:instance proper-normalp-ppq-8 (p 2) (q 3))))))

(local-defthm proper-normalp-ppq-19
  (implies (and (groupp g)
                (equal (order g) 12)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
	   (let ((l (append-list (non-trivial-elts-list (conjs-sub (sylow-subgroup g 3) g)))))
	     (and (sublistp l (elts g))
	          (dlistp l)
	          (equal (len l) (* 4 (1- 3)))
		  (implies (member-equal x l)
		           (equal (ord x g) 3)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (proper-normalp-ppq-16 proper-normalp-ppq-17 proper-normalp-ppq-18
			(:instance non-trivial-elts-conjs-sub (h (sylow-subgroup g 3)))))))

(local-defund union12 (g)
  (union-equal (elts (car (conjs-sub (sylow-subgroup g 2) g)))
               (elts (cadr (conjs-sub (sylow-subgroup g 2) g)))))

(local-defund append12 (g)
  (append-list (non-trivial-elts-list (conjs-sub (sylow-subgroup g 3) g))))

(local-defund biglist12 (g)
  (append (union12 g) (append12 g)))
  
(local-defthmd proper-normalp-ppq-20
  (implies (and (groupp g)
                (equal (order g) 12)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
	   (and (sublistp (union12 g) (elts g))
	        (dlistp (union12 g))
	        (> (len (union12 g)) 4)
		(sublistp (append12 g) (elts g))
	        (dlistp (append12 g))
	        (equal (len (append12 g)) 8)
		(disjointp (union12 g) (append12 g))))
  :hints (("Goal" :in-theory (enable union12 append12)
                  :use ((:instance proper-normalp-ppq-15 (x (common-member (union12 g) (append12 g))))
		        (:instance proper-normalp-ppq-19 (x (common-member (union12 g) (append12 g))))
		        (:instance common-member-shared (l (union12 g)) (m (append12 g)))))))

(local-defthmd proper-normalp-ppq-21
  (implies (and (groupp g)
                (equal (order g) 12)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
	   (and (sublistp (biglist12 g) (elts g))
	        (dlistp (biglist12 g))
	        (> (len (biglist12 g)) 12)))
  :hints (("Goal" :in-theory (enable biglist12)
                  :use (proper-normalp-ppq-20
		        (:instance length-append (l (union12 g)) (m (append12 g)))
		        (:instance dlistp-append (l (union12 g)) (m (append12 g)))
		        (:instance sublistp-append (l (union12 g)) (m (append12 g)))))))

(local-defthmd proper-normalp-ppq-22
  (implies (and (groupp g)
                (equal (order g) 12)
		(not (equal (len (conjs-sub (sylow-subgroup g 2) g)) 1)))
           (equal (len (conjs-sub (sylow-subgroup g 3) g)) 1))
  :hints (("Goal" :in-theory (enable biglist12)
                  :use (proper-normalp-ppq-21
		        (:instance posp-len-conjs-sub-sylow-subgroup (p 2))
		        (:instance posp-len-conjs-sub-sylow-subgroup (p 3))
		        (:instance sublistp-<=-len (l (biglist12 g)) (m (elts g)))))))

(defthm proper-normalp-ppq
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p)
		(primep q)
		(not (equal p q)))
	   (proper-normalp (normal-subgroup-ppq p q g) g))
  :hints (("Goal" :in-theory (enable normal-subgroup-ppq  proper-normalp)
                  :use (proper-normalp-ppq-12 proper-normalp-ppq-22 order-sylow-subgroup
		        posp-len-conjs-sub-sylow-subgroup proper-normalp-ppq-3
			(:instance order-sylow-subgroup (p q))
		        (:instance posp-len-conjs-sub-sylow-subgroup (p q))
                        (:instance len-conjs-sub-normalp (h (sylow-subgroup g p)))
                        (:instance len-conjs-sub-normalp (h (sylow-subgroup g q)))))))

;; There are 8 remaining cases, which are treated individually: 24, 30, 36, 40, 42, 48, 54, and 56.
;; The cases 40, 42, 54 follow easily from the Sylow theorems.

;; n = 40: Since n5 divides 8 and (mod n5 5) = 1, n5 = 1 and h5 is normal in g.

(defund normal-subgroup-40 (g)
  (sylow-subgroup g 5))

(local-defthmd mod>2p
  (implies (and (primep p)
                (posp n)
		(not (equal n 1))
		(equal (mod n p) 1))
	   (or (equal n (1+ p)) (> n (* 2 p))))
  :hints (("Goal" :nonlinearp t :use ((:instance rtl::mod-def (x n) (acl2::y p))))))

(in-theory (disable index-sylow-subgroup))

(local-defthmd proper-normalp-40-1
  (implies (and (groupp g)
                (equal (order g) 40))
	   (equal (len (conjs-sub (sylow-subgroup g 5) g))
	          1))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
		  :use ((:instance sylow-1 (p 5))
                        (:instance sylow-2 (p 5))
			(:instance order-sylow-subgroup (p 5))
			(:instance mod>2p (p 5) (n (len (conjs-sub (sylow-subgroup g 5) g))))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g 5) g))) (y 8))
			(:instance lagrange (h (sylow-subgroup g 5)))))))

(defthm proper-normalp-40
  (implies (and (groupp g)
                (equal (order g) 40))
	   (proper-normalp (normal-subgroup-40 g) g))
  :hints (("Goal" :in-theory (enable normal-subgroup-40 proper-normalp)
                  :use (proper-normalp-40-1
                        (:instance order-sylow-subgroup (p 5))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 5)))))))

;; n = 42: Since n7 divides 6 and (mod n7 7) = 1, n7 = 1 and h7 is normal in g.

(defund normal-subgroup-42 (g)
  (sylow-subgroup g 7))

(local-defthmd proper-normalp-42-1
  (implies (and (groupp g)
                (equal (order g) 42))
	   (equal (len (conjs-sub (sylow-subgroup g 7) g))
	          1))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
		  :use ((:instance sylow-1 (p 7))
                        (:instance sylow-2 (p 7))
			(:instance order-sylow-subgroup (p 7))
			(:instance mod>p (p 7) (n (len (conjs-sub (sylow-subgroup g 7) g))))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g 7) g))) (y 6))
			(:instance lagrange (h (sylow-subgroup g 7)))))))

(defthm proper-normalp-42
  (implies (and (groupp g)
                (equal (order g) 42))
	   (proper-normalp (normal-subgroup-42 g) g))
  :hints (("Goal" :in-theory (enable normal-subgroup-42 proper-normalp)
                  :use (proper-normalp-42-1
                        (:instance order-sylow-subgroup (p 7))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 7)))))))

;; n = 54: Since n3 divides 2 and (mod n3 3) = 1, n3 = 1 and h3 is normal in g.

(defund normal-subgroup-54 (g)
  (sylow-subgroup g 3))

(local-defthmd proper-normalp-54-1
  (implies (and (groupp g)
                (equal (order g) 54))
	   (equal (len (conjs-sub (sylow-subgroup g 3) g))
	          1))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
		  :use ((:instance sylow-1 (p 3))
                        (:instance sylow-2 (p 3))
			(:instance order-sylow-subgroup (p 3))
			(:instance mod>p (p 7) (n (len (conjs-sub (sylow-subgroup g 3) g))))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g 3) g))) (y 2))
			(:instance lagrange (h (sylow-subgroup g 3)))))))

(defthm proper-normalp-54
  (implies (and (groupp g)
                (equal (order g) 54))
	   (proper-normalp (normal-subgroup-54 g) g))
  :hints (("Goal" :in-theory (enable normal-subgroup-54 proper-normalp)
                  :use (proper-normalp-54-1
                        (:instance order-sylow-subgroup (p 3))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 3)))))))

;; The cases 56 and 30 involve counting elements of different orders.

;; n = 56: Suppose n7 > 1.  Then n7 = 8 and g has 8*6 = 48 elements of ord 7.  Therefore,
;; g has no more than 8 elements of order dividing 8, which implies n2 = 1.

(defund normal-subgroup-56 (g)
  (if (normalp (sylow-subgroup g 2) g)
      (sylow-subgroup g 2)
    (sylow-subgroup g 7)))

(local-defthmd proper-normalp-56-1
  (implies (and (groupp g)
                (equal (order g) 56)
                (> (len (conjs-sub (sylow-subgroup g 7) g)) 1))
	   (equal (len (conjs-sub (sylow-subgroup g 7) g)) 8))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
                  :use ((:instance order-sylow-subgroup (p 7))
                        (:instance sylow-1 (p 7))
                        (:instance sylow-2 (p 7))
			(:instance order-sylow-subgroup (p 7))
			(:instance mod>p (p 7) (n (len (conjs-sub (sylow-subgroup g 7) g))))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g 7) g))) (y 8))))))

(local-defthmd proper-normalp-56-2
  (implies (and (groupp g)
                (equal (order g) 56)
                (> (len (conjs-sub (sylow-subgroup g 2) g)) 1))
	   (equal (len (conjs-sub (sylow-subgroup g 2) g)) 7))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
                  :use ((:instance order-sylow-subgroup (p 2))
                        (:instance sylow-1 (p 2))
                        (:instance sylow-2 (p 2))
			(:instance order-sylow-subgroup (p 2))
			(:instance mod>p (p 2) (n (len (conjs-sub (sylow-subgroup g 2) g))))
			(:instance primep-no-divisor (p 7) (d (len (conjs-sub (sylow-subgroup g 2) g))))))))

(local-defund union56 (g)
  (union-equal (elts (car (conjs-sub (sylow-subgroup g 2) g)))
               (elts (cadr (conjs-sub (sylow-subgroup g 2) g)))))

(local-defthmd proper-normalp-56-3
  (implies (and (groupp g)
                (equal (order g) 56)
                (> (len (conjs-sub (sylow-subgroup g 2) g)) 1))
	   (and (sublistp (union56 g) (elts g))
	        (dlistp (union56 g))
	        (> (len (union56 g)) 8)
		(implies (member-equal x (union56 g))
		         (divides (ord x g) 8))))
  :hints (("Goal" :in-theory (enable union56)
                  :use (proper-normalp-56-2
		        (:instance order-sylow-subgroup (p 2))
			(:instance union-conjs (h (sylow-subgroup g 2)))))))

(local-defund append56 (g)
  (append-list (non-trivial-elts-list (conjs-sub (sylow-subgroup g 7) g))))

(local-defthmd proper-normalp-56-4
  (implies (and (groupp g)
                (equal (order g) 56)
		(> (len (conjs-sub (sylow-subgroup g 7) g)) 1))
	   (and (sublistp (append56 g) (elts g))
	        (dlistp (append56 g))
	        (equal (len (append56 g)) 48)
		(implies (member-equal x (append56 g))
		         (equal (ord x g) 7))))
  :hints (("Goal" :in-theory (enable append56)
                  :use (proper-normalp-56-1
		        (:instance order-sylow-subgroup (p 7))
			(:instance non-trivial-elts-conjs-sub (h (sylow-subgroup g 7)))))))

(local-defund biglist56 (g)
  (append (union56 g) (append56 g)))

(local-defthmd proper-normalp-56-5
  (implies (and (groupp g)
                (equal (order g) 56)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g 7) g)) 1))
	   (and (sublistp (biglist56 g) (elts g))
	        (dlistp (biglist56 g))
		(> (len (biglist56 g)) 56)))
  :hints (("Goal" :in-theory (enable biglist56)
                  :use ((:instance proper-normalp-56-3 (x (common-member (union56 g) (append56 g))))
		        (:instance proper-normalp-56-4 (x (common-member (union56 g) (append56 g))))
		        (:instance length-append (l (union56 g)) (m (append56 g)))
			(:instance dlistp-append (l (union56 g)) (m (append56 g)))
			(:instance sublistp-append (l (union56 g)) (m (append56 g)))
			(:instance common-member-shared (l (union56 g)) (m (append56 g)))))))

(local-defthmd proper-normalp-56-6
  (implies (and (groupp g)
                (equal (order g) 56)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1))
           (<= (len (conjs-sub (sylow-subgroup g 7) g)) 1))
  :hints (("Goal" :in-theory (enable biglist56)
                  :use (proper-normalp-56-5
		        (:instance sublistp-<=-len (l (biglist56 g)) (m (elts g)))))))
			
(defthm proper-normalp-56
  (implies (and (groupp g)
                (equal (order g) 56))
	   (proper-normalp (normal-subgroup-56 g) g))
  :hints (("Goal" :in-theory (enable proper-normalp normal-subgroup-56)
                  :use (proper-normalp-56-6
                        (:instance order-sylow-subgroup (p 2))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 2)))
                        (:instance order-sylow-subgroup (p 7))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 7)))))))                  

;; n = 30: Suppose n3 > 1 and n5 > 1.  Then n3 = 10 and m5 = 6.  Consequently, g has 10*2 = 20
;; elements of ord 3 and 6*4 = 24 elements of ord 5, a contradiction.

(defund normal-subgroup-30 (g)
  (if (normalp (sylow-subgroup g 3) g)
      (sylow-subgroup g 3)
    (sylow-subgroup g 5)))

(local-defthmd proper-normalp-30-1
  (implies (and (groupp g)
                (equal (order g) 30)
                (> (len (conjs-sub (sylow-subgroup g 5) g)) 1))
	   (equal (len (conjs-sub (sylow-subgroup g 5) g)) 6))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
                  :use ((:instance order-sylow-subgroup (p 5))
                        (:instance sylow-1 (p 5))
                        (:instance sylow-2 (p 5))
			(:instance mod>p (p 5) (n (len (conjs-sub (sylow-subgroup g 5) g))))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g 5) g))) (y 6))))))

(local-defthmd mod>3p
  (implies (and (primep p)
                (posp n)
		(not (equal n 1))
		(equal (mod n p) 1))
	   (or (equal n (1+ p)) (equal n (1+ (* 2 p))) (> n (* 3 p))))
  :hints (("Goal" :nonlinearp t :use ((:instance rtl::mod-def (x n) (acl2::y p))))))

(local-defthmd proper-normalp-30-2
  (implies (and (groupp g)
                (equal (order g) 30)
                (> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
	   (equal (len (conjs-sub (sylow-subgroup g 3) g)) 10))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
                  :use ((:instance order-sylow-subgroup (p 3))
                        (:instance sylow-1 (p 3))
                        (:instance sylow-2 (p 3))
			(:instance mod>3p (p 3) (n (len (conjs-sub (sylow-subgroup g 3) g))))
			(:instance divides-leq (x (len (conjs-sub (sylow-subgroup g 3) g))) (y 10))))))

(local-defund append5 (g)
  (append-list (non-trivial-elts-list (conjs-sub (sylow-subgroup g 5) g))))

(local-defthmd proper-normalp-30-3
  (implies (and (groupp g)
                (equal (order g) 30)
		(> (len (conjs-sub (sylow-subgroup g 5) g)) 1))
	   (and (sublistp (append5 g) (elts g))
	        (dlistp (append5 g))
	        (equal (len (append5 g)) 24)
		(implies (member-equal x (append5 g))
		         (equal (ord x g) 5))))
  :hints (("Goal" :in-theory (enable append5)
                  :use (proper-normalp-30-1
		        (:instance order-sylow-subgroup (p 5))
			(:instance non-trivial-elts-conjs-sub (h (sylow-subgroup g 5)))))))

(local-defund append3 (g)
  (append-list (non-trivial-elts-list (conjs-sub (sylow-subgroup g 3) g))))

(local-defthmd proper-normalp-30-4
  (implies (and (groupp g)
                (equal (order g) 30)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
	   (and (sublistp (append3 g) (elts g))
	        (dlistp (append3 g))
	        (equal (len (append3 g)) 20)
		(implies (member-equal x (append3 g))
		         (equal (ord x g) 3))))
  :hints (("Goal" :in-theory (enable append3)
                  :use (proper-normalp-30-2
		        (:instance order-sylow-subgroup (p 3))
			(:instance non-trivial-elts-conjs-sub (h (sylow-subgroup g 3)))))))

(local-defund biglist30 (g)
  (append (append3 g) (append5 g)))

(local-defthmd proper-normalp-30-5
  (implies (and (groupp g)
                (equal (order g) 30)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1)
		(> (len (conjs-sub (sylow-subgroup g 5) g)) 1))
	   (and (sublistp (biglist30 g) (elts g))
	        (dlistp (biglist30 g))
		(> (len (biglist30 g)) 30)))
  :hints (("Goal" :in-theory (enable biglist30)
                  :use ((:instance proper-normalp-30-3 (x (common-member (append3 g) (append5 g))))
		        (:instance proper-normalp-30-4 (x (common-member (append3 g) (append5 g))))
		        (:instance length-append (l (append3 g)) (m (append5 g)))
			(:instance dlistp-append (l (append3 g)) (m (append5 g)))
			(:instance sublistp-append (l (append3 g)) (m (append5 g)))
			(:instance common-member-shared (l (append3 g)) (m (append5 g)))))))

(local-defthmd proper-normalp-30-6
  (implies (and (groupp g)
                (equal (order g) 30)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
           (<= (len (conjs-sub (sylow-subgroup g 5) g)) 1))
  :hints (("Goal" :use (proper-normalp-30-5
		        (:instance sublistp-<=-len (l (biglist30 g)) (m (elts g)))))))
			
(defthm proper-normalp-30
  (implies (and (groupp g)
                (equal (order g) 30))
	   (proper-normalp (normal-subgroup-30 g) g))
  :hints (("Goal" :in-theory (enable proper-normalp normal-subgroup-30)
                  :use (proper-normalp-30-6
                        (:instance order-sylow-subgroup (p 3))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 3)))
                        (:instance order-sylow-subgroup (p 5))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 5)))))))

;; The remaining 3 cases, 24, 48, and 36, all require len-products, index-least-divisor-normal, and the
;; properties of the normalizer of a subgroup.

;; n = 24: Suppose n2 > 1.  Let h21 and h22 be distinct members of (conj-subs h2 g).  Then (order h21)
;; = order h22) = 8.  Let k = (group-intersection h21 h22 g).  Then (order k) <= 4 and by len-products,

;;    (len (products h21 h22 g)) = 8*8/(order k) <= 24,

;; which implies (order k) = 4 and (len (products h21 h22 g)) = 16.  By index-least-divisor-normal,
;; k is normal in both h21 and h22.  It follows that

;;  (order (normalizer k g)) >= (len (products h21 h22 g)) = 16

;; and therefore (normalizer k g) = g and k is normal in g.

(defund normal-subgroup-24 (g)
  (let* ((h2 (sylow-subgroup g 2))
         (h21 (car (conjs-sub h2 g)))
         (h22 (cadr (conjs-sub h2 g)))
	 (k (group-intersection h21 h22 g)))
    (if (normalp h2 g)
        h2
      k)))

(local-defthmd proper-normalp-24-1
  (implies (and (groupp g)
                (equal (order g) 24)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1))
	   (let* ((h2 (sylow-subgroup g 2))
                  (h21 (car (conjs-sub h2 g)))
                  (h22 (cadr (conjs-sub h2 g))))
	     (and (subgroupp h21 g)
	          (equal (order h21) 8)
		  (subgroupp h22 g)
	          (equal (order h22) 8)
		  (not (subgroupp h21 h22)))))
  :hints (("Goal" :in-theory (disable subgroupp-conjs-sub dlistp-conjs-sub)
                  :use ((:instance conjs-sub-not-subgroup (k1 (car (conjs-sub (sylow-subgroup g 2) g)))
                                                          (k2 (cadr (conjs-sub (sylow-subgroup g 2) g)))
							  (h (sylow-subgroup g 2)))
			(:instance order-sylow-subgroup (p 2))
			(:instance dlistp-conjs-sub (h (sylow-subgroup g 2)))
			(:instance subgroupp-conjs-sub (h (sylow-subgroup g 2)) (k (car (conjs-sub (sylow-subgroup g 2) g))))
			(:instance subgroupp-conjs-sub (h (sylow-subgroup g 2)) (k (cadr (conjs-sub (sylow-subgroup g 2) g))))
			(:instance order-conjs-sub (h (sylow-subgroup g 2)) (k (car (conjs-sub (sylow-subgroup g 2) g))))
			(:instance order-conjs-sub (h (sylow-subgroup g 2)) (k (cadr (conjs-sub (sylow-subgroup g 2) g))))))))

(local-defthmd proper-normalp-24-2
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (not (equal (order (group-intersection h k g))
	               8)))
  :hints (("Goal" :use (order-group-intersection-less))))

(local-defthmd proper-normalp-24-3
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (let ((r (group-intersection h k g)))
	     (and (subgroupp r h)
	          (subgroupp r k)
		  (divides (order r) 8))))
  :hints (("Goal" :use (subgroupp-int-both (:instance order-subgroup-divides (h (group-intersection h k g)) (g h))))))

(local-defthmd divides<half-1
  (implies (and (natp k) (natp n) (> n 1) (< k n) (divides k n))
           (>= (/ n k) 2)))
			
(local-defthmd divides<half
  (implies (and (natp k) (natp n) (> n 1) (< k n) (divides k n))
           (<= k (/ n 2)))
  :hints (("Goal" :use (divides<half-1) :nonlinearp t)))

(local-defthmd proper-normalp-24-4
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (<= (order (group-intersection h k g))
	       4))
  :hints (("Goal" :use (proper-normalp-24-2 proper-normalp-24-3
                        (:instance divides<half (k (order (group-intersection h k g))) (n 8))))))

(local-defthmd proper-normalp-24-5
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (>= (order (group-intersection h k g))
	       8/3))
  :hints (("Goal" :nonlinearp t
                  :use (proper-normalp-24-3 len-products dlistp-products ordp-products
                        (:instance ordp-sublistp (l (products h k g)))
                        (:instance sublistp-<=-len (l (products h k g)) (m (elts g)))))))

(local-defthmd proper-normalp-24-6
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (equal (order (group-intersection h k g)) 4))
  :hints (("Goal" :use (proper-normalp-24-3 proper-normalp-24-4 proper-normalp-24-5))))

(local-defthmd proper-normalp-24-7
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (equal (len (products h k g)) 16))
  :hints (("Goal" :use (len-products proper-normalp-24-6))))

(local-defthmd proper-normalp-24-8
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (and (normalp (group-intersection h k g) h)
	        (normalp (group-intersection h k g) k)))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
                  :use (proper-normalp-24-3 proper-normalp-24-6
		        (:instance index-least-divisor-normal (h (group-intersection h k g)) (g h))
		        (:instance index-least-divisor-normal (h (group-intersection h k g)) (g k))))))

(local-defthmd proper-normalp-24-9
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k))
		(in x h)
		(in y k)
		(in z (group-intersection h k g)))
	   (in (conj z (op x y g) g)
	       (group-intersection h k g)))
  :hints (("Goal" :in-theory (enable subgroup-conj)
                  :use (proper-normalp-24-8
                        (:instance conj-conj (x z) (a x) (b y))
			(:instance normalp-conj (x z) (h (group-intersection h k g)) (g k))
			(:instance normalp-conj (x (conj z y g)) (y x) (h (group-intersection h k g)) (g h))))))

(local-defthmd proper-normalp-24-10
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k))
		(in x h)
		(in y k))
	   (in (op x y g) (normalizer (group-intersection h k g) g)))
  :hints (("Goal" :use ((:instance proper-normalp-24-9 (z (normalizer-cex (op x y g) (group-intersection h k g) g)))
                        (:instance normalizer-cex-lemma (h (group-intersection h k g)) (x (op x y g)))))))

(local-defthmd proper-normalp-24-11
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k))
		(member-equal x (products h k g)))
	   (in x (normalizer (group-intersection h k g) g)))
  :hints (("Goal" :use (product-in-products-converse
                        (:instance proper-normalp-24-10 (x (car (factor-elt x h k g))) (y (cadr (factor-elt x h k g))))))))

(local-defthmd proper-normalp-24-12
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (sublistp (products h k g)
	             (elts (normalizer (group-intersection h k g) g))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (products h k g)) (m (elts (normalizer (group-intersection h k g) g))))
                        (:instance proper-normalp-24-11 (x (scex1 (products h k g) (elts (normalizer (group-intersection h k g) g)))))))))

(local-defthmd proper-normalp-24-13
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (>= (order (normalizer (group-intersection h k g) g))
	       16))
  :hints (("Goal" :use (proper-normalp-24-7 proper-normalp-24-12
                        (:instance sublistp-<=-len (l (products h k g)) (m (elts (normalizer (group-intersection h k g) g))))))))

(local-defthmd proper-normalp-24-14
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (equal (order (normalizer (group-intersection h k g) g))
	          24))
  :hints (("Goal" :use (proper-normalp-24-3 proper-normalp-24-13
                        (:instance order-subgroup-divides (h (normalizer (group-intersection h k g) g)))
			(:instance divides<half (k (order (normalizer (group-intersection h k g) g))) (n 24))))))

(local-defthmd proper-normalp-24-15
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (equal (normalizer (group-intersection h k g) g)
	          g))
  :hints (("Goal" :use (proper-normalp-24-3 proper-normalp-24-14
                        (:instance ordp-subgroup-equal (h (normalizer (group-intersection h k g) g)))))))

(local-defthmd proper-normalp-24-16
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 24)
		(equal (order h) 8)
		(equal (order k) 8)
		(not (subgroupp h k)))
	   (and (normalp (group-intersection h k g) g)
	        (equal (order (group-intersection h k g)) 4)))
  :hints (("Goal" :use (proper-normalp-24-3 proper-normalp-24-6 proper-normalp-24-15
		        (:instance normalizer-normp (h (group-intersection h k g)))))))

(local-defthmd proper-normalp-24-17
  (implies (and (groupp g)
                (equal (order g) 24)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1))
	   (let* ((h2 (sylow-subgroup g 2))
                  (h21 (car (conjs-sub h2 g)))
                  (h22 (cadr (conjs-sub h2 g)))
		  (k (group-intersection h21 h22 g)))
	     (and (normalp k g)
	          (equal (order k) 4))))
  :hints (("Goal" :use (proper-normalp-24-1
                        (:instance proper-normalp-24-16 (h (car (conjs-sub (sylow-subgroup g 2) g)))
			                                (k (cadr (conjs-sub (sylow-subgroup g 2) g))))))))

(defthm proper-normalp-24
  (implies (and (groupp g)
                (equal (order g) 24))
	   (proper-normalp (normal-subgroup-24 g) g))
  :hints (("Goal" :in-theory (enable proper-normalp normal-subgroup-24)
                  :use (proper-normalp-24-17
		        (:instance order-sylow-subgroup (p 2))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 2)))))))

;; n = 48: Suppose n2 > 1.  Let h21 and h22 be distinct members of (conj-subs h2 g).  Then (order h21)
;; = order h22) = 8.  Let k = (group-intersection h21 h22 g).  Then (order k) divides 8 and

;;    (len (products h21 h22 g)) = 16*16/(order k) <= 48,

;; which implies (order k) = 8 and (len (products h21 h22 g)) = 32.  By index-least-divisor-normal,
;; k is normal in both h21 and h22.  It follows that

;;  (order (normalizer k g)) >= (len (products h21 h22 g)) = 32

;; and therefore (normalizer k g) = g and k is normal in g.

(local-defthmd proper-normalp-48-1
  (implies (and (groupp g)
                (equal (order g) 48)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1))
	   (let* ((h2 (sylow-subgroup g 2))
                  (h21 (car (conjs-sub h2 g)))
                  (h22 (cadr (conjs-sub h2 g))))
	     (and (subgroupp h21 g)
	          (equal (order h21) 16)
		  (subgroupp h22 g)
	          (equal (order h22) 16)
		  (not (subgroupp h21 h22)))))
  :hints (("Goal" :in-theory (disable subgroupp-conjs-sub dlistp-conjs-sub)
                  :use ((:instance conjs-sub-not-subgroup (k1 (car (conjs-sub (sylow-subgroup g 2) g)))
                                                          (k2 (cadr (conjs-sub (sylow-subgroup g 2) g)))
							  (h (sylow-subgroup g 2)))
			(:instance order-sylow-subgroup (p 2))
			(:instance dlistp-conjs-sub (h (sylow-subgroup g 2)))
			(:instance subgroupp-conjs-sub (h (sylow-subgroup g 2)) (k (car (conjs-sub (sylow-subgroup g 2) g))))
			(:instance subgroupp-conjs-sub (h (sylow-subgroup g 2)) (k (cadr (conjs-sub (sylow-subgroup g 2) g))))
			(:instance order-conjs-sub (h (sylow-subgroup g 2)) (k (car (conjs-sub (sylow-subgroup g 2) g))))
			(:instance order-conjs-sub (h (sylow-subgroup g 2)) (k (cadr (conjs-sub (sylow-subgroup g 2) g))))))))

(local-defthmd proper-normalp-48-2
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (not (equal (order (group-intersection h k g))
	               16)))
  :hints (("Goal" :use (order-group-intersection-less))))

(local-defthmd proper-normalp-48-3
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (let ((r (group-intersection h k g)))
	     (and (subgroupp r h)
	          (subgroupp r k)
		  (divides (order r) 16))))
  :hints (("Goal" :use (subgroupp-int-both (:instance order-subgroup-divides (h (group-intersection h k g)) (g h))))))

(local-defthmd proper-normalp-48-4
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (<= (order (group-intersection h k g))
	       8))
  :hints (("Goal" :use (proper-normalp-48-2 proper-normalp-48-3
                        (:instance divides<half (k (order (group-intersection h k g))) (n 16))))))

(local-defthmd proper-normalp-48-5
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (>= (order (group-intersection h k g))
	       16/3))
  :hints (("Goal" :nonlinearp t
                  :use (proper-normalp-48-3 len-products dlistp-products ordp-products
                        (:instance ordp-sublistp (l (products h k g)))
                        (:instance sublistp-<=-len (l (products h k g)) (m (elts g)))))))

(local-defthmd proper-normalp-48-6
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (equal (order (group-intersection h k g)) 8))
  :hints (("Goal" :in-theory (enable rtl::bvecp)
                  :use (proper-normalp-48-3 proper-normalp-48-4 proper-normalp-48-5
                        (:instance rtl::bvecp-member (x (order (group-intersection h k g))) (acl2::n 3))))))

(local-defthmd proper-normalp-48-7
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (equal (len (products h k g)) 32))
  :hints (("Goal" :use (len-products proper-normalp-48-6))))

(local-defthmd proper-normalp-48-8
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (and (normalp (group-intersection h k g) h)
	        (normalp (group-intersection h k g) k)))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
                  :use (proper-normalp-48-3 proper-normalp-48-6
		        (:instance index-least-divisor-normal (h (group-intersection h k g)) (g h))
		        (:instance index-least-divisor-normal (h (group-intersection h k g)) (g k))))))

(local-defthmd proper-normalp-48-9
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k))
		(in x h)
		(in y k)
		(in z (group-intersection h k g)))
	   (in (conj z (op x y g) g)
	       (group-intersection h k g)))
  :hints (("Goal" :in-theory (enable subgroup-conj)
                  :use (proper-normalp-48-8
                        (:instance conj-conj (x z) (a x) (b y))
			(:instance normalp-conj (x z) (h (group-intersection h k g)) (g k))
			(:instance normalp-conj (x (conj z y g)) (y x) (h (group-intersection h k g)) (g h))))))

(local-defthmd proper-normalp-48-10
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k))
		(in x h)
		(in y k))
	   (in (op x y g) (normalizer (group-intersection h k g) g)))
  :hints (("Goal" :use ((:instance proper-normalp-48-9 (z (normalizer-cex (op x y g) (group-intersection h k g) g)))
                        (:instance normalizer-cex-lemma (h (group-intersection h k g)) (x (op x y g)))))))

(local-defthmd proper-normalp-48-11
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k))
		(member-equal x (products h k g)))
	   (in x (normalizer (group-intersection h k g) g)))
  :hints (("Goal" :use (product-in-products-converse
                        (:instance proper-normalp-48-10 (x (car (factor-elt x h k g))) (y (cadr (factor-elt x h k g))))))))

(local-defthmd proper-normalp-48-12
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (sublistp (products h k g)
	             (elts (normalizer (group-intersection h k g) g))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (products h k g)) (m (elts (normalizer (group-intersection h k g) g))))
                        (:instance proper-normalp-48-11 (x (scex1 (products h k g) (elts (normalizer (group-intersection h k g) g)))))))))

(local-defthmd proper-normalp-48-13
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (>= (order (normalizer (group-intersection h k g) g))
	       32))
  :hints (("Goal" :use (proper-normalp-48-7 proper-normalp-48-12
                        (:instance sublistp-<=-len (l (products h k g)) (m (elts (normalizer (group-intersection h k g) g))))))))

(local-defthmd proper-normalp-48-14
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (equal (order (normalizer (group-intersection h k g) g))
	          48))
  :hints (("Goal" :use (proper-normalp-48-3 proper-normalp-48-13
                        (:instance order-subgroup-divides (h (normalizer (group-intersection h k g) g)))
			(:instance divides<half (k (order (normalizer (group-intersection h k g) g))) (n 48))))))

(local-defthmd proper-normalp-48-15
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (equal (normalizer (group-intersection h k g) g)
	          g))
  :hints (("Goal" :use (proper-normalp-48-3 proper-normalp-48-14
                        (:instance ordp-subgroup-equal (h (normalizer (group-intersection h k g) g)))))))

(local-defthmd proper-normalp-48-16
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 48)
		(equal (order h) 16)
		(equal (order k) 16)
		(not (subgroupp h k)))
	   (and (normalp (group-intersection h k g) g)
	        (equal (order (group-intersection h k g)) 8)))
  :hints (("Goal" :use (proper-normalp-48-3 proper-normalp-48-6 proper-normalp-48-15
		        (:instance normalizer-normp (h (group-intersection h k g)))))))

(local-defthmd proper-normalp-48-17
  (implies (and (groupp g)
                (equal (order g) 48)
		(> (len (conjs-sub (sylow-subgroup g 2) g)) 1))
	   (let* ((h2 (sylow-subgroup g 2))
                  (h21 (car (conjs-sub h2 g)))
                  (h22 (cadr (conjs-sub h2 g)))
		  (k (group-intersection h21 h22 g)))
	     (and (normalp k g)
	          (equal (order k) 8))))
  :hints (("Goal" :use (proper-normalp-48-1
                        (:instance proper-normalp-48-16 (h (car (conjs-sub (sylow-subgroup g 2) g)))
			                                (k (cadr (conjs-sub (sylow-subgroup g 2) g))))))))

(defund normal-subgroup-48 (g)
  (let* ((h2 (sylow-subgroup g 2))
         (h21 (car (conjs-sub h2 g)))
         (h22 (cadr (conjs-sub h2 g)))
	 (k (group-intersection h21 h22 g)))
    (if (normalp h2 g)
        h2
      k)))

(defthm proper-normalp-48
  (implies (and (groupp g)
                (equal (order g) 48))
	   (proper-normalp (normal-subgroup-48 g) g))
  :hints (("Goal" :in-theory (enable proper-normalp normal-subgroup-48)
                  :use (proper-normalp-48-17
		        (:instance order-sylow-subgroup (p 2))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 2)))))))

;; n = 36: Suppose n3 > 1.  Let h31 and h32 be distinct members of (conj-subs h3 g).  Then (order h31)
;; = order h32) = 9.  Let k = (group-intersection h31 h32 g).  Then (order k) <= 3 and

;;    (len (products h31 h32 g)) = 9*9/(order k) <= 36,

;; which implies (order k) = 3 and (len (products h31 h32 g)) = 27.  By index-least-divisor-normal,
;; k is normal in both h31 and h32.  It follows that

;;  (order (normalizer k g)) >= (len (products h31 h32 g)) = 27

;; and therefore (normalizer k g) = g and k is normal in g.

(local-defthmd proper-normalp-36-1
  (implies (and (groupp g)
                (equal (order g) 36)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
	   (let* ((h3 (sylow-subgroup g 3))
                  (h31 (car (conjs-sub h3 g)))
                  (h32 (cadr (conjs-sub h3 g))))
	     (and (subgroupp h31 g)
	          (equal (order h31) 9)
		  (subgroupp h32 g)
	          (equal (order h32) 9)
		  (not (subgroupp h31 h32)))))
  :hints (("Goal" :in-theory (disable subgroupp-conjs-sub dlistp-conjs-sub)
                  :use ((:instance conjs-sub-not-subgroup (k1 (car (conjs-sub (sylow-subgroup g 3) g)))
                                                          (k2 (cadr (conjs-sub (sylow-subgroup g 3) g)))
							  (h (sylow-subgroup g 3)))
			(:instance order-sylow-subgroup (p 3))
			(:instance dlistp-conjs-sub (h (sylow-subgroup g 3)))
			(:instance subgroupp-conjs-sub (h (sylow-subgroup g 3)) (k (car (conjs-sub (sylow-subgroup g 3) g))))
			(:instance subgroupp-conjs-sub (h (sylow-subgroup g 3)) (k (cadr (conjs-sub (sylow-subgroup g 3) g))))
			(:instance order-conjs-sub (h (sylow-subgroup g 3)) (k (car (conjs-sub (sylow-subgroup g 3) g))))
			(:instance order-conjs-sub (h (sylow-subgroup g 3)) (k (cadr (conjs-sub (sylow-subgroup g 3) g))))))))

(local-defthmd proper-normalp-36-2
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (not (equal (order (group-intersection h k g))
	               9)))
  :hints (("Goal" :use (order-group-intersection-less))))

(local-defthmd proper-normalp-36-3
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (let ((r (group-intersection h k g)))
	     (and (subgroupp r h)
	          (subgroupp r k)
		  (divides (order r) 9))))
  :hints (("Goal" :use (subgroupp-int-both (:instance order-subgroup-divides (h (group-intersection h k g)) (g h))))))

(local-defthmd proper-normalp-36-4
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (<= (order (group-intersection h k g))
	       3))
  :hints (("Goal" :in-theory (enable rtl::bvecp)
                  :use (proper-normalp-36-2 proper-normalp-36-3
                        (:instance rtl::bvecp-member (x (order (group-intersection h k g))) (acl2::n 4))))))

(local-defthmd proper-normalp-36-5
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (>= (order (group-intersection h k g))
	       9/4))
  :hints (("Goal" :nonlinearp t
                  :use (proper-normalp-36-3 len-products dlistp-products ordp-products
                        (:instance ordp-sublistp (l (products h k g)))
                        (:instance sublistp-<=-len (l (products h k g)) (m (elts g)))))))

(local-defthmd proper-normalp-36-6
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (equal (order (group-intersection h k g)) 3))
  :hints (("Goal" :in-theory (enable rtl::bvecp)
                  :use (proper-normalp-36-3 proper-normalp-36-4 proper-normalp-36-5
                        (:instance rtl::bvecp-member (x (order (group-intersection h k g))) (acl2::n 2))))))

(local-defthmd proper-normalp-36-7
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (equal (len (products h k g)) 27))
  :hints (("Goal" :use (len-products proper-normalp-36-6))))

(local-defthmd proper-normalp-36-8
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (and (normalp (group-intersection h k g) h)
	        (normalp (group-intersection h k g) k)))
  :hints (("Goal" :in-theory (enable subgroup-index-rewrite)
                  :use (proper-normalp-36-3 proper-normalp-36-6
		        (:instance index-least-divisor-normal (h (group-intersection h k g)) (g h))
		        (:instance index-least-divisor-normal (h (group-intersection h k g)) (g k))))))

(local-defthmd proper-normalp-36-9
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k))
		(in x h)
		(in y k)
		(in z (group-intersection h k g)))
	   (in (conj z (op x y g) g)
	       (group-intersection h k g)))
  :hints (("Goal" :in-theory (enable subgroup-conj)
                  :use (proper-normalp-36-8
                        (:instance conj-conj (x z) (a x) (b y))
			(:instance normalp-conj (x z) (h (group-intersection h k g)) (g k))
			(:instance normalp-conj (x (conj z y g)) (y x) (h (group-intersection h k g)) (g h))))))

(local-defthmd proper-normalp-36-10
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k))
		(in x h)
		(in y k))
	   (in (op x y g) (normalizer (group-intersection h k g) g)))
  :hints (("Goal" :use ((:instance proper-normalp-36-9 (z (normalizer-cex (op x y g) (group-intersection h k g) g)))
                        (:instance normalizer-cex-lemma (h (group-intersection h k g)) (x (op x y g)))))))

(local-defthmd proper-normalp-36-11
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k))
		(member-equal x (products h k g)))
	   (in x (normalizer (group-intersection h k g) g)))
  :hints (("Goal" :use (product-in-products-converse
                        (:instance proper-normalp-36-10 (x (car (factor-elt x h k g))) (y (cadr (factor-elt x h k g))))))))

(local-defthmd proper-normalp-36-12
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (sublistp (products h k g)
	             (elts (normalizer (group-intersection h k g) g))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (products h k g)) (m (elts (normalizer (group-intersection h k g) g))))
                        (:instance proper-normalp-36-11 (x (scex1 (products h k g) (elts (normalizer (group-intersection h k g) g)))))))))

(local-defthmd proper-normalp-36-13
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (>= (order (normalizer (group-intersection h k g) g))
	       27))
  :hints (("Goal" :use (proper-normalp-36-7 proper-normalp-36-12
                        (:instance sublistp-<=-len (l (products h k g)) (m (elts (normalizer (group-intersection h k g) g))))))))

(local-defthmd proper-normalp-36-14
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (equal (order (normalizer (group-intersection h k g) g))
	          36))
  :hints (("Goal" :use (proper-normalp-36-3 proper-normalp-36-13
                        (:instance order-subgroup-divides (h (normalizer (group-intersection h k g) g)))
			(:instance divides<half (k (order (normalizer (group-intersection h k g) g))) (n 36))))))

(local-defthmd proper-normalp-36-15
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (equal (normalizer (group-intersection h k g) g)
	          g))
  :hints (("Goal" :use (proper-normalp-36-3 proper-normalp-36-14
                        (:instance ordp-subgroup-equal (h (normalizer (group-intersection h k g) g)))))))

(local-defthmd proper-normalp-36-16
  (implies (and (groupp g)
                (subgroupp h g)
		(subgroupp k g)
		(equal (order g) 36)
		(equal (order h) 9)
		(equal (order k) 9)
		(not (subgroupp h k)))
	   (and (normalp (group-intersection h k g) g)
	        (equal (order (group-intersection h k g)) 3)))
  :hints (("Goal" :use (proper-normalp-36-3 proper-normalp-36-6 proper-normalp-36-15
		        (:instance normalizer-normp (h (group-intersection h k g)))))))

(local-defthmd proper-normalp-36-17
  (implies (and (groupp g)
                (equal (order g) 36)
		(> (len (conjs-sub (sylow-subgroup g 3) g)) 1))
	   (let* ((h3 (sylow-subgroup g 3))
                  (h31 (car (conjs-sub h3 g)))
                  (h32 (cadr (conjs-sub h3 g)))
		  (k (group-intersection h31 h32 g)))
	     (and (normalp k g)
	          (equal (order k) 3))))
  :hints (("Goal" :use (proper-normalp-36-1
                        (:instance proper-normalp-36-16 (h (car (conjs-sub (sylow-subgroup g 3) g)))
			                               (k (cadr (conjs-sub (sylow-subgroup g 3) g))))))))

(defund normal-subgroup-36 (g)
  (let* ((h3 (sylow-subgroup g 3))
         (h31 (car (conjs-sub h3 g)))
         (h32 (cadr (conjs-sub h3 g)))
	 (k (group-intersection h31 h32 g)))
    (if (normalp h3 g)
        h3
      k)))

(defthm proper-normalp-36
  (implies (and (groupp g)
                (equal (order g) 36))
	   (proper-normalp (normal-subgroup-36 g) g))
  :hints (("Goal" :in-theory (enable proper-normalp normal-subgroup-36)
                  :use (proper-normalp-36-17
		        (:instance order-sylow-subgroup (p 3))
			(:instance len-conjs-sub-normalp (h (sylow-subgroup g 3)))))))

(defund normal-subgroup (g)
  (case (order g)
    (4 (normal-subgroup-prime-power 2 2 g))
    (6 (normal-subgroup-pq 2 3 g))
    (8 (normal-subgroup-prime-power 2 3 g))
    (9 (normal-subgroup-prime-power 3 2 g))
    (10 (normal-subgroup-pq 2 5 g))
    (12 (normal-subgroup-ppq 2 3 g))
    (14 (normal-subgroup-pq 2 7 g))
    (15 (normal-subgroup-pq 3 5 g))
    (16 (normal-subgroup-prime-power 2 4 g))
    (18 (normal-subgroup-ppq 3 2 g))
    (20 (normal-subgroup-ppq 2 5 g))
    (21 (normal-subgroup-pq 3 7 g))
    (22 (normal-subgroup-pq 2 11 g))
    (24 (normal-subgroup-24 g))
    (25 (normal-subgroup-prime-power 5 2 g))
    (26 (normal-subgroup-pq 2 13 g))
    (27 (normal-subgroup-prime-power 3 3 g))
    (28 (normal-subgroup-ppq 2 7 g))
    (30 (normal-subgroup-30 g))
    (32 (normal-subgroup-prime-power 2 5 g))
    (33 (normal-subgroup-pq 3 11 g))
    (34 (normal-subgroup-pq 2 17 g))
    (35 (normal-subgroup-pq 5 7 g))
    (36 (normal-subgroup-36 g))
    (38 (normal-subgroup-pq 2 19 g))
    (39 (normal-subgroup-pq 3 13 g))
    (40 (normal-subgroup-40 g))
    (42 (normal-subgroup-42 g))
    (44 (normal-subgroup-ppq 2 11 g))
    (45 (normal-subgroup-ppq 3 5 g))
    (46 (normal-subgroup-pq 2 23 g))
    (48 (normal-subgroup-48 g))
    (49 (normal-subgroup-prime-power 7 2 g))
    (50 (normal-subgroup-ppq 5 2 g))
    (51 (normal-subgroup-pq 3 17 g))
    (52 (normal-subgroup-ppq 2 13 g))
    (54 (normal-subgroup-54 g))
    (55 (normal-subgroup-pq 5 11 g))
    (56 (normal-subgroup-56 g))
    (57 (normal-subgroup-pq 3 19 g))
    (58 (normal-subgroup-pq 2 29 g))))

(defthm no-simple-group-of-composite-order<60
  (implies (and (natp n)
		(> n 1)
		(< n 60)
		(not (primep n))
		(groupp g)
		(equal (order g) n))
	   (proper-normalp (normal-subgroup g) g))
  :hints (("Goal" :in-theory (enable rtl::bvecp normal-subgroup)
                  :use ((:instance rtl::bvecp-member (x n) (acl2::n 6))))))
