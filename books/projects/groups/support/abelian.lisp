(in-package "DM")

(include-book "products")

;; Fundamental Theorem of Finite Abelian Groups: Every finitie abelian group is isomorphic to a direct
;; product of cyclic p-groups, the order of which are unique up to permutation.

;;-------------------------------------------------------------------------------------------------------
;; Factorization of a p-Group
;;-------------------------------------------------------------------------------------------------------

;; LEMMA: Let g be an abelian group of order p^n, where p is prime, and assume g is not cyclic.
;; Let a be an element of g of maximal ord p^k.  Let g1 = (cyclic a g).
;; There exists a subgroup g2 of g such that
;;   (1) (order g2) =  p^(n-k) and
;;   (2) g2 intersects g1 trivially.

;; Proof:  We shall construct an element y of ord p in g that is not in g1.
;; First, let (lcoset x g1 g) be of ord p in (quotient g g1).  Thus, x is not in g1 but x^p = a^i.
;; It follows that i is divisible by p, for otherwise a^i has ord p^k and
;;   x^(p^k) = (x^p)^(p^(k-1)) = (a^i)^p^(k-1) != e,
;; contradicting the maximality of the ord of a.  Let j = i/p and y = a^(-j)x.  Then y is not in g1 and
;; y^p = a^(-jp)x^p = a^(-i)x^p = e.
;; Let c = (cyclic y g).  Then g1 and c intersect trivially.  Let g' = (quotient g c) and a' = (lcoset a c g).  
;; The ord of a' in g' is p^k, for otherwise a^(p^(k-1)) is in c, implying a^(p^(k-1)) = e.
;; Thus, a' has maximal ord in g'.  If g' is cyclic, then its order is p^k, which implies
;;   (order g) = p^(k+1) = (order g1) * (order c), and we may define g2 = c.
;; Otherwiae, we proceed by induction on (order g), substituting g' for g and a' for a.
;; Let g1' = (cyclic a' g').   By inductive hypothesis, g' is the internal direct product of g1' and g2'
;; for some g2' with
;;    (order g2') = (/ (order g') (order g1')) = p^(n-1)/p^k = p^(n-k-1).
;; Let g2 = (lift g2' c g).  Then g2 is easily shown to satisfy the requirements of the lemma:
;;   (1) By lift-order, (order g2) = p * (order g2') = p^(n-k}.
;;   (2) If r is in both g1 and g2, then (lcoset r c g) is in both g1' and g2', which implies r is in c.
;;       But then r is in both g1 and c, which implies r = e.

;; Let's formalize this proof.

;; The maximal ord in a p-group:

(defun max-ord-aux (g n)
  (if (zp n)
      1
    (if (elt-of-ord n g)
        n
      (max-ord-aux g (1- n)))))

(defund max-ord (g)
  (max-ord-aux g (order g)))

(local-defun elt-of-greater-ord-aux (l n g)
  (if (consp l)
      (if (> (ord (car l) g) n)
          (car l)
	(elt-of-greater-ord-aux (cdr l) n g))
    ()))

(local-defun elt-of-greater-ord (n g) (elt-of-greater-ord-aux (elts g) n g))

(local-defthm elt-of-greater-ord-aux-ord
  (implies (and (groupp g)
                (natp n)
		(sublistp l (elts g))
                (elt-of-greater-ord-aux l n g))
	   (and (in (elt-of-greater-ord-aux l n g) g)
	        (> (ord (elt-of-greater-ord-aux l n g) g)
		   n))))

(local-defthm elt-of-greater-ord-ord
  (implies (and (groupp g)
                (natp n)
                (elt-of-greater-ord n g))
	   (and (in (elt-of-greater-ord n g) g)
	        (> (ord (elt-of-greater-ord n g) g)
		   n))))

(local-defthm ord-elt-of-greater-ord-aux
  (implies (and (groupp g)
                (natp n)
		(sublistp l (elts g))
		(member-equal x l)
		(> (ord x g) n))
           (elt-of-greater-ord-aux l n g))
  :hints (("Subgoal *1/1" :in-theory (enable groupp))))

(local-defthm ord-elt-of-greater-ord
  (implies (and (groupp g)
                (natp n)
		(in x g)
		(> (ord x g) n))
           (elt-of-greater-ord n g)))

(local-in-theory (disable elt-of-ord elt-of-greater-ord))

(local-defthm elt-of-greater-ord-0
  (implies (groupp g)
           (elt-of-greater-ord 0 g))
  :hints (("Goal" :use ((:instance ord>1 (a (e g)))
                        (:instance ord-elt-of-greater-ord (n 0) (x (e g)))))))

(local-defthmd not-elt-of-greater-ord-order
  (implies (groupp g)
           (not (elt-of-greater-ord (order g) g)))
  :hints (("Goal" :use ((:instance ord<=order (a (elt-of-greater-ord (order g) g)))
                        (:instance elt-of-greater-ord-ord (n (order g)))))))

(local-defthmd elt-of-ord-max-ord-aux
  (implies (and (groupp g)
                (natp n)
		(not (elt-of-greater-ord n g)))
	   (and (elt-of-ord (max-ord-aux g n) g)
		(equal (ord (elt-of-ord (max-ord-aux g n) g) g)
		       (max-ord-aux g n))
		(implies (in x g)
		         (<= (ord x g) (max-ord-aux g n)))))
  :hints (("Subgoal *1/3" :use ((:instance ord-elt-of-greater-ord (x (elt-of-greater-ord (1- n) g)))
                                (:instance elt-of-greater-ord-ord (n (1- n)))))))

(local-defthmd elt-of-ord-max-ord
  (implies (groupp g)
           (and (elt-of-ord (max-ord g) g)
	        (equal (ord (elt-of-ord (max-ord g) g) g)
		       (max-ord g))
		(implies (in x g)
		         (<= (ord x g) (max-ord g)))))
  :hints (("Goal" :in-theory (enable max-ord)
                  :use (not-elt-of-greater-ord-order (:instance elt-of-ord-max-ord-aux (n (order g)))))))

(local-defthmd max-ord<=order
  (implies (groupp g)
           (and (<= (max-ord g) (order g))
	        (divides (max-ord g) (order g))))
  :hints (("Goal" :use (elt-of-ord-max-ord
                        (:instance ord<=order (a (elt-of-ord (max-ord g) g)))
			(:instance ord-divides-order (x (elt-of-ord (max-ord g) g)))
                        (:instance elt-of-ord-ord (n (max-ord g)))))))

(local-defthmd max-ord-cyclicp
  (implies (cyclicp g)
	   (equal (max-ord g) (order g)))
  :hints (("Goal" :in-theory (enable cyclicp group-gen)
                  :use (max-ord<=order
		        (:instance elt-of-ord-max-ord (x (group-gen g)))
		        (:instance elt-of-ord-ord (n (order g)))))))

(local-defthmd power-divides-power
  (implies (and (primep p)
                (powerp n p)
		(powerp m p)
		(<= n m))
	   (divides n m))
  :hints (("Goal" :use (powerp-log (:instance powerp-log (n m))))))

(local-defthmd p-group-ord-divides-max-ord
  (implies (and (p-groupp g p)
                (in x g))
	   (divides (ord x g) (max-ord g)))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (elt-of-ord-max-ord p-groupp-ord-powerp
                        (:instance p-groupp-ord-powerp (x (elt-of-ord (max-ord g) g)))
                        (:instance power-divides-power (n (ord x g)) (m (max-ord g)))))))

(local-defthmd power-max-ord-e
  (implies (and (p-groupp g p)
                (in x g))
	   (equal (power x (max-ord g) g)
	          (e g)))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (p-group-ord-divides-max-ord
		        (:instance divides-ord (a x) (n (max-ord g)))))))

(local-defthmd max-ord-upper-bound
  (implies (and (groupp g)
                (not (cyclicp g)))
	   (< (max-ord g) (order g)))
  :hints (("Goal" :in-theory (enable cyclicp group-gen)
                  :use (not-elt-of-greater-ord-order elt-of-ord-max-ord
		        (:instance ord-elt-of-greater-ord (n (order g)) (x (elt-of-ord (max-ord g) g)))))))

(local-defthmd max-ord-lower-bound
  (implies (and (groupp g)
                (not (cyclicp g)))
	   (> (max-ord g) 1))
  :hints (("Goal" :in-theory (e/d (e cyclicp group-gen) (dlistp-elts))
                  :use (max-ord-upper-bound dlistp-elts
		        (:instance elt-of-ord-max-ord (x (cadar g)))
		        (:instance ord>1 (a (cadar g)))
		        (:instance elt-of-greater-ord-ord (n 0))))))

(local-defthmd max-ord-bounds
  (implies (and (groupp g)
                (not (cyclicp g)))
	   (and (> (max-ord g) 1)
	        (< (max-ord g) (order g))))
  :hints (("Goal" :use (max-ord-upper-bound max-ord-lower-bound))))

(local-defthmd p-divides-max-ord
  (implies (and (p-groupp g p)
                (not (cyclicp g)))
	   (and (powerp (max-ord g) p)
	        (divides p (max-ord g))))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (max-ord-bounds elt-of-ord-max-ord
                        (:instance p-groupp-ord-powerp (x (elt-of-ord (max-ord g) g)))
			(:instance p-divides-power-p (n (max-ord g)))))))

;; Let a be an element of maximal ord p^k in a non-cyclic group g of order p^n, and let g1 = (cyclic a g):

(defund g1 (a g)
  (cyclic a g))

;; Our objective is to construct a subgroup g2 of g such that
;;   (1) (order g2) =  p^(n-k) and
;;   (2) g1 intersects g2 trivially.

;; The purpose of the following definition is to avoid typing its body repeatedly:

(defund phyp (a p g)
  (and (p-groupp g p)
       (abelianp g)
       (not (cyclicp g))
       (in a g)
       (equal (ord a g) (max-ord g))))

;; By Cauchy's Theorem, for some x in g, (lcoset x h g) has ord p in (quotient g h):

(local-defthmd order-g1
  (implies (phyp a p g)
	   (and (normalp (g1 a g) g)
	        (cyclicp (g1 a g))
	        (p-groupp (g1 a g) p)
		(divides p (order (g1 a g)))
	        (>= (order (g1 a g)) p)
	        (< (order (g1 a g)) (order g))))
  :hints (("Goal" :in-theory (enable p-groupp g1 phyp)
                  :use (max-ord-bounds
		        (:instance abelianp-normalp (h (g1 a g)))
			(:instance lagrange (h (cyclic a g)))
			(:instance powerp-divides (n (order g)) (m (order (g1 a g))))
			(:instance p-divides-power-p (n (subgroup-index (g1 a g) g)))))))

(local-defthmd elt-of-ord-p-quotient-1
  (implies (phyp a p g)
	   (let ((q (quotient g (g1 a g))))
	     (and (normalp (g1 a g) g)
	          (p-groupp q p)
		  (> (order q) 1)
	          (< (order q) (order g)))))
  :hints (("Goal" :in-theory (enable p-groupp order-quotient phyp)
                  :use (order-g1
			(:instance lagrange (h (g1 a g)))
			(:instance powerp-divides (n (order g)) (m (subgroup-index (g1 a g) g)))
			(:instance p-divides-power-p (n (subgroup-index (g1 a g) g)))))))

(local-defthmd elt-of-ord-p-quotient
  (implies (phyp a p g)
	   (let ((q (quotient g (g1 a g))))
	     (and (normalp (g1 a g) g)
	          (p-groupp q p)
		  (> (order q) 1)
	          (< (order q) (order g))
		  (elt-of-ord p q))))
  :hints (("Goal" :in-theory (enable p-groupp phyp)
                  :use (elt-of-ord-p-quotient-1
			(:instance p-divides-power-p (n (order (quotient g (g1 a g)))))
			(:instance cauchy (g (quotient g (g1 a g))))))))

(defund x$ (a p g)
  (car (elt-of-ord p (quotient g (g1 a g)))))

;; Thus, x is not in g1 but x^p is in g1, which implies x^p = a^i, where i = (index (power x p g) (powers a g)).
;; It follows that i is divisible by p, for otherwise a^i has ord p^k and
;;   x^(p^k) = (x^p)^(p^(k-1)) = (a^i)^p^(k-1) != e,
;; contradicting the maximality of the ord of a.  Let j = i/p and y =  a^(-j)x.  Then y is not in g1 and
;; y^p =  a^(-jp)x^p = a^(-i)x^p = e.  Thus, the ord of y is p.
;; Let c = (cyclic y g).

(defund i$ (a p g)
  (index (power (x$ a p g) p g) (powers a g)))

(defund j$ (a p g)
  (/ (i$ a p g) p))

(defund y$ (a p g)
  (op (power (inv a g) (j$ a p g) g)
      (x$ a p g)
      g))

(defun c$ (a p g)
  (cyclic (y$ a p g) g))

(local-defthmd elt-of-ord-p-quotient-ord
  (implies (phyp a p g)
	   (and (in (elt-of-ord p (quotient g (g1 a g)))
	            (quotient g (g1 a g)))
	        (and (primep p)
		     (not (equal (elt-of-ord p (quotient g (g1 a g)))
		                 (lcoset (e g) (g1 a g) g)))
		     (equal (ord (elt-of-ord p (quotient g (g1 a g)))
		                 (quotient g (g1 a g)))
		            p))))
  :hints (("Goal" :in-theory (enable p-groupp phyp)
                  :use (elt-of-ord-p-quotient
		        (:instance ord>1 (a (elt-of-ord p (quotient g (g1 a g)))) (g (quotient g (g1 a g))))
                        (:instance elt-of-ord-ord (n p) (g (quotient g (g1 a g))))))))

(local-defthmd x$-not-in-g1
  (implies (phyp a p g)
	   (not (in (x$ a p g) (g1 a g))))
  :hints (("Goal" :in-theory (enable x$ p-groupp phyp)
                  :use (elt-of-ord-p-quotient elt-of-ord-p-quotient-ord
		        (:instance ord>1 (a (elt-of-ord p (quotient g (g1 a g)))) (g (quotient g (g1 a g))))
			(:instance member-lcoset-iff (x (e g)) (y (x$ a p g)) (h (g1 a g)))
			(:instance equal-lcoset (x (e g)) (y (x$ a p g)) (h (g1 a g)))
			(:instance lcosets-cars (c (elt-of-ord p (quotient g (g1 a g)))) (h (g1 a g)))
			(:instance member-lcoset-qlist-iff (x (elt-of-ord p (quotient g (g1 a g)))) (h (g1 a g)))
                        (:instance elt-of-ord-ord (n p) (g (quotient g (g1 a g))))))))

(local-defthmd x$-in-g
  (implies (phyp a p g)
	   (in (x$ a p g) g))
  :hints (("Goal" :in-theory (enable x$ p-groupp phyp)
                  :use (elt-of-ord-p-quotient elt-of-ord-p-quotient-ord
		        (:instance ord>1 (a (elt-of-ord p (quotient g (g1 a g)))) (g (quotient g (g1 a g))))
			(:instance member-lcoset-iff (x (e g)) (y (x$ a p g)) (h (g1 a g)))
			(:instance equal-lcoset (x (e g)) (y (x$ a p g)) (h (g1 a g)))
			(:instance lcosets-cars (c (elt-of-ord p (quotient g (g1 a g)))) (h (g1 a g)))
			(:instance member-lcoset-qlist-iff (x (elt-of-ord p (quotient g (g1 a g)))) (h (g1 a g)))
                        (:instance elt-of-ord-ord (n p) (g (quotient g (g1 a g))))))))

(local-defthmd x$-p-in-g1
  (implies (phyp a p g)
	   (in (power (x$ a p g) p g)
	       (g1 a g)))
  :hints (("Goal" :in-theory (enable x$ p-groupp phyp)
                  :use (elt-of-ord-p-quotient elt-of-ord-p-quotient-ord
		        (:instance ord>1 (a (elt-of-ord p (quotient g (g1 a g)))) (g (quotient g (g1 a g))))
			(:instance member-lcoset-iff (x (e g)) (y (power (x$ a p g) p g)) (h (g1 a g)))
			(:instance equal-lcoset (x (e g)) (y (x$ a p g)) (h (g1 a g)))
			(:instance lcosets-cars (c (elt-of-ord p (quotient g (g1 a g)))) (h (g1 a g)))
			(:instance member-lcoset-qlist-iff (x (elt-of-ord p (quotient g (g1 a g)))) (h (g1 a g)))
			(:instance power-lcoset (a (x$ a p g)) (x (elt-of-ord p (quotient g (g1 a g)))) (n p) (h (g1 a g)))
			(:instance ord-power (a (elt-of-ord p (quotient g (g1 a g)))) (g (quotient g (g1 a g))))
			(:instance member-self-lcoset (x (power (x$ a p g) p g)) (h (g1 a g)))
                        (:instance elt-of-ord-ord (n p) (g (quotient g (g1 a g))))))))

(local-defthmd x$-p-power-a
  (implies (phyp a p g)
           (and (natp (i$ a p g))
	        (equal (power (x$ a p g) p g)
	               (power a (i$ a p g) g))))
  :hints (("Goal" :in-theory (enable phyp i$ g1)
                  :use (x$-in-g x$-p-in-g1 x$-not-in-g1
		        (:instance power-member (a (x$ a p g)) (n (ord (x$ a p g) g)))
		        (:instance power-member (a (x$ a p g)) (n (i$ a n g)))
			(:instance ord-power (a (x$ a p g)))
			(:instance ord>1 (a (x$ a p g)))
                        (:instance member-powers-power (x (power (x$ a p g) p g)))))))

(local-defthmd divides-p-i$
  (implies (phyp a p g)
	   (divides p (i$ a p g)))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (p-divides-max-ord x$-p-power-a power-max-ord-e x$-in-g
                        (:instance power* (a (x$ a p g)) (n p) (m (/ (max-ord g) p)))
			(:instance power* (n (i$ a p g)) (m (/ (max-ord g) p)))
			(:instance p-group-ord-divides-max-ord (x (x$ a p g)))
			(:instance divides-ord (n (/ (* (i$ a p g) (max-ord g)) p)))))))

(local-defthmd y$-p
  (implies (phyp a p g)
           (equal (power (y$ a p g) p g)
	          (e g)))
  :hints (("Goal" :in-theory (e/d (phyp j$ y$) (power-in-g))
                  :use (x$-p-power-a divides-p-i$ x$-in-g
		        (:instance power-abelian (n p) (x (power (inv a g) (j$ a p g) g)) (y (x$ a p g)))
		        (:instance power* (a (inv a g)) (n (j$ a p g)) (m p))
			(:instance power-inv (x a) (n (i$ a p g)))
			(:instance power-in-g (a (inv a g)) (n (j$ a p g)))))))

(local-defthmd y$-in-g
  (implies (phyp a p g)
           (in (y$ a p g) g))
  :hints (("Goal" :in-theory (e/d (phyp y$) (power-in-g))
                  :use (x$-in-g
			(:instance power-in-g (a (inv a g)) (n (j$ a p g)))))))

(local-defthmd y$-not-in-g1-1
  (implies (phyp a p g)
           (equal (op (power a (j$ a p g) g) (y$ a p g) g)
	          (x$ a p g)))
  :hints (("Goal" :in-theory (e/d (phyp j$ y$) (power-in-g))
                  :use (y$-in-g x$-in-g
		        (:instance left-cancel (a (power (inv a g) (j$ a p g) g)) (x (op (power a (j$ a p g) g) (y$ a p g) g)) (y (x$ a p g)))
                        (:instance power-inv (x a) (n (j$ a p g)))
			(:instance group-assoc (x (power (inv a g) (j$ a p g) g)) (y (power a (j$ a p g) g)) (z (y$ a p g)))
			(:instance power-in-g (n (j$ a p g)))))))

(local-defthmd in-a-g1
  (implies (phyp a p g)
           (in a (g1 a g)))
  :hints (("Goal" :in-theory (e/d (phyp g1) (power-member))
                  :expand ((power a 1 g))
                  :use ((:instance power-member (n 1))))))

(local-defthmd in-a-j$-g1
  (implies (phyp a p g)
           (in (power a (j$ a p g) g) (g1 a g)))
  :hints (("Goal" :in-theory (e/d (phyp p-groupp j$) (power-in-g))
                  :use (elt-of-ord-p-quotient in-a-g1 divides-p-i$
		        (:instance power-in-g (g (g1 a g)) (n (j$ a p g)))))))

(local-defthmd y$-not-in-g1
  (implies (phyp a p g)
           (not (in (y$ a p g) (g1 a g))))
  :hints (("Goal" :in-theory (e/d (phyp j$) (group-closure subgroup-op))
                  :use (in-a-j$-g1 in-a-g1 y$-not-in-g1-1 x$-in-g x$-not-in-g1 elt-of-ord-p-quotient
		        (:instance subgroup-op (h (g1 a g)) (x (y$ a p g)) (y (power a (j$ a p g) g)))
		        (:instance group-closure (g (g1 a g)) (x (y$ a p g)) (y (power a (j$ a p g) g)))))))

(local-defthmd y$-not-e
  (implies (phyp a p g)
           (not (equal (y$ a p g) (e g))))
  :hints (("Goal" :in-theory (e/d (phyp j$ y$) (subgroup-e in-e-g))
                  :use (y$-not-in-g1 elt-of-ord-p-quotient
			(:instance subgroup-e (h (g1 a g)))
			(:instance in-e-g (g (g1 a g)))))))

(local-defthmd ord-y$
  (implies (phyp a p g)
           (equal (ord (y$ a p g) g)
	          p))
  :hints (("Goal" :in-theory (enable p-groupp phyp)
                  :use (y$-in-g y$-not-e y$-p
                        (:instance divides-ord (a (y$ a p g)) (n p))
			(:instance ord>1 (a (y$ a p g)))
			(:instance primep-no-divisor (d (ord (y$ a p g) g)))))))

(local-defthmd order-quotient-c$
  (implies (phyp a p g)
           (and (normalp (c$ a p g) g)
	        (equal (order (c$ a p g)) p)
	        (equal (order (quotient g (c$ a p g)))
		       (/ (order g) p))))
  :hints (("Goal" :in-theory (e/d (order-quotient phyp) (order-ord abelianp-normalp))
                  :use (elt-of-ord-p-quotient y$-in-g ord-y$
		        (:instance order-quotient (h (c$ a p g)))
			(:instance order-ord (a (y$ a p g)))
			(:instance lagrange (h (c$ a p g)))
			(:instance abelianp-normalp (h (c$ a p g)))))))

;; Then g1 and c intersect trivially.  The ord of (lcoset a c g) is p^k, for otherwise a^(p^(k-1)) is in c,
;; implying a^(p^(k-1)) = e.  Thus, (lcoset a c g) has maximal ord in (quotient g c).

(local-defthmd subgroup-equal-order
  (implies (and (subgroupp h g)
                (equal (order h) (order g)))
	   (permp (elts h) (elts g)))
  :hints (("Goal" :in-theory (enable subgroupp)
                  :use ((:instance permp-eq-len (l (elts h)) (m (elts g)))))))

(local-defthmd in-y$-c$
  (implies (phyp a p g)
           (in (y$ a p g) (c$ a p g)))
  :hints (("Goal" :in-theory (e/d (phyp c$) (power-member))
                  :expand ((power (y$ a p g) 1 g))
                  :use (y$-in-g (:instance power-member (a (y$ a p g)) (n 1))))))
	 
(local-defthm primep-p
  (implies (phyp a p g)
           (primep p))
  :hints (("Goal" :in-theory (enable phyp p-groupp))))	   

(local-defthmd g1-int-c$-1
  (implies (phyp a p g)
           (not (equal (order (group-intersection (g1 a g) (c$ a p g) g))
	               (order (c$ a p g)))))
  :hints (("Goal" :in-theory (e/d (phyp p-groupp subgroupp permp) (member-sublist))
                  :use (y$-in-g y$-not-in-g1 in-y$-c$ elt-of-ord-p-quotient
		        (:instance member-sublist (x (y$ a p g))
			                          (l (elts (c$ a p g)))
						  (m (elts (group-intersection (g1 a g) (c$ a p g) g))))
		        (:instance subgroup-equal-order (g (c$ a p g)) (h (group-intersection (g1 a g) (c$ a p g) g)))))))		        

(defthmd g1-int-c$
  (implies (phyp a p g)
           (equal (group-intersection (g1 a g) (c$ a p g) g)
	          (trivial-subgroup g)))
  :hints (("Goal" :use (g1-int-c$-1 order-quotient-c$ elt-of-ord-p-quotient
                        (:instance primep-no-divisor (d (order (group-intersection (g1 a g) (c$ a p g) g))))
			(:instance order-1-trivial (h (group-intersection (g1 a g) (c$ a p g) g)))
			(:instance order-subgroup-divides (h (group-intersection (g1 a g) (c$ a p g) g)) (g (c$ a p g)))))))

;; Let g' = (quotient g c) and a' = (lcoset a c g).  
;; The ord of a' in g' is p^k, for otherwise a^(p^(k-1)) is in c, implying a^(p^(k-1)) = e.
;; Thus, a' has maximal ord in g'.  If g' is cyclic, then its order is p^k, which implies
;;   (order g) = p^(k+1) = (order g1) * (order c), and we may define g2 = c.
;; Otherwiae, we proceed by induction on (order g), substituting g' for g and a' for a.
;; Let g1' = (cyclic a' g').   By inductive hypothesis, g' is the internal direct product of g1' and g2'
;; for some g2' with
;;    (order g2') = (/ (order g') (order g1')) = p^(n-1)/p^k = p^(n-k-1).
;; Let g2 = (lift g2' c g).

(defun g* (a p g)
  (quotient g (c$ a p g)))

(defun a* (a p g)
  (lcoset a (c$ a p g) g))

(local-defthmd power-coset-max-ord
  (implies (and (phyp a p g)
                (in x (g* a p g)))
	   (equal (power x (max-ord g) (g* a p g))
	          (lcoset (e g) (c$ a p g) g)))
  :hints (("Goal" :in-theory (enable power-max-ord-e phyp)
                  :use (order-quotient-c$
                        (:instance power-lcoset (a (car x)) (n (max-ord g)) (h (c$ a p g)))
			(:instance lcosets-cars (c x) (h (c$ a p g)))
			(:instance member-lcoset-qlist-iff (h (c$ a p g)))))))

(local-defthmd divides-ord-lcoset-max-ord
  (implies (and (phyp a p g)
                (in x (g* a p g)))
	   (divides (ord x (g* a p g))
	            (max-ord g)))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (power-coset-max-ord order-quotient-c$
                        (:instance divides-ord (a x) (n (max-ord g)) (g (g* a p g)))))))

(local-defthmd power-a-in-c$
  (implies (phyp a p g)
           (in (power a (ord (a* a p g) (g* a p g)) g)
	       (c$ a p g)))
  :hints (("Goal" :in-theory (e/d (phyp) (power-in-g))
                  :use (order-quotient-c$
		        (:instance power-lcoset (x (a* a p g))
			                        (n (ord (a* a p g) (g* a p g)))
						(h (c$ a p g)))
		        (:instance member-self-lcoset (x a) (h (c$ a p g)))
			(:instance power-in-g (n (ord (a* a p g) (g* a p g))))
			(:instance member-lcoset-iff (y (power a (ord (a* a p g) (g* a p g)) g))
			                             (x (e g))
			                             (h (c$ a p g)))))))

(local-defthmd power-a-in-g1
  (implies (phyp a p g)
           (in (power a (ord (a* a p g) (g* a p g)) g)
	       (g1 a g)))
  :hints (("Goal" :in-theory (e/d (phyp p-groupp) (subgroup-e power-in-g))
                  :use (elt-of-ord-p-quotient in-a-g1
		        (:instance subgroup-e (h (g1 a g)))
		        (:instance power-subgroup (x a) (h (g1 a g)) (n (ord (a* a p g) (g* a p g))))))))

(local-defthmd power-a-in-int
  (implies (phyp a p g)
           (in (power a (ord (a* a p g) (g* a p g)) g)
	       (group-intersection (g1 a g) (c$ a p g) g)))
  :hints (("Goal" :use (power-a-in-g1 power-a-in-c$ elt-of-ord-p-quotient order-quotient-c$))))

(local-defthmd power-a-e
  (implies (phyp a p g)
           (equal (power a (ord (a* a p g) (g* a p g)) g)
	          (e g)))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (g1-int-c$ power-a-in-int))))

(defthmd ord-lcoset-a
  (implies (phyp a p g)
           (equal (ord (a* a p g)
	               (g* a p g))
	          (max-ord g)))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (power-a-e order-quotient-c$ elt-of-ord-p-quotient
		        (:instance divides-leq (x (ord (a* a p g) (g* a p g)))
			                       (y (max-ord g)))
		        (:instance divides-leq (y (ord (a* a p g) (g* a p g)))
			                       (x (max-ord g)))
                        (:instance divides-ord-lcoset-max-ord (x (a* a p g)))
			(:instance member-lcoset-qlist-iff (x (a* a p g)) (h (c$ a p g)))
			(:instance member-lcoset-cosets (x a) (h (c$ a p g)))))))

(defthmd max-ord-quotient
  (implies (phyp a p g)
           (equal (max-ord (g* a p g))
	          (max-ord g)))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (order-quotient-c$ elt-of-ord-p-quotient ord-lcoset-a
		        (:instance elt-of-ord-max-ord (g (g* a p g)) (x (a* a p g)))
			(:instance elt-of-ord-ord (n (max-ord (g* a p g))) (g (g* a p g)))
			(:instance divides-ord-lcoset-max-ord (x (elt-of-ord (max-ord (g* a p g)) (g* a p g))))
			(:instance divides-leq (x (max-ord (g* a p g))) (y (max-ord g)))))))

(local-defthmd quotient-c$-smaller
  (implies (phyp a p g)
           (and (natp (order g))
                (natp (order (g* a p g)))
	        (< (order (g* a p g))
	           (order g))))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (elt-of-ord-p-quotient order-quotient-c$ primep-p))))

(defund g2 (a p g)
  (declare (xargs :measure (order g) :hints (("Goal" :use (quotient-c$-smaller)))))
  (if (phyp a p g)
      (if (cyclicp (g* a p g))
          (c$ a p g)
        (lift (g2 (a* a p g)
                   p
	           (g* a p g))
              (c$ a p g)
   	      g))
    ()))

(defund desired-properties (g g1 g2)
  (and (subgroupp g1 g)
       (cyclicp g1)
       (subgroupp g2 g)
       ;(<= (max-ord g2) (order g1))
       (equal (* (order g1) (order g2))
              (order g))
       (equal (group-intersection g1 g2 g)
              (trivial-subgroup g))))
	      
;; Then g2 is easily shown to satisfy the requirements of the lemma:
;;   (1) By lift-order, (order g2) = p * (order g2') = p^(n-k}.
;;   (2) If r is in both g1 and g2, then (lcoset r c g) is in both g1' and g2', which implies r is in c.
;;       But then r is in both g1 and c, which implies r = e.

(local-defthmd factor-p-group-base-case
  (implies (and (phyp a p g)
                (cyclicp (g* a p g)))
	   (desired-properties g (g1 a g) (g2 a p g)))
  :hints (("Goal" :in-theory (enable desired-properties g1 g2 phyp)
                  :use (order-quotient-c$ order-g1 g1-int-c$ max-ord-quotient p-divides-max-ord
		        (:instance divides-leq (x p) (y (max-ord g)))
		        (:instance max-ord<=order (g (g2 a p g)))
			(:instance max-ord-cyclicp (g (g* a p g)))
			(:instance max-ord-cyclicp (g (g1 a g)))))))

(local-defthmd factor-p-group-induction-case-1
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g))))
	   (phyp (a* a p g) p (g* a p g)))
  :hints (("Goal" :in-theory (enable p-groupp phyp)
                  :use (order-quotient-c$ ord-lcoset-a max-ord-quotient
		        (:instance powerp-divides (m (order (g* a p g))) (n (order g)))))))

(local-defthmd factor-p-group-induction-case-2
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
	        (desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g))))
	   (and (subgroupp (g1 a g) g)
	        (cyclicp (g1 a g))
		(subgroupp (g2 a p g) g)))
  :hints (("Goal" :in-theory (enable phyp g1 g2 desired-properties)
                  :use (elt-of-ord-p-quotient order-quotient-c$))))

(local-defthmd factor-p-group-induction-case-3
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
	        (desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g))))
           (equal (order (g1 (a* a p g) (g* a p g)))
	          (order (g1 a g))))
  :hints (("Goal" :in-theory (enable desired-properties phyp g1)
                  :use (factor-p-group-induction-case-1 max-ord-quotient
		        (:instance max-ord-cyclicp (g (g1 a g)))
		        (:instance max-ord-cyclicp (g (g1 (a* a p g) (g* a p g))))))))

(local-defthmd factor-p-group-induction-case-4
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
	        (desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g))))
           (equal (* (order (g1 a g)) (order (g2 a p g)))
	          (order g)))
  :hints (("Goal" :in-theory (enable phyp g1 g2 desired-properties)
                  :use (order-quotient-c$ factor-p-group-induction-case-3 primep-p
		        (:instance lift-order (h (g2 (a* a p g) p (g* a p g)))
			                      (n (c$ a p g)))))))

(local-defthmd factor-p-group-induction-case-5
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
		(desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g)))
	        (in x g))
	   (iff (in x (g2 a p g))
	        (in (lcoset x (c$ a p g) g) (g2 (a* a p g) p (g* a p g)))))
  :hints (("Goal" :in-theory (enable desired-properties g2 phyp)
                  :use (factor-p-group-induction-case-1 order-quotient-c$
		        (:instance in-lift-subgroup-iff (n (c$ a p g)) (h (g2 (a* a p g) p (g* a p g))))))))

(local-defthmd factor-p-group-induction-case-6
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
		(in x (g1 a g)))
	   (equal (power (lcoset a (c$ a p g) g) (index x (powers a g)) (g* a p g))
	          (lcoset x (c$ a p g) g)))
  :hints (("Goal" :in-theory (enable g1 phyp)
                  :use (member-powers-power order-quotient-c$
		        (:instance member-lcoset-qlist-iff (x (lcoset x (c$ a p g) g)) (h (c$ a p g)))
			(:instance member-lcoset-cosets (h (c$ a p g)))
			(:instance member-self-lcoset (x a) (h (c$ a p g)))			
		        (:instance power-lcoset (x (lcoset a (c$ a p g) g))
			                        (h (c$ a p g))
						(n (index x (powers a g))))))))

(local-defthmd factor-p-group-induction-case-7
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
		(in x (g1 a g)))
	   (in (lcoset x (c$ a p g) g)
	       (g1 (a* a p g) (g* a p g))))
  :hints (("Goal" :in-theory (enable g1 phyp)
                  :use (factor-p-group-induction-case-6 order-quotient-c$))))

(local-defthmd factor-p-group-induction-case-8
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
		(desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g)))
		(SUBGROUPP (G1 (LCOSET A (CYCLIC (Y$ A P G) G) G)
                                (QUOTIENT G (CYCLIC (Y$ A P G) G)))
                           (QUOTIENT G (CYCLIC (Y$ A P G) G)))
		(SUBGROUPP (G2 (LCOSET A (CYCLIC (Y$ A P G) G) G)
                                P (QUOTIENT G (CYCLIC (Y$ A P G) G)))
                           (QUOTIENT G (CYCLIC (Y$ A P G) G)))
	        (in x (group-intersection (g1 a g) (g2 a p g) g)))
	   (in (lcoset x (c$ a p g) g)
	       (group-intersection (g1 (a* a p g) (g* a p g))
	                           (g2 (a* a p g) p (g* a p g))
				   (g* a p g))))
  :hints (("Goal" :in-theory (enable phyp)
                  :use ( factor-p-group-induction-case-2 factor-p-group-induction-case-5 factor-p-group-induction-case-7))))

(local-defthmd factor-p-group-induction-case-9
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
		(desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g)))
	        (in x (group-intersection (g1 a g) (g2 a p g) g)))
	   (equal (lcoset x (c$ a p g) g)
	          (lcoset (e g) (c$ a p g) g)))
  :hints (("Goal" :in-theory (enable phyp quotient-e desired-properties)
                  :use (order-quotient-c$ factor-p-group-induction-case-8))))

(local-defthmd factor-p-group-induction-case-10
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
		(desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g)))
	        (in x (group-intersection (g1 a g) (g2 a p g) g)))
	   (in x (group-intersection (g1 a g) (c$ a p g) g)))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (order-quotient-c$ factor-p-group-induction-case-2 factor-p-group-induction-case-9
		        (:instance equal-lcoset-lcoset-e (h (c$ a p g)))))))

(local-defthmd factor-p-group-induction-case-11
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
		(desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g)))
	        (in x (group-intersection (g1 a g) (g2 a p g) g)))
	   (equal (e g) x))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (g1-int-c$ order-quotient-c$ factor-p-group-induction-case-2 factor-p-group-induction-case-10))))

(local-defthmd factor-p-group-induction-case-12
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g)))
		(desired-properties (g* a p g)
                                    (g1 (a* a p g) (g* a p g))
				    (g2 (a* a p g) p (g* a p g))))
	   (equal (group-intersection (g1 a g) (g2 a p g) g)
	          (trivial-subgroup g)))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (g1-int-c$ order-quotient-c$ factor-p-group-induction-case-2
		        (:instance factor-p-group-induction-case-11 (x (cadr (elts (group-intersection (g1 a g) (g2 a p g) g)))))
			(:instance not-trivial-elt (h (group-intersection (g1 a g) (g2 a p g) g)))))))

(local-defthmd factor-p-group-induction-case
  (implies (and (phyp a p g)
                (not (cyclicp (g* a p g))))
	   (and (phyp (a* a p g) p (g* a p g))
	        (implies (desired-properties (g* a p g) (g1 (a* a p g) (g* a p g)) (g2 (a* a p g) p (g* a p g)))
	                 (desired-properties g (g1 a g) (g2 a p g)))))
  :hints (("Goal" :expand ((desired-properties g (g1 a g) (g2 a p g)))
                  :use (factor-p-group-induction-case-1 factor-p-group-induction-case-2 factor-p-group-induction-case-4
		        factor-p-group-induction-case-12))))

(defthmd factor-p-group
  (implies (phyp a p g)
	   (desired-properties g (g1 a g) (g2 a p g)))
  :hints (("Goal" :in-theory (enable g2)
                  :induct (g2 a p g))
          ("Subgoal *1/2" :use (factor-p-group-induction-case))
          ("Subgoal *1/1" :use (factor-p-group-base-case))))

;; Applying factor-p-group recursively, we can represent an abelian p-group as an internal direct product
;; of a list of cyclic subgroups:

(local-defthmd g2-smaller-1
  (implies (phyp a p g)
           (and (natp (order g))
	        (natp (order (g2 a p g)))
		(> (order (g2 a p g)) 1)
	        (< (order (g2 a p g)) (order g))))
  :hints (("Goal" :in-theory (enable phyp desired-properties)
                  :use (primep-p order-g1 factor-p-group))))

(local-defthmd g2-smaller-2
  (implies (and (p-groupp g p) (abelianp g) (> (order g) 1) (not (cyclicp g)))
           (phyp (elt-of-ord (max-ord g) g) p g))
  :hints (("Goal" :in-theory (enable phyp)
                  :use (elt-of-ord-max-ord
		        (:instance elt-of-ord-ord (n (max-ord g)))))))

(local-defthmd g2-smaller
  (implies (and (p-groupp g p) (abelianp g) (> (order g) 1) (not (cyclicp g)))
           (let ((a (elt-of-ord (max-ord g) g)))
             (and (natp (order g))
	          (natp (order (g2 a p g)))
		  (> (order (g2 a p g)) 1)
	          (< (order (g2 a p g)) (order g)))))
  :hints (("Goal" :use (g2-smaller-2
                        (:instance g2-smaller-1 (a (elt-of-ord (max-ord g) g)))))))

(defun cyclic-p-subgroup-list (p g)
  (declare (xargs :measure (order g) :hints (("Goal" :use (g2-smaller)))))
  (if (and (p-groupp g p) (abelianp g) (> (order g) 1))
      (if (cyclicp g)
          (list g)
        (let ((a (elt-of-ord (max-ord g) g)))
          (cons (g1 a g)
                (cyclic-p-subgroup-list p (g2 a p g)))))
    ()))

(defund cyclic-p-group-p (g)
  (and (cyclicp g)
       (> (order g) 1)
       (p-groupp g (least-prime-divisor (order g)))))

(defun cyclic-p-group-list-p (l)
  (if (consp l)
      (and (cyclic-p-group-p (car l))
	   (cyclic-p-group-list-p (cdr l)))
    (null l)))

(local-defthmd product-group-subgroup-1
  (implies (and (subgroupp h g)
                (subgroupp k0 h)
		(subgroupp k1 h)
		(subgroupp k2 k1)
	        (member-equal x (products k0 k2 g)))
	   (member-equal x (products k0 k1 h)))
  :hints (("Goal" :in-theory (disable subgroup-op)
                  :use ((:instance product-in-products-converse (h k0) (k k2))
                        (:instance subgroupp-transitive (h k0) (k h))
			(:instance subgroupp-transitive (h k2) (k k1) (g h))
			(:instance subgroupp-transitive (h k2) (k h))
			(:instance subgroup-op (x (car (factor-elt x k0 k2 g))) (y (cadr (factor-elt x k0 k2 g))))
			(:instance product-in-products (x (car (factor-elt x k0 k2 g)))
			                               (y (cadr (factor-elt x k0 k2 g)))
						       (h k0)
						       (k k1)
						       (g h))))))

(local-defthmd product-group-subgroup
  (implies (and (abelianp g)
                (subgroupp h g)
                (subgroupp k0 h)
		(subgroupp k1 h)
		(subgroupp k2 k1))
	   (subgroupp (product-group k0 k2 g)
	              (product-group k0 k1 h)))
  :hints (("Goal" :use ((:instance scex1-lemma (l (products k0 k2 g)) (m (products k0 k1 h)))
                        (:instance product-group-subgroup-1 (x (scex1 (products k0 k2 g) (products k0 k1 h))))
			(:instance subgroupp-transitive (h (product-group k0 k1 h)) (k h))
                        (:instance subgroupp-transitive (h k0) (k h))
			(:instance subgroupp-transitive (h k2) (k k1) (g h))
			(:instance subgroupp-transitive (h k2) (k h))
			(:instance normalp-product-group (h k0) (k k2))
			(:instance normalp-product-group (h k0) (k k1) (g h))
			(:instance subgroup-subgroup (h (product-group k0 k2 g)) (k (product-group k0 k1 h)))))))

(local-defthmd internal-direct-product-subgroup-1
  (implies (and (abelianp g)
                (subgroupp h g)
		(internal-direct-product-p l h))
	   (subgroupp (product-group-list l g)
	              (product-group-list l h)))
  :hints (("Subgoal *1/2" :use ((:instance product-group-subgroup (k0 (car l))
                                                                  (k1 (product-group-list (cdr l) h))
                                                                  (k2 (product-group-list (cdr l) g)))))
	  ("Subgoal *1/3" :use ((:instance subgroup-subgroup (h (trivial-subgroup g)) (k (trivial-subgroup h)))
	                        (:instance subgroupp-transitive (h (trivial-subgroup h)) (k h))))))
		      
(local-defthmd internal-direct-product-subgroup-2
  (implies (and (abelianp g)
                (subgroupp h g)
		(subgroupp k0 h)
		(subgroupp k1 h)
		(subgroupp k2 k1)
		(in x (group-intersection k0 k2 g)))
	   (in x (group-intersection k0 k1 h)))	   
  :hints (("Goal" :use ((:instance subgroupp-transitive (h k0) (k h))
			(:instance subgroupp-transitive (h k2) (k k1) (g h))
			(:instance subgroupp-transitive (h k2) (k h))))))

(local-defthmd internal-direct-product-subgroup-3
  (implies (and (abelianp g)
                (subgroupp h g)
		(subgroupp k0 h)
		(subgroupp k1 h)
		(subgroupp k2 k1)
		(equal (group-intersection k0 k1 h) (trivial-subgroup h)))
	   (equal (group-intersection k0 k2 g) (trivial-subgroup g)))
  :hints (("Goal" :use ((:instance not-trivial-elt (h (group-intersection k0 k2 g)))
                        (:instance iff-trivial-order-1 (h (group-intersection k0 k1 h)) (g h))
			(:instance internal-direct-product-subgroup-2 (x (cadr (INTERSECTION-EQUAL (CAR K0) (CAR K2)))))
                        (:instance subgroupp-transitive (h k0) (k h))
			(:instance subgroupp-transitive (h k2) (k k1) (g h))
			(:instance subgroupp-transitive (h k2) (k h))))))

(defthmd internal-direct-product-subgroup
  (implies (and (abelianp g)
                (subgroupp h g)
		(internal-direct-product-p l h))
	   (internal-direct-product-p l g))	   
  :hints (("Subgoal *1/2" :use ((:instance subgroupp-transitive (h (car l)) (k h))
                                (:instance internal-direct-product-subgroup-3 (k0 (car l))
				                                              (k1 (PRODUCT-GROUP-LIST (CDR L) H))
				                                              (k2 (PRODUCT-GROUP-LIST (CDR L) g)))
				(:instance internal-direct-product-subgroup-1 (l (cdr l)))))))

(local-defthmd p-group-factorization-base-case
  (implies (and (p-groupp g p) (abelianp g) (> (order g) 1) (cyclicp g))
           (let ((l (cyclic-p-subgroup-list p g)))
	     (and (consp l)
	          (cyclic-p-group-list-p l)
	          (internal-direct-product-p l g)
		  (equal (order g) (product-orders l)))))
  :hints (("Goal" :in-theory (enable p-groupp cyclic-p-group-p cyclic-p-group-list-p)
                  :use ((:instance least-prime-divisor-powerp (n (order g)))))))

(local-defthm p-group-factorization-induction-case-1
  (let ((a (elt-of-ord (max-ord g) g)))
    (implies (and (p-groupp g p) (abelianp g) (> (order g) 1) (not (cyclicp g)))
	     (cyclic-p-group-p (g1 a g))))
  :hints (("Goal" :in-theory (enable p-groupp cyclic-p-group-p)
                  :use (g2-smaller-2 primep-p
		        (:instance least-prime-divisor-powerp (n (order (g1 (elt-of-ord (max-ord g) g) g))))
			(:instance order-g1 (a (elt-of-ord (max-ord g) g)))))))

(local-defthmd p-group-factorization-induction-case-3
  (implies (and (abelianp g)
                (subgroupp h g)
		(internal-direct-product-p l h))
	   (subgroupp (product-group-list l g) h))
  :hints (("Goal" :use (internal-direct-product-subgroup-1
                        (:instance subgroupp-transitive (h (product-group-list l g)) (k (product-group-list l h)) (g h))))))

(local-defthmd p-group-factorization-induction-case-4
  (let ((l (cyclic-p-subgroup-list p g))
        (g2 (g2 (elt-of-ord (max-ord g) g) p g)))
    (implies (and (p-groupp g p) (abelianp g) (> (order g) 1) (not (cyclicp g))
	          (internal-direct-product-p (cdr l) g2))
	     (internal-direct-product-p l g)))
  :hints (("Goal" :in-theory (enable desired-properties)
                  :use (g2-smaller-2
		        (:instance factor-p-group (a (elt-of-ord (max-ord g) g)))
		        (:instance internal-direct-product-subgroup (l (cdr (cyclic-p-subgroup-list p g)))
			                                            (h (g2 (elt-of-ord (max-ord g) g) p g)))
			(:instance p-group-factorization-induction-case-3 (h (g2 (ELT-OF-ORD (MAX-ORD G) G) P G))
			                                                  (l (cdr (cyclic-p-subgroup-list p g))))
			(:instance internal-direct-product-subgroup-3
			  (h g)
			  (k0 (G1 (ELT-OF-ORD (MAX-ORD G) G) G))
			  (k1 (G2 (ELT-OF-ORD (MAX-ORD G) G) P G))
			  (k2 (PRODUCT-GROUP-LIST (CYCLIC-P-SUBGROUP-LIST P (G2 (ELT-OF-ORD (MAX-ORD G) G) P G)) G)))))))

(local-defthmd p-group-factorization-induction-case-5
  (let ((l (cyclic-p-subgroup-list p g))
        (g2 (g2 (elt-of-ord (max-ord g) g) p g)))
    (implies (and (p-groupp g p) (abelianp g) (> (order g) 1) (not (cyclicp g))
	          (consp (cdr l))
	          (cyclic-p-group-list-p (cdr l))
	          (internal-direct-product-p (cdr l) g2)
		  (equal (order g2) (product-orders (cdr l))))
	     (equal (order g) (product-orders l))))
  :hints (("Goal" :in-theory (enable desired-properties)
                  :use (g2-smaller-2
		        (:instance factor-p-group (a (elt-of-ord (max-ord g) g)))))))

(local-defthmd p-group-factorization-induction-case
  (let ((l (cyclic-p-subgroup-list p g))
        (g2 (g2 (elt-of-ord (max-ord g) g) p g)))
    (implies (and (p-groupp g p) (abelianp g) (> (order g) 1) (not (cyclicp g))
	          (consp (cdr l))
	          (cyclic-p-group-list-p (cdr l))
	          (internal-direct-product-p (cdr l) g2)
		  (equal (order g2) (product-orders (cdr l))))
	     (and (consp l)
	          (cyclic-p-group-list-p l)
	          (internal-direct-product-p l g)
		  (equal (order g) (product-orders l)))))
  :hints (("Goal" :use (p-group-factorization-induction-case-1
                        p-group-factorization-induction-case-4
			p-group-factorization-induction-case-5))))

(defthmd p-group-factorization
  (implies (and (p-groupp g p) (abelianp g) (> (order g) 1))
           (let ((l (cyclic-p-subgroup-list p g)))
	     (and (consp l)
	          (cyclic-p-group-list-p l)
	          (internal-direct-product-p l g)
		  (equal (order g) (product-orders l)))))
  :hints (("Subgoal *1/2" :in-theory (enable p-groupp desired-properties)
                          :use (g2-smaller-2 g2-smaller p-group-factorization-induction-case
			        (:instance powerp-divides (m (order (g2 (elt-of-ord (max-ord g) g) p g))) (n (order g)))
		                (:instance factor-p-group (a (elt-of-ord (max-ord g) g)))))
	  ("Subgoal *1/1" :use (p-group-factorization-base-case))))


;;-------------------------------------------------------------------------------------------------------
;; Factorization of an Abelian Group
;;-------------------------------------------------------------------------------------------------------

; The ordered list of all elements of g with order dividing m:

(defun elts-of-ord-dividing-aux (m l g)
  (if (consp l)
      (if (divides (ord (car l) g) m)
	  (cons (car l) (elts-of-ord-dividing-aux m (cdr l) g))
	(elts-of-ord-dividing-aux m (cdr l) g))
    ()))

(defund elts-of-ord-dividing (m g)
  (elts-of-ord-dividing-aux m (elts g) g))

(local-defthm elts-of-ord-dividing-aux-elts
  (implies (and (groupp g)
		(posp m)
		(sublistp l (elts g))
		(member x l))
	   (iff (member x (elts-of-ord-dividing-aux m l g))
		(divides (ord x g) m))))

(local-defthm sublistp-elts-of-ord-dividing-aux
  (implies (and (groupp g)
		(posp m)
		(dlistp l)
		(sublistp l (elts g)))
	   (and (dlistp (elts-of-ord-dividing-aux m l g))
		(sublistp (elts-of-ord-dividing-aux m l g) l))))

(local-defthm car-elts-of-ord-dividing-aux
  (implies (and (groupp g)
		(posp m)
		(sublistp l (elts g))
		(equal (car l) (e g)))
	   (equal (car (elts-of-ord-dividing-aux m l g))
		  (e g)))
  :hints (("Subgoal *1/2" :use ((:instance ord>1 (a (e g)))))))

(local-defthm consp-elts-of-ord-dividing-aux
  (implies (and (groupp g)
		(posp m)
		(consp l)
		(sublistp l (elts g))
		(equal (car l) (e g)))
	   (consp (elts-of-ord-dividing-aux m l g)))
  :hints (("Goal" :use ((:instance ord>1 (a (e g)))))))

(local-defthmd elts-of-ord-dividing-elts
  (implies (and (groupp g)
		(posp m)
		(in x g))
	   (iff (member x (elts-of-ord-dividing m g))
		(divides (ord x g) m)))
  :hints (("Goal" :in-theory (enable elts-of-ord-dividing))))

(local-defthm sublistp-elts-of-ord-dividing
  (implies (and (groupp g)
		(posp m))
	   (and (dlistp (elts-of-ord-dividing m g))
		(sublistp (elts-of-ord-dividing m g) (elts g))))
  :hints (("Goal" :in-theory (enable elts-of-ord-dividing))))

(local-defthm car-elts-of-ord-dividing
  (implies (and (groupp g)
		(posp m))
	   (equal (car (elts-of-ord-dividing m g))
		  (e g)))
  :hints (("Goal" :in-theory (enable e elts-of-ord-dividing))))

(local-defthm consp-elts-of-ord-dividing
  (implies (and (groupp g)
		(posp m))
	   (consp (elts-of-ord-dividing m g)))
  :hints (("Goal" :in-theory (enable e elts-of-ord-dividing))))

(local-defthm elts-of-ord-dividing-closed
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(member-equal x (elts-of-ord-dividing m g))
		(member-equal y (elts-of-ord-dividing m g)))
	   (member-equal (op x y g) (elts-of-ord-dividing m g)))
  :hints (("Goal" :use (ord-divides-lcm elts-of-ord-dividing-elts
                        (:instance ord>1 (a x))
                        (:instance ord>1 (a y))
                        (:instance ord>1 (a (op x y g)))
                        (:instance elts-of-ord-dividing-elts (x y))
			(:instance elts-of-ord-dividing-elts (x (op x y g)))
			(:instance lcm-is-least (x (ord x g)) (y (ord y g)))
			(:instance divides-transitive (x (ord (op x y g) g)) (y (lcm (ord x g) (ord y g))) (z m))))))

(local-defthm elts-of-ord-dividing-inv
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(member-equal x (elts-of-ord-dividing m g)))
	   (member-equal (inv x g) (elts-of-ord-dividing m g)))
  :hints (("Goal" :use (elts-of-ord-dividing-elts ord-inv
                        (:instance ord>1 (a x))
			(:instance elts-of-ord-dividing-elts (x (inv x g)))))))
			
(in-theory (disable group-abelianp))

;; If g is abelian, then these elements form a subgroup of g:

(defsubgroup subgroup-ord-dividing (k) g
  (and (abelianp g) (posp k))
  (elts-of-ord-dividing k g))

;; Suppose (order g) = mn, where m and n are relatively prime. Let h = (subgroup-ord-dividing m g) and
;; k = (subgroup-ord-dividing n g).  If x is in h and k, then (ord x) | m and (ord x) | n implies
;; (ord x) | gcd(m, n) = 1, and therefore x = e.  That is, h and k intersect trivially:

(local-defthmd rel-prime-factors-intersection-1
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
	        (in x  (subgroup-ord-dividing m g))
		(in x (subgroup-ord-dividing n g)))
	     (equal (e g) x))
  :hints (("Goal" :use (elts-of-ord-dividing-elts
                        (:instance elts-of-ord-dividing-elts (m n))
			(:instance ord>1 (a x))
			(:instance divides-gcd (x m) (y n) (d (ord x g)))))))

(defthmd rel-prime-factors-intersection
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1))
	   (let ((h (subgroup-ord-dividing m g))
		 (k (subgroup-ord-dividing n g)))
	     (equal (group-intersection h k g)
		    (trivial-subgroup g))))
  :hints (("Goal" :use ((:instance rel-prime-factors-intersection-1
                                    (x (cadr (elts (group-intersection (subgroup-ord-dividing m g) (subgroup-ord-dividing n g) g)))))
                        (:instance not-trivial-elt (h (group-intersection (subgroup-ord-dividing m g) (subgroup-ord-dividing n g) g)))))))

;; Since gcd(m, n) = 1, there exist r and s such that 1 = rn + sm.  Let x be in g.  Then x = x^(rn)x^(sm),
;; where (x^(rn)^m = x^(rmn) = e and (x^(sm))^n = x^(smn) = e, i.e., x^{rn) is in h and x^(sm) is in k, 
;; and therefore x is in (products h k g).  By len-products, the order of g is the product of the orders
;; of h and k:

(local-defthmd rel-prime-factors-product-1
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n)))
	   (let ((h (subgroup-ord-dividing m g))
		 (k (subgroup-ord-dividing n g)))
	     (and (divides (order h) (order g))
	          (divides (order k) (order g)))))
  :hints (("Goal" :use ((:instance order-subgroup-divides (h (subgroup-ord-dividing m g)))
                        (:instance order-subgroup-divides (h (subgroup-ord-dividing n g)))))))

(local-defthmd rel-prime-factors-product-2
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g)
		(>= (r m n) 0)
		(<= (s m n) 0))
	   (equal (op (power x (* (r m n) m) g)
	              (power (inv x g) (- (* (s m n) n)) g)
		      g)
		  x))
  :hints (("Goal" :use ((:instance gcd-linear-combination (x m) (y n))
                        (:instance power- (a x) (n  (* (r m n) m)) (m (- (* (s m n) n))))))))

(local-defthmd rel-prime-factors-product-3
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g)
		(>= (r m n) 0)
		(<= (s m n) 0))
	   (member-equal (power x (* (r m n) m) g)
	                 (elts-of-ord-dividing n g)))
  :hints (("Goal" :in-theory (disable divides-ord)
                  :use (ord-divides-order
                        (:instance elts-of-ord-dividing-elts (x (power x (* (r m n) m) g)) (m n))
                        (:instance power* (a x) (n (* (r m n) m)) (m n))
			(:instance power* (a x) (n (* n m)) (m (r m n)))
			(:instance divides-ord (a x) (n (order g)))
			(:instance divides-ord (a (power x (* m (r m n)) g)))))))

(local-defthmd rel-prime-factors-product-4
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g)
		(>= (r m n) 0)
		(<= (s m n) 0))
	   (member-equal (power (inv x g) (- (* (s m n) n)) g)
	                 (elts-of-ord-dividing m g)))
  :hints (("Goal" :in-theory (disable divides-ord)
                  :use (ord-divides-order ord-inv
                        (:instance elts-of-ord-dividing-elts (x (power (inv x g) (- (* (s m n) n)) g)))
                        (:instance power* (a (inv x g)) (n (* (- (s m n)) n)))
			(:instance power* (a (inv x g)) (n (* n m)) (m (- (s m n))))
			(:instance divides-ord (a (inv x g)) (n (order g)))
			(:instance divides-ord (a (power (inv x g) (* n (- (s m n))) g)) (n m))))))

(local-defthmd rel-prime-factors-product-5
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g)
		(>= (r m n) 0)
		(<= (s m n) 0))
	   (member-equal x (products (subgroup-ord-dividing m g) (subgroup-ord-dividing n g) g)))
  :hints (("Goal" :in-theory (enable group-abelianp)
                  :use (rel-prime-factors-product-2 rel-prime-factors-product-3 rel-prime-factors-product-4
                        (:instance product-in-products (h (subgroup-ord-dividing m g)) (k (subgroup-ord-dividing n g))
			                               (x (power (inv x g) (- (* (s m n) n)) g))
						       (y (power x (* (r m n) m) g)))))))

(local-defthmd rel-prime-factors-product-6
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g)
		(<= (r m n) 0)
		(>= (s m n) 0))
	   (equal (op (power x (* (s m n) n) g)
	              (power (inv x g) (- (* (r m n) m)) g)
		      g)
		  x))
  :hints (("Goal" :use ((:instance gcd-linear-combination (x m) (y n))
                        (:instance power- (a x) (n (* (s m n) n)) (m (- (* (r m n) m))))))))

(local-defthmd rel-prime-factors-product-7
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g)
		(<= (r m n) 0)
		(>= (s m n) 0))
	   (member-equal (power x (* (s m n) n) g)
	                 (elts-of-ord-dividing m g)))
  :hints (("Goal" :in-theory (disable divides-ord)
                  :use (ord-divides-order
                        (:instance elts-of-ord-dividing-elts (x (power x (* (s m n) n) g)))
                        (:instance power* (a x) (n (* (s m n) n)))
			(:instance power* (a x) (n (* n m)) (m (s m n)))
			(:instance divides-ord (a x) (n (order g)))
			(:instance divides-ord (a (power x (* n (s m n)) g)) (n m))))))

(local-defthmd rel-prime-factors-product-8
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g)
		(<= (r m n) 0)
		(>= (s m n) 0))
	   (member-equal (power (inv x g) (- (* (r m n) m)) g)
	                 (elts-of-ord-dividing n g)))
  :hints (("Goal" :in-theory (disable divides-ord)
                  :use (ord-divides-order ord-inv
                        (:instance elts-of-ord-dividing-elts (x (power (inv x g) (- (* (r m n) m)) g)) (m n))
                        (:instance power* (a (inv x g)) (n (* (- (r m n)) m)) (m n))
			(:instance power* (a (inv x g)) (n (* n m)) (m (- (r m n))))
			(:instance divides-ord (a (inv x g)) (n (order g)))
			(:instance divides-ord (a (power (inv x g) (* m (- (r m n))) g)))))))

(local-defthmd rel-prime-factors-product-9
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g)
		(<= (r m n) 0)
		(>= (s m n) 0))
	   (member-equal x (products (subgroup-ord-dividing m g) (subgroup-ord-dividing n g) g)))
  :hints (("Goal" :in-theory (enable group-abelianp)
                  :use (rel-prime-factors-product-6 rel-prime-factors-product-7 rel-prime-factors-product-8
                        (:instance product-in-products (h (subgroup-ord-dividing m g)) (k (subgroup-ord-dividing n g))
			                               (y (power (inv x g) (- (* (r m n) m)) g))
						       (x (power x (* (s m n) n) g)))))))

(local-defthmd rel-prime-factors-product-10
  (implies (and (posp m)
		(posp n)
		(= (gcd m n) 1))
	   (or (and (>= (r m n) 0)
		    (<= (s m n) 0))
	       (and (<= (r m n) 0)
		    (>= (s m n) 0))))
  :hints (("Goal" :use ((:instance gcd-linear-combination (x m) (y n))))))

(local-defthmd rel-prime-factors-product-11
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n))
		(in x g))
	   (member-equal x (products (subgroup-ord-dividing m g) (subgroup-ord-dividing n g) g)))
  :hints (("Goal" :use (rel-prime-factors-product-5 rel-prime-factors-product-9 rel-prime-factors-product-10))))

(local-defthmd rel-prime-factors-product-12
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n)))
	   (sublistp (elts g)
	             (products (subgroup-ord-dividing m g)
		               (subgroup-ord-dividing n g)
			       g)))
  :hints (("Goal" :use ((:instance rel-prime-factors-product-11
                                    (x (scex1 (elts g) (products (subgroup-ord-dividing m g) (subgroup-ord-dividing n g) g))))
		        (:instance scex1-lemma (l (elts g)) (m (products (subgroup-ord-dividing m g) (subgroup-ord-dividing n g) g)))))))

(local-defthmd rel-prime-factors-product-13
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n)))
	   (permp (elts g)
	          (products (subgroup-ord-dividing m g)
		            (subgroup-ord-dividing n g)
		            g)))
  :hints (("Goal" :in-theory (enable permp)
                  :use (rel-prime-factors-product-12))))

(defthmd rel-prime-factors-product
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n)))
	   (let ((h (subgroup-ord-dividing m g))
		 (k (subgroup-ord-dividing n g)))
	     (equal (* (order h) (order k))
		    (order g))))
  :hints (("Goal" :use (rel-prime-factors-product-13 rel-prime-factors-intersection
                        (:instance len-products (h (subgroup-ord-dividing m g)) (k (subgroup-ord-dividing n g)))
			(:instance eq-len-permp (l (elts g))
			                        (m (products (subgroup-ord-dividing m g) (subgroup-ord-dividing n g) g)))))))


;; If p is a prime dividing (order h), then by cauchy, h has an element of order p, and therefore p | m,
;; which implies p does not divide n.  By lagrange and divides-product-divides-factor, (order h) | m,  
;; and therefore (order h) <= m.  Similarly, (order k) <= n.  If either inequality were strict, then
;; (order h) * (order k) < mn, contradicting rel-prime-factors-product.  Thus, both equalities must hold:

(local-defthmd rel-prime-factors-orders-1
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n)))
	   (let ((h (subgroup-ord-dividing m g)))
	     (implies (and (primep p)
	                   (divides p (order h)))
		      (not (divides p n)))))
  :hints (("Goal" :use ((:instance cauchy (g (subgroup-ord-dividing m g)))
                        (:instance elts-of-ord-dividing-elts (x (elt-of-ord p (subgroup-ord-dividing m g))))
			(:instance divides-gcd (d p) (x m) (y n))
			(:instance equal-ord-subgroup (a (elt-of-ord p (subgroup-ord-dividing m g)))
			                              (h  (subgroup-ord-dividing m g)))))))

(local-defthmd rel-prime-factors-orders-2
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n)))
	   (let ((h (subgroup-ord-dividing m g)))
	     (equal (gcd (order h) n) 1)))
  :hints (("Goal" :use ((:instance rel-prime-factors-orders-1 (p (least-prime-divisor (gcd (order (subgroup-ord-dividing m g)) n))))
                        (:instance primep-least-divisor (n (gcd (order (subgroup-ord-dividing m g)) n)))
			(:instance least-divisor-divides (k 2) (n (gcd (order  (subgroup-ord-dividing m g)) n)))
			(:instance gcd-divides (x (order (subgroup-ord-dividing m g))) (y n))
			(:instance divides-transitive (x (least-prime-divisor (gcd (order (subgroup-ord-dividing m g)) n)))
			                              (y (gcd (order (subgroup-ord-dividing m g)) n))
						      (z n))
			(:instance divides-transitive (x (least-prime-divisor (gcd (order (subgroup-ord-dividing m g)) n)))
			                              (y (gcd (order (subgroup-ord-dividing m g)) n))
						      (z (order (subgroup-ord-dividing m g))))
			(:instance order-pos (g (subgroup-ord-dividing m g)))
			(:instance gcd-pos (x (order (subgroup-ord-dividing m g))) (y n))))))

(local-defthmd rel-prime-factors-orders-3
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n)))
	   (let ((h (subgroup-ord-dividing m g)))
	     (divides (order h) m)))
  :hints (("Goal" :use (rel-prime-factors-product-1 rel-prime-factors-orders-2
                        (:instance divides-product-divides-factor (d (order (subgroup-ord-dividing m g))) (m n) (n m))))))

(defthmd rel-prime-factors-orders
  (implies (and (groupp g)
                (abelianp g)
		(posp m)
		(posp n)
		(= (gcd m n) 1)
		(= (order g) (* m n)))
	   (let ((h (subgroup-ord-dividing m g))
		 (k (subgroup-ord-dividing n g)))
	     (and (equal (order h) m)
		  (equal (order k) n))))
  :hints (("Goal" :nonlinearp t :use (rel-prime-factors-orders-3 rel-prime-factors-product
                        (:instance rel-prime-factors-orders-3 (m n) (n m))
			(:instance gcd-commutative (x m) (y n))
			(:instance divides-leq (x (order (subgroup-ord-dividing m g))) (y m))
			(:instance divides-leq (x (order (subgroup-ord-dividing n g))) (y n))))))

;; The existence claim of the Fundamental Theorem is proved by combining The following is proved by induction, applying
;; internal-direct-product-append and p-group-factorization.

(defun max-power-dividing (p n)
  (if (and (primep p) (posp n))
      (if (divides p n)
          (* p (max-power-dividing p (/ n p)))
	1)
    0))

(local-defthmd powerp-max-power
  (implies (and (primep p) (posp n) (divides p n))
           (and (powerp (max-power-dividing p n) p)
	        (divides p (max-power-dividing p n))
		(posp (max-power-dividing p n))
		(> (max-power-dividing p n) 1)
	        (posp (/ n (max-power-dividing p n)))
		(< (/ n (max-power-dividing p n)) n)
	        (not (divides p (/ n (max-power-dividing p n)))))))

(defthmd rel-prime-max-power
  (implies (and (primep p) (posp n))
           (equal (gcd (max-power-dividing p n)
	               (/ n (max-power-dividing p n)))
		  1))
  :hints (("Goal" :use (powerp-max-power
                        (:instance primep-least-divisor (n (gcd (max-power-dividing p n) (/ n (max-power-dividing p n)))))
			(:instance least-divisor-divides (k 2) (n (gcd (max-power-dividing p n) (/ n (max-power-dividing p n)))))
			(:instance gcd-divides (x (max-power-dividing p n))
			                       (y (/ n (max-power-dividing p n))))
			(:instance divides-transitive (x (least-prime-divisor (gcd (max-power-dividing p n) (/ n (max-power-dividing p n)))))
			                              (y (gcd (max-power-dividing p n) (/ n (max-power-dividing p n))))
						      (z (max-power-dividing p n)))
			(:instance divides-transitive (x (least-prime-divisor (gcd (max-power-dividing p n) (/ n (max-power-dividing p n)))))
			                              (y (gcd (max-power-dividing p n) (/ n (max-power-dividing p n))))
						      (z (/ n (max-power-dividing p n))))
			(:instance powerp-prime-divisor (n (max-power-dividing p n))
			                                (q (least-prime-divisor (gcd (max-power-dividing p n) (/ n (max-power-dividing p n))))))
			(:instance gcd-pos (x  (max-power-dividing p n)) (y (/ n  (max-power-dividing p n))))))))	               

(local-defthmd cyclic-subgroup-list-wf
  (implies (and (groupp g)
                (abelianp g)
		(not (= (order g) 1)))
	   (< (order (subgroup-ord-dividing (/ (order g) (max-power-dividing (least-prime-divisor (order g)) (order g)))
	                                    g))
	      (order g)))
 :hints (("Goal" :use  (order-pos
                        (:instance powerp-max-power (n (order g)) (p (least-prime-divisor (order g))))
		        (:instance rel-prime-max-power (n (order g)) (p (least-prime-divisor (order g))))
			(:instance least-divisor-divides (k 2) (n (order g)))
			(:instance primep-least-divisor (n (order g)))
                        (:instance rel-prime-factors-orders (m (max-power-dividing (least-prime-divisor (order g)) (order g)))
					                    (n (/ (order g)
							          (max-power-dividing (least-prime-divisor (order g)) (order g)))))))))

(defun cyclic-subgroup-list (g)
  (declare (xargs :measure (order g) :hints (("Goal" :use (cyclic-subgroup-list-wf)))))
  (if (and (groupp g)
           (abelianp g))
      (if (= (order g) 1)
          ()
	(let* ((p (least-prime-divisor (order g)))
	       (m (max-power-dividing p (order g)))
	       (n (/ (order g) m))
	       (h (subgroup-ord-dividing m g))
	       (k (subgroup-ord-dividing n g)))
	  (append (cyclic-p-subgroup-list p h)
	          (cyclic-subgroup-list k))))
    ()))

(local-defthmd idp-cyclic-subgroup-list-1
  (implies (and (groupp g)
                (abelianp g)
		(> (order g) 1))
	   (let* ((p (least-prime-divisor (order g)))
	          (m (max-power-dividing p (order g)))
		  (n (/ (order g) m))
		  (h (subgroup-ord-dividing m g))
		  (k (subgroup-ord-dividing n g))
		  (l (cyclic-p-subgroup-list p h)))
	     (and (posp m)
	          (> m 1)
		  (posp n)
		  (equal (order h) m)
		  (equal (order k) n)
		  (abelianp h)
		  (abelianp k)
		  (equal (gcd m n) 1)
		  (equal (order g) (* m n))
		  (p-groupp h p)
		  (divides p m)
		  (not (divides p n))
	          (cyclic-p-group-list-p l)
	          (internal-direct-product-p l g)
		  (equal (product-orders l) (order h))
		  (subgroupp (product-group-list l g) h))))
  :hints (("Goal" :in-theory (e/d (p-groupp) (abelian-subgroup powerp max-power-dividing))
                  :use ((:instance powerp-max-power (p (least-prime-divisor (order g))) (n (order g)))
                        (:instance primep-least-divisor (n (order g)))
			(:instance rel-prime-max-power (p (least-prime-divisor (order g))) (n (order g)))
			(:instance abelian-subgroup (h (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
			                                                                          (order g))
						                              g)))
			(:instance abelian-subgroup (h (subgroup-ord-dividing (/ (order g)
			                                                         (max-power-dividing (least-prime-divisor (order g))
			                                                                             (order g)))
									      g)))
			(:instance least-divisor-divides (k 2) (n (order g)))
			(:instance rel-prime-factors-orders (m (max-power-dividing (least-prime-divisor (order g)) (order g)))
			                                    (n (/ (order g) (max-power-dividing (least-prime-divisor (order g)) (order g)))))
			(:instance p-group-factorization-induction-case-3
		          (l (cyclic-p-subgroup-list
		               (least-prime-divisor (order g))
		               (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
			                                                  (order g))
						      g)))
		          (h (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g)) (order g)) g)))
			(:instance internal-direct-product-subgroup
			             (h (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
		  				                                   (order g))
							       g))
			             (l (cyclic-p-subgroup-list
				          (least-prime-divisor (order g))
				          (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
		  				                                     (order g))
								 g))))
			(:instance  p-group-factorization (p (least-prime-divisor (order g)))
			                                  (g (subgroup-ord-dividing
							       (max-power-dividing (least-prime-divisor (order g))
		  				                                   (order g))
							       g)))))))

(local-defthmd idp-cyclic-subgroup-list-2
  (implies (and (groupp g)
                (abelianp g)
		(> (order g) 1)
		(= (order (subgroup-ord-dividing (/ (order g) (max-power-dividing (least-prime-divisor (order g)) (order g))) g))
		   1))
	   (let ((l (cyclic-subgroup-list g)))
	     (and (cyclic-p-group-list-p l)
	          (internal-direct-product-p l g)
		  (equal (product-orders l) (order g)))))
  :hints (("Goal" :use (idp-cyclic-subgroup-list-1)
                  :expand ((cyclic-subgroup-list g)))))

(defthmd product-orders-append
  (implies (and (group-list-p l)
                (group-list-p m))
	   (equal (product-orders (append l m))
	          (* (product-orders l) (product-orders m)))))
 
(defthmd cyclic-p-group-list-append
  (implies (and (cyclic-p-group-list-p l1)
                (cyclic-p-group-list-p l2))
	   (cyclic-p-group-list-p (append l1 l2))))

(defthmd cyclic-p-group-list-group-list
  (implies (cyclic-p-group-list-p l)
           (group-list-p l))
  :hints (("Goal" :in-theory (enable cyclic-p-group-p))))

(local-defthmd idp-cyclic-subgroup-list-3
  (let* ((p (least-prime-divisor (order g)))
         (m (max-power-dividing p (order g)))
         (n (/ (order g) m))
         (k (subgroup-ord-dividing n g))
	 (l2 (cyclic-subgroup-list k))
	 (l (cyclic-subgroup-list g)))
    (implies (and (groupp g)
                  (abelianp g)
		  (> (order g) 1)
		  (not (= (order k) 1))
                  (cyclic-p-group-list-p l2)
		  (equal (product-orders l2) (order k)))
	     (and (cyclic-p-group-list-p l)
		  (equal (product-orders l) (order g)))))
  :hints (("Goal" :use (idp-cyclic-subgroup-list-1
		        (:instance cyclic-p-group-list-append
			             (l1 (cyclic-p-subgroup-list (least-prime-divisor (order g))
				                                 (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
			                                                                                    (order g))
						                                        g)))
				     (l2 (cyclic-subgroup-list (subgroup-ord-dividing (/ (order g)
			                                                                 (max-power-dividing (least-prime-divisor (order g))
			                                                                                     (order g)))
									              g))))
		        (:instance product-orders-append
			             (l (cyclic-p-subgroup-list (least-prime-divisor (order g))
				                                (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
			                                                                                   (order g))
						                                       g)))
				     (m (cyclic-subgroup-list (subgroup-ord-dividing (/ (order g)
			                                                                (max-power-dividing (least-prime-divisor (order g))
			                                                                                    (order g)))
									             g))))
			(:instance cyclic-p-group-list-group-list
			             (l (cyclic-p-subgroup-list (least-prime-divisor (order g))
				                                (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
			                                                                                   (order g))
						                                       g))))
			(:instance cyclic-p-group-list-group-list
			             (l (cyclic-subgroup-list (subgroup-ord-dividing (/ (order g)
			                                                                (max-power-dividing (least-prime-divisor (order g))
			                                                                                    (order g)))
									             g))))))))

(local-defthmd idp-cyclic-subgroup-list-4
  (let* ((p (least-prime-divisor (order g)))
         (m (max-power-dividing p (order g)))
         (n (/ (order g) m))
         (h (subgroup-ord-dividing m g))
         (k (subgroup-ord-dividing n g))
         (l1 (cyclic-p-subgroup-list p h))
	 (l2 (cyclic-subgroup-list k)))
    (implies (and (groupp g)
                  (abelianp g)
		  (> (order g) 1)
		  (not (= (order k) 1))
	          (internal-direct-product-p l2 k)
                  (cyclic-p-group-list-p l2))
	     (and (internal-direct-product-p l1 g)
	          (equal (group-intersection h k g)
		         (trivial-subgroup g))
		  (subgroupp (product-group-list l1 g) h)
                  (subgroupp (product-group-list l2 g) k))))
  :hints (("Goal" :expand ((cyclic-subgroup-list g))
                  :use (idp-cyclic-subgroup-list-1
		        (:instance product-orders-append (l l1) (m l2))
			(:instance cyclic-p-group-list-group-list (l l1))
			(:instance cyclic-p-group-list-group-list (l l2))
			(:instance rel-prime-factors-intersection (m (max-power-dividing (least-prime-divisor (order g)) (order g)))
			                                          (n (/ (order g)
								        (max-power-dividing (least-prime-divisor (order g)) (order g)))))
			(:instance internal-direct-product-subgroup
			             (l (cyclic-subgroup-list (subgroup-ord-dividing (/ (order g)
			                                                                (max-power-dividing (least-prime-divisor (order g))
			                                                                                    (order g)))
									             g)))
				     (h (subgroup-ord-dividing (/ (order g)
				                                  (max-power-dividing (least-prime-divisor (order g))
			                                                              (order g)))
					                       g)))
			(:instance p-group-factorization-induction-case-3
			             (l (cyclic-subgroup-list (subgroup-ord-dividing (/ (order g)
			                                                                (max-power-dividing (least-prime-divisor (order g))
			                                                                                    (order g)))
									             g)))
				     (h (subgroup-ord-dividing (/ (order g)
				                                  (max-power-dividing (least-prime-divisor (order g))
			                                                              (order g)))
					                       g)))))))

(local-defthmd idp-cyclic-subgroup-list-5
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in x h)
		(in x k)
		(equal (group-intersection h k g) (trivial-subgroup g)))
	   (equal (e g) x))
  :hints (("Goal" :in-theory (e/d (e) (TRIVIAL-SUBGROUP-ELTS))
                  :use (in-trivial-subgroup group-intersection-elts))))

(local-defthmd idp-cyclic-subgroup-list-6
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(subgroupp h1 h)
		(subgroupp k1 k)
		(equal (group-intersection h k g) (trivial-subgroup g)))
	   (equal (group-intersection h1 k1 g) (trivial-subgroup g)))
  :hints (("Goal" :in-theory (disable SUBGROUPP-SUBLISTP subgroupp-subsetp)
                  :use ((:instance idp-cyclic-subgroup-list-5 (x (CADR (INTERSECTION-EQUAL (CAR H1) (CAR K1)))))
		        (:instance subgroupp-transitive (h h1) (k h))
                        (:instance subgroupp-transitive (h k1))			
			(:instance subgroupp-subsetp (h h1) (g h) (x (CADR (INTERSECTION-EQUAL (CAR H1) (CAR K1)))))
			(:instance subgroupp-subsetp (h k1) (g k) (x (CADR (INTERSECTION-EQUAL (CAR H1) (CAR K1)))))
			(:instance not-trivial-elt (h (group-intersection h1 k1 g)))))))

(local-defthmd idp-cyclic-subgroup-list-7
  (let* ((p (least-prime-divisor (order g)))
         (m (max-power-dividing p (order g)))
         (n (/ (order g) m))
         (k (subgroup-ord-dividing n g))
	 (l2 (cyclic-subgroup-list k))
	 (l (cyclic-subgroup-list g)))
    (implies (and (groupp g)
                  (abelianp g)
		  (> (order g) 1)
		  (not (= (order k) 1))
	          (internal-direct-product-p l2 k)
                  (cyclic-p-group-list-p l2))
	     (internal-direct-product-p l g)))
  :hints (("Goal" :expand ((cyclic-subgroup-list g))
                  :use (idp-cyclic-subgroup-list-1 idp-cyclic-subgroup-list-4
		        (:instance internal-direct-product-subgroup
			             (h (subgroup-ord-dividing (/ (order g)
			                                          (max-power-dividing (least-prime-divisor (order g))
			                                                              (order g)))
						               g))
				     (l  (cyclic-subgroup-list (subgroup-ord-dividing (/ (order g)
			                                                                (max-power-dividing (least-prime-divisor (order g))
			                                                                                    (order g)))
									             g))))
		        (:instance idp-cyclic-subgroup-list-6
			             (h (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
			                                                           (order g))
						               g))
				     (k (subgroup-ord-dividing (/ (order g)
			                                          (max-power-dividing (least-prime-divisor (order g))
			                                                              (order g)))
						               g))
			             (h1 (product-group-list
				           (cyclic-p-subgroup-list (least-prime-divisor (order g))
				                                   (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
			                                                                                      (order g))
						                                          g))
					   g))
				     (k1 (product-group-list
				           (cyclic-subgroup-list (subgroup-ord-dividing (/ (order g)
			                                                                   (max-power-dividing (least-prime-divisor (order g))
			                                                                                       (order g)))
									                g))
					   g)))
			(:instance internal-direct-product-append
			            (l (cyclic-p-subgroup-list (least-prime-divisor (order g))
				                               (subgroup-ord-dividing (max-power-dividing (least-prime-divisor (order g))
			                                                                                  (order g))
						                                      g)))
				    (m (cyclic-subgroup-list (subgroup-ord-dividing (/ (order g)
			                                                               (max-power-dividing (least-prime-divisor (order g))
			                                                                                   (order g)))
									            g))))))))

(local-defthmd idp-cyclic-subgroup-list-8
  (let* ((p (least-prime-divisor (order g)))
         (m (max-power-dividing p (order g)))
         (n (/ (order g) m))
         (k (subgroup-ord-dividing n g))
	 (l2 (cyclic-subgroup-list k))
	 (l (cyclic-subgroup-list g)))
    (implies (and (groupp g)
                  (abelianp g)
		  (> (order g) 1)
		  (not (= (order k) 1))
                  (cyclic-p-group-list-p l2)
		  (equal (product-orders l2) (order k))
	          (internal-direct-product-p l2 k))
	     (and (cyclic-p-group-list-p l)
		  (equal (product-orders l) (order g))
		  (internal-direct-product-p l g))))
  :hints (("Goal" :use (idp-cyclic-subgroup-list-3 idp-cyclic-subgroup-list-7))))

(defthmd idp-cyclic-subgroup-list
  (implies (and (groupp g)
                (abelianp g)
		(> (order g) 1))
	   (let ((l (cyclic-subgroup-list g)))
	     (and (cyclic-p-group-list-p l)
	          (internal-direct-product-p l g)
		  (equal (product-orders l) (order g)))))
  :hints (("Subgoal *1/2" :use (idp-cyclic-subgroup-list-1 idp-cyclic-subgroup-list-2 idp-cyclic-subgroup-list-8))))

(defthmd abelian-factorization
  (implies (and (groupp g)
                (abelianp g)
		(> (order g) 1))
	   (let ((l (cyclic-subgroup-list g)))
	     (and (cyclic-p-group-list-p l)
	          (isomorphismp (product-list-map l g)
	                        (direct-product l)
				g))))
  :hints (("Goal" :use (idp-cyclic-subgroup-list
                        (:instance isomorphismp-dp-idp (l (cyclic-subgroup-list g)))))))


;;-------------------------------------------------------------------------------------------------------
;; Powers of Abelian Groups
;;-------------------------------------------------------------------------------------------------------

;; The list of nth powers of the elements of g:

(defun power-list-aux (l n g)
  (if (consp l)
      (insert (power (car l) n g)
              (power-list-aux (cdr l) n g)
	      g)
    ()))

(defund power-list (n g)
  (power-list-aux (elts g) n g))

(local-defthm member-power-power-list-aux
  (implies (and (groupp g)
		(natp n)
		(sublistp l (elts g))
		(member-equal x l))
	   (member-equal (power x n g) (power-list-aux l n g)))
  :hints (("Subgoal *1/1" :use ((:instance member-insert (x (power (car l) n g))
                                                         (y (power x n g))
                                                         (l (POWER-LIST-AUX (CDR L) N G)))
				(:instance member-insert (x (power (car l) n g))
                                                         (y (power (car l) n g))
                                                         (l (POWER-LIST-AUX (CDR L) N G)))))))

(defthm member-power-power-list
  (implies (and (groupp g)
		(natp n)
		(in x g))
	   (member-equal (power x n g) (power-list n g)))
  :hints (("Goal" :in-theory (enable power-list))))

(defun nth-root-aux (x l n g)
  (if (consp l)
      (if (member-equal x (power-list-aux (cdr l) n g))
          (nth-root-aux x (cdr l) n g)
	(if (equal x (power (car l) n g))
	    (car l)
	  ()))
    ()))

(defund nth-root (x n g)
  (nth-root-aux x (elts g) n g))

(local-defthm power-nth-root-aux
  (implies (and (groupp g)
                (natp n)
		(sublistp l (elts g))
		(member-equal x (power-list-aux l n g)))
	   (and (member-equal (nth-root-aux x l n g) l)
	        (equal (power (nth-root-aux x l n g) n g)
		       x)))
  :hints (("Goal" :induct (nth-root-aux x l n g))
          ("Subgoal *1/3" :use ((:instance member-insert (y x) (x (POWER (CAR L) N G)) (l (POWER-LIST-AUX (CDR L) N G)))))  
          ("Subgoal *1/2" :use ((:instance member-insert (y x) (x (POWER (CAR L) N G)) (l (POWER-LIST-AUX (CDR L) N G)))))))

(defthmd power-nth-root
  (implies (and (groupp g)
                (natp n)
		(member-equal x (power-list n g)))
	   (and (in (nth-root x n g) g)
	        (equal (power (nth-root x n g) n g)
		       x)))
  :hints (("Goal" :in-theory (enable nth-root power-list))))

(local-defthm sublistp-power-list-aux
  (implies (and (groupp g)
		(natp n)
		(sublistp l (elts g)))
	   (and (sublistp (power-list-aux l n g) (elts g))
		(ordp (power-list-aux l n g) g))))

(local-defthm sublistp-power-list
  (implies (and (groupp g)
		(natp n))
	   (and (sublistp (power-list n g) (elts g))
		(ordp (power-list n g) g)))
  :hints (("Goal" :in-theory (enable power-list))))

(local-defthm dlistp-power-list
  (implies (and (groupp g)
		(natp n))
	   (dlistp (power-list n g)))
  :hints (("Goal" :use ((:instance ordp-dlistp (l (power-list n g)))))))

(local-defthm consp-power-list-aux
  (implies (and (groupp g)
		(natp n)
		(sublistp l (elts g))
		(consp l))
	   (consp (power-list-aux l n g))))

(local-defthm consp-power-list
  (implies (and (groupp g)
		(natp n))
	   (consp (power-list n g)))
  :hints (("Goal" :in-theory (enable power-list))))

(local-defthm member-e--power-list-aux
  (implies (and (groupp g)
		(natp n)
		(sublistp l (elts g))
		(member-equal (e g) l))
	   (member-equal (e g) (power-list-aux l n g)))
  :hints (("Subgoal *1/1" :in-theory (disable power-e)
	                  :use (power-e
			        (:instance member-insert (x (e g)) (y (e g)) (l (POWER-LIST-AUX (CDR L) N G)))))))

(local-defthm car-power-list-aux
  (implies (and (groupp g)
		(natp n)
		(sublistp l (elts g))
		(consp l)
		(member-equal (e g) l))
	   (equal (car (power-list-aux l n g))
		  (e g)))
  :hints (("Goal" :use (member-e--power-list-aux
                        (:instance car-ordp-e (l (power-list-aux l n g)))))))

(local-defthm car-power-list
  (implies (and (groupp g)
		(natp n))
	   (equal (car (power-list n g))
		  (e g)))
  :hints (("Goal" :in-theory (enable power-list))))

(local-defthm power-list-closed
  (implies (and (groupp g)
                (abelianp g)
		(natp n)
		(member-equal x (power-list n g))
		(member-equal y (power-list n g)))
	   (member-equal (op x y g) (power-list n g)))
  :hints (("Goal" :use (power-nth-root
                        (:instance power-nth-root (x y))
			(:instance power-abelian (x (nth-root x n g)) (y (nth-root y n g)))
			(:instance member-power-power-list (x (op (nth-root x n g) (nth-root y n g) g)))))))

(local-defthm power-list-inv
  (implies (and (groupp g)
                (abelianp g)
		(natp n)
		(member-equal x (power-list n g)))
	   (member-equal (inv x g) (power-list n g)))
  :hints (("Goal" :use (power-nth-root
                        (:instance power-inv (x (nth-root x n g)))
			(:instance member-power-power-list (x (inv (nth-root x n g) g)))))))


;; If g is abelian, then this list is a subgroup of g:

(defsubgroup group-power (n) g
  (and (posp n) (groupp g) (abelianp g))
  (power-list n g))

;; If 2 abelian groups are isomorphic, then so are their nth powers:

(local-defthmd isomorphismp-power-1
  (implies (and (groupp g)
                (abelianp g)
		(posp n)
		(epimorphismp map g h)
		(in x (image map (group-power n g) h)))
	   (in x (group-power n h)))
  :hints (("Goal" :in-theory (e/d (epimorphismp) (member-power-power-list homomorphism-power))
                  :use (homomorphismp-abelianp-image
		        (:instance image-preimage (g (group-power n g)))
		        (:instance power-nth-root (x (preimage x map (group-power n g))))
			(:instance homomorphismp-subgroup (k (group-power n g)))
			(:instance member-power-power-list (x (mapply map (nth-root (preimage x map (group-power n g)) n g)))
			                                   (g h))
			(:instance homomorphism-power (x (nth-root (preimage x map (group-power n g)) n g)))))))

(local-defthmd isomorphismp-power-2
  (implies (epimorphismp map g h)
           (iff (in x h)
	        (member-equal x (ielts map g h))))
  :hints (("Goal" :in-theory (enable epimorphismp) :use (image-elts))))

(local-defthmd isomorphismp-power-3
  (implies (and (groupp g)
                (abelianp g)
		(posp n)
		(epimorphismp map g h)
		(in x (group-power n h)))
           (in x (image map (group-power n g) h)))
  :hints (("Goal" :in-theory (e/d (epimorphismp) (member-power-power-list homomorphism-power))
                  :use (homomorphismp-abelianp-image
		        (:instance isomorphismp-power-2 (x (nth-root x n h)))
		        (:instance power-nth-root (g h))
		        (:instance image-preimage (x (nth-root x n h)))
			(:instance homomorphismp-subgroup (k (group-power n g)))
			(:instance member-power-power-list (x (preimage (nth-root x n h) map g)))
			(:instance homomorphism-power (x (preimage (nth-root x n h) map g)))
			(:instance member-ielts (x (power (preimage (nth-root x n h) map g) n g))
			                        (g (group-power n g)))))))

(local-defthmd isomorphismp-power-4
  (implies (and (groupp g)
                (abelianp g)
		(posp n)
		(epimorphismp map g h))
           (and (sublistp (elts (group-power n h))
                          (elts (image map (group-power n g) h)))
	        (sublistp (elts (image map (group-power n g) h))
		          (elts (group-power n h)))))                          
  :hints (("Goal" :use ((:instance scex1-lemma (l (elts (group-power n h))) (m (elts (image map (group-power n g) h))))
                        (:instance scex1-lemma (m (elts (group-power n h))) (l (elts (image map (group-power n g) h))))
	                (:instance isomorphismp-power-1 (x (scex1 (elts (image map (group-power n g) h))
			                                          (elts (group-power n h)))))
	                (:instance isomorphismp-power-3 (x (scex1 (elts (group-power n h))
			                                          (elts (image map (group-power n g) h)))))))))

(local-defthmd isomorphismp-power-5
  (implies (and (groupp g)
                (abelianp g)
		(posp n)
		(epimorphismp map g h))
           (equal (group-power n h)
                  (image map (group-power n g) h)))
  :hints (("Goal" :in-theory (enable epimorphismp)
                  :use (isomorphismp-power-4 homomorphismp-abelianp-image
			(:instance homomorphismp-subgroup (k (group-power n g)))
			(:instance abelian-subgroup (h (group-power n g)))
                        (:instance ordp-equal (g h) (x (elts (group-power n h))) (y (elts (image map (group-power n g) h))))
	                (:instance subgroups-equal-elts (g h) (h (group-power n h)) (k (image map (group-power n g) h)))))))

(defthmd isomorphismp-power
  (implies (and (isomorphismp map g h)
                (abelianp g)
		(posp n))
	   (isomorphismp map (group-power n g) (group-power n h)))
  :hints (("Goal" :use (isomorphismp-power-5
                        (:instance endomorphismp-subgroup (k (group-power n g)))
                        (:instance endomorphismp-isomorphismp (g (group-power n g)))))))

;; Power of a direct product:

(defun group-power-list (n l)
  (if (consp l)
      (cons (group-power n (car l))
            (group-power-list n (cdr l)))
    ()))

(defun abelian-list-p (l)
  (if (consp l)
      (and (groupp (car l))
           (abelianp (car l))
	   (abelian-list-p (cdr l)))
    (null l)))

(defthm abelian-group-list-p
  (implies (abelian-list-p l)
           (group-list-p l)))

(defthm group-list-p-group-power-list
  (implies (and (abelian-list-p l)
                (posp n))
           (group-list-p (group-power-list n l))))

(defthm abelian-list-p-group-power-list
  (implies (and (abelian-list-p l)
                (posp n))
           (abelian-list-p (group-power-list n l)))
  :hints (("Subgoal *1/2" :in-theory (disable abelian-subgroup)
                          :use ((:instance abelian-subgroup (g (car l)) (h (group-power n (car l))))))))

(defthm abelian-cyclic-p-group-list-p
  (implies (cyclic-p-group-list-p l)
           (abelian-list-p l))
  :hints (("Subgoal *1/4" :in-theory (enable CYCLIC-P-GROUP-P))
          ("Subgoal *1/3" :in-theory (enable CYCLIC-P-GROUP-P))))

(in-theory (disable member-power-power-list))

(local-defthm group-power-dp-1
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (direct-product l)))
	   (in (dp-power x n l)
	       (direct-product (group-power-list n l))))
  :hints (("Subgoal *1/4" :in-theory (disable abelian-group-list-p)
                          :use (in-dp power-dp
                                (:instance abelian-group-list-p (l (cdr l)))
				(:instance in-dp (x (power x n (direct-product l))) (l (GROUP-POWER-LIST N L)))
                                (:instance in-dp (x (list (power (car x) n (car l)))) (l (list (group-power n (car l)))))
                                (:instance member-power-power-list (x (car x)) (g (car l)))))
	  ("Subgoal *1/3" :use (in-dp))
          ("Subgoal *1/2" :use (in-dp
	                        (:instance in-dp (x (list (power (car x) n (car l)))) (l (list (group-power n (car l)))))
	                        (:instance member-power-power-list (x (car x)) (g (car l)))))))  

(local-defthmd abelianp-dp-1
  (implies (and (abelian-list-p l)
                (consp l)
		(in x (direct-product l))
		(in y (direct-product l)))
           (equal (dp-op x y l)
	          (dp-op y x l)))
  :hints (("Subgoal *1/5" :use (in-dp
                                (:instance in-dp (x y))
				(:instance group-abelianp (x (car x)) (y (car y)) (g (car l)))))
	  ("Subgoal *1/4" :use (in-dp
                                (:instance in-dp (x y))
				(:instance direct-product-elts (gl (cdr l)))
				(:instance group-abelianp (x (car x)) (y (car y)) (g (car l)))))
	  ("Subgoal *1/3" :use (in-dp
                                (:instance in-dp (x y))
				(:instance direct-product-elts (gl (cdr l)))
				(:instance group-abelianp (x (car x)) (y (car y)) (g (car l)))))
	  ("Subgoal *1/2" :use (in-dp
                                (:instance in-dp (x y))
				(:instance group-abelianp (x (car x)) (y (car y)) (g (car l)))))))

(defthmd abelianp-dp
  (implies (and (abelian-list-p l)
                (consp l))
	   (abelianp (direct-product l)))
  :hints (("Goal" :use ((:instance not-abelianp-cex (g (direct-product l)))
                        (:instance abelianp-dp-1 (x (car (abelianp-cex (direct-product l))))
			                         (y (cadr (abelianp-cex (direct-product l)))))))))
	
(local-defthm group-power-dp-2
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (group-power n (direct-product l))))
	   (in x (direct-product (group-power-list n l))))
  :hints (("Goal" :use ((:instance power-nth-root (g (direct-product l)))
                        (:instance power-dp (x (nth-root x n (direct-product l))))
			(:instance group-power-elts (g (direct-product l)))
			(:instance group-power-dp-1 (x (nth-root x n (direct-product l))))))))

(local-defthmd group-power-dp-3
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (direct-product (group-power-list n l))))
	   (and (consp x)
	        (in (nth-root (car x) n (car l)) (car l))
		(equal (power (nth-root (car x) n (car l)) n (car l))
		       (car x))))
  :hints (("Goal" :use ((:instance in-dp (l (group-power-list n l)))
                        (:instance power-nth-root (x (car x)) (g (car l)))))))

(local-defthmd group-power-dp-4
  (implies (and (abelian-list-p l)
                (consp l)
		(null (cdr l))
		(posp n)
                (in x (direct-product (group-power-list n l))))
	   (and (consp x)
	        (in (list (nth-root (car x) n (car l))) (direct-product l))
		(equal (power (list (nth-root (car x) n (car l))) n (direct-product l))
		       x)))
  :hints (("Goal" :use ((:instance in-dp (l (group-power-list n l)))
                        (:instance in-dp (x (list (nth-root (car x) n (car l)))))
			(:instance power-dp (x (list (nth-root (car x) n (car l)))))
                        (:instance power-nth-root (x (car x)) (g (car l)))))))

(local-defthmd group-power-dp-5
  (implies (and (abelian-list-p l)
                (consp l)
		(null (cdr l))
		(posp n)
                (in x (direct-product (group-power-list n l))))
	   (in x (group-power n (direct-product l))))
  :hints (("Goal" :use (group-power-dp-4 abelianp-dp
                        (:instance member-power-power-list (x (list (nth-root (car x) n (car l)))) (g (direct-product l)))))))

(local-defthmd group-power-dp-6
  (implies (and (abelian-list-p l)
                (consp l)
		(consp (cdr l))
		(posp n)
                (in x (direct-product (group-power-list n l))))
	   (and (consp x)
	        (in (cdr x) (direct-product (group-power-list n (cdr l))))))
  :hints (("Goal" :use ((:instance in-dp (l (group-power-list n l)))))))

(local-defthmd group-power-dp-7
  (implies (and (abelian-list-p l)
                (consp l)
		(consp (cdr l))
		(posp n)
                (in x (direct-product (group-power-list n l)))
		(implies (in (cdr x) (direct-product (group-power-list n (cdr l))))
		         (in (cdr x) (group-power n (direct-product (cdr l))))))
	   (and (in (nth-root (cdr x) n (direct-product (cdr l)))
	            (direct-product (cdr l)))
		(equal (power (nth-root (cdr x) n (direct-product (cdr l)))
		              n
			      (direct-product (cdr l)))
		       (cdr x))))
  :hints (("Goal" :in-theory (enable abelianp-dp)
                  :use (group-power-dp-6
                        (:instance power-nth-root (x (cdr x)) (g (direct-product (cdr l))))))))

(local-defthmd group-power-dp-8
  (implies (and (abelian-list-p l)
                (consp l)
		(consp (cdr l))
		(posp n)
                (in x (direct-product (group-power-list n l)))
		(implies (in (cdr x) (direct-product (group-power-list n (cdr l))))
		         (in (cdr x) (group-power n (direct-product (cdr l))))))
	   (and (in (cons (nth-root (car x) n (car l))
	                  (nth-root (cdr x) n (direct-product (cdr l))))
	            (direct-product l))
		(equal (power (cons (nth-root (car x) n (car l))
		                    (nth-root (cdr x) n (direct-product (cdr l))))
		              n
			      (direct-product l))
		       x)))
  :hints (("Goal" :in-theory (enable abelianp-dp)
                  :use (group-power-dp-3 group-power-dp-7
			(:instance power-dp (x (nth-root (cdr x) n (direct-product (cdr l)))) (l (cdr l)))
		        (:instance in-dp (x (cons (nth-root (car x) n (car l))
		                                  (nth-root (cdr x) n (direct-product (cdr l))))))						  
                        (:instance power-dp (x (cons (nth-root (car x) n (car l))
		                                     (nth-root (cdr x) n (direct-product (cdr l))))))))))

(local-defthmd group-power-dp-9
  (implies (and (abelian-list-p l)
                (consp l)
		(consp (cdr l))
		(posp n)
                (in x (direct-product (group-power-list n l)))
		(implies (in (cdr x) (direct-product (group-power-list n (cdr l))))
		         (in (cdr x) (group-power n (direct-product (cdr l))))))
	   (in x (group-power n (direct-product l))))
  :hints (("Goal" :in-theory (enable abelianp-dp)
                  :use (group-power-dp-8
			(:instance member-power-power-list (x (cons (nth-root (car x) n (car l))
		                                                    (nth-root (cdr x) n (direct-product (cdr l)))))
							   (g (direct-product l)))))))

(local-defthmd group-power-dp-10
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (direct-product (group-power-list n l))))
	   (in x (group-power n (direct-product l))))
  :hints (("Goal" :induct (cdrs-induct x l))
          ("Subgoal *1/2" :use (group-power-dp-5))
          ("Subgoal *1/3" :in-theory (enable abelianp-dp) :use (group-power-dp-5 group-power-dp-9))
          ("Subgoal *1/1" :in-theory (e/d (abelianp-dp) (group-power-elts))
	                  :use (group-power-dp-5 group-power-dp-9 (:instance group-power-elts (g (direct-product (cdr l))))))))

(local-defthmd group-power-dp-11
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n))
           (iff (in x (direct-product (group-power-list n l)))
	        (in x (group-power n (direct-product l)))))
  :hints (("Goal" :use (group-power-dp-2 group-power-dp-10))))

(defun cdrs-3-induct (x y l)
  (if (consp l)
      (list (cdrs-3-induct (cdr x) (cdr y) (cdr l)))
    (list x y)))

(in-theory (enable in-dp))

(local-defthmd group-power-dp-12
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (direct-product (group-power-list n l)))
                (in y (direct-product (group-power-list n l))))
	   (equal (dp-op x y (group-power-list n l))
	          (dp-op x y l)))
  :hints (("Goal" :induct (cdrs-3-induct x y l))
          ("Subgoal *1/6" :use ((:instance in-dp (l (group-power-list n l)))
	                        (:instance in-dp (x y) (l (group-power-list n l)))))
          ("Subgoal *1/5" :use ((:instance in-dp (l (group-power-list n l)))
	                        (:instance in-dp (x y) (l (group-power-list n l)))))
          ("Subgoal *1/4" :use ((:instance in-dp (l (group-power-list n l)))
	                        (:instance in-dp (x y) (l (group-power-list n l)))))
          ("Subgoal *1/3" :use ((:instance in-dp (l (group-power-list n l)))
	                        (:instance in-dp (x y) (l (group-power-list n l)))))
          ("Subgoal *1/2" :use ((:instance in-dp (l (group-power-list n l)))
	                        (:instance in-dp (x y) (l (group-power-list n l)))))
          ("Subgoal *1/1" :use ((:instance in-dp (l (group-power-list n l)))
	                        (:instance in-dp (x y) (l (group-power-list n l)))))))

(local-defthm group-power-dp-13
  (implies (consp l)
           (consp (group-power-list n l))))

(local-defthmd group-power-dp-14
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (direct-product (group-power-list n l))))
	   (in x (direct-product l)))
  :hints (("Goal" :induct (cdrs-induct x l))
          ("Subgoal *1/4" :use (in-dp (:instance in-dp (l (group-power-list n l)))))
          ("Subgoal *1/3" :use (in-dp (:instance in-dp (l (group-power-list n l)))))
          ("Subgoal *1/2" :use (in-dp (:instance in-dp (l (group-power-list n l)))))
          ("Subgoal *1/1" :use (in-dp (:instance in-dp (l (group-power-list n l)))))))


(local-defthmd group-power-dp-15
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (direct-product (group-power-list n l)))
                (in y (direct-product (group-power-list n l))))
	   (equal (op x y (direct-product (group-power-list n l)))
	          (op x y (direct-product l))))
  :hints (("Goal" :in-theory (disable direct-product-op-rewrite)
                  :use (group-power-dp-12 group-power-dp-14
		        (:instance group-power-dp-14 (x y))
		        (:instance direct-product-elts (gl l))
		        (:instance direct-product-elts (gl (GROUP-POWER-LIST N L)))
                        (:instance direct-product-op-rewrite (gl l))
                        (:instance direct-product-op-rewrite (gl (GROUP-POWER-LIST N L)))))))

(local-defthm group-power-dp-16
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (direct-product (group-power-list n l)))
                (in y (direct-product (group-power-list n l))))
	   (equal (op x y (direct-product (group-power-list n l)))
	          (op x y (group-power n (direct-product l)))))
  :hints (("Goal" :in-theory (e/d (abelianp-dp) (DIRECT-PRODUCT-OP-REWRITE SUBGROUPP-GROUP-POWER))
                  :use (group-power-dp-15 group-power-dp-10
		        (:instance group-power-dp-10 (x y))
		        (:instance subgroup-op (h (group-power n (direct-product l))) (g (direct-product l)))
		        (:instance SUBGROUPP-GROUP-POWER (g (direct-product l)))))))

(local-defthmd group-power-dp-17
  (implies (and (abelian-list-p l)
                (consp l)
 		(posp n)
                (in x (direct-product (group-power-list n l))))
	   (in x (direct-product l)))
  :hints (("Goal" :in-theory (disable subgroupp-subsetp subgroupp-group-power)
                  :use (group-power-dp-11
		        (:instance subgroupp-subsetp (g (direct-product l)) (h (group-power n (direct-product l))))
                        (:instance subgroupp-group-power (g (direct-product l)))))))

(local-defthmd group-power-dp-18
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
                (in x (direct-product (group-power-list n l)))
                (in y (direct-product (group-power-list n l)))
		(< (ind x (direct-product (group-power-list n l)))
		   (ind y (direct-product (group-power-list n l)))))
	   (< (ind x (direct-product l))
	      (ind y (direct-product l))))
  :hints (("Goal" :induct (cdrs-3-induct x y l))
          ("Subgoal *1/5" :use (in-dp group-power-dp-11 ind-dp-compare
	                        (:instance in-dp (x y))
				(:instance in-dp (l (group-power-list n l)))
				(:instance in-dp (x y) (l (group-power-list n l)))
				(:instance group-power-dp-11 (x y))
				(:instance ind-dp-compare (l (group-power-list n l)))))
          ("Subgoal *1/4" :use (in-dp group-power-dp-11 ind-dp-compare
	                        (:instance in-dp (x y))
				(:instance in-dp (l (group-power-list n l)))
				(:instance in-dp (x y) (l (group-power-list n l)))
				(:instance group-power-dp-11 (x y))
				(:instance ind-dp-compare (l (group-power-list n l)))))
          ("Subgoal *1/3" :use (in-dp group-power-dp-11 ind-dp-compare
	                        (:instance in-dp (x y))
				(:instance in-dp (l (group-power-list n l)))
				(:instance in-dp (x y) (l (group-power-list n l)))
				(:instance group-power-dp-11 (x y))
				(:instance ind-dp-compare (l (group-power-list n l)))
				(:instance ordp<ind (x (car x)) (y (car y)) (l (elts (group-power n (car l)))) (g (car l)))))
	  ("Subgoal *1/2" :use (in-dp group-power-dp-11 ind-dp-compare group-power-dp-17
	                        (:instance direct-product-elts (gl (cdr l)))
	                        (:instance in-dp (x y))
				(:instance in-dp (l (group-power-list n l)))
				(:instance in-dp (x y) (l (group-power-list n l)))
				(:instance group-power-dp-11 (x y))
				(:instance ind-dp-compare (l (group-power-list n l)))
				(:instance ordp<ind (x (car x)) (y (car y)) (l (elts (group-power n (car l)))) (g (car l)))))
          ("Subgoal *1/1" :use (in-dp group-power-dp-11 ind-dp-compare group-power-dp-17
	                        (:instance in-dp (x y))
				(:instance in-dp (l (group-power-list n l)))
				(:instance in-dp (x y) (l (group-power-list n l)))
				(:instance group-power-dp-11 (x y))
				(:instance ind-dp-compare (l (group-power-list n l)))
				(:instance ordp<ind (x (car x)) (y (car y)) (l (elts (group-power n (car l)))) (g (car l)))))))

(local-defthmd group-power-dp-19
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n)
		(sublistp s (elts (direct-product (group-power-list n l))))
		(ordp s (direct-product (group-power-list n l))))
           (ordp s (direct-product l)))
  :hints (("Goal" :induct (len s))
          ("Subgoal *1/1" :use ((:instance group-power-dp-18 (x (car s)) (y (cadr s)))
	                        (:instance group-power-dp-17 (x (car s)))))))

(local-defthmd group-power-dp-20
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n))
           (ordp (elts (direct-product (group-power-list n l)))
                 (direct-product l)))
  :hints (("Goal" :use ((:instance group-power-dp-19 (s (elts (direct-product (group-power-list n l)))))
                        (:instance ordp-g (g (direct-product (group-power-list n l))))))))
		       
(local-defthmd group-power-dp-21
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n))
           (and (sublistp (elts (direct-product (group-power-list n l)))
	                  (elts (group-power n (direct-product l))))
	        (sublistp (elts (group-power n (direct-product l)))
	                  (elts (direct-product (group-power-list n l))))))
  :hints (("Goal" :use ((:instance group-power-dp-2 (x (scex1 (elts (group-power n (direct-product l)))
                                                              (elts (direct-product (group-power-list n l))))))
			(:instance group-power-dp-10 (x (scex1 (elts (direct-product (group-power-list n l)))
			                                       (elts (group-power n (direct-product l))))))
			(:instance scex1-lemma (l (elts (group-power n (direct-product l))))
                                               (m (elts (direct-product (group-power-list n l)))))
			(:instance scex1-lemma (m (elts (group-power n (direct-product l))))
                                               (l (elts (direct-product (group-power-list n l)))))))))

(local-defthmd group-power-dp-22
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n))
           (ordp (elts (group-power n (direct-product l)))
                 (direct-product l)))		 
  :hints (("Goal" :in-theory (e/d (abelianp-dp) (sublistp-power-list))
                  :use ((:instance sublistp-power-list (g (direct-product l)))))))

(local-defthmd group-power-dp-23
  (implies (and (abelian-list-p l)
                (consp l)
		(posp n))
           (equal (elts (group-power n (direct-product l)))
                  (elts (direct-product (group-power-list n l)))))
  :hints (("Goal" :use (group-power-dp-20 group-power-dp-21 group-power-dp-22
                        (:instance ordp-equal (x (elts (group-power n (direct-product l))))
			                      (y (elts (direct-product (group-power-list n l))))
					      (g (direct-product l)))))))                                                              
		       
(defthmd group-power-dp
  (implies (and (posp n) (consp l) (abelian-list-p l))
           (equal (group-power n (direct-product l))
	          (direct-product (group-power-list n l))))
  :hints (("Goal" :use (group-power-dp-23
                        (:instance group-power-dp-16 (x (diff-elt-1 (group-power n (direct-product l)) (direct-product (group-power-list n l))))
			                             (y (diff-elt-2 (group-power n (direct-product l)) (direct-product (group-power-list n l)))))
			(:instance diff-group-op (h (group-power n (direct-product l))) (k (direct-product (group-power-list n l))))))))

(local-defthmd power-cyclic-1
  (implies (and (cyclicp g)
		(posp n)
		(in x (cyclic (power (group-gen g) n g) g)))
	   (in x (group-power n g)))
  :hints (("Goal" :in-theory (enable abelianp-cyclic)
                  :use (order-group-gen
		        (:instance member-powers-power (a (power (group-gen g) n g)))
			(:instance power* (a (group-gen g)) (n (index x (powers (power (group-gen g) n g) g))) (m n))
			(:instance power* (a (group-gen g)) (m (index x (powers (power (group-gen g) n g) g))))
                        (:instance member-power-power-list (x (power (group-gen g) (index x (powers (power (group-gen g) n g) g)) g)))))))

(local-defthmd power-cyclic-2
  (implies (and (cyclicp g)
		(posp n)
		(in x (group-power n g)))
	   (in x (cyclic (power (group-gen g) n g) g)))
  :hints (("Goal" :in-theory (e/d (permp) (power-member))
                  :use (power-nth-root permp-cyclic order-group-gen
		        (:instance member-powers-power (a (group-gen g)) (x (nth-root x n g)))
			(:instance power* (a (group-gen g)) (n (index (nth-root x n g) (powers (group-gen g) g))) (m n))
			(:instance power* (a (group-gen g)) (m (index (nth-root x n g) (powers (group-gen g) g))))
			(:instance power-member (a (power (group-gen g) n g)) (n (index (nth-root x n g) (powers (group-gen g) g))))))))

(local-defthmd power-cyclic-3
  (implies (and (cyclicp g)
		(posp n))
	   (equal (order (group-power n g))
	          (order (cyclic (power (group-gen g) n g) g))))
  :hints (("Goal" :in-theory (enable permp)
                  :use (order-group-gen
		        (:instance power-cyclic-1 (x (scex1 (powers (power (group-gen g) n g) g) (power-list n g))))
                        (:instance power-cyclic-2 (x (scex1 (power-list n g) (powers (power (group-gen g) n g) g))))
			(:instance scex1-lemma (l (power-list n g)) (m (powers (power (group-gen g) n g) g)))
			(:instance scex1-lemma (m (power-list n g)) (l (powers (power (group-gen g) n g) g)))
			(:instance eq-len-permp (l (power-list n g)) (m (powers (power (group-gen g) n g) g)))))))

(local-defthmd power-cyclic-4
  (implies (and (cyclicp g)
		(posp n))
	   (and (in (power (group-gen g) n g)
	            (group-power n g))
		(equal (ord (power (group-gen g) n g) g)
		       (order (group-power n g)))
		(equal (ord (power (group-gen g) n g)
		            (group-power n g))
		       (order (group-power n g)))))
  :hints (("Goal" :in-theory (e/d (permp) (equal-ord-subgroup power-member))
                  :use (order-group-gen power-cyclic-3
		        (:instance power-cyclic-1 (x (power (group-gen g) n g)))
			(:instance equal-ord-subgroup (a (power (group-gen g) n g)) (h (group-power n g)))
			(:instance power-member (a (power (group-gen g) n g)) (n 1))))))

(local-defthmd power-cyclic-5
  (implies (and (cyclicp g)
		(posp n))
	   (cyclicp (group-power n g)))
  :hints (("Goal" :in-theory (enable cyclicp group-gen)
                  :use (order-group-gen power-cyclic-4
		        (:instance ord-elt-of-ord (x (power (group-gen g) n g)) (n (order (group-power n g))) (g (group-power n g)))))))

(defthmd power-cyclic
  (implies (and (cyclicp g)
		(posp n))
	   (and (cyclicp (group-power n g))
	        (equal (order (group-power n g))
		       (/ (order g) (gcd (order g) n)))))
  :hints (("Goal" :use (power-cyclic-4 power-cyclic-5 order-group-gen
                        (:instance ord-power-gcd (a (group-gen g)))))))

;; For prime p and cyclic g, the order of (group-power n g) depends on whether p divides the order of g:

(defund reduce-order (n p)
  (if (divides p n)
      (/ n p)
    n))

(defthmd prime-power-cyclic
  (implies (and (cyclicp g)
		(primep p))
	   (and (cyclicp (group-power p g))
	        (equal (order (group-power p g))
		       (reduce-order (order g) p))))
  :hints (("Goal" :in-theory (enable reduce-order)
                  :use (power-cyclic-4 order-group-gen
		        (:instance power-cyclic (n p))
		        (:instance gcd-prime (a (order g)))
			(:instance ord-power-gcd (a (group-gen g)) (n p))
			(:instance gcd-commutative (x (order g)) (y p))))))
		  

;;-------------------------------------------------------------------------------------------------------
;; Uniqueness
;;-------------------------------------------------------------------------------------------------------

;; Our objective is to show that if the direct products of two lists of cyclic p-groups l and m are 
;; isomorphic, then they have the same list of orders up to permutation.

;; Pick a prime dividing one of the orders:

(defund first-prime (l)
  (least-prime-divisor (order (car l))))

(defthmd primep-first-prime
  (implies (and (cyclic-p-group-list-p l)
		(consp l))
	   (and (primep (first-prime l))
		(divides (first-prime l)
			 (order (car l)))))
  :hints (("Goal" :in-theory (enable cyclic-p-group-p first-prime)
                  :expand ((cyclic-p-group-list-p l))
		  :use ((:instance least-divisor-divides (k 2) (n (order (car l))))
		        (:instance primep-least-divisor (n (order (car l))))))))

;; We would like to use an induction scheme that replaces l and m with (group-power-list l (first-prime l))
;; and (group-power-list m (first-prime l)), but in order to ensure that they inherit the properties of l
;; and m, we have to delete any occurrences of trivial groups from the lists.

;; Delete the trivial groups occurring in a list of groups:

(defun delete-trivial (l)
  (if (consp l)
      (if (= (order (car l)) 1)
          (delete-trivial (cdr l))
	(cons (car l) (delete-trivial (cdr l))))
    ()))

(defthm group-list-p-delete-trivial
  (implies (group-list-p l)
           (group-list-p (delete-trivial l))))

(defthm groupp-direct-product-delete-trivial
  (implies (and (group-list-p l) (consp (delete-trivial l)))
           (groupp (direct-product (delete-trivial l)))))

(defthm product-orders-delete-trivial
  (implies (group-list-p l)
           (equal (product-orders (delete-trivial l))
	          (product-orders l))))

(defthmd order-dp-delete-trivial
  (implies (group-list-p l)
           (equal (order (direct-product (delete-trivial l)))
	          (order (direct-product l))))
  :hints (("Goal" :use (order-of-dp (:instance order-of-dp (l (delete-trivial l)))))))

;; We shall show that (direct-product (delete-trivial l)) is isomorphic to (direct-product l):

(defun delete-trivial-elt (x l)
  (if (consp x)
      (if (= (order (car l)) 1)
          (delete-trivial-elt (cdr x) (cdr l))
	(cons (car x) (delete-trivial-elt (cdr x) (cdr l))))
    ()))

(defmap delete-trivial-iso (gl)
  (group-tuples gl)
  (delete-trivial-elt x gl))

;; We must assume that (delete-trivial l) is non-nil:

(defthm in-delete-trivial-elt
  (implies (and (group-list-p l)
                (member-equal x (group-tuples l)))
	   (member-equal (delete-trivial-elt x l)
	                 (group-tuples (delete-trivial l))))
  :hints (("Goal" :in-theory (enable member-group-tuples))))

(defthm delete-trivial-op
  (implies (and (group-list-p l)
		(member-equal x (group-tuples l))
		(member-equal y (group-tuples l)))
	   (equal (delete-trivial-elt (dp-op x y l) l)
		  (dp-op (delete-trivial-elt x l)
			 (delete-trivial-elt y l)
			 (delete-trivial l))))
  :hints (("Goal" :in-theory (enable member-group-tuples))))

(defthm delete-trivial-e
  (implies (group-list-p l)
	   (equal (delete-trivial-elt (e-list l) l)
		  (e-list (delete-trivial l)))))

(defthmd member-order-1
  (implies (and (groupp g)
		(equal (order g) 1)
		(in x g))
	   (equal (e g) x))
  :hints (("Goal" :in-theory (disable trivial-subgroup-elts)
                  :use (trivial-subgroup-elts  (:instance iff-trivial-order-1 (h g))))))                        

(defthmd delete-trivial-kernel
  (implies (and (group-list-p l)
		(member-equal x (group-tuples l))
	        (equal (delete-trivial-elt x l)
		       (e-list (delete-trivial l))))
	   (equal (e-list l) x))
  :hints (("Goal" :in-theory (enable member-group-tuples))
          ("Subgoal *1/4" :use ((:instance member-order-1 (g (car l)) (x (car x)))))))

(defthm consp-delete-trivial
  (implies (consp (delete-trivial l))
           (consp l)))

(prove-homomorphismp delete-trivial
  (delete-trivial-iso l)
  (direct-product l)
  (direct-product (delete-trivial l))
  (and (group-list-p l) (consp (delete-trivial l))))

(local-defthmd endomorphismp-delete-trivial
  (implies (and (group-list-p l) (consp (delete-trivial l)))
           (endomorphismp (delete-trivial-iso l)
	                  (direct-product l)
                          (direct-product (delete-trivial l))))
  :hints (("Goal" :use ((:instance homomorphism-endomorphism (map (delete-trivial-iso l))
                                                             (g (direct-product l))
							     (h (direct-product (delete-trivial l))))
			(:instance delete-trivial-kernel (x (cadr (kelts (delete-trivial-iso l)
	                                                                 (direct-product l)
                                                                         (direct-product (delete-trivial l))))))))))

(defthmd isomorphismp-delete-trivial
  (implies (and (group-list-p l)
                (consp (delete-trivial l)))
           (isomorphismp (delete-trivial-iso l)
	                  (direct-product l)
                          (direct-product (delete-trivial l))))
  :hints (("Goal" :use (endomorphismp-delete-trivial order-dp-delete-trivial
                        (:instance equal-orders-isomorphism (map (delete-trivial-iso l))
                                                            (g (direct-product l))
							    (h (direct-product (delete-trivial l))))))))


;;-------------------------------------------------------------------------------------------------------

;; The list of orders of a list of groups:

(defun orders (l)
  (if (consp l)
      (cons (order (car l)) (orders (cdr l)))
    ()))

;; The list of orders of (delete-trivial l):

(defun delete-1 (orders)
  (if (consp orders)
      (if (equal (car orders) 1)
          (delete-1 (cdr orders))
	(cons (car orders) (delete-1 (cdr orders))))
    ()))

(defthm orders-delete-trivial
  (implies (group-list-p l)
           (equal (orders (delete-trivial l))
	          (delete-1 (orders l)))))

;; Our inductive hypothesis will replace l and m with the lists computed by the following,
;; with p = (first-prime l):

(defund reduce-cyclic (l p)
  (delete-trivial (group-power-list p l)))

(defun reduce-orders (orders p)
  (if (consp orders)
      (cons (reduce-order (car orders) p)
            (reduce-orders (cdr orders) p))
    ()))

(defthm order-group-power-list
  (implies (and (primep p) (cyclic-p-group-list-p l))
           (equal (orders (group-power-list p l))
	          (reduce-orders (orders l) p)))
  :hints (("Subgoal *1/2" :in-theory (enable CYCLIC-P-GROUP-P)
                          :use ((:instance prime-power-cyclic (g (car l)))))))

;; The case (or (null (reduce-cyclic l p)) (null (reduce-cyclic m p))) must be handled separately:

;; (TODO)

;; The properties of l and m are inherited:

(local-defun cyclic-p-group-or-trivial-list-p (l)
  (if (consp l)
      (and (or (cyclic-p-group-p (car l))
               (equal (order (car l)) 1))
	   (cyclic-p-group-or-trivial-list-p (cdr l)))
    (null l)))

(defthmd powerp-n/p
  (implies (and (primep p)
                (powerp n p)
		(not (equal n 1)))
	   (and (powerp (/ n p) p)
	        (or (equal (/ n p) 1)
		    (equal (least-prime-divisor (/ n p)) p))))
  :hints (("Goal" :nonlinearp t
                  :use ((:instance primep-least-divisor (n (/ n p)))
			(:instance powerp-prime-divisor (q (least-prime-divisor (/ n p))))
			(:instance divides-transitive (x (LEAST-DIVISOR 2 (/ n p))) (y (/ n p)) (z n))
		        (:instance least-divisor-divides (k 2) (n (/ n p)))))))

(local-defthmd group-power-list-p-group-list
  (implies (and (primep p)
                (cyclic-p-group-list-p l))
           (cyclic-p-group-or-trivial-list-p (group-power-list p l)))
  :hints (("Subgoal *1/2" :in-theory (enable reduce-order p-groupp CYCLIC-P-GROUP-P)
                          :use ((:instance prime-power-cyclic (g (car l)))
			        (:instance powerp-n/p (n (order (car l))))				
				(:instance powerp-prime-divisor (n (order (car l))) (q p) (p (least-prime-divisor (order (car l)))))))))

(local-defthm cyclic-p-group-or-trivial-list-p-delete-trivial
  (implies (cyclic-p-group-or-trivial-list-p l)
           (cyclic-p-group-or-trivial-list-p (delete-trivial l))))

(defun non-trivial-list-p (l)
  (if (consp l)
      (and (not (equal (order (car l)) 1))
           (non-trivial-list-p (cdr l)))
    t))

(local-defthm cyclic-p-group-list-p-delete-trivial
  (implies (and (non-trivial-list-p l)
                (cyclic-p-group-or-trivial-list-p l))
           (cyclic-p-group-list-p l)))

(local-defthm non-trivial-list-p-delete-trivial
  (non-trivial-list-p (delete-trivial l)))

(defthmd reduce-cyclic-p-group-list
  (implies (and (primep p)
                (cyclic-p-group-list-p l))
           (cyclic-p-group-list-p (reduce-cyclic l p)))
  :hints (("Goal" :in-theory (enable reduce-cyclic)
                  :use (group-power-list-p-group-list))))


;;-------------------------------------------------------------------------------------------------------

;; The induction measure:

(local-defthmd reduce-cyclic-product-1
  (implies (and (cyclic-p-group-list-p l) (primep p))
           (<= (product-orders (group-power-list p l))
	       (product-orders l)))
  :hints (("Subgoal *1/2" :in-theory (enable reduce-order cyclic-p-group-p)
                          :nonlinearp t
                          :use ((:instance prime-power-cyclic (g (car l)))))))

(local-defthmd reduce-cyclic-product-2
  (implies (and (cyclic-p-group-list-p l)
                (consp l))
           (< (order (car (group-power-list (first-prime l) l)))
	      (order (car l))))
  :hints (("Goal" :in-theory (enable cyclic-p-group-p reduce-order)
                  :expand ((cyclic-p-group-list-p l))
                  :use (primep-first-prime
                        (:instance prime-power-cyclic (p (first-prime l)) (g (car l)))))))

(local-defthmd reduce-cyclic-product-3
  (implies (group-list-p l)
           (not (equal (product-orders l)
	               0)))
  :hints (("Subgoal *1/2" :use ((:instance order-pos (g (car l)))))))

(local-defthmd reduce-cyclic-product-4
  (implies (and (cyclic-p-group-list-p l)
                (consp l))
           (< (product-orders (group-power-list (first-prime l) l))
	      (product-orders l)))
  :hints (("Goal" :nonlinearp t
                  :use (reduce-cyclic-product-2 primep-first-prime
		        (:instance reduce-cyclic-product-3 (l (cdr l)))
                        (:instance reduce-cyclic-product-1 (p (first-prime l)) (l (cdr l)))))))
  
(defthmd reduce-cyclic-product
  (implies (and (cyclic-p-group-list-p l)
                (consp l))
           (< (product-orders (reduce-cyclic l (first-prime l)))
	      (product-orders l)))
  :hints (("Goal" :in-theory (enable reduce-cyclic)
                  :use (reduce-cyclic-product-4
                        (:instance product-orders-delete-trivial (l (group-power-list (first-prime l) l)))))))


;;-------------------------------------------------------------------------------------------------------

;; The isomorphism from (direct-product (reduce-cyclic l p)) to (direct-product (reduce-cyclic m p)):

(defund reduce-cyclic-iso (map l m p)
  (compose-maps (delete-trivial-iso (group-power-list p m))
                (compose-maps map
                              (inv-isomorphism (delete-trivial-iso (group-power-list p l))
                                               (direct-product (group-power-list p l))
	                                       (direct-product (reduce-cyclic l p))))))

(defthmd isomorphismp-reduce-cyclic
  (implies (and (consp l)
                (consp m)
		(primep p)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
		(consp (reduce-cyclic l p))
		(consp (reduce-cyclic m p))
		(isomorphismp map (direct-product l) (direct-product m)))
	   (isomorphismp (reduce-cyclic-iso map l m p)
	                 (direct-product (reduce-cyclic l p))
			 (direct-product (reduce-cyclic m p))))
  :hints (("Goal" :in-theory (e/d (reduce-cyclic reduce-cyclic-iso) (isomorphismp-compose-maps))
                  :use ((:instance isomorphismp-delete-trivial (l (group-power-list p l)))
		        (:instance isomorphismp-inv (map (delete-trivial-iso (group-power-list p l)))
			                            (g (direct-product (group-power-list p l)))
						    (h (direct-product (reduce-cyclic l p))))
			(:instance group-power-dp (n p))
			(:instance isomorphismp-power (g (direct-product l)) (h (direct-product m)) (n p))
			(:instance group-power-dp (n p) (l m))
			(:instance isomorphismp-delete-trivial (l (group-power-list p m)))
			(:instance isomorphismp-compose-maps (map1 (inv-isomorphism (delete-trivial-iso (group-power-list p l))
                                                                                    (direct-product (group-power-list p l))
			    	                                                    (direct-product (reduce-cyclic l p))))
							     (g (direct-product (reduce-cyclic l p)))
							     (h (direct-product (group-power-list p l)))
							     (map2 map)
							     (k (direct-product (group-power-list p m))))
                       (:instance isomorphismp-compose-maps (map1 (compose-maps map
		                                                                (inv-isomorphism (delete-trivial-iso (group-power-list p l))
                                                                                                 (direct-product (group-power-list p l))
			    	                                                                 (direct-product (reduce-cyclic l p)))))
							    (g (direct-product (reduce-cyclic l p)))
							    (h (direct-product (group-power-list p m)))
							    (map2 (delete-trivial-iso (group-power-list p m)))
							    (k (direct-product (reduce-cyclic m p))))))))


;;-------------------------------------------------------------------------------------------------------

;; Now assume the inductive hypothesis holds. We shall show that every x has the same number of occurrences
;; in (orders l) as in (orders m).  First we show that this holds unless x = p.

(defthmd hits-orders-delete-trivial
  (implies (and (group-list-p l) (not (equal x 1)))
           (equal (hits x (orders (delete-trivial l)))
	          (hits x (orders l)))))

(defund prime-power-p (n)
  (and (natp n)
       (> n 1)
       (powerp n (least-prime-divisor n))))

(local-defthm hack-23
  (IMPLIES (AND (EQUAL (* N (/ P)) 1)
                (PRIMEP P)
                (INTEGERP N)
                (< 0 N)
                (INTEGERP X)
                (< 0 X)
                (EQUAL (* (/ P) X) 1))
           (EQUAL X N))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t)))

(local-defthm reduce-order-powerp
  (implies (and (primep p)
                (primep q)
                (primep r)
		(powerp n q)
		(powerp x r)
		(> n 1)
		(> x 1)
		(equal (reduce-order x p)
		       (reduce-order n p)))
	   (equal x n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable reduce-order) 
                  :cases ((= p q) (= p r) (= q r))
                  :use (hack-23
		        (:instance powerp-n/p (p q))
                        (:instance powerp-n/p (n x) (p r))
			(:instance powerp-prime-divisor (p q) (q p))
			(:instance powerp-prime-divisor (n x) (p r) (q p))))
	  ("Subgoal 3.8" :nonlinearp t)
	  ("Subgoal 2.4" :use hack-23)
	  ("Subgoal 1.24" :nonlinearp t)))

(defthmd hits-group-power-list
  (implies (and (primep p)
                (cyclic-p-group-list-p l)
		(prime-power-p x))
           (equal (hits x (orders l))
	          (hits (reduce-order x p) (orders (group-power-list p l)))))
  :hints (("Subgoal *1/2" :in-theory (enable p-groupp prime-power-p cyclic-p-group-p)
                          :use ((:instance reduce-order-powerp (n (order (car l)))
			                                       (q (least-prime-divisor (order (car l))))
							       (r (least-prime-divisor x)))
				(:instance primep-least-divisor (n x))
				(:instance primep-least-divisor (n (order (car l))))))))

(defthmd hits-orders-reduce-cyclic
  (implies (and (cyclic-p-group-list-p l)
                (primep p)
		(prime-power-p x)
		(not (equal x p)))
           (equal (hits x (orders l))
	          (hits (reduce-order x p)
		        (orders (reduce-cyclic l p)))))
  :hints (("Goal" :in-theory (enable reduce-order reduce-cyclic)
                  :use (hits-group-power-list
		        (:instance hits-orders-delete-trivial (x (reduce-order x p)) (l (group-power-list p l)))))))

(local-defthmd hits-equal-but-p-1
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(prime-power-p x)
		(permutationp (orders (reduce-cyclic l p))
		              (orders (reduce-cyclic m p)))
	        (not (equal x p)))
	   (equal (hits x (orders l))
	          (hits x (orders m))))
  :hints (("Goal" :use (hits-orders-reduce-cyclic
                        (:instance hits-orders-reduce-cyclic (l m))
			(:instance perm-equal-hits (l (orders (reduce-cyclic l p))) (m (orders (reduce-cyclic m p))) (x (reduce-order x p)))))))

(local-defthmd hits-equal-but-p-2
  (implies (and (cyclic-p-group-list-p l)
                (not (prime-power-p x)))
	   (equal (hits x (orders l))
	          0))
  :hints (("Subgoal *1/2" :in-theory (enable prime-power-p p-groupp cyclic-p-group-p))))                        

(defthmd hits-equal-but-p
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(permutationp (orders (reduce-cyclic l p))
		              (orders (reduce-cyclic m p)))
	        (not (equal x p)))
	   (equal (hits x (orders l))
	          (hits x (orders m))))
  :hints (("Goal" :use (hits-equal-but-p-1 hits-equal-but-p-2
                        (:instance hits-equal-but-p-2 (l m))))))

;; But since (orders l) and (orders m) have the same product, this must hold for p as well:

(defun hits-diff-other-aux (test p l m)
  (if (consp test)
      (if (or (equal (car test) p)
              (equal (hits (car test) l) (hits (car test) m)))
          (hits-diff-other-aux (cdr test) p l m)
	(list (car test)))
    ()))

(defund hits-diff-other (p l m)
  (hits-diff-other-aux (append l m) p l m))

(defund hits-other-cex (p l m)
  (car (hits-diff-other p l m)))

(local-defthm hits-diff-aux-diff
  (implies (hits-diff-other-aux test p l m)
           (and (not (equal (car (hits-diff-other-aux test p l m)) p))
	        (not (equal (hits (car (hits-diff-other-aux test p l m)) l)
                            (hits (car (hits-diff-other-aux test p l m)) m))))))

(local-defthmd hits-diff-other-aux-equal
  (implies (and (not (hits-diff-other-aux test p l m))
		(member-equal x test)
		(not (equal x p)))
	   (equal (hits x l) (hits x m))))

(defthmd hits-diff-other-diff
  (if (hits-diff-other p l m)
      (and (not (equal (hits-other-cex p l m) p))
           (not (equal (hits (hits-other-cex p l m) l)
                       (hits (hits-other-cex p l m) m))))
   (implies (not (equal x p))
            (equal (hits x l) (hits x m))))
  :hints (("Goal" :in-theory (enable hits-diff-other hits-other-cex)
	          :use ((:instance hits-diff-other-aux-equal (test (append l m)))))))

(defun pos-list-p (l)
  (if (consp l)
      (and (posp (car l))
           (pos-list-p (cdr l)))
    t))

(defthm pos-list-p-orders
  (implies (group-list-p l)
           (pos-list-p (orders l)))
  :hints (("Subgoal *1/2" :use ((:instance order-pos (g (car l)))))))

(local-defthm consp-orders
  (implies (consp l)
           (consp (orders l))))

(defun product-list (l)
  (if (consp l)
      (* (car l) (product-list (cdr l)))
    1))

(in-theory (disable hits-diff-perm))

(local-defthm product-list-remove1
  (implies (and (pos-list-p l)
                (member x l))
	   (equal (product-list (remove1-equal x l))
	          (/ (product-list l) x))))

(local-defthm pos-list-p-remove1
  (implies (pos-list-p l)
           (pos-list-p (remove1-equal x l))))

(defthmd perm-prod-list
  (implies (and (pos-list-p l)
                (pos-list-p m)
		(permutationp l m))
	   (equal (product-list l)
	          (product-list m))))

(defun select-p (p l)
  (if (consp l)
      (if (equal (car l) p)
          (cons p (select-p p (cdr l)))
	(select-p p (cdr l)))
    ()))

(defun delete-p (p l)
  (if (consp l)
      (if (equal (car l) p)
          (delete-p p (cdr l))
	(cons (car l) (delete-p p (cdr l))))
    ()))

(defthmd product-select-delete
  (implies (and (pos-list-p l)
                (posp p))
	   (equal (product-list l)
	          (* (product-list (select-p p l))
		     (product-list (delete-p p l))))))

(defthmd product-select
  (implies (and (pos-list-p l)
                (posp p))
	   (equal (product-list (select-p p l))
	          (expt p (hits p l)))))

(defthmd hits-delete
  (equal (hits x (delete-p p l))
         (if (equal x p)
	     0
	   (hits x l))))

(defthm pos-list-p-select-delete
  (implies (pos-list-p l)
           (and (pos-list-p (delete-p p l))
	        (pos-list-p (select-p p l)))))

(defthmd perm-delete
  (implies (and (pos-list-p l)
                (pos-list-p m)
		(posp p)
		(not (hits-diff-other p l m)))
	   (permutationp (delete-p p l) (delete-p p m)))
  :hints (("Goal" :use ((:instance hits-diff-perm (l (delete-p p l)) (m (delete-p p m)))
                        (:instance hits-diff-diff (l (delete-p p l)) (m (delete-p p m)))
			(:instance hits-diff-other-diff (x (hits-cex (delete-p p l) (delete-p p m))) (l (delete-p p l)) (m (delete-p p m)))
			(:instance hits-delete (x p))
			(:instance hits-delete (x p) (l m))
			(:instance hits-delete (x (hits-other-cex p (delete-p p l) (delete-p p m))))
			(:instance hits-delete (l m) (x (hits-other-cex p (delete-p p l) (delete-p p m))))
			(:instance hits-diff-other-diff (x (hits-other-cex p (delete-p p l) (delete-p p m))))))))

(defthmd posp-product-list
  (implies (pos-list-p l)
           (posp (product-list l))))

(local-defthmd equal-hits-other-1
  (implies (and (pos-list-p l)
                (pos-list-p m)
                (natp p)
		(> p 1)
		(not (hits-diff-other p l m))
		(equal (product-list l) (product-list m)))
	   (equal (product-list (select-p p l))
	          (product-list (select-p p m))))
  :hints (("Goal" :nonlinearp t
                  :use (perm-delete product-select-delete
                        (:instance posp-product-list (l (delete-p p l)))
                        (:instance product-select-delete (l m))
                        (:instance perm-prod-list (l (delete-p p l)) (m (delete-p p m)))))))

(local-defthm expt-equal
  (implies (and (natp n) (natp m) (natp p) (> p 1) (equal (expt p n) (expt p m)))
           (equal n m))
  :rule-classes ())

(defthmd equal-hits-other
  (implies (and (pos-list-p l)
                (pos-list-p m)
                (natp p)
		(> p 1)
		(not (hits-diff-other p l m))
		(equal (product-list l) (product-list m)))
	   (equal (hits p l) (hits p m)))
  :hints (("Goal" :use (equal-hits-other-1 product-select
                        (:instance expt-equal (n (hits p l)) (m (hits p m)))
			(:instance product-select (l m))))))

;; Combine equal-hits-other and hits-equal-but-p:

(local-defthmd permutationp-orders-1
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(equal (product-list (orders l))
		       (product-list (orders m)))
		(permutationp (orders (reduce-cyclic l p))
		              (orders (reduce-cyclic m p))))
	   (permutationp (orders l) (orders m)))
  :hints (("Goal" :use ((:instance equal-hits-other (l (orders l)) (m (orders m)))
                        (:instance hits-diff-other-diff (l (orders l)) (m (orders m)))
			(:instance hits-diff-perm (l (orders l)) (m (orders m)))
			(:instance hits-diff-diff (l (orders l)) (m (orders m)))
                        (:instance hits-equal-but-p (x (hits-other-cex p (orders l) (orders m))))
                        (:instance hits-equal-but-p (x (hits-cex (orders l) (orders m))))))))

(defthmd product-orders-product-list
  (implies (group-list-p l)
           (equal (product-list (orders l))
	          (product-orders l))))

(defthmd permutationp-orders
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(isomorphismp map (direct-product l) (direct-product m))
		(permutationp (orders (reduce-cyclic l p))
		              (orders (reduce-cyclic m p))))
	   (permutationp (orders l) (orders m)))
  :hints (("Goal" :in-theory (enable product-orders-product-list)
                  :use (permutationp-orders-1 order-of-dp
                        (:instance order-of-dp (l m))
			(:instance isomorphism-equal-orders (g (direct-product l)) (h (direct-product m)))))))


;;-------------------------------------------------------------------------------------------------------

;; The case (null (reduce-cyclic l p)) must be handled separately.  We shall show that in this case,
;; we also must have (null (reduce-cyclic m p)).  Thus, the hypothesis of permutationp-orders holds
;; trivially and (permutationp (orders l) (orders m)) follows.

(local-defthmd null-reduce-cyclic-1
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(null (reduce-cyclic l p))
		(member-equal x (group-tuples l)))
	   (equal (dp-power x p l)
	          (e-list l)))
  :hints (("Goal" :in-theory (enable member-group-tuples reduce-cyclic))
          ("Subgoal *1/19" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))))
          ("Subgoal *1/17" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))))
          ("Subgoal *1/11" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))))
          ("Subgoal *1/9" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))))
          ("Subgoal *1/16" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))
				 (:instance len-group-tuple (x (cdr x)) (l (cdr l)))))
          ("Subgoal *1/5" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))))
          ("Subgoal *1/3" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))))
          ("Subgoal *1/8" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))))
          ("Subgoal *1/15" :in-theory (enable reduce-order cyclic-p-group-p)
	                   :nonlinearp t
	                   :use ((:instance prime-power-cyclic (g (car l)))
			         (:instance divides-ord (a (car x)) (n p) (g (car l)))
				 (:instance ord-divides-order (x (car x)) (g (car l)))))))

(defthmd null-reduce-cyclic-power
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(null (reduce-cyclic l p))
		(in x (direct-product l)))
	   (equal (power x p (direct-product l))
	          (e (direct-product l))))
  :hints (("Goal" :use (null-reduce-cyclic-1 (:instance power-dp (n p))))))

(defthmd null-reduce-cyclic-power-m
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(null (reduce-cyclic l p))
		(isomorphismp map (direct-product l) (direct-product m))
		(in x (direct-product m)))
	   (equal (power x p (direct-product m))
	          (e (direct-product m))))
  :hints (("Goal" :use ((:instance isomorphismp-inv (g (direct-product l)) (h (direct-product m)))
                        (:instance null-reduce-cyclic-power (x (mapply (inv-isomorphism map (direct-product l) (direct-product m)) x)))
			(:instance power-in-g (a x) (n p) (g (direct-product m)))
			(:instance homomorphism-power (map (inv-isomorphism map (direct-product l) (direct-product m)))
						      (g (direct-product m))
						      (h (direct-product l))
						      (n p))
			(:instance homomorphism-codomain (map (inv-isomorphism map (direct-product l) (direct-product m)))
							 (g (direct-product m))
							 (h (direct-product l)))
			(:instance endomorphism-kernel-e (map (inv-isomorphism map (direct-product l) (direct-product m)))
			                                 (x (power x p (direct-product m)))
							 (g (direct-product m))
							 (h (direct-product l)))))))

(defun group-gen-list (m)
  (if (consp m)
      (cons (group-gen (car m))
            (group-gen-list (cdr m)))
    ()))

(local-defthmd group-list-p-consp
  (implies (and (group-list-p l)
                (not (null l)))
	   (consp l)))

(local-defthmd group-gen-list-in-dp
  (implies (and (cyclic-p-group-list-p m)
                (consp m))
	   (in (group-gen-list m)
	       (direct-product m)))
  :hints (("Goal" :in-theory (enable member-group-tuples cyclic-p-group-p cyclicp order-group-gen))
          ("Subgoal *1/1" :use ((:instance group-list-p-consp (l (cdr m)))))))

(defthmd power-group-gen-list
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(null (reduce-cyclic l p))
		(isomorphismp map (direct-product l) (direct-product m)))
	   (equal (dp-power (group-gen-list m) p m)
	          (e (direct-product m))))
  :hints (("Goal" :in-theory (enable power-dp)
                  :use (group-gen-list-in-dp
                        (:instance null-reduce-cyclic-power-m (x (group-gen-list m)))))))

(local-defthmd null-reduce-cyclic-5
  (implies (and (cyclic-p-group-p g)
                (primep p)
		(equal (power (group-gen g) p g)
		       (e g)))
	   (equal (order g) p))
  :hints (("Goal" :in-theory (enable cyclic-p-group-p cyclicp p-groupp)
                  :use (order-group-gen
		        (:instance primep-no-divisor (d (order g)))))))

(defthmd power-group-gen-order-p
  (implies (and (cyclic-p-group-list-p m)
                (consp m)
		(primep p)
		(equal (dp-power (group-gen-list m) p m)
		       (e-list m))
		(member-equal g m))
	   (equal (order g) p))
  :hints (("Subgoal *1/2" :use ((:instance null-reduce-cyclic-5 (g (car m)))))))

(local-defthm null-reduce-cyclic-7
  (implies (and (cyclic-p-group-list-p m)
		(member-equal g m))
	   (cyclicp g))
  :hints (("Goal" :in-theory (enable cyclic-p-group-p))))

(local-defthmd null-reduce-cyclic-8
  (implies (and (cyclic-p-group-list-p m)
                (consp m)
		(primep p)
		(equal (dp-power (group-gen-list m) p m)
		       (e-list m))
		(member-equal g m))
	   (equal (order (group-power p g))
	          1))
  :hints (("Goal" :in-theory (enable reduce-order)
                  :use (power-group-gen-order-p prime-power-cyclic))))

(local-defthmd null-reduce-cyclic-9
  (implies (and (cyclic-p-group-list-p m)
                (consp m)
		(primep p)
		(equal (dp-power (group-gen-list m) p m)
		       (e-list m)))
	   (equal (reduce-cyclic m p) ()))
  :hints (("Goal" :in-theory (e/d (reduce-cyclic) (group-power-elts)))
          ("Subgoal *1/4" :use ((:instance null-reduce-cyclic-8 (g (car m)))))
          ("Subgoal *1/2" :use ((:instance null-reduce-cyclic-8 (g (car m)))))))

(defthmd null-reduce-cyclic
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(null (reduce-cyclic l p))
		(isomorphismp map (direct-product l) (direct-product m)))
	   (null (reduce-cyclic m p)))
  :hints (("Goal" :use (power-group-gen-list null-reduce-cyclic-9))))

(defthmd null-reduce-cyclic-case
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
                (primep p)
		(or (null (reduce-cyclic l p))
		    (null (reduce-cyclic m p)))
		(isomorphismp map (direct-product l) (direct-product m)))
	   (permutationp (orders l) (orders m)))
  :hints (("Goal" :use (null-reduce-cyclic permutationp-orders
                        (:instance null-reduce-cyclic (l m) (m l) (map (inv-isomorphism map (direct-product l) (direct-product m))))
			(:instance isomorphismp-inv (g (direct-product l)) (h (direct-product m)))))))


;;-------------------------------------------------------------------------------------------------------

;; The theorem follows by induction from reduce-cyclic-product, null-reduce-cyclic-case, reduce-cyclic-p-group-list,
;; isomorphismp-reduce-cyclic, and permutationp-orders:

(defun abelian-factorization-unique-induction (l m map)
  (declare (xargs :measure (product-orders l) :hints (("Goal" :use (reduce-cyclic-product)))))
  (if (and (consp l)
           (cyclic-p-group-list-p l)
	   (consp (reduce-cyclic l (first-prime l)))
	   (consp (reduce-cyclic m (first-prime l))))
      (abelian-factorization-unique-induction (reduce-cyclic l (first-prime l))
                                              (reduce-cyclic m (first-prime l))
					      (reduce-cyclic-iso map l m (first-prime l)))
    (list l m map)))

(defthmd abelian-factorization-unique
  (implies (and (consp l)
                (consp m)
                (cyclic-p-group-list-p l)
		(cyclic-p-group-list-p m)
		(isomorphismp map (direct-product l) (direct-product m)))
	   (permutationp (orders l) (orders m)))
  :hints (("Goal" :induct (abelian-factorization-unique-induction l m map))  
          ("Subgoal *1/2" :use (primep-first-prime (:instance null-reduce-cyclic-case (p (first-prime l)))))
	  ("Subgoal *1/1" :use (primep-first-prime
	                        (:instance reduce-cyclic-p-group-list (p (first-prime l)))
	                        (:instance reduce-cyclic-p-group-list (p (first-prime l)) (l m))
				(:instance isomorphismp-reduce-cyclic (p (first-prime l)))
				(:instance permutationp-orders (p (first-prime l)))))))
				
#|
;;-------------------------------------------------------------------------------------------------------

Here is a proposal for another approach to the uniqueness proof, which I abandonned.  
Maybe some of this will be useful some day.

;; We define a total ordering of cyclic p-groups:

(defun lex2<= (p1 n1 p2 n2)
  (or (< p1 p2)
      (and (= p1 p2) (<= n1 n2))))

(defun cleq (h k)
  (lex2<= (least-prime-divisor (order h))
          (order h)
	  (least-prime-divisor (order k))
          (order k)))

;; Recognizer of an ordered list of cyclic p-groups:

(defun cleq-orderedp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (cleq (car l) (cadr l))
           (cleq-orderedp (cdr l)))
    t))

;; We shall show that any list of cyclic p-groups has an ordered permutation, by functional instantiation
;; of tleq-ordering-perm-orders, substituting cyclic-p-group-p for tleq-dom and cleq for tleq.  This
;; requires as analog of tleq-ordering-perm:

(defun cleq-min-aux (ind inds l)
  (if (consp inds)
      (cleq-min-aux (if (cleq (nth ind l) (nth (car inds) l))
                      ind
	            (car inds))
		  (cdr inds)
		  l)
    ind))

(defund cleq-min (inds l)
  (cleq-min-aux (car inds) (cdr inds) l))

(defun cleq-ordering-perm-aux (inds l)
  (declare (xargs :measure (len inds)))
  (if (and (consp inds) (consp (cdr inds)))
      (let ((min (cleq-min inds l)))
        (if (equal min (car inds))
            (cons (car inds) (cleq-ordering-perm-aux (cdr inds) l))
          (cons min (cleq-ordering-perm-aux (replace (car inds) min (cdr inds)) l))))
   inds))

(defund cleq-ordering-perm (l)
  (cleq-ordering-perm-aux (ninit (len l)) l))

;; Functinal instantiation yields the following:

(defthmd cleq-ordering-perm-orders
  (implies (and (consp l)
                (cyclic-p-group-list-p l)
           (let ((p (cleq-ordering-perm l)))
	     (and (in p (sym (len l)))
	          (cleq-orderedp (permute l p))))))

;; Thus, the reordered list is ordered.  It is also a true-list.  Since it is a permutation of l,
;; it has the same members as l, and is therefore a cyclic-p-group-list:

(defund cleq-reordering (l)
  (permute l (cleq-ordering-perm l)))

(defthmd cleq-reordering-ordered-cyclicp
  (implies (and (consp l)
                (cyclic-p-subgroup-list-p l))
	   (and (cyclic-p-subgroup-list-p (cleq-reordering l))
	        (cleq-orderedp (cleq-reordering l)))))

;; The following is a functional instance of permutationp-permute-vals:

(defthms permutationp-reordering-orders
  (implies (and (consp l)
                (cyclic-p-subgroup-list-p l))
           (permutationp (orders l) (orders (cleq-reordering l)))))

;; Now by permute-direct-product, we have an isomorphism from l to the ordered direct-product:

(defund cleq-ordering-iso (l)
  (permute-dpl-iso l (cleq-ordering-perm l)))

(defthmd isomorphismp-cleq-ordering-iso
  (implies (and (consp l)
                (cyclic-p-subgroup-list-p l))
	   (isomorphismp (cleq-ordering-iso l)
	                 (direct-product l)
			 (direct-product (cleq-reordering l)))))

;; Thus, if two direct products are isomorphic, then so are their reorderings:

(defthmd isomorphismp-cleq-reorderings
  (implies (and (consp l)
                (consp m)
                (cyclic-p-subgroup-list-p l)
		(cyclic-p-subgroup-list-p l)
		(isomorphismp map (direct-product l) (direct-product m)))
	    (isomorphismp (compose-maps (cleq-reordering-iso m)
	                                (compose-maps map
					              (inv-isomorphism (cleq-ordering-iso l))))
			  (cleq-reordering l)
			  (cleq-reordering m))))


;;------------------------------------------------------

;; Next we show that if the direct products of two ordered lists of cyclic p-groups are isomorphic,
;; then the lists of their orders are equal.

(defthmd isomorphismp-cleq-orderedp-equal-orders
  (implies (and (consp l)
                (consp m)
                (cyclic-p-subgroup-list-p l)
		(cyclic-p-subgroup-list-p l)
		(isomorphismp map (direct-product l) (direct-product m))
		(cleq-orderedp l)
		(cleq-orderedp m))
	   (equal (orders l) (orders m))))


;;------------------------------------------------------

;; Finally, combine permutationp-reordering-orders, isomorphismp-cleq-reorderings, and
;; isomorphismp-cleq-orderedp-equal-orders:

(defthmd abelian-factorization-uniqueness
  (implies (and (cyclic-p-group-list-p l)
                (cyclic-p-group-list-p m)
		(isomporpismp map (direct-product l) (direct-product m)))
	   (permutationp (orders l) (orders m))))

|#
