;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")

(include-book "quotients")
(local (include-book "support/groups"))

;; THEOREM: If the order of a group g is divisible by a prime p, then G has an element of order p.
 
;;---------------------------------------------------------------------------------------------------
;; Cauchy's Theorem for Abelian Groups
;;---------------------------------------------------------------------------------------------------

;; If there is an element of order divisible by n then there is an element of order n:

(defthmd exists-elt-of-ord
  (implies (and (groupp g)
                (posp n)
		(in x g)
		(divides n (ord x g)))
	   (elt-of-ord n g)))

;; A consequence of lagrange and euclid:

(defthmd divides-order-quotient
  (implies (and (groupp g)
                (abelianp g)
                (primep p)
		(divides p (order g))
                (not (elt-of-ord p g))
		(in a g))
	   (divides p (order (quotient g (cyclic a g))))))

;; Power of an element of the quotient group:

(defthmd lcoset-power
  (implies (and (normalp h g)
                (in x (quotient g h))
		(natp n))
	   (equal (power x n (quotient g h))
	          (lcoset (power (car x) n g) h g))))

(defthmd divides-ord-quotient
  (implies (and (normalp h g)
                (in x (quotient g h)))
	   (divides (ord x (quotient g h))
	            (ord (car x) g))))

;; A critical lemma for the induction:

(defthmd lift-elt-of-ord
  (implies (and (normalp h g)
                (posp m)
                (elt-of-ord m (quotient g h)))
           (elt-of-ord m g)))

(defun cauchy-abelian-induction (g)
  (declare (xargs :measure (order g)))
  (if (and (groupp g)
           (abelianp g)
	   (> (order g) 1))
      (cauchy-abelian-induction (quotient g (cyclic (cadr (elts g)) g)))
    ()))

(defthmd cauchy-abelian
  (implies (and (groupp g)
                (abelianp g)
		(primep p)
		(divides p (order g)))
	   (and (in (elt-of-ord p g) g)
	        (equal (ord (elt-of-ord p g) g) p))))


;;----------------------------------------------------------------------------------------------------------
;; Conjugacy Classes
;;----------------------------------------------------------------------------------------------------------

;; Ordered list of conjugates of x:

(defun conjs-aux (x l g)
  (if (consp l)
      (if (member-equal (conj x (car l) g)
                        (conjs-aux x (cdr l) g))
	  (conjs-aux x (cdr l) g)
	(insert (conj x (car l) g)
	        (conjs-aux x (cdr l) g)
		g))
    ()))

(defund conjs (x g) (conjs-aux x (elts g) g))

(defthm ordp-conjs
  (implies (and (groupp g) (in x g))
           (ordp (conjs x g) g)))

(defthm dlistp-conjs
  (implies (and (groupp g) (in x g))
           (dlistp (conjs x g))))

(defthmd conj-in-conjs
  (implies (and (groupp g) (in x g) (in a g))
           (member-equal (conj x a g) (conjs x g))))

;; Given a member y of that list, we would like to find the conjugator that put it there,
;; i.e., the element a such that y = (conj x a g):

(defun conjer-aux (y x l g)
  (if (consp l)
      (if (equal (conj x (car l) g) y)
          (car l)
	(conjer-aux y x (cdr l) g))
    ()))

(defund conjer (y x g) (conjer-aux y x (elts g) g))

(defthmd conjs-conjer
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (let ((c (conjer y x g)))
	     (and (in c g)
	          (equal (conj x c g) y)))))

(defthmd conjs-in-g
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (in y g)))

;; Conjugacy is an equivalence relation:

(defthmd conj-reflexive
  (implies (and (groupp g) (in x g))
           (member-equal x (conjs x g))))

(defthmd conj-symmetric
  (implies (and (groupp g) (in x g) (in y g) (member-equal y (conjs x g)))
           (member-equal x (conjs y g))))

(defthmd conj-trans
  (implies (and (groupp g) (in x g) (in y g) (in z g)
                (member-equal y (conjs x g))
                (member-equal z (conjs y g)))
           (member-equal z (conjs x g))))

;; If two conjugacy classes intersect, then they are equal:

(defthmd sublistp-conjs
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(member-equal y (conjs x g)))
	   (sublistp (conjs y g) (conjs x g))))
	   
(defthmd equal-conjs
  (implies (and (groupp g)
		(in x g)
		(in y g)
		(member-equal y (conjs x g)))
	   (equal (conjs y g) (conjs x g))))

(defthmd equal-conjs-2
  (implies (and (groupp g)
		(in x1 g)
		(in x2 g)
		(in y g)
		(member-equal y (conjs x1 g))
		(member-equal y (conjs x2 g)))
	   (equal (conjs x1 g) (conjs x2 g))))

;; 1-1 map between (conjs x g) and (lcosets (centralizer x g) g):

(defund conj2coset (y x g)
  (lcoset (conjer y x g) (centralizer x g) g))

(defund coset2conj (c x g)
  (conj x (car c) g))

(defthmd coset2conj-conj2coset
  (implies (and (groupp g) (in x g) (member-equal y (conjs x g)))
           (equal (coset2conj (conj2coset y x g) x g)
	          y)))

(defthmd conj2coset-coset2conj
  (implies (and (groupp g) (in x g) (member-equal c (lcosets (centralizer x g) g)))
           (equal (conj2coset (coset2conj c x g) x g)
	          c)))

;; This is proved by functional instantiation of len-1-1-equal:

(defthmd len-conjs-cosets
  (implies (and (groupp g) (in x g))
           (equal (len (conjs x g))
	          (subgroup-index (centralizer x g) g))))


;;----------------------------------------------------------------------------------------------------------
;; Class Equation
;;----------------------------------------------------------------------------------------------------------

;; The nontrivial conjugacy classes of g together with its center form a partition of g.
;; This provides a useful expression for the order of g.

;; A list of the nontrivial conjugacy classes:

(defun conjs-list-aux (l g)
  (if (consp l)
      (let ((conjs (conjs-list-aux (cdr l) g)))
	(if (or (in (car l) (center g))
	        (member-list (car l) conjs))
	    conjs
	  (cons (conjs (car l) g) conjs)))
    ()))

(defund conjs-list (g)
  (conjs-list-aux (elts g) g))

;; We shall show that (append (center g) (append-list (conjs-list g))) is a permutation of (elts g).

;; (append-list (conjs-list g)) contains every non-central element:

(defthmd member-lconjs-conjs-list
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g))))
	   (member (conjs x g) (conjs-list g))))

(defthmd member-append-list-conjs-list
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g))))
	   (member x (append-list (conjs-list g)))))

;; (append-list (conjs-list g)) is disjoint from the center:

(defthmd center-conjs
  (implies (and (groupp g)
                (in x g)
		(not (in x (center g)))
		(in c (center g)))
	   (not (member-equal c (conjs x g)))))

(defthmd center-conjs-list
  (implies (and (groupp g)
		(in c (center g)))
	   (not (member-equal c (append-list (conjs-list g))))))

(defthmd dlistp-conj-list
  (implies (groupp g)
           (dlistp (conjs-list g))))

;; (append (center g) (append-list (conjs-list g))) is a dlist:

(defthmd conjs-car
  (implies (and (groupp g)
		(in x g))
	   (and (in (car (conjs x g)) g)
	        (equal (conjs (car (conjs x g)) g)
	               (conjs x g)))))

(defthmd conjs-list-cars
  (implies (and (groupp g)
		(member c (conjs-list g)))
	   (and (in (car c ) g)
		(equal (conjs (car c) g)
		       c))))

(defthm conjs-list-disjointp-pairwise
  (implies (groupp g)
	   (disjointp-pairwise (conjs-list g))))

(defthm dlistp-list-conjs-list
  (implies (groupp g)
	   (dlistp-list (conjs-list g))))

(defthm dlistp-append-list-conjs-list
  (implies (groupp g)
	   (dlistp (append-list (conjs-list g)))))

(defthm dijjointp-center-conjs-list
  (implies (groupp g)
           (disjointp (elts (center g))
	              (append-list (conjs-list g)))))

(defthm dlistp-big-list
  (implies (groupp g)
           (dlistp (append (elts (center g))
	                   (append-list (conjs-list g))))))

;; The two lists are sublists of each other:

(defthm sublistp-elts-big-list
  (implies (groupp g)
           (sublistp (elts g)
                     (append (elts (center g))
	                     (append-list (conjs-list g))))))

(defthm sublistp-conjs-list-elts
  (implies (groupp g)
	   (sublistp (append-list (conjs-list g))
	             (elts g))))

(defthm sublistp-big-list-elts
  (implies (groupp g)
	   (sublistp (append (elts (center g))
	                     (append-list (conjs-list g)))
	             (elts g))))

;; Thus, the two lists have the same length:

(defthmd class-equation
  (implies (groupp g)
	   (equal (len (append (elts (center g))
	                       (append-list (conjs-list g))))
	          (order g))))


;;----------------------------------------------------------------------------------------------------------
;; Cauchy's Theorem for Non-abelian Groups
;;----------------------------------------------------------------------------------------------------------

;; Search for a non-central group element the centralizer of which has order divisible by p:

(defun find-elt-aux (l g p)
  (if (consp l)
      (if (and (not (in (car l) (center g)))
               (divides p (order (centralizer (car l) g))))
	  (car l)
	(find-elt-aux (cdr l) g p))
    ()))

(defund find-elt (g p) (find-elt-aux (elts g) g p))

;; If such an element exists, then since it in not in the center, the order of its centralizer is
;; less than that of g:

(defthmd find-elt-centralizer
  (implies (and (groupp g)
                (primep p)
                (find-elt g p))
	   (let ((cent (centralizer (find-elt g p) g)))
	     (and (subgroupp cent g)
	          (< (order cent) (order g))
		  (divides p (order cent))))))

;; Assume that p divides the order of g.  If no such element exists, then the length of every nontrivial
;; cojugacy class is divisible by p, and according to the class equation, so is the order of the center:

(defthmd find-elt-center
  (implies (and (groupp g)
                (primep p)
		(divides p (order g))
                (null (find-elt g p)))
	   (divides p (order (center g)))))

;; Clearly, if any subgroup of g has an element of order p, then so does g:

(defthmd ord-subgroup
  (implies (and (subgroupp h g)
                (in x h))
	   (equal (ord x h) (ord x g))))

(defthmd elt-of-ord-subgroup
  (implies (and (groupp g)
                (natp n)
		(subgroupp h g)
		(elt-of-ord n h))
	   (elt-of-ord n g)))

;; The theorem follows by induction:

(defun cauchy-induction (g p)
  (declare (xargs :measure (order g)))
  (if (and (groupp g)
           (primep p)
	   (find-elt g p))
      (cauchy-induction (centralizer (find-elt g p) g) p)
    t))

(defthmd cauchy
  (implies (and (groupp g)
		(primep p)
		(divides p (order g)))
	   (and (in (elt-of-ord p g) g)
	        (equal (ord (elt-of-ord p g) g) p))))


;;------------------------------------------------------------------------------------------------------
;; Prime Powers and p-Groups
;;------------------------------------------------------------------------------------------------------

;; Recognizer of powers of n, where n > 1:

(defun powerp (n p)
  (if (and (natp p) (> p 1) (posp n) (divides p n))
      (powerp (/ n p) p)
    (equal n 1)))

(defthmd p-divides-power-p
  (implies (and (powerp n p)
                (not (equal n 1)))
	   (divides p n)))

(defun log (n p)
  (if (and (natp p) (> p 1) (posp n) (integerp (/ n p)))
      (1+ (log (/ n p) p))
    0))

(defthmd max-power-p-dividing
  (implies (and (primep p)
                (posp n)
		(natp k))
	   (iff (divides (expt p k) n)
	        (<= k (log n p)))))

(defthmd powerp-log
  (implies (and (natp p) (> p 1) (powerp n p))
           (equal (expt p (log n p)) n)))

(defthm powerp-power
  (implies (and (natp p) (> p 1) (natp n))
           (powerp (expt p n) p)))

;; Any divisor of a power of a prime p is a power of p:

(defthmd divides-power
  (implies (and (primep p) (natp k) (posp m) (divides m (expt p k)))
           (powerp m p)))

(defthmd powerp-divides
  (implies (and (primep p) (powerp n p) (posp m) (divides m n))
           (powerp m p)))

;; A prime is a power only of itself:

(defthm not-powerp-prime
  (implies (and (primep q) (posp n) (powerp q n))
           (equal q n))
  :rule-classes ())

;; p is the only prime divisor of a power of p:

(defthm powerp-prime-divisor
  (implies (and (primep p)
                (primep q)
		(powerp n p)
		(divides q n))
           (equal p q))
  :rule-classes ())

;; p is the least prime divisor of a power of p:

(defthmd least-prime-divisor-powerp
  (implies (and (powerp n p)
                (primep p)                
                (> n 1))
	   (equal (least-prime-divisor n)
	          p)))

;; The least (prime) divisor of n other than p:

(defun least-divisor-not-p (n p)
  (declare (xargs :measure (nfix n)))
  (if (and (natp n) (> n 1))
      (let ((q (least-prime-divisor n)))
        (if (= q p)
	    (least-divisor-not-p (/ n p) p)
	  q))
    ()))

;; In n is not a power of prime p, then n has a prime divisor other than p:

(defthmd primep-least-divisor-not-p
  (implies (and (natp n)
                (> n 1)
                (primep p)
		(not (powerp n p)))
	   (let ((q (least-divisor-not-p n p)))
	     (and (primep q)
	          (not (= q p))
	          (divides q n)))))

;; A p-group is usually defined to be a group in which the order of every element is a power of p.
;; For finite groups, as a consequence of Cauchy's Theorem, this is equivalent to the following
;; (see not-p-groupp-not-powerp-ord below):

(defund p-groupp (g p)
  (and (primep p)
       (groupp g)
       (powerp (order g) p)))

;; The order of an element of a p-group is a power of p:

(defthmd p-groupp-ord-powerp
  (implies (and (p-groupp g p)
		(in x g))
	   (powerp (ord x g) p)))

;; The converse is a consequence of cauchy's theorem:

(defthmd not-p-groupp-divisor
  (implies (and (primep p)
                (groupp g)
		(> (order g) 1)
		(not (p-groupp g p)))
	   (let ((q (least-divisor-not-p (order g) p)))
	     (and (primep q)
	          (not (= q p))
	          (divides q (order g))))))

(defthmd not-p-groupp-ord-prime
  (implies (and (primep p)
                (groupp g)
		(> (order g) 1)
		(not (p-groupp g p)))
	   (let* ((q (least-divisor-not-p (order g) p))
	          (x (elt-of-ord q g)))
	     (and (primep q)
	          (not (= q p))
		  (in x g)
	          (equal (ord x g) q)))))

(defthmd not-p-groupp-not-powerp-ord
  (implies (and (primep p)
                (groupp g)
		(> (order g) 1)
		(not (p-groupp g p)))
	   (let* ((q (least-divisor-not-p (order g) p))
	          (x (elt-of-ord q g)))
	     (not (powerp (ord x g) p)))))

;; Another consequence of the class equation is that the center of a non-trivial p-group is non-trivial:

(defthm center-p-group
  (implies (and (primep p)
                (p-groupp g p)                
		(> (order g) 1))
	   (divides p (order (center g)))))

;; If g is a group of order p^2, then the quotient of its center must be cyclic, and by quotient-center-cyclic-abelian,
;; g is abelian:

(defthmd p-squared-abelian
  (implies (and (groupp g)
		(primep p)
		(equal (order g) (* p p)))
	   (abelianp g)))
