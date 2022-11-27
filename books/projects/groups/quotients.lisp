;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")

(local (include-book "support/groups"))
(include-book "groups")

;;---------------------------------------------------------------------------------------------------
;; Cosets
;;---------------------------------------------------------------------------------------------------

;; Informally, the left coset of a subgroup H of G determined by an element x of G is the set of
;; elements of G of the form xh, where h is in H.  In our formalization, we define a left coset
;; to be the list of these elements ordered according to group index.  This ensures that intersecting
;; cosets are equal.

;; The coset xH:

(defun lcoset-aux (x h g)
  (if (consp h)
      (insert (op x (car h) g)
              (lcoset-aux x (cdr h) g)
	      g)
    ()))

(defund lcoset (x h g)
  (lcoset-aux x (elts h) g))

;; A coset is a list of group elements:

(defthmd sublistp-lcoset-g
  (implies (and (subgroupp h g)
		(in x g))
	   (sublistp (lcoset x h g) (elts g))))

(defthmd member-lcoset-g
  (implies (and (subgroupp h g)
		(in x g)
		(member-equal y (lcoset x h g)))
	   (in y g)))

;; A coset is an ordered list of group elements:

(defthm ordp-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (ordp (lcoset x h g) g)))

;;  The length of a coset is the order of the subgroup:

(defthmd len-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (equal (len (lcoset x h g))
		  (order h))))

;; A characterization of coset elements:

(defthmd member-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y h))
	   (member-equal (op x y g) (lcoset x h g))))

(defthmd member-lcoset-iff
  (implies (and (subgroupp h g)
		(in x g)
		(in y g))
	   (iff (member-equal y (lcoset x h g))
	        (in (op (inv x g) y g) h))))

(defthmd equal-lcoset-lcoset-e
  (implies (and (subgroupp h g) (in x g)
                (equal (lcoset x h g) (lcoset (e g) h g)))
	   (in x h)))

(defthmd member-self-lcoset
  (implies (and (subgroupp h g)
		(in x g))
	   (member-equal x (lcoset x h g))))

;; Intersecting cosets are equal:

(defthmd member-lcoset-symmetry
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
	        (member-equal y (lcoset x h g)))
	   (member-equal x (lcoset y h g))))

(defthmd lcosets-intersect
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal a (lcoset x h g))
		(member-equal a (lcoset y h g))
		(member-equal b (lcoset x h g)))
	   (member-equal b (lcoset y h g))))
			
(defthmd sublistp-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal y (lcoset x h g)))
	   (sublistp (lcoset y h g) (lcoset x h g))))
	   
(defthmd equal-lcoset
  (implies (and (subgroupp h g)
		(in x g)
		(in y g)
		(member-equal y (lcoset x h g)))
	   (equal (lcoset y h g) (lcoset x h g))))

(defthmd equal-lcoset-2
  (implies (and (subgroupp h g)
		(in x1 g)
		(in x2 g)
		(in y g)
		(member-equal y (lcoset x1 h g))
		(member-equal y (lcoset x2 h g)))
	   (equal (lcoset x1 h g) (lcoset x2 h g))))
	   

;;---------------------------------------------------------------------------------------------------
;; Lagrange's Theorem
;;---------------------------------------------------------------------------------------------------

;; THEOREM: If H is a subgroup of G, the the order of G is the product of the order of H and the
;; number of left cosets of H in G.

;; A list of all left cosets of H:

(defun member-list (x l)
  (if (consp l)
      (or (member-equal x (car l))
	  (member-list x (cdr l)))
    ()))

(defun lcosets-aux (l h g)
  (if (consp l)
      (let ((cosets (lcosets-aux (cdr l) h g)))
	(if (member-list (car l) cosets)
	    cosets
	  (cons (lcoset (car l) h g) cosets)))
    ()))

(defund lcosets (h g)
  (lcosets-aux (elts g) h g))

;; The index of a subgroup:

(defund subgroup-index (h g) (len (lcosets h g)))

;; lcosets contains every lcoset:

(defthmd member-lcoset-cosets
  (implies (and (subgroupp h g)
                (in x g))
	   (member (lcoset x h g) (lcosets h g))))

(defthmd lcoset-member-lcoset
  (implies (and (subgroupp h g)
		(member-equal c (lcosets h g))
		(member-equal x c))
	   (equal (lcoset x h g) c)))

;; lcosets are distinct and non-nil:

(defthmd member-member-list
  (implies (and (consp x) (member x l))
           (member-list (car x) l)))

(defthm dlistp-lcosets
  (implies (subgroupp h g)
           (dlistp (lcosets h g))))

(defthmd lcosets-non-nil
  (implies (subgroupp h g)
           (not (member-equal () (lcosets h g)))))

(defthmd len-lcosets
  (implies (subgroupp h g)
	   (equal (len (append-list (lcosets h g)))
	          (* (order h) (subgroup-index h g)))))

(defthmd lcoset-car
  (implies (and (subgroupp h g)
		(in x g))
	   (and (in (car (lcoset x h g)) g)
	        (equal (lcoset (car (lcoset x h g)) h g)
	               (lcoset x h g)))))

(defthmd lcosets-cars
  (implies (and (subgroupp h g)
		(member c (lcosets h g)))
	   (and (in (car c ) g)
		(equal (lcoset (car c) h g)
		       c))))
	          
(defthm lcosets-disjointp-pairwise
  (implies (subgroupp h g)
	   (disjointp-pairwise (lcosets h g))))

(defthm dlistp-list-lcosets
  (implies (subgroupp h g)
	   (dlistp-list (lcosets h g))))

(defthm dlistp-append-list-lcosets
  (implies (subgroupp h g)
	   (dlistp (append-list (lcosets h g)))))

(defthm sublistp-elts-lcosets
  (implies (subgroupp h g)
	   (sublistp (elts g) (append-list (lcosets h g)))))

(defthm sublistp-lcosets-elts
  (implies (subgroupp h g)
	   (sublistp (append-list (lcosets h g))
	             (elts g))))

;; Thus, the two lists have the same length, and Lagrange's Theorem follows:

(defthmd len-append-list-lcosets
  (implies (subgroupp h g)
	   (equal (len (append-list (lcosets h g)))
	          (order g))))

(defthmd lagrange
  (implies (subgroupp h g)
           (equal (* (order h) (subgroup-index h g))
                  (order g))))

(defthmd order-subgroup-divides
  (implies (subgroupp h g)
           (divides (order h) (order g))))

(defthmd subgroup-index-pos
  (implies (subgroupp h g)
           (posp (subgroup-index h g))))

(defthmd prod-indices
  (implies (and (subgroupp h k)
                (subgroupp k g))
	   (equal (subgroup-index h g)
	          (* (subgroup-index k g)
		     (subgroup-index h k)))))

(defthmd ord-divides-order
  (implies (and (groupp g)
		(in x g))
	   (divides (ord x g) (order g))))


;;---------------------------------------------------------------------------------------------------
;; Normal Subgroups and Quotient Groups
;;---------------------------------------------------------------------------------------------------

;; The conjugate of x by a:

(defund conj (x a g)
  (op (op a x g) (inv a g) g))

(defthm conj-in-g
  (implies (and (groupp g) (in x g) (in a g))
           (in (conj x a g) g)))

(defthmd conj-op
  (implies (and (groupp g)
                (in x g)
		(in y g)
		(in a g))
	   (equal (conj (op x y g) a g)
	          (op (conj x a g) (conj y a g) g))))

(defthmd inv-conj
  (implies (and (groupp g)
                (in x g)
		(in a g))
	   (equal (conj (inv x g) a g)
	          (inv (conj x a g) g))))


(defthmd conj-commute
  (implies (and (groupp g)
                (in x g)
		(in y g))
	   (iff (equal (conj x y g) x)
	        (equal (op x y g) (op y x g)))))

(defthmd subgroup-conj
  (implies (and (subgroupp h g)
                (in x h)
		(in y h))
	   (equal (conj y x h)
	          (conj y x g))))

(defthmd centralizer-conj-iff
  (implies (and (groupp g) (in a g))
           (iff (in x (centralizer a g))
	        (and (in x g) (equal (conj a x g) a)))))

(defthm conj-e
  (implies (and (groupp g) (in x g))
           (equal (conj x (e g) g)
	          x)))

(defthmd conj-conj
  (implies (and (groupp g) (in x g) (in a g) (in b g))
           (equal (conj (conj x b g) a g)
	          (conj x (op a b g) g))))

;; h is normal in g if every conjugate of an element of h by an element of g is in h:

(defun normalp-elt (x l h g)
  (if (consp l)
      (and (in (conj x (car l) g) h)
           (normalp-elt x (cdr l) h g))
    t))

(defun normalp-aux (l h g)
  (if (consp l)
      (and (normalp-elt (car l) (elts g) h g)
           (normalp-aux (cdr l) h g))
    t))

(defund normalp (h g)
  (and (subgroupp h g)
       (normalp-aux (elts h) h g)))

(defthm normalp-subgroupp
  (implies (normalp h g)
           (subgroupp h g)))

(defthm normalp-groupp
  (implies (normalp h g)
           (and (groupp h) (groupp g))))

(defthmd normalp-conj
  (implies (and (normalp h g)
                (in x h)
		(in y g))
	   (in (conj x y g) h)))

(defthmd normalp-reverse
  (implies (and (normalp h g)
                (in x g)
		(in y g)
		(in (op x y g) h))
	   (in (op y x g) h)))

;; If h is not normal in g, then we can construct a counterexample to the definition:

(defun normalp-elt-cex (x l h g)
  (if (consp l)
      (if (in (conj x (car l) g) h)
          (normalp-elt-cex x (cdr l) h g)
	(car l))
    ()))

(defun normalp-aux-cex (l h g)
  (if (consp l)
      (if (normalp-elt (car l) (elts g) h g)
          (normalp-aux-cex (cdr l) h g)
	(list (car l) (normalp-elt-cex (car l) (elts g) h g)))
    ()))

(defund normalp-cex (h g)
  (normalp-aux-cex (elts h) h g))

(defthmd not-normalp-cex
  (let* ((cex (normalp-cex h g))
         (x (car cex))
	 (y (cadr cex)))
    (implies (and (subgroupp h g)
                  (not (normalp h g)))
	     (and (in x h)
	          (in y g)
		  (not (in (conj x y g) h))))))

;; A subgroup of an abelian group is normal:
  
(defthmd abelianp-normalp
  (implies (and (abelianp g)
		(subgroupp h g))
	   (normalp h g)))

;; We shall use defgroup to define quotient groups.

;; Identity element of the quotient group:

(defun qe (h g) (lcoset (e g) h g))

(defthm car-qe
  (implies (normalp h g)
           (equal (car (lcoset (e g) h g))
	          (e g))))

(defthm qe-exists
  (implies (subgroupp h g)
           (member-equal (qe h g) (lcosets h g))))


;; The element list of the quotient group is the coset list with the identity moved to the front:

(defun qlist (h g)
  (cons (qe h g) (remove1-equal (qe h g) (lcosets h g))))

(defthmd len-qlist
  (implies (normalp h g)
           (equal (len (qlist h g)) (subgroup-index h g))))

(defthmd member-qlist-car
  (implies (and (normalp h g)
                (member x (qlist h g)))
	   (in (car x) g)))

(defthmd car-member-qlist
  (implies (and (normalp h g)
                (member x (qlist h g)))
	   (and (in (car x) g)
	        (equal (lcoset (car x) h g)
		       x))))

(defthmd member-lcoset-qlist
  (implies (and (normalp h g) (member x (lcosets h g)))
           (member x (qlist h g))))
                

(defthmd member-lcoset-qlist-iff
  (implies (normalp h g)
           (iff (member x (qlist h g))
                (member x (lcosets h g)))))

(defthm qe-car
  (equal (car (qlist h g))
         (qe h g)))

(defthm consp-qlist
  (consp (qlist h g)))


(defthm dlistp-qlist
  (implies (normalp h g)
           (dlistp (qlist h g))))

(defthm qlist-non-nil
  (implies (normalp h g)
           (not (member-equal () (qlist h g)))))

;; The quotient group operation and inverse operator:

(defun qop (x y h g)
  (lcoset (op (car x) (car y) g) h g))

(defun qinv (x h g)
  (lcoset (inv (car x) g) h g))

(defthm op-qop
  (implies (and (normalp h g)
                (member-equal x (qlist h g)) (member-equal y (qlist h g))
		(member-equal a x) (member-equal b y))
	   (member-equal (op a b g) (qop x y h g))))

(defthm q-identity
  (implies (and (normalp h g)
                (member-equal x (qlist h g)))
	   (equal (qop (qe h g) x h g)
	          x)))

(defthm q-closed
  (implies (and (normalp h g)
                (member-equal x (qlist h g))
                (member-equal y (qlist h g)))
           (member-equal (qop x y h g) (qlist h g))))

(defthm q-assoc
  (implies (and (normalp h g)
                (member-equal x (qlist h g))
                (member-equal y (qlist h g))
                (member-equal z (qlist h g)))
	   (equal (qop x (qop y z h g) h g)
	          (qop (qop x y h g) z h g))))

(defthm q-inverse
  (implies (and (normalp h g)
                (member-equal x (qlist h g)))
	   (and (member-equal (qinv x h g) (qlist h g))
	        (equal (qop (qinv x h g) x h g) (qe h g)))))
  
;; Quotient group:

(defgroup quotient (g h)
  (normalp h g)
  (qlist h g)
  (qop x y h g)
  (qinv x h g))

(defthmd order-quotient
  (implies (normalp h g)
           (equal (order (quotient g h))
	          (subgroup-index h g))))

(defthmd quotient-e
  (implies (normalp h g)
           (equal (e (quotient g h))
	          (lcoset (e g) h g))))

(defthmd sublistp-elts-quotient-lcosets
  (implies (normalp h g)
           (sublistp (elts (quotient g h)) (lcosets h g))))

(defthmd sublistp-subgroup-lcosets
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (sublistp (elts h) (lcosets n g))))

(defthmd abelian-quotient
  (implies (and (subgroupp h g)
                (abelianp g))
	   (abelianp (quotient g h))))

(defthmd op-quotient-lcoset
  (implies (and (normalp h g)
                (in x (quotient g h ))
                (in y (quotient g h))
		(member-equal a x)
		(member-equal b y))
	   (equal (op x y (quotient g h))
	          (lcoset (op a b g) h g))))

(defthmd inv-quotient-lcoset
  (implies (and (normalp h g)
                (in x (quotient g h))
		(member-equal a x))
	   (equal (inv x (quotient g h))
	          (lcoset (inv a g) h g))))

(defthmd power-in-quotient
  (implies (and (normalp h g)
                (in x (quotient g h))
		(natp n))
	   (in (power x n (quotient g h)) (quotient g h))))

(defthmd power-lcoset
  (implies (and (normalp h g)
                (in x (quotient g h))
		(member-equal a x)
		(natp n))
	   (equal (power x n (quotient g h))
	          (lcoset (power a n g) h g))))

(defthmd ord-lcoset-divides
  (implies (and (normalp h g)
                (in x (quotient g h))
		(member-equal a x))
	   (divides (ord x (quotient g h))
		    (ord a g))))

;; In order to manage concrete quotient groups, the function quot remanes the elements of a quotient
;; group by replacing each coset with its car:

(defun collect-cars-aux (l)
  (if (consp l)
      (cons (caar l) (collect-cars-aux (cdr l)))
    ()))

(defun collect-cars (l)
  (if (consp l)
      (cons (collect-cars-aux (car l)) (collect-cars (cdr l)))
    ()))

(defun quot (g h)
  (collect-cars (quotient g h)))
