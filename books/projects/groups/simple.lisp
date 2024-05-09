(in-package "DM")

(local (include-book "support/alt5"))
(local (include-book "support/simple"))
(include-book "sylow")

;; A simple group is one that does not have a proper normal subgroup:

(defund proper-normalp (h g)
  (and (normalp h g)
       (> (order h) 1)
       (< (order h) (order g))))

;;  For example, (alt 4) is not simple:

(defund normal-subgroup-of-alt-4 ()
  (subgroup '((0 1 2 3) (1 0 3 2) (2 3 0 1) (3 2 1 0))
	    (sym 4)))

(defthmd alt-4-not-simple
  (proper-normalp (normal-subgroup-of-alt-4) (alt 4))
  :hints (("Goal" :in-theory (enable alt proper-normalp))))

;; However, (alt n) is simple for all n > 4.  For no reason other than sheer laziness, we shall prove
;; this only for n = 5.  We shall also show that if the order of g is a composite number less than
;; (order (alt 5)) = 60, then g is not simple.


;;---------------------------------------------------------------------------------------------------
;; Simplicity of (alt 5)
;;---------------------------------------------------------------------------------------------------

;; Let h be a normal subgroup of g.  If x is in h, then (conjs x g) is a sublist of (elts h).  We define
;; (select-conjs (conjs-list g) h) to be a list of all non-trivial conjugacy classes that are included in h:

(defun select-conjs (l h)
  (if (consp l)
      (if (in (caar l) h)
	  (cons (car l) (select-conjs (cdr l) h))
	(select-conjs (cdr l) h))
    ()))

;; Thus, if we append the elements of that list and throw in the elements of h that belong to the center, 
;; we have a permutation of the elements of h.  In the case of interest the center happens to be trivial:

(defthmd permp-select-conjs
  (implies (and (normalp h g)
                (equal (cent-elts g) (list (e g))))
           (permp (cons (e g) (append-list (select-conjs (conjs-list g) h)))
	          (elts h))))

;; This gives us an expression for the order of h:

(defthmd len-select-conjs
  (implies (and (normalp h g)
                (equal (cent-elts g) (list (e g))))
           (equal (order h)
	          (1+ (len (append-list (select-conjs (conjs-list g) h)))))))

;; Thus, (order h) = (1+ (len (append-list l))) for some dlist sublist l of (conjs-list g).  We shall compute this
;; value for all such sublists of (conjs-list (alt 5)) and observe that none of these values is a proper divisor of
;; 60, and therefore none of these values can be the order of a proper subgroup of (alt 5).

;; Unfortunately, the function conjs-list is computationally impractical for a group of order 60.  We shall define a
;; more efficient equivalent function, based on a tail-recursive version of conjs:

(defun conjs-fast-aux (x l m g)
  (if (consp l)
      (let ((c (conj x (car l) g)))
        (if (member-equal c m)
	    (conjs-fast-aux x (cdr l) m g)
	  (conjs-fast-aux x (cdr l) (insert c m g) g)))
    m))

(defun conjs-fast (x g)
  (conjs-fast-aux x (elts g) () g))

(defthmd conjs-fast-conjs
  (implies (and (groupp g)
		(in x g))
	   (equal (conjs-fast x g)
		  (conjs x g))))


(defun conjs-list-fast-aux (l g)
  (if (consp l)
      (let ((conjs (conjs-list-fast-aux (cdr l) g)))
	(if (or (in (car l) (center g))
	        (member-list (car l) conjs))
	    conjs
	  (cons (conjs-fast (car l) g) conjs)))
    ()))

(defund conjs-list-fast (g)
  (conjs-list-fast-aux (elts g) g))

(defthmd conjs-list-fast-conjs-list
  (implies (groupp g)
	   (equal (conjs-list-fast g)
	          (conjs-list g))))

;; The lengths of the conjugacy classes can now be easily computed using conj-list-fast:

(defun lens (l)
  (if (consp l)
      (cons (len (car l)) (lens (cdr l)))
    ()))

(defthmd lens-conjs-list-alt-5
  (equal (lens (conjs-list-fast (alt 5)))
         '(20 12 12 15)))

;; Clearly, no sublist of this list has a sum that is 1 less than a divisor of 60.  To prove this, we shall 
;; compute a list of numbers that contains (len (append-list s)) for every sublist s of (conjs-list (alt 5)).

;; A list of the sublists of a list:

(defun sublists (l)
  (if (consp l)
      (append (conses (car l) (sublists (cdr l)))
	      (sublists (cdr l)))
    (list ())))

;; In particular, (select-conjs l h) must be one of these sublists:

(defthmd member-select-conjs
  (member-equal (select-conjs l h)
                (sublists l)))

;; If l is a list of lists of lists, then for every s in l, (len (append-list s)) is a member of
;; (append-lens l), which is defined as follows:

(defun append-lens (l)
  (if (consp l)
      (cons (len (append-list (car l)))
            (append-lens (cdr l)))
    ()))

(defthmd member-append-len
  (implies (member-equal s l)
           (member-equal (len (append-list s))
	                 (append-lens l))))

;; This provides a list that contains the order of any normal subgroup.  Note that we invoke the equivalence
;; of conjs-list-fast and conjs-list:

(defun add1-list (l)
  (if (consp l)
      (cons (1+ (car l)) (add1-list (cdr l)))
    ()))

(defthmd normalp-order
  (implies (and (normalp h g)
                (equal (cent-elts g) (list (e g))))
	   (member-equal (order h)
	                 (add1-list (append-lens (sublists (conjs-list-fast g)))))))

;; The case g = (alt 5), by direct computation:

(defthmd normalp-lens-alt-5
  (and (equal (cent-elts (alt 5)) (list (e (alt 5))))
       (equal (add1-list (append-lens (sublists (conjs-list-fast (alt 5)))))
              '(60 45 48 33 48 33 36 21 40 25 28 13 28 13 16 1))))

;; Finally, using lagrange, we observe that none of these values can be the order of a proper subgroup:

(defthmd alt-5-simple
  (not (proper-normalp h (alt 5))))


;;---------------------------------------------------------------------------------------------------
;; Groups of Order Less Than 60
;;---------------------------------------------------------------------------------------------------

;; For every composite n < 60, we shall construct a proper normal subgroup of a given group g of 
;; order n.  The proof for a prime power is based on center-p-group; the other cases are based mainly 
;; on the Sylow theorems.

;; Notation: If p is a prime dividing (order g), we shall denote (sylow-subgroup g p) by hp,
;; and (len (conjs-sub hp g)) by np.

;; We have the following cases.

;; n = p^k, where p is prime and k > 1: By center-p-group, (order (center g)) > 1.  If
;; (order (center g)) < (order g), then (center (g)) is a proper normal subgroup by normalp-center.
;; But in the remaining case, (center g) = g by ordp-subgroup-equal, and hence g is abelian by
;; abelianp-center.  By cauchy, g has an element of order p.  By order-ord, (cyclic (elt-of-ord p g) g) 
;; is a subgroup of order p, and by abelianp-normal, it is a proper normal subgroup.

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
	   (proper-normalp (normal-subgroup-prime-power p k g) g)))

;; n = pq, where p and q are primes and p < q: By the Sylow theorems, nq divides p and (mod nq p) = 1.
;; It follows that np = 1, and by len-conjs-sub-normalp, (sylow-subgroup g q) is normal in g.

(defund normal-subgroup-pq (p q g)
  (declare (ignore p))
  (sylow-subgroup g q))

(defthm proper-normalp-pq
  (implies (and (groupp g)
                (equal (order g) (* p q))
		(primep p)
		(primep q)
		(< p q))
	   (proper-normalp (normal-subgroup-pq p q g) g)))

;; n = ppq, where p and q are primes: We must show that either np = 1 or nq = 1.  Suppose not.  Since
;; np divides q and (mod np p) = 1, q > p.  Since nq divides p^2 and (mod nq q) = 1, nq = p^2 and q
;; divides p^2 - 1.  Thus, q divides either p - 1 or p + 1.  Since q > p, q = p + 1, which implies p = 2,
;; q = 3, and (order g) = 12. Since n3 = 4, g has 4*2 = 8 elements of order 3.  Since n2 > 1, g has more
;; than 4 elements of order dividing 4, a contradiction.

(defund normal-subgroup-ppq (p q g)
  (if (normalp (sylow-subgroup g p) g)
      (sylow-subgroup g p)
    (sylow-subgroup g q)))

(defthm proper-normalp-ppq
  (implies (and (groupp g)
                (equal (order g) (* p p q))
		(primep p)
		(primep q)
		(not (equal p q)))
	   (proper-normalp (normal-subgroup-ppq p q g) g)))

;; There are 8 remaining cases, which are treated individually: 24, 30, 36, 40, 42, 48, 54, and 56.
;; The cases 40, 42, and 54 follow easily from the Sylow theorems.

;; n = 40: Since n5 divides 8 and (mod n5 5) = 1, n5 = 1 and h5 is normal in g.

(defund normal-subgroup-40 (g)
  (sylow-subgroup g 5))

(defthm proper-normalp-40
  (implies (and (groupp g)
                (equal (order g) 40))
	   (proper-normalp (normal-subgroup-40 g) g)))

;; n = 42: Since n7 divides 6 and (mod n7 7) = 1, n7 = 1 and h7 is normal in g.

(defund normal-subgroup-42 (g)
  (sylow-subgroup g 7))

(defthm proper-normalp-42
  (implies (and (groupp g)
                (equal (order g) 42))
	   (proper-normalp (normal-subgroup-42 g) g)))

;; n = 54: Since n3 divides 2 and (mod n3 3) = 1, n3 = 1 and h3 is normal in g.

(defund normal-subgroup-54 (g)
  (sylow-subgroup g 3))

(defthm proper-normalp-54
  (implies (and (groupp g)
                (equal (order g) 54))
	   (proper-normalp (normal-subgroup-54 g) g)))

;; The cases 56 and 30 involve counting elements of different orders.

;; n = 56: Suppose n7 > 1.  Then n7 = 8, which means that g has 8 distinct subgroups of order 8,
;; every pair of which intersect trivially.  Thus, g has 8*6 = 48 elements of ord 7.  Therefore,
;; g has no more than 8 elements of order dividing 8, which implies n2 = 1.

(defund normal-subgroup-56 (g)
  (if (normalp (sylow-subgroup g 2) g)
      (sylow-subgroup g 2)
    (sylow-subgroup g 7)))

(defthm proper-normalp-56
  (implies (and (groupp g)
                (equal (order g) 56))
	   (proper-normalp (normal-subgroup-56 g) g)))

;; n = 30: Suppose n3 > 1 and n5 > 1.  Then n3 = 10 and m5 = 6.  Consequently, g has 10*2 = 20
;; elements of ord 3 and 6*4 = 24 elements of ord 5, a contradiction.

(defund normal-subgroup-30 (g)
  (if (normalp (sylow-subgroup g 3) g)
      (sylow-subgroup g 3)
    (sylow-subgroup g 5)))

(defthm proper-normalp-30
  (implies (and (groupp g)
                (equal (order g) 30))
	   (proper-normalp (normal-subgroup-30 g) g)))

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

(defthm proper-normalp-24
  (implies (and (groupp g)
                (equal (order g) 24))
	   (proper-normalp (normal-subgroup-24 g) g)))

;; n = 48: Suppose n2 > 1.  Let h21 and h22 be distinct members of (conj-subs h2 g).  Then (order h21)
;; = order h22) = 8.  Let k = (group-intersection h21 h22 g).  Then (order k) divides 8 and

;;    (len (products h21 h22 g)) = 16*16/(order k) <= 48,

;; which implies (order k) = 8 and (len (products h21 h22 g)) = 32.  By index-least-divisor-normal,
;; k is normal in both h21 and h22.  It follows that

;;  (order (normalizer k g)) >= (len (products h21 h22 g)) = 32

;; and therefore (normalizer k g) = g and k is normal in g.

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
	   (proper-normalp (normal-subgroup-48 g) g)))

;; n = 36: Suppose n3 > 1.  Let h31 and h32 be distinct members of (conj-subs h3 g).  Then (order h31)
;; = order h32) = 9.  Let k = (group-intersection h31 h32 g).  Then (order k) <= 3 and

;;    (len (products h31 h32 g)) = 9*9/(order k) <= 36,

;; which implies (order k) = 3 and (len (products h31 h32 g)) = 27.  By index-least-divisor-normal,
;; k is normal in both h31 and h32.  It follows that

;;  (order (normalizer k g)) >= (len (products h31 h32 g)) = 27

;; and therefore (normalizer k g) = g and k is normal in g.

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
	   (proper-normalp (normal-subgroup-36 g) g)))

;; Assemble the functions defined above:

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

;; The final result:

(defthm no-simple-group-of-composite-order<60
  (implies (and (natp n)
		(> n 1)
		(< n 60)
		(not (primep n))
		(groupp g)
		(equal (order g) n))
	   (proper-normalp (normal-subgroup g) g)))
