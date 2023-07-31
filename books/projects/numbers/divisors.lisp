(in-package "DM")

(include-book "euclid")
(include-book "projects/groups/lists" :dir :system)

(local (include-book "support/divisors"))

;; A list of the divisors of n:

(defun divisors-aux (k n)
  (if (zp k)
      ()
    (if (divides k n)
	(cons k (divisors-aux (1- k) n))
      (divisors-aux (1- k) n))))

(defund divisors (n)
  (divisors-aux n n))

;; (divisors n) is a dlist whose members are the divisors of n:

(defthmd member-divisors
  (implies (posp n)
	   (iff (member-equal k (divisors n))
		(and (posp k) (divides k n)))))

(defthm dlistp-divisors
  (implies (posp n)
	   (dlistp (divisors n))))

(defun pos-listp (l)
  (if (consp l)
      (and (posp (car l))
           (pos-listp (cdr l)))
    (null l)))

(defthm pos-listp-divisors
  (implies (and (posp n) (true-listp l) (sublistp l (divisors n)))
           (pos-listp l)))

;; We shall prove that the number of divisors of n is a multiplicative function of n:

;; (defthmd len-divisors-multiplicative
;;   (implies (and (posp m) (posp n) (equal (gcd m n) 1))
;;            (equal (len (divisors (* m n)))
;;                   (* (len (divisors m)) (len (divisors n))))))

;; We shall also prove the same about the sum of the divisors of n:

(defun sum-list (l)
  (if (consp l)
      (+ (car l) (sum-list (cdr l)))
    0))

;; (defthmd sum-divisors-multiplicative
;;   (implies (and (posp m) (posp n) (equal (gcd m n) 1))
;;            (equal (sum-list (divisors (* m n)))
;;                   (* (sum-list (divisors m))
;;                      (sum-list (divisors n))))))

;; These results lead to convenient formulas for both quantities.

;; We begin by defining the Cartesian product of 2 lists:

(defun pairs (l r)
  (if (consp l)
      (append (conses (car l) r)
	      (pairs (cdr l) r))
    ()))

(defthm len-pairs
  (equal (len (pairs l r))
	 (* (len l) (len r))))

(defthmd member-pairs
  (iff (member-equal x (pairs l r))
       (and (consp x)
	    (member-equal (car x) l)
	    (member-equal (cdr x) r))))

(defthm dlistp-pairs
  (implies (and (dlistp l) (dlistp r))
	   (dlistp (pairs l r))))

;; Let m and n be positive relatively prime integers.  If a and b are divisors of
;; m and n, respectively, then a * b is a divisor of m * n.  In fact, this induces
;; a bijection from (pairs (divisors m) (divisors n)) to (divisors (* m n)):

(defun prod-divisors (x)
  (* (car x) (cdr x)))

;; Its inverse is the following function:

(defund factor-divisor (x m n)
  (cons (gcd x m) (gcd x n)))

;; We must show that each composition is the identity.

;; Suppose a and b are divisors of m and n, respectively.  We shall show that
;; (gcd a*b m) = a.  
;; Let g = (gcd a*b m).  Since a divides both a * b and m, a divides g.  Since 
;; (gcd g b) divides b, (gcd g b) divides n.  But since (gcd g b) divides g, 
;; (gcd g b) divides m, which implies (gcd g b) = 1.  Since g divides a * b,
;; divides-product-divides-factor implies g divides a, and hence g = a.

(defthmd gcd-ab-m
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (posp a) (posp b) (divides a m) (divides b n))
	   (equal (gcd (* a b) m) a)))

;; Similarly, Similarly, (gcd a*b n) = b.  It follows that the composition of
;; factor-divisor and prod-divisors is the identity on
;; (pairs (divisors m) (divisors n)) :

(defthmd factor-prod
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(member-equal x (pairs (divisors m) (divisors n))))
	   (and (member-equal (* (car x) (cdr x)) (divisors (* m n)))
		(equal (factor-divisor (prod-divisors x) m n)
		       x))))

;; Supoose x is a divisor of m * n.  Let g1 = (gcd x m) and g2 = (gcd x n).  We
;; shall show that x = g1 * g2.  By gcd-quotient-2, (gcd x/g1 m/g1) = g1/g1 = 1. 
;; Since x divides x = m * n, x/g1 divides (m/g1) * n, and by 
;; divides-product-divides-factor, x/g1 divides n.  Since x/g1 also divides x, x/g1
;; divides g2, and hence x divides g1 * g2.
;; Let g3 = (gcd g1 g2).  Since g3 divides g1 and g1 divides m, g3 divides m.
;; Similarly, g3 divides n, which implies g3 = 1.  By product-rel-prime-divides,
;; since g1 and g2 both divide x, g1 * g2 divides x, and hence x = g1 * g2.

(defthmd prod-gcds
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (equal (* (gcd x m) (gcd x n)) x)))

;; It follows that the other composition is the identity on (divisors (* m n)):

(defthmd prod-factor
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(member-equal x (divisors (* m n))))
	   (and (member-equal (factor-divisor x m n) (pairs (divisors m) (divisors n)))
		(equal (prod-divisors (factor-divisor x m n))
		       x))))

;; It follows by functional instantiation of len-1-1-equal that the lists have the
;; same length:

(defthmd len-divisors-multiplicative
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
	   (equal (len (divisors (* m n)))
		  (* (len (divisors m)) (len (divisors n))))))

;; The list of products of a list of pairs:

(defun prods (l)
  (if (consp l)
      (cons (prod-divisors (car l))
            (prods (cdr l)))
    ()))

;; (prods (pairs (divisors m) (divisors n))) is a dlist and a sublist of 
;; (divisors (* m n)) of the same length.  It is therefore a permutation of
;; (divisors (* m n)):

(defthmd dlistp-prods-pairs
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
	   (dlistp (prods (pairs (divisors m) (divisors n))))))

(defthmd sublistp-prods
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
	   (sublistp (prods (pairs (divisors m) (divisors n)))
	             (divisors (* m n)))))

(defthm len-prods
  (equal (len (prods l)) (len l)))

(defthmd permp-divisors
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
           (permutationp (prods (pairs (divisors m) (divisors n)))
	                 (divisors (* m n)))))

;; We shall prove sum-divisors-multiplicative as a special case of a more general
;; theorem.  Let mu be an arbitrary multiplicative function:

(encapsulate (((mu *) => *))
  (local (defun mu (x) x))
  (defthm rationalp-mu
    (implies (posp n) (rationalp (mu n)))
    :rule-classes (:type-prescription :rewrite))
  (defthmd mu-mult
    (implies (and (posp m) (posp n) (equal (gcd m n) 1))
             (equal (mu (* m n)) (* (mu m) (mu n))))))

;; The following function applies mu to each member of a list and sums the values:

(defun sum-mu (l)
  (if (consp l)
      (+ (mu (car l)) (sum-mu (cdr l)))
    0))

;; Note that (sum-mu l) is invariant under permutation of l:

(defthmd sum-mu-perm
  (implies (and (pos-listp l) (permutationp r l))
           (equal (sum-mu l) (sum-mu r))))

;; Our objective is to prove that

;;   (sum-mu (divisors (* m n)) = (sum-mu (divisors m)) * (sum-mu (divisors n)).

;; This requires 4 induction steps:

(defthm sum-mu-append
  (implies (and (pos-listp l) (pos-listp r))
           (equal (sum-mu (append l r))
                  (+ (sum-mu l) (sum-mu r)))))

(defthm prods-append
  (equal (prods (append l r))
         (append (prods l) (prods r))))

(defthmd sum-mu-prods-conses
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (member-equal d (divisors m))
		(sublistp l (divisors n)))
	   (equal (sum-mu (prods (conses d l)))
	          (* (mu d) (sum-mu l)))))

(defthmd sum-mu-prods-pairs
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (true-listp l) (sublistp l (divisors m)))
	   (equal (sum-mu (prods (pairs l (divisors n)))) 
	          (* (sum-mu l) (sum-mu (divisors n))))))

;; Now instantiate sum-mu-prods-pairs:

(defthmd sum-mu-prods-divisors
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
           (equal (sum-mu (prods (pairs (divisors m) (divisors n))))
	          (* (sum-mu (divisors m))
		     (sum-mu (divisors n))))))

;; The desired result follows from permp-divisors and sum-mu-perm:

(defthmd sum-mu-divisors-multiplicative
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
           (equal (sum-mu (divisors (* m n)))
	          (* (sum-mu (divisors m))
		     (sum-mu (divisors n))))))

;; For any integer k, (expt x k) is a multiplicative function of x.  We functionally
;; instantiate the last result, substituting (lambda (x) (expt x k)) for mu and
;; the following for sum-mu:

(defun sum-powers (l k)
  (if (consp l)
      (+ (expt (car l) k)
         (sum-powers (cdr l) k))
    0))

(defthmd sum-powers-divisors-multiplicative
  (implies (and (posp m) (posp n) (equal (gcd m n) 1) (integerp k))
           (equal (sum-powers (divisors (* m n)) k)
	          (* (sum-powers (divisors m) k)
		     (sum-powers (divisors n) k)))))

;; The cases of interest are k = 0, which we have already proved, and k = 1:

(defthmd sum-divisors-multiplicative
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
           (equal (sum-list (divisors (* m n)))
	          (* (sum-list (divisors m))
		     (sum-list (divisors n))))))

;; len-divisors-multiplicative and sum-divisors-multiplicative lead to formulas
;; for the number of divisors of n and the sum of the divisors of n.

;; The divisors of a prime power:

(defun power-list (p k)
  (if (posp k)
      (cons (expt p k) (power-list p (1- k)))
    (list 1)))

(defthmd prime-power-divisors
  (implies (and (primep p) (natp k))
           (equal (divisors (expt p k))
	          (power-list p k))))

;; len-divisors-multiplicative and prime-fact-existence yield a formula for the
;; number of divisors of n:

(defthmd len-prime-power-divisors
  (implies (and (primep p) (natp k))
           (equal (len (divisors (expt p k)))
	          (1+ k))))

(defun len-divisors-aux (l)
  (if (consp l)
      (* (1+ (cdar l))
	 (len-divisors-aux (cdr l)))
    1))

(defund len-divisors (n)
  (len-divisors-aux (prime-fact n)))

(defthm len-divisors-aux-pow-prod
  (implies (prime-pow-list-p l)
           (equal (len-divisors-aux l)
	          (len (divisors (pow-prod l))))))

(defthmd correctness-of-len-divisors
  (implies (posp n)
           (equal (len (divisors n))
	          (len-divisors n))))

;; sum-divisors-multiplicative and prime-fact-existence yield a formula for the
;; sum of the divisors of n:

(defthmd sum-list-power-list
  (implies (and (primep p) (natp k))
           (equal (sum-list (power-list p k))
	          (/ (1- (expt p (1+ k)))
		     (1- p)))))

(defthmd sum-prime-power-divisors
  (implies (and (primep p) (natp k))
           (equal (sum-list (divisors (expt p k)))
	          (/ (1- (expt p (1+ k)))
		     (1- p)))))

(defun sum-divisors-aux (l)
  (if (consp l)
      (* (/ (1- (expt (caar l) (1+ (cdar l))))
            (1- (caar l)))
	 (sum-divisors-aux (cdr l)))
    1))

(defund sum-divisors (n)
  (sum-divisors-aux (prime-fact n)))

(defthm sum-divisors-aux-pow-prod
  (implies (prime-pow-list-p l)
           (equal (sum-divisors-aux l)
	          (sum-list (divisors (pow-prod l))))))

(defthmd correctness-of-sum-divisors
  (implies (posp n)
           (equal (sum-list (divisors n))
	          (sum-divisors n))))
