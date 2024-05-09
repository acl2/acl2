(in-package "DM")

(include-book "euclid")
(include-book "fta")
(include-book "projects/groups/lists" :dir :system)
(include-book "projects/groups/cauchy" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

(in-theory (enable divides))

;; A list of the divisors of n:

(defun divisors-aux (k n)
  (if (zp k)
      ()
    (if (divides k n)
	(cons k (divisors-aux (1- k) n))
      (divisors-aux (1- k) n))))

(defund divisors (n)
  (divisors-aux n n))

(local-defthm member-divisors-aux
  (implies (and (posp n) (natp k))
	   (iff (member-equal j (divisors-aux k n))
		(and (posp j) (<= j k) (divides j n)))))

;; (divisors n) is a dlist whose members are all divisors of n:

(defthmd member-divisors
  (implies (posp n)
	   (iff (member-equal k (divisors n))
		(and (posp k) (divides k n))))
  :hints (("Goal" :in-theory (enable divisors)
                  :use ((:instance member-divisors-aux (j k) (k n))
		        (:instance divides-leq (x k) (y n))))))

(local-defthm dlistp-divisors-aux
  (implies (and (posp n) (natp k))
	   (dlistp (divisors-aux k n))))

(defthm dlistp-divisors
  (implies (posp n)
	   (dlistp (divisors n)))
  :hints (("Goal" :in-theory (enable divisors))))

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

;; These results lead to convenient formulas for both quantities, the second of
;; which will be used to derive a characterization of the even perfect numbers.

;; We begin by defining the Cartesian product of 2 lists:

(defun cart-prod (l r)
  (if (consp l)
      (append (conses (car l) r)
	      (cart-prod (cdr l) r))
    ()))

(local-defthm len-append
  (equal  (len (append l r)) (+ (len l) (len r))))

(local-defthm len-conses
  (equal (len (conses x l))
         (len l)))

(defthm len-cart-prod
  (equal (len (cart-prod l r))
	 (* (len l) (len r))))

(local-defthmd member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
	   (member-equal x m))))

(local-defthm consp-conses
  (implies (member-equal y (conses x l))
           (consp y)))

(defthmd member-cart-prod
  (iff (member-equal x (cart-prod l r))
       (and (consp x)
	    (member-equal (car x) l)
	    (member-equal (cdr x) r)))
  :hints (("Goal" :in-theory (enable member-append))))

(local-defthm member-cons-conses
  (implies (member (cons x y) (conses x l))
           (member y l)))

(local-defthm dlistp-conses
  (implies (dlistp l)
           (dlistp (conses k l))))

(local-defthmd car-member-conses
  (implies (member z (conses x l))
           (equal (car z) x)))

(defthm dlistp-cart-prod
  (implies (and (dlistp l) (dlistp r))
	   (dlistp (cart-prod l r)))
  :hints (("Subgoal *1/2" :in-theory (e/d (car-member-conses) (common-member-shared))
                          :use ((:instance dlistp-append (l (conses (car l) r)) (m (cart-prod (cdr l) r)))  
				(:instance common-member-shared (l (conses (car l) r)) (m (cart-prod (cdr l) r)))
				(:instance member-cart-prod (x (common-member (conses (car l) r) (cart-prod (cdr l) r)))
				                        (l (cdr l)))))))

;; Let m and n be positive relatively prime integers.  If a and b are divisors of
;; m and n, respectively, then a * b is a divisor of m * n.  In fact, this induces
;; a bijection from (cart-prod (divisors m) (divisors n)) to (divisors (* m n)):

(defun prod-divisors (x)
  (* (car x) (cdr x)))

;; Its inverse is the following function:

(defund factor-divisor (x m n)
  (cons (gcd x m) (gcd x n)))

;; We must show that each composition is the identity:

(local-defthmd gcd-ab-m-1
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (posp a) (posp b) (divides a m) (divides b n))
	   (divides a (gcd (* a b) m)))
  :hints (("Goal" :use ((:instance divides-gcd (d a) (x (* a b)) (y m))))))

(local-defthmd gcd-ab-m-2
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (posp a) (posp b) (divides a m) (divides b n))
	   (let ((g (gcd (* a b) m)))
	     (divides (gcd g b) n)))
  :hints (("Goal" :use ((:instance gcd-divides (x (gcd (* a b) m)) (y b))
                        (:instance gcd-pos (x (* a b)) (y m))
                        (:instance divides-transitive (x (gcd (gcd (* a b) m) b)) (y b) (z n))))))

(local-defthmd gcd-ab-m-3
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (posp a) (posp b) (divides a m) (divides b n))
	   (let ((g (gcd (* a b) m)))
	     (divides (gcd g b) m)))
  :hints (("Goal" :use ((:instance gcd-divides (x (gcd (* a b) m)) (y b))
                        (:instance gcd-divides (x (* a b)) (y m))
                        (:instance gcd-pos (x (* a b)) (y m))
                        (:instance divides-transitive (x (gcd (gcd (* a b) m) b)) (y (gcd (* a b) m)) (z m))))))

(local-defthmd gcd-ab-m-4
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (posp a) (posp b) (divides a m) (divides b n))
	   (let ((g (gcd (* a b) m)))
	     (equal (gcd g b) 1)))
  :hints (("Goal" :use (gcd-ab-m-2 gcd-ab-m-3
                        (:instance divides-gcd (d (gcd (gcd (* a b) m) b)) (x m) (y n))
                        (:instance gcd-pos (x (* a b)) (y m))
                        (:instance gcd-pos (x (gcd (* a b) m)) (y b))))))

(local-defthmd gcd-ab-m-5
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (posp a) (posp b) (divides a m) (divides b n))
	   (let ((g (gcd (* a b) m)))
	     (divides g a)))
  :hints (("Goal" :use (gcd-ab-m-4
                        (:instance gcd-divides (x (* a b)) (y m))
                        (:instance gcd-pos (x (* a b)) (y m))
                        (:instance divides-product-divides-factor (d (gcd (* a b) m)) (m b) (n a))))))

(local-defthm gcd-ab-m-6
  (implies (and (posp x) (integerp (/ x)))
           (equal x 1))
  :rule-classes ())

(defthmd gcd-ab-m
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (posp a) (posp b) (divides a m) (divides b n))
	   (equal (gcd (* a b) m) a))
  :hints (("Goal" :use (gcd-ab-m-1 gcd-ab-m-5
                        (:instance gcd-ab-m-6 (x (/ (gcd (* a b) m) a)))
                        (:instance gcd-pos (x (* a b)) (y m))))))

(defthmd factor-prod
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(member-equal x (cart-prod (divisors m) (divisors n))))
	   (and (member-equal (* (car x) (cdr x)) (divisors (* m n)))
		(equal (factor-divisor (prod-divisors x) m n)
		       x)))
  :hints (("Goal" :in-theory (enable factor-divisor prod-divisors)
                  :use ((:instance gcd-ab-m (a (car x)) (b (cdr x)))
		        (:instance gcd-ab-m (a (cdr x)) (b (car x)) (m n) (n m))
			(:instance gcd-commutative (x m) (y n))
			(:instance member-cart-prod (l (divisors m)) (r (divisors n)))
			(:instance member-divisors (k (car x)) (n m))
			(:instance member-divisors (k (cdr x)))
			(:instance member-divisors (k (* (car x) (cdr x))) (n (* m n)))))))

(defthmd prod-gcds-1
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (equal (gcd (/ x (gcd x m)) (/ m (gcd x m)))
	          1))
  :hints (("Goal" :use ((:instance gcd-divides (y m))
                        (:instance gcd-pos (y m))
			(:instance gcd-quotient-2 (d (gcd x m)) (y m))))))

(defthmd prod-gcds-2
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (divides (/ x (gcd x m)) n))
  :hints (("Goal" :use (prod-gcds-1
                        (:instance gcd-divides (y m))
                        (:instance gcd-pos (y m))
			(:instance divides-product-divides-factor (d (/ x (gcd x m))) (m (/ m (gcd x m))))))))

(defthmd prod-gcds-3
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (divides (/ x (gcd x m)) (gcd x n)))
  :hints (("Goal" :use (prod-gcds-2
                        (:instance gcd-divides (y m))
                        (:instance gcd-pos (y m))
			(:instance divides-gcd (d (/ x (gcd x m))) (y n))))))

(defthmd prod-gcds-4
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (divides x (* (gcd x m) (gcd x n))))
  :hints (("Goal" :use (prod-gcds-3))))

(defthmd prod-gcds-5
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (and (divides (gcd (gcd x m) (gcd x n)) m)
	        (divides (gcd (gcd x m) (gcd x n)) n)))
  :hints (("Goal" :use ((:instance gcd-pos (y m))
                        (:instance gcd-pos (y n))
			(:instance gcd-divides (x (gcd x m)) (y (gcd x n)))
			(:instance gcd-divides (y m))
			(:instance gcd-divides (y n))
			(:instance divides-transitive (x (gcd (gcd x m) (gcd x n))) (y (gcd x m)) (z m))
			(:instance divides-transitive (x (gcd (gcd x m) (gcd x n))) (y (gcd x n)) (z n))))))

(defthmd prod-gcds-6
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (equal (gcd (gcd x m) (gcd x n))
	          1))
  :hints (("Goal" :use (prod-gcds-5
                        (:instance gcd-pos (y m))
                        (:instance gcd-pos (y n))
			(:instance gcd-pos (x (gcd x m)) (y (gcd x n)))
			(:instance divides-gcd (d (gcd (gcd x m) (gcd x n))) (x m) (y n))))))

(defthmd prod-gcds-7
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (divides (* (gcd x m) (gcd x n))
	            x))
  :hints (("Goal" :use (prod-gcds-6
                        (:instance gcd-pos (y m))
                        (:instance gcd-pos (y n))
			(:instance gcd-divides (y m))
			(:instance gcd-divides (y n))
			(:instance product-rel-prime-divides (x (gcd x m)) (y (gcd x n)) (m x))))))

(defthmd prod-gcds
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(posp x) (divides x (* m n)))
	   (equal (* (gcd x m) (gcd x n)) x))
  :hints (("Goal" :use (prod-gcds-3 prod-gcds-7
                        (:instance gcd-pos (y m))
                        (:instance gcd-pos (y n))
			(:instance gcd-ab-m-6 (x (/ x (* (gcd x m) (gcd x n)))))))))

(defthmd prod-factor
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
		(member-equal x (divisors (* m n))))
	   (and (member-equal (factor-divisor x m n) (cart-prod (divisors m) (divisors n)))
		(equal (prod-divisors (factor-divisor x m n))
		       x)))
  :hints (("Goal" :in-theory (enable factor-divisor prod-divisors)
                  :use (prod-gcds
			(:instance member-cart-prod (x (cons (gcd x m) (gcd x n))) (l (divisors m)) (r (divisors n)))
			(:instance member-divisors (k (gcd x m)) (n m))
			(:instance member-divisors (k (gcd x n)))
			(:instance gcd-divides (y m))
			(:instance gcd-divides (y n))
			(:instance gcd-pos (y m))
			(:instance gcd-pos (y n))
			(:instance member-divisors (k x) (n (* m n)))))))

;; It follows by functional instantiation of len-1-1-equal that the lists have the
;; same length:

(defthmd len-divisors-multiplicative
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
	   (equal (len (divisors (* m n)))
		  (* (len (divisors m)) (len (divisors n)))))
  :hints (("Goal" :use ((:functional-instance len-1-1-equal
                         (x (lambda () (if (and (posp m) (posp n) (equal (gcd m n) 1)) (divisors (* m n)) (x))))
                         (y (lambda () (if (and (posp m) (posp n) (equal (gcd m n) 1)) (cart-prod (divisors m) (divisors n)) (y))))
		         (xy (lambda (x) (if (and (posp m) (posp n) (equal (gcd m n) 1)) (factor-divisor x m n) (xy x))))
		         (yx (lambda (y) (if (and (posp m) (posp n) (equal (gcd m n) 1)) (prod-divisors y) (yx y)))))))
	  ("Subgoal 2" :use ((:instance prod-factor (x a))
			     (:instance factor-prod (x a))))
	  ("Subgoal 1" :use ((:instance prod-factor (x a))
			     (:instance factor-prod (x a))))))

;; The list of products of a list of pairs:

(defun prods-divisors (l)
  (if (consp l)
      (cons (prod-divisors (car l))
            (prods-divisors (cdr l)))
    ()))

;; (prods-divisors (cart-prod (divisors m) (divisors n))) is a dlist and a sublist of 
;; (divisors (* m n)) of the same length.  It is therefore a permutation of
;; (divisors (* m n)):

(defthm prod-divisors-1-1
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (member-equal x (cart-prod (divisors m) (divisors n)))
		(member-equal y (cart-prod (divisors m) (divisors n)))
		(equal (prod-divisors x) (prod-divisors y)))
           (equal x y))
  :rule-classes ()
  :hints (("Goal" :use (factor-prod (:instance factor-prod (x y))))))

(defthm dlistp-prods-divisors-cart-prod-1
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (sublistp l (cart-prod (divisors m) (divisors n)))
                (member-equal x (cart-prod (divisors m) (divisors n)))
                (member-equal (prod-divisors x) (prods-divisors l)))
	   (member x l))
  :hints (("Subgoal *1/3" :use ((:instance prod-divisors-1-1 (y (car l)))))))

(defthm dlistp-prods-divisors-cart-prod-2
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (dlistp l)
                (sublistp l (cart-prod (divisors m) (divisors n))))
           (dlistp (prods-divisors l)))
  :hints (("Subgoal *1/2" :use ((:instance dlistp-prods-divisors-cart-prod-1 (x (car l)) (l (cdr l)))))))

(defthmd dlistp-prods-divisors-cart-prod
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
	   (dlistp (prods-divisors (cart-prod (divisors m) (divisors n)))))
  :hints (("Goal" :use ((:instance dlistp-prods-divisors-cart-prod-2 (l (cart-prod (divisors m) (divisors n))))))))

(defthmd sublistp-prods-divisors-1
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (sublistp l (cart-prod (divisors m) (divisors n))))
	   (sublistp (prods-divisors l) (divisors (* m n))))
  :hints (("Subgoal *1/2" :use ((:instance factor-prod (x (car l)))))))

(defthmd sublistp-prods-divisors
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
	   (sublistp (prods-divisors (cart-prod (divisors m) (divisors n)))
	             (divisors (* m n))))
  :hints (("Goal" :use ((:instance sublistp-prods-divisors-1 (l (cart-prod (divisors m) (divisors n))))))))

(defthm len-prods-divisors
  (equal (len (prods-divisors l)) (len l)))

(defthmd permp-divisors
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
           (permutationp (prods-divisors (cart-prod (divisors m) (divisors n)))
	                 (divisors (* m n))))
  :hints (("Goal" :use (sublistp-prods-divisors dlistp-prods-divisors-cart-prod len-divisors-multiplicative
                        (:instance permp-eq-len (l (prods-divisors (cart-prod (divisors m) (divisors n))))
                                                (m (divisors (* m n))))
			(:instance permp-permutationp (l (prods-divisors (cart-prod (divisors m) (divisors n))))
                                                      (m (divisors (* m n))))))))

;; We shall prove sum-divisors-multiplicative as a special case of a more general
;; theorem.  Let mf be an arbitrary multiplicative function:

(encapsulate (((mf *) => *))
  (local (defun mf (x) x))
  (defthm rationalp-mu
    (implies (posp n) (rationalp (mf n)))
    :rule-classes (:type-prescription :rewrite))
  (defthmd mu-mult
    (implies (and (posp m) (posp n) (equal (gcd m n) 1))
             (equal (mf (* m n)) (* (mf m) (mf n))))))

;; The following function applies mf to each member of a list and sums the values:

(defun sum-mf (l)
  (if (consp l)
      (+ (mf (car l)) (sum-mf (cdr l)))
    0))

(defun pos-listp (l)
  (if (consp l)
      (and (posp (car l))
           (pos-listp (cdr l)))
    (null l)))

(defthm pos-listp-divisors
  (implies (and (posp n) (true-listp l) (sublistp l (divisors n)))
           (pos-listp l))
  :hints (("Subgoal *1/4" :use ((:instance member-divisors (k (car l)))))))

(defthm true-listp-divisors
  (implies (posp n)
           (true-listp (divisors n))))

(defthm pos-listp-prods-divisors-conses
  (implies (and (posp x) (pos-listp l))
           (pos-listp (prods-divisors (conses x l)))))

(defthm pos-listp-prods-divisors-cart-prod
  (implies (and (pos-listp l) (pos-listp r))
           (pos-listp (prods-divisors (cart-prod l r)))))

(defthm rationalp-sum-mu
  (implies (pos-listp l)
           (rationalp (sum-mf l))))

;; Note that (sum-mf l) is invariant under permutation of l:

(defthm sum-mu-remove1
  (implies (and (pos-listp l) (member-equal x l))
           (and (pos-listp (remove1-equal x l))
	        (equal (sum-mf (remove1-equal x l))
	               (- (sum-mf l) (mf x))))))

(defthmd sum-mu-perm
  (implies (and (pos-listp l) (permutationp r l))
           (equal (sum-mf l) (sum-mf r))))

;; Our objective is to prove that

;;   (sum-mf (divisors (* m n)) = (sum-mf (divisors m)) * (sum-mf (divisors n)).

;; This requires 4 induction steps:

(defthm sum-mu-append
  (implies (and (pos-listp l) (pos-listp r))
           (equal (sum-mf (append l r))
                  (+ (sum-mf l) (sum-mf r)))))

(defthm prods-divisors-append
  (equal (prods-divisors (append l r))
         (append (prods-divisors l) (prods-divisors r))))

(defthmd sum-mu-prods-divisors-conses
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (member-equal d (divisors m))
		(sublistp l (divisors n)))
	   (equal (sum-mf (prods-divisors (conses d l)))
	          (* (mf d) (sum-mf l))))
  :hints (("Subgoal *1/1" :in-theory (enable mu-mult)
                          :use ((:instance member-divisors (k (car l)))
				(:instance member-divisors (k d) (n m))
				(:instance gcd-divisor-2 (x m) (y n) (c d) (d (car l)))
				(:instance gcd-commutative (x c) (y d))))))

(defthmd sum-mu-prods-divisors-cart-prod
  (implies (and (posp m) (posp n) (equal (gcd m n) 1)
                (true-listp l) (sublistp l (divisors m)))
	   (equal (sum-mf (prods-divisors (cart-prod l (divisors n)))) 
	          (* (sum-mf l) (sum-mf (divisors n)))))
  :hints (("Subgoal *1/3" :in-theory (enable sum-mu-prods-divisors-conses)
                          :use ((:instance member-divisors (k (car l)) (n m))))))

;; Now instantiate sum-mu-prods-divisors-cart-prod:

(defthmd sum-mu-prods-divisors-divisors
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
           (equal (sum-mf (prods-divisors (cart-prod (divisors m) (divisors n))))
	          (* (sum-mf (divisors m))
		     (sum-mf (divisors n)))))
  :hints (("Goal" :use ((:instance sum-mu-prods-divisors-cart-prod (l (divisors m)))))))

;; The desired result follows from permp-divisors and sum-mu-perm:

(defthmd sum-mu-divisors-multiplicative
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
           (equal (sum-mf (divisors (* m n)))
	          (* (sum-mf (divisors m))
		     (sum-mf (divisors n)))))
  :hints (("Goal" :use (sum-mu-prods-divisors-divisors permp-divisors
                        (:instance pos-listp-divisors (n (* m n)) (l (divisors (* m n))))
                        (:instance sum-mu-perm (l (divisors (* m n))) (r (prods-divisors (cart-prod (divisors m) (divisors n)))))))))

;; For any integer k, (expt x k) is a multiplicative function of x.  We functionally
;; instantiate the last result, substituting (lambda (x) (expt x k)) for mf and
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
		     (sum-powers (divisors n) k))))
  :hints (("Goal" :in-theory (enable mu-mult)
                  :use ((:functional-instance sum-mu-divisors-multiplicative
                          (mf (lambda (x) (if (and (posp m) (posp n) (equal (gcd m n) 1) (integerp k))
			                      (expt x k) (mf x))))
			  (sum-mf (lambda (l) (if (and (posp m) (posp n) (equal (gcd m n) 1) (integerp k))
			                          (sum-powers l k) (sum-mf l)))))))))

;; The case of interest is k = 1:

(defthm sum-list-1
  (implies (pos-listp l)
           (equal (sum-powers l 1)
	          (sum-list l))))

(defthmd sum-divisors-multiplicative
  (implies (and (posp m) (posp n) (equal (gcd m n) 1))
           (equal (sum-list (divisors (* m n)))
	          (* (sum-list (divisors m))
		     (sum-list (divisors n)))))
  :hints (("Goal" :use ((:instance sum-powers-divisors-multiplicative (k 1))
                        (:instance pos-listp-divisors (n (* m n)) (l (divisors (* m n))))))))

;; The divisors of a prime power:

(defun prime-powers (p k)
  (if (posp k)
      (cons (expt p k) (prime-powers p (1- k)))
    (list 1)))

(defthmd ppda-1
  (implies (and (primep p) (natp k) (natp j) (<= j k) (natp n) (>= n (expt p j)) (< n (expt p (1+ j))))
           (iff (divides n (expt p k))
	        (equal n (expt p j))))
  :hints (("Goal" :use (powerp-log (:instance divides-power (m n))))))

(defthmd ppda-2
  (implies (and (primep p) (posp j))
           (>= (expt p j) (1+ (expt p (1- j)))))
  :hints (("Goal" :nonlinearp t)))

(defun ppda-induct (n j)
  (declare (irrelevant j))
  (if (posp n)
      (list (ppda-induct (1- n) j)
            (ppda-induct (1- n) (1- j)))
    ()))

(defthmd prime-power-divisors-aux
  (implies (and (primep p) (natp k) (natp j) (<= j k) (natp n) (>= n (expt p j)) (< n (expt p (1+ j))))
           (equal (divisors-aux n (expt p k))
	          (prime-powers p j)))
  :hints (("Goal" :induct (ppda-induct n j))
          ("Subgoal *1/1" :cases ((= n (expt p j))) :nonlinearp t
	                  :use (ppda-1 ppda-2))))

(defthmd prime-power-divisors
  (implies (and (primep p) (natp k))
           (equal (divisors (expt p k))
	          (prime-powers p k)))
  :hints (("Goal" :use ((:instance prime-power-divisors-aux (n (expt p k)) (j k)))
                  :in-theory (enable divisors))))

;; len-divisors-multiplicative and prime-fact-existence yield a formula for the
;; number of divisors of n:

(defthmd len-prime-powers
  (implies (and (primep p) (natp k))
           (equal (len (prime-powers p k))
	          (1+ k))))

(defthmd len-prime-power-divisors
  (implies (and (primep p) (natp k))
           (equal (len (divisors (expt p k)))
	          (1+ k)))
  :hints (("Goal" :use (len-prime-powers prime-power-divisors))))

(defun len-divisors-aux (l)
  (if (consp l)
      (* (1+ (cdar l))
	 (len-divisors-aux (cdr l)))
    1))

(defthm len-divisors-aux-pow-prod
  (implies (prime-pow-list-p l)
           (equal (len-divisors-aux l)
	          (len (divisors (pow-prod l)))))		  
  :hints (("Subgoal *1/2" :use (rel-prime-pow-list
                                (:instance len-prime-power-divisors (p (caar l)) (k (cdar l)))
                                (:instance len-divisors-multiplicative (m (expt (caar l) (cdar l)))
				                                       (n (pow-prod (cdr l))))))))

(defund len-divisors (n)
  (len-divisors-aux (prime-fact n)))

(defthmd correctness-of-len-divisors
  (implies (posp n)
           (equal (len (divisors n))
	          (len-divisors n)))
  :hints (("Goal" :in-theory (enable len-divisors)
                  :use (prime-fact-existence
		        (:instance len-divisors-aux-pow-prod (l (prime-fact n)))))))

;; sum-divisors-multiplicative and prime-fact-existence yield a formula for the
;; sum of the divisors of n:

(defthmd slpl-1
  (implies (and (primep p) (natp k))
           (equal (* (1- p) (sum-list (prime-powers p k)))
	          (1- (expt p (1+ k)))))
  :hints (("Goal" :induct (fact k))))

(defthmd slpl-2
  (implies (and (posp n) (rationalp a) (rationalp b) (= (* n a) b))
           (equal (/ b n) a)))

(defthmd slpl-3
  (implies (and (primep p) (natp k))
           (posp (sum-list (prime-powers p k)))))

(defthmd sum-list-prime-powers
  (implies (and (primep p) (natp k))
           (equal (sum-list (prime-powers p k))
	          (/ (1- (expt p (1+ k)))
		     (1- p))))
  :hints (("Goal" :in-theory (disable prime-powers)
                  :use (slpl-1 slpl-3
		        (:instance slpl-2 (n (1- p)) (a (sum-list (prime-powers p k))) (b (1- (expt p (1+ k)))))))))

(defthmd sum-prime-power-divisors
  (implies (and (primep p) (natp k))
           (equal (sum-list (divisors (expt p k)))
	          (/ (1- (expt p (1+ k)))
		     (1- p))))
  :hints (("Goal" :use (prime-power-divisors sum-list-prime-powers))))

(defun sum-divisors-aux (l)
  (if (consp l)
      (* (/ (1- (expt (caar l) (1+ (cdar l))))
            (1- (caar l)))
	 (sum-divisors-aux (cdr l)))
    1))

(defthm sum-divisors-aux-pow-prod
  (implies (prime-pow-list-p l)
           (equal (sum-divisors-aux l)
	          (sum-list (divisors (pow-prod l)))))		  
  :hints (("Subgoal *1/2" :use (rel-prime-pow-list
                                (:instance sum-prime-power-divisors (p (caar l)) (k (cdar l)))
                                (:instance sum-divisors-multiplicative (m (expt (caar l) (cdar l)))
				                                       (n (pow-prod (cdr l))))))))

(defund sum-divisors (n)
  (sum-divisors-aux (prime-fact n)))

(defthmd correctness-of-sum-divisors
  (implies (posp n)
           (equal (sum-list (divisors n))
	          (sum-divisors n)))
  :hints (("Goal" :in-theory (enable sum-divisors)
                  :use (prime-fact-existence
		        (:instance sum-divisors-aux-pow-prod (l (prime-fact n)))))))


;; A positive integer n is perfect if n is the sum of its proper divisors, i.e.,
;; (sum-list (divisors n)) = 2 * n:

(defund perfectp (n)
  (and (posp n)
       (equal (sum-list (divisors n))
              (* 2 n))))

;; Let n = (expt 2 k) * p, where p = (expt 2 (1+ k)) - 1 is prime.  Then

;;   (sum-list (divisors n)) = (sum-list (divisors (expt 2 k))) * (sum-list (divisors p))
;;                           = ((expt 2 (1+ k)) - 1) * (p + 1)
;;                           = ((expt 2 (1+ k)) - 1) * (expt 2 (1+ k))
;;                           = 2 * n,

;; i.e., n is perfect:

(local-defthmd pow2-odd-rel-prime
  (implies (and (natp k) (posp x) (oddp x))
	   (equal (gcd (expt 2 k) x) 1))
  :hints (("Goal" :use ((:instance cpd-divides (x (expt 2 k)) (y x))
                        (:instance powerp-prime-divisor (p 2) (n (expt 2 k)) (q (cpd (expt 2 k) x)))))))

(local-defthm sum-list-divisors-2**k
  (implies (posp k)
           (equal (sum-list (divisors (expt 2 k)))
	          (1- (expt 2 (1+ k)))))
  :hints (("Goal" :use ((:instance sum-prime-power-divisors (p 2))))))

(local-defthmd sum-list-divisors-p-1
  (implies (primep p)
           (equal (sum-list (divisors p))
	          (/ (1- (* p p)) (1- p))))
  :hints (("Goal" :use ((:instance sum-prime-power-divisors (k 1))))))

(local-defthmd sum-list-divisors-p-2
  (implies (primep p)
           (equal (1- (* p p)) (* (1- p) (1+ p)))))

(local-defthmd sum-list-divisors-p-3
  (implies (primep p)
           (equal (/ (* (1- p) (1+ p)) (1- p)) (1+ p))))

(local-defthm sum-list-divisors-p
  (implies (primep p)
           (equal (sum-list (divisors p))
	          (1+ p)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (sum-list-divisors-p-1 sum-list-divisors-p-2 sum-list-divisors-p-3))))

(defthmd perfectp-sufficiency
  (implies (and (posp k) (primep (1- (expt 2 (1+ k)))))
	   (perfectp (* (expt 2 k) (1- (expt 2 (1+ k))))))
  :hints (("Goal" :in-theory (enable perfectp)
                  :use ((:instance pow2-odd-rel-prime (x (1- (expt 2 (1+ k)))))
                        (:instance sum-divisors-multiplicative (m (expt 2 k)) (n (1- (expt 2 (1+ k)))))))))

;; Conversely, assume that n is even and perfect and let k = (log n 2).  Then
;; n = (expt 2 k) * x, where x is odd, and

;;  (sum-list (divisors n)) = (1- (expt 2 (1+ k))) * (sum-list (divisors x))
;;                          = 2 * n
;;                          = (expt 2 (1+ k)) * x.

(local-defthmd sum-list-divisors-perfect-1
  (implies (and (posp n) (evenp n) (perfectp n))
           (let* ((k (log n 2)) (x (/ n (expt 2 k))))
	     (and (posp x) (oddp x))))
  :hints (("Goal" :use ((:instance max-power-p-dividing (p 2) (k (log n 2)))
                        (:instance max-power-p-dividing (p 2) (k (1+ (log n 2))))))))

(local-defthmd sum-list-divisors-perfect-2
  (implies (and (posp n) (evenp n) (perfectp n))
           (let* ((k (log n 2)) (x (/ n (expt 2 k))))
	     (equal (gcd (expt 2 k) x)
	            1)))
  :hints (("Goal" :use (sum-list-divisors-perfect-1
                        (:instance cpd-divides (x (expt 2 (log n 2))) (y (/ n (expt 2 (log n 2)))))
                        (:instance powerp-prime-divisor (p 2) (n (expt 2 (log n 2)))
			                                (q (cpd (expt 2 (log n 2)) (/ n (expt 2 (log n 2))))))))))

(defthmd sum-list-divisors-perfect
  (implies (and (posp n) (evenp n) (perfectp n))
           (let* ((k (log n 2)) (x (/ n (expt 2 k))))
	     (and (posp x)
	          (oddp x)
	          (equal (* (1- (expt 2 (1+ k))) (sum-list (divisors x)))
	                 (* (expt 2 (1+ k)) x)))))
  :hints (("Goal" :in-theory (enable perfectp)
                  :use (sum-list-divisors-perfect-1 sum-list-divisors-perfect-2
                        (:instance sum-divisors-multiplicative (m (expt 2 (log n 2))) (n (/ n (expt 2 (log n 2)))))))))

;; We shall show that x = (expt 2 (1+ k)) - 1 and x is prime.  Since
;; (1- (expt 2 (1+ k))) is odd and divides (expt 2 (1+ k)) * x,
;; (1- (expt 2 (1+ k))) divides x.  Let y = x/(1- (expt 2 (1+ k))).  Suppose y is
;; not 1.  Then x, y, and 1 are distinct divisors of x.  On the other hand, if
;; y = 1 and x is not prime, then x, y, and the least prime divisor of x are
;; distinct divisors of x.  In either case, (sum-divisors x) > x + y and

;;    (expt 2 (1+ k)) * x =  2 * n
;;                        =  (sum-list (divisors n))
;;                        =  (1- (expt 2 (1+ k))) * (sum-list (divisors x))
;;                        >  (1- (expt 2 (1+ k))) * (y + x)
;;                        =  x + (1- (expt 2 (1+ k))) * x
;;                        =  (expt 2 (1+ k)) * x,

;; a contradiction.  Thus, y = 1 and x = (1- (expt 2 (1+ k))) is prime.

(local-defthmd posp-pos-list
  (implies (and (pos-listp l) (consp l))
            (posp (sum-list l))))

(local-defthmd posp-sum-list-divisors
  (implies (posp n)
           (posp (sum-list (divisors n))))
  :hints (("Goal" :use ((:instance member-divisors (k 1))
                        (:instance posp-pos-list (l (divisors n)))))))
                        
(local-defthmd perfectp-necessity-1
  (implies (and (posp n) (evenp n) (perfectp n))
           (let* ((k (log n 2)) (x (/ n (expt 2 k))))
	     (and (posp x)
	          (oddp x)
	          (posp (1- (expt 2 (1+ k))))
	          (> (1- (expt 2 (1+ k))) 1)
	          (oddp (1- (expt 2 (1+ k))))
		  (posp (sum-list (divisors x))))))
  :hints (("Goal" :use (sum-list-divisors-perfect
                        (:instance posp-sum-list-divisors (n (/ n (expt 2 (log n 2)))))))))

(local-defthmd perfectp-necessity-2
  (implies (and (posp a) (posp b))
           (divides a (* a b))))

(local-defund x$ (n)
  (/ n (expt 2 (log n 2))))

(local-defund o$ (n)
  (1- (expt 2 (1+ (log n 2)))))

(local-defund y$ (n)
  (/ (x$ n) (o$ n)))

(local-defthmd perfectp-necessity-3
  (implies (and (posp n) (evenp n) (perfectp n))
           (and (posp (x$ n))
	        (oddp (x$ n))
		(posp (o$ n))
		(oddp (o$ n))
		(> (o$ n) 1)
		(divides (o$ n) (* (expt 2 (1+ (log n 2))) (x$ n)))))
  :hints (("Goal" :in-theory '(x$ o$)
                  :use (sum-list-divisors-perfect perfectp-necessity-1
                        (:instance perfectp-necessity-2 (a (1- (expt 2 (1+ (log n 2)))))
			                                (b (sum-list (divisors (/ n (expt 2 (log n 2)))))))))))

(local-defthmd perfectp-necessity-4
  (implies (and (posp n) (evenp n) (perfectp n))
           (and (posp (x$ n))
	        (oddp (x$ n))
		(posp (o$ n))
		(oddp (o$ n))
		(> (o$ n) 1)
		(posp (y$ n))
		(divides (y$ n) (x$ n))
		(divides (o$ n) (x$ n))
		(= (x$ n) (* (y$ n) (o$ n)))
		(not (= (x$ n) (y$ n)))
		(not (= (x$ n) 1))))
  :hints (("Goal" :in-theory (enable y$)
                  :use (perfectp-necessity-3
		        (:instance cpd-divides (x (expt 2 (1+ (log n 2)))) (y (o$ n)))
                        (:instance powerp-prime-divisor (p 2) (n (expt 2 (1+ (log n 2)))) (q (cpd (expt 2 (1+ (log n 2))) (o$ n))))
			(:instance divides-product-divides-factor (d (o$ n)) (m (expt 2 (1+ (log n 2)))) (n (x$ n)))
			(:instance gcd-commutative (x (expt 2 (1+ (log n 2)))) (y (o$ n)))))))

(local-defun cdr-cdr-induct (l m)
  (if (consp l)
      (list (cdr-cdr-induct (cdr l) (remove1-equal (car l) m)))
    (list l m)))

(local-defthm sum-list-remove1
  (implies (and (pos-listp l) (member-equal x l))
           (equal (sum-list (remove1-equal x l))
	          (- (sum-list l) x))))

(local-defthmd perfectp-necessity-5
  (implies (and (pos-listp l) (pos-listp m) (dlistp l) (sublistp l m))
           (<= (sum-list l) (sum-list m)))
  :hints (("Goal" :induct (cdr-cdr-induct l m))))

(local-defthmd perfectp-necessity-6
  (implies (and (posp n) (evenp n) (perfectp n) (not (= (y$ n) 1)))
           (and (dlistp (list 1 (y$ n) (x$ n)))
	        (sublistp (list 1 (y$ n) (x$ n)) (divisors (x$ n)))
		(> (sum-list (list 1 (y$ n) (x$ n))) (+ (x$ n) (y$ n)))))
  :hints (("Goal" :use (perfectp-necessity-4
                        (:instance member-divisors (k 1) (n (x$ n)))
                        (:instance member-divisors (k (y$ n)) (n (x$ n)))
                        (:instance member-divisors (k (x$ n)) (n (x$ n)))))))

(local-defthmd perfectp-necessity-7
  (implies (and (posp n) (evenp n) (perfectp n) (not (= (y$ n) 1)))
           (> (sum-list (divisors (x$ n)))
	      (+ (x$ n) (y$ n))))
  :hints (("Goal" :use (perfectp-necessity-4 perfectp-necessity-6
                        (:instance perfectp-necessity-5 (l (list 1 (y$ n) (x$ n))) (m (divisors (x$ n))))))))

(local-defthmd perfectp-necessity-8
  (implies (and (posp n) (evenp n) (perfectp n) (= (y$ n) 1) (not (primep (x$ n))))
           (and (dlistp (list 1 (least-prime-divisor (x$ n)) (x$ n)))
	        (sublistp (list 1 (least-prime-divisor (x$ n)) (x$ n)) (divisors (x$ n)))
		(> (sum-list (list 1 (least-prime-divisor (x$ n)) (x$ n))) (+ (x$ n) (y$ n)))))
  :hints (("Goal" :use (perfectp-necessity-4
                        (:instance least-divisor-divides (k 2) (n (x$ n)))
                        (:instance primep-least-divisor (n (x$ n)))
                        (:instance member-divisors (k 1) (n (x$ n)))
                        (:instance member-divisors (k (least-prime-divisor (x$ n))) (n (x$ n)))
                        (:instance member-divisors (k (x$ n)) (n (x$ n)))))))

(local-defthmd perfectp-necessity-9
  (implies (and (posp n) (evenp n) (perfectp n) (= (y$ n) 1) (not (primep (x$ n))))
           (> (sum-list (divisors (x$ n)))
	      (+ (x$ n) (y$ n))))
  :hints (("Goal" :use (perfectp-necessity-4 perfectp-necessity-8
                        (:instance perfectp-necessity-5 (l (list 1 (least-prime-divisor (x$ n)) (x$ n))) (m (divisors (x$ n))))))))

(local-defthmd perfectp-necessity-10
  (implies (and (posp n) (evenp n) (perfectp n))
           (equal (* (o$ n) (sum-list (divisors (x$ n))))
	          (* (1+ (o$ n)) (x$ n))))
  :hints (("Goal" :in-theory (enable o$ x$)
                  :use (sum-list-divisors-perfect))))

(local-defthmd perfectp-necessity-11
  (implies (and (posp n) (evenp n) (perfectp n))
           (and (= (y$ n) 1) (primep (x$ n))))
  :hints (("Goal" :use (perfectp-necessity-4 perfectp-necessity-7 perfectp-necessity-9  perfectp-necessity-10)
                  :in-theory (enable y$)
                  :nonlinearp t)))

(local-defthmd perfectp-necessity-11
  (implies (and (posp n) (evenp n) (perfectp n))
           (and (= (y$ n) 1) (primep (x$ n))))
  :hints (("Goal" :use (perfectp-necessity-4 perfectp-necessity-7 perfectp-necessity-9  perfectp-necessity-10)
                  :in-theory (enable y$)
                  :nonlinearp t)))

(local-defthmd perfectp-necessity-12
  (implies (and (posp n) (evenp n) (perfectp n))
           (= (x$ n) (o$ n)))
  :hints (("Goal" :use (perfectp-necessity-4 perfectp-necessity-11)
                  :in-theory (enable y$)
                  :nonlinearp t)))

(local-defthmd perfectp-necessity-13
  (implies (and (posp n) (evenp n) (perfectp n))
           (equal (* (expt 2 (log n 2)) (x$ n))
		  n))
  :hints (("Goal" :in-theory (enable x$)
                  :nonlinearp t)))

(defthmd perfectp-necessity
  (implies (and (posp n) (evenp n) (perfectp n))
           (let ((k (log n 2)))
	     (and (primep (1- (expt 2 (1+ k))))
	          (equal (* (expt 2 k) (1- (expt 2 (1+ k))))
	                 n))))
  :hints (("Goal" :in-theory '(x$ o$)
                  :use (perfectp-necessity-12 perfectp-necessity-13 perfectp-necessity-11))))
