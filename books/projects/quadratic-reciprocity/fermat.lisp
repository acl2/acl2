;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "RTL")

(local (include-book "support/fermat"))

(set-enforce-redundancy t)
(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; The proof depends on Euclid's Theorem:

(include-book "euclid")

(defsection fermat
  :parents (number-theory)
  :short "This book contains a proof of Fermat's Theorem: if @('p') is a prime and @('m')
 is not divisible by @('p'), then @('mod(m^(p-1),p) = 1')."
  :long "The proof depends on Euclid's Theorem:"

"We shall construct two lists of integers, each of which is a permutation of the other.
 @(def perm)"

(defun perm (a b)
  (if (consp a)
      (if (member (car a) b)
          (perm (cdr a) (remove1 (car a) b))
	())
    (not (consp b))))

"The first list is @({positives(p-1) = (1, 2, ..., p-1)})
 @(def positives)"

(defun positives (n)
  (if (zp n)
      ()
    (cons n (positives (1- n)))))

"The second list is @({mod-prods(p-1,a,p) = (mod(a,p), mod(2*a,p), ..., mod((p-1)*a,p))})
 @(def mod-prods)"

(defun mod-prods (n m p)
  (if (zp n)
      ()
    (cons (mod (* m n) p)
	  (mod-prods (1- n) m p))))

"The proof is based on the pigeonhole principle, as stated below.
 @(thm not-member-remove1)
 @(thm perm-member)
 @(def distinct-positives)
 @(thm member-positives)
 @(thm pigeonhole-principle)"

(defthm not-member-remove1
    (implies (not (member x l))
	     (not (member x (remove1 y l)))))

(defthm perm-member
  (implies (and (perm a b)
		(member x a))
	   (member x b)))

(defun distinct-positives (l n)
  (if (consp l)
      (and (not (zp n))
	   (not (zp (car l)))
	   (<= (car l) n)
	   (not (member (car l) (cdr l)))
           (distinct-positives (cdr l) n))
    t))

(defthm member-positives
    (iff (member x (positives n))
	 (and (not (zp n))
	      (not (zp x))
	      (<= x n))))

(defthm pigeonhole-principle
    (implies (distinct-positives l (len l))
	     (perm (positives (len l)) l))
  :rule-classes ())

"We must show that @('mod-prods(p-1,m,p)') is a list of length @('p-1') of distinct
 integers between @('1') and @('p-1').
 @(thm len-mod-prods)
 @(thm mod-distinct)
 @(thm mod-p-bnds)
 @(thm mod-prods-distinct-positives)
 @(thm perm-mod-prods)"

(defthm len-mod-prods
    (implies (natp n)
	     (equal (len (mod-prods n m p)) n)))

(defthm mod-distinct
    (implies (and (primep p)
		  (not (zp i))
		  (< i p)
		  (not (zp j))
		  (< j p)
		  (not (= j i))
		  (integerp m)
		  (not (divides p m)))
	     (not (equal (mod (* m i) p) (mod (* m j) p)))))

(defthm mod-p-bnds
    (implies (and (primep p)
		  (not (zp i))
		  (< i p)
		  (integerp m)
		  (not (divides p m)))
	     (and (< 0 (mod (* m i) p))
		  (> p (mod (* m i) p))))
  :rule-classes ())

(defthm mod-prods-distinct-positives
    (implies (and (primep p)
		  (natp n)
		  (< n p)
		  (integerp m)
		  (not (divides p m)))
	     (distinct-positives (mod-prods n m p) (1- p)))
  :rule-classes ())

(defthm perm-mod-prods
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m)))
	     (perm (positives (1- p))
		   (mod-prods (1- p) m p)))
  :rule-classes ())

"The product of the members of a list is invariant under permutation:
 @(def times-list)
 @(thm perm-times-list)"

(defun times-list (l)
  (if (consp l)
      (* (ifix (car l))
	 (times-list (cdr l)))
    1))

(defthm perm-times-list
    (implies (perm l1 l2)
	     (equal (times-list l1)
		    (times-list l2)))
  :rule-classes ())

"It follows that the product of the members of @('mod-prods(p-1,m,p)') is @('(p-1)!').
 @(thm times-list-positives)
 @(thm times-list-equal-fact)
 @(thm times-list-mod-prods)"

(defthm times-list-positives
  (equal (times-list (positives n))
	 (fact n)))

(defthm times-list-equal-fact
    (implies (perm (positives n) l)
	     (equal (times-list l) (fact n))))

(defthm times-list-mod-prods
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m)))
	     (equal (times-list (mod-prods (1- p) m p))
		    (fact (1- p)))))

"On the other hand, the product modulo @('p') may be computed as follows.
 @(thm mod-mod-prods)"

(defthm mod-mod-prods
    (implies (and (not (zp p))
		  (integerp m)
		  (natp n))
	     (equal (mod (times-list (mod-prods n m p)) p)
		    (mod (* (fact n) (expt m n)) p)))
  :rule-classes ())

"Fermat's theorem now follows easily.
 @(thm not-divides-p-fact)
 @(thm mod-times-prime)
 @(thm fermat)"

(defthm not-divides-p-fact
    (implies (and (primep p)
		  (natp n)
		  (< n p))
	     (not (divides p (fact n))))
  :rule-classes ())

(defthm mod-times-prime
    (implies (and (primep p)
		  (integerp a)
		  (integerp b)
		  (integerp c)
		  (not (divides p a))
		  (= (mod (* a b) p) (mod (* a c) p)))
	     (= (mod b p) (mod c p)))
  :rule-classes ())

(defthm fermat
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m)))
	     (equal (mod (expt m (1- p)) p)
		    1))
  :rule-classes ())

)
