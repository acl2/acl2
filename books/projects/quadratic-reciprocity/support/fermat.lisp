(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system)) ;; It's hard to do any arithmetic without something like this

;; This book contains a proof of Fermat's Theorem: if p is a prime and m
;; is not divisible by p, then mod(m^(p-1),p) = 1.

;; The proof depends on Euclid's Theorem:

(include-book "euclid")

;; We shall construct two lists of integers, each of which is a permutation of the other.

(defun perm (a b)
  (if (consp a)
      (if (member (car a) b)
          (perm (cdr a) (remove1 (car a) b))
	())
    (not (consp b))))

;; The first list is positives(p-1) = (1, 2, ..., p-1):

(defun positives (n)
  (if (zp n)
      ()
    (cons n (positives (1- n)))))

;;The second list is mod-prods(p-1,a,p) = (mod(a,p), mod(2*a,p), ..., mod((p-1)*a,p)):

(defun mod-prods (n m p)
  (if (zp n)
      ()
    (cons (mod (* m n) p)
	  (mod-prods (1- n) m p))))

;; The proof is based on the pigeonhole principle, as stated below.

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

(defthm pigeonhole-principle-lemma-1
    (implies (and (natp n)
		  (distinct-positives l (1+ n))
		  (not (member (1+ n) l)))
	     (distinct-positives l n)))

(defthm pigeonhole-principle-lemma-2
    (implies (and (not (zp n))
		  (distinct-positives l n)
		  (member n l))
	     (distinct-positives (remove1 n l) (+ -1 n))))

(defthm len-remove1
    (implies (member x l)
	     (equal (len (remove1 x l))
		    (1- (len l)))))

(defun pigeonhole-induction (l)
  (declare (xargs :measure (len l)))
  (if (consp l)
      (if (member (len l) l)
	  (pigeonhole-induction (remove1 (len l) l))
	(pigeonhole-induction (cdr l)))
    t))

(defthm pigeonhole-principle
    (implies (distinct-positives l (len l))
	     (perm (positives (len l)) l))
  :rule-classes ()
  :hints (("Goal" :induct (pigeonhole-induction l))))

;; We must show that mod-prods(p-1,m,p) is a list of length p-1 of distinct
;; integers between 1 and p-1.

(defthm len-mod-prods
    (implies (natp n)
	     (equal (len (mod-prods n m p)) n)))

(defthm mod-distinct-lemma
    (implies (and (integerp p)
		  (not (zp i))
		  (< i p)
		  (not (zp j))
		  (< j p))
	     (< (abs (- i j)) p))
  :rule-classes ())

(defthm mod-distinct
    (implies (and (primep p)
		  (not (zp i))
		  (< i p)
		  (not (zp j))
		  (< j p)
		  (not (= j i))
		  (integerp m)
		  (not (divides p m)))
	     (not (equal (mod (* m i) p) (mod (* m j) p))))
  :hints (("Goal" :in-theory (enable divides)
		  :use (mod-distinct-lemma
			(:instance divides-leq (x p) (y (abs (- i j))))
			(:instance mod-equal-int (a (* m i)) (b (* m j)) (n p))
			(:instance mod-equal-int (a (* m j)) (b (* m i)) (n p))
			(:instance euclid (a (abs (- i j))) (b m))))))

(defthm mod-p-bnds
    (implies (and (primep p)
		  (not (zp i))
		  (< i p)
		  (integerp m)
		  (not (divides p m)))
	     (and (< 0 (mod (* m i) p))
		  (> p (mod (* m i) p))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
		  :use ((:instance mod-bnd-1 (m (* m i)) (n p))
			(:instance mod-0-int (m (* m i)) (n p))
			(:instance natp-mod-2 (m (* m i)) (n p))
			(:instance euclid (a i) (b m))))))

(defthm mod-prods-distinct-positives-lemma
    (implies (and (primep p)
		  (integerp p)
		  (>= p 2)
		  (natp n)
		  (< n p)
		  (integerp r)
		  (< r n)
		  (integerp m)
		  (not (divides p m)))
	     (not (member (mod (* m n) p) (mod-prods r m p)))))

(defthm mod-prods-distinct-positives
    (implies (and (primep p)
		  (natp n)
		  (< n p)
		  (integerp m)
		  (not (divides p m)))
	     (distinct-positives (mod-prods n m p) (1- p)))
  :rule-classes ()
  :hints (("Subgoal *1/5.1" :use ((:instance mod-p-bnds (i n))))))

(defthm perm-mod-prods
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m)))
	     (perm (positives (1- p))
		   (mod-prods (1- p) m p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-prods-distinct-positives (n (1- p)))
			(:instance pigeonhole-principle (l (mod-prods (1- p) m p)))))))

;; The product of the members of a list is invariant under permutation:

(defun times-list (l)
  (if (consp l)
      (* (ifix (car l))
	 (times-list (cdr l)))
    1))

(defthm times-list-remove1
    (implies (and (consp l)
		  (member x l))
	     (equal (times-list l)
		    (* (ifix x) (times-list (remove1 x l)))))
  :rule-classes ())

(defthm perm-times-list
    (implies (perm l1 l2)
	     (equal (times-list l1)
		    (times-list l2)))
  :rule-classes ()
  :hints (("Subgoal *1/2" :use (:instance times-list-remove1 (x (car l1)) (l l2)))))

;; It follows that the product of the members of mod-prods(p-1,m,p) is (p-1)!.

(defthm times-list-positives
  (equal (times-list (positives n))
	 (fact n)))

(defthm times-list-equal-fact
    (implies (perm (positives n) l)
	     (equal (times-list l) (fact n)))
  :hints (("Goal" :use ((:instance perm-times-list (l1 (positives n)) (l2 l))))))

(defthm times-list-mod-prods
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m)))
	     (equal (times-list (mod-prods (1- p) m p))
		    (fact (1- p))))
  :hints (("Goal" :use (perm-mod-prods))))

;; On the other hand, the product modulo p may be computed as follows.

(defthm mod-mod-prods-lemma-1
    (implies (and (integerp x)
		  (integerp y)
		  (integerp z)
		  (not (zp n))
		  (= (mod x n) (mod y n)))
	     (= (mod (* x (mod z n)) n)
		(mod (* y z) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-mod-times (a z) (b x))
			(:instance mod-mod-times (a x) (b z))
			(:instance mod-mod-times (a y) (b z))))))

(defthm mod-mod-prods-lemma-2
    (implies (and (not (zp p))
		  (integerp m)
		  (not (zp n))
		  (equal (mod (times-list (mod-prods (+ -1 n) m p)) p)
			 (mod (* (fact (+ -1 n)) (expt m (+ -1 n))) p)))
	     (equal (mod (times-list (mod-prods n m p)) p)
		    (mod (* (fact n) (expt m n)) p)))
  :hints (("Goal" :use ((:instance mod-mod-prods-lemma-1
				   (n p)
				   (x (times-list (mod-prods (1- n) m p)))
				   (y (* (fact (1- n)) (expt m (1- n))))
				   (z (* m n)))))))

(defthm mod-mod-prods
    (implies (and (not (zp p))
		  (integerp m)
		  (natp n))
	     (equal (mod (times-list (mod-prods n m p)) p)
		    (mod (* (fact n) (expt m n)) p)))
  :hints (("Subgoal *1/4" :use mod-mod-prods-lemma-2))
  :rule-classes ())

;; Fermat's theorem now follows easily.

(defthm not-divides-p-fact
    (implies (and (primep p)
		  (natp n)
		  (< n p))
	     (not (divides p (fact n))))
  :rule-classes ()
  :hints (("Subgoal *1/5" :use ((:instance euclid (a (fact (1- n))) (b n))
				(:instance divides-leq (x p) (y n))))
	  ("Subgoal *1/1" :use ((:instance divides-leq (x p) (y 1))))))

(defthm mod-times-prime
    (implies (and (primep p)
		  (integerp a)
		  (integerp b)
		  (integerp c)
		  (not (divides p a))
		  (= (mod (* a b) p) (mod (* a c) p)))
	     (= (mod b p) (mod c p)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
		  :use ((:instance euclid (b (- b c)))
			(:instance mod-equal-int (n p) (a (* a b)) (b (* a c)))
			(:instance mod-equal-int-reverse (n p) (a b) (b c))))))

(defthm fermat
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m)))
	     (equal (mod (expt m (1- p)) p)
		    1))
  :rule-classes ()
  :hints (("Goal" :use (times-list-mod-prods
			(:instance not-divides-p-fact (n (1- p)))
			(:instance mod-mod-prods (n (1- p)))
			(:instance mod-times-prime (a (fact (1- p))) (b 1) (c (expt m (1- p))))
			(:instance mod-does-nothing (m 1) (n p))))))


