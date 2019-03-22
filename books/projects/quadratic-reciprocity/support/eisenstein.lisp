(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system)) ;; It's hard to do any arithmetic without something like this

;; This book contains a formalization of Eisenstein's proof of Gauss's
;; Law of Quadratic Reciprocity: If p and q are distinct odd primes,
;; then
;;  (residue(p,q) <=> residue(q,p)) <=> ((p-1)/2)*((q-1)/2) is even.

;; The proof is based on Gauss's Lemma:

(include-book "gauss")

;; We shall need the following facts pertaining to divisibility by 2.

(defthm evenp-mod
    (implies (integerp x)
	     (= (mod x 2)
		(if (evenp x)
		    0
		  1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
		  :use ((:instance mod012 (m x))
			(:instance divides-mod-0 (a x) (n 2))))))

(defthm evenp-iff-evenp-plus
    (implies (and (integerp x)
		  (integerp y))
	     (equal (equal (evenp x) (evenp y))
		    (evenp (+ x y))))
  :rule-classes ()
  :hints (("Goal" :use (evenp-mod
			(:instance evenp-mod (x y))
			(:instance evenp-mod (x (+ x y)))
			(:instance mod-sum (a x) (b y) (n 2))))))

(defthm evenp-minus
    (implies (integerp x)
	     (equal (evenp (- x)) (evenp x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
		  :use ((:instance divides-product (x 2) (y (- x)) (z -1))
			(:instance divides-product (x 2) (y x) (z -1))))))

(defthm evenp-iff-evenp-minus
    (implies (and (integerp x)
		  (integerp y))
	     (equal (equal (evenp x) (evenp y))
		    (evenp (- x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance evenp-minus (x y))
			(:instance evenp-iff-evenp-plus (y (- y)))))))

(defthm evenp-iff-evenp-iff-evenp-plus
    (implies (and (integerp x)
		  (integerp y)
		  (integerp z))
	     (equal (equal (evenp x) (evenp y))
		    (equal (evenp (+ x z)) (evenp (+ y z)))))
  :rule-classes ()
  :hints (("Goal" :use (evenp-iff-evenp-minus
			(:instance evenp-iff-evenp-minus (x (+ x z)) (y (+ y z)))))))

(defthm evenp-times
    (implies (and (integerp x)
		  (integerp y))
	     (equal (evenp (* x y))
		    (or (evenp x) (evenp y))))
  :hints (("Goal" :in-theory (enable divides)
		  :use (evenp-iff-evenp-minus
			(:instance euclid (p 2) (a x) (b y))
			(:instance divides-product (x 2) (y x) (z y))
			(:instance divides-product (x 2) (y y) (z x))))))

(defthm oddp-odd-prime
    (implies (and (primep p)
		  (not (equal p 2)))
	     (not (evenp p)))
  :hints (("Goal" :in-theory (enable divides)
		  :use ((:instance primep-no-divisor (d 2))))))

(in-theory (disable evenp))

;; Our first goal is to derive yet another characterization of quadratic residues:
;; if m is odd and not divisible by an odd prime p, then m is a quadratic residue
;; mod p iff the sum
;;    fl(m/p) + fl(2*m/p) + fl(3*m/p) + ... + fl(((p-1)/2)*m/p)
;; is even.

;; We require the following relation between reflections, mod-prods, and mu, which
;; follows easily from the definitions:

(defun plus-list (l)
  (if (consp l)
      (+ (ifix (car l)) (plus-list (cdr l)))
    0))

(defthm even-mu
    (implies (and (primep p)
		  (not (equal p 2))
		  (integerp m))
	     (equal (evenp (mu n m p))
		    (equal (evenp (plus-list (mod-prods n m p)))
			   (evenp (plus-list (reflections n m p))))))
  :rule-classes ()
  :hints (("Subgoal *1/3" :use ((:instance evenp-iff-evenp-iff-evenp-plus
					   (x (plus-list (mod-prods (1- n) m p)))
					   (y (plus-list (reflections (1- n) m p)))
					   (z (mod (* m n) p)))))
	  ("Subgoal *1/2" :use ((:instance evenp-iff-evenp-plus
					   (x (plus-list (mod-prods (1- n) m p)))
					   (y (mod (* m n) p)))
				(:instance evenp-iff-evenp-plus
					   (x (plus-list (reflections (1- n) m p)))
					   (y (- p (mod (* m n) p))))
				(:instance evenp-iff-evenp-minus
					   (x p)
					   (y (mod (* m n) p)))
				(:instance evenp-oddp (m (mu (1- n) m p)))))))

;; We shall instantiate the above lemma with n = (p-1)/2.  In "gauss",
;; we showed that reflections((p-1)/2,m,p) is a permutation of
;; positives((p-1)/2).  It follows that these two lists have the same
;; sum:

(defthm perm-plus-list-lemma
  (implies (member x m)
	   (equal (+ (ifix x) (plus-list (remove1 x m))) (plus-list m)))
  :rule-classes ())

(defthm perm-plus-list
  (implies (perm l m)
	   (equal (plus-list l) (plus-list m)))
  :rule-classes ()
  :hints (("Subgoal *1/2" :use ((:instance perm-plus-list-lemma (x (car l)))))))

(defthm plus-list-reflections
  (implies (and (primep p)
		(not (equal p 2))
		(integerp m)
		(not (divides p m)))
	   (equal (plus-list (positives (/ (1- p) 2)))
		  (plus-list (reflections (/ (1- p) 2) m p))))
  :rule-classes ()
  :hints (("Goal" :use (perm-reflections
			(:instance perm-plus-list
				   (m (reflections (/ (1- p) 2) m p))
				   (l (positives (/ (1- p) 2))))))))

;; Combining Gauss's Lemma with the above results, we have the following
;; characterization of quadratic residues:

(defthm residue-mod-prods-positives
    (implies (and (primep p)
		  (not (equal p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (residue m p)
		    (equal (evenp (plus-list (mod-prods (/ (1- p) 2) m p)))
			   (evenp (plus-list (positives (/ (1- p) 2)))))))
  :rule-classes ()
  :hints (("Goal" :use (plus-list-reflections
			gauss-lemma
			(:instance even-mu (n (/ (1- p) 2)))))))

;;  Next, we sum the equation
;;        m*n = fl(m*n/p)* p + mod(m*n,p)
;; from n = 1 to n = (p-1)/2:

(defun fl-prods (n m p)
  (if (zp n)
      ()
      (cons (fl (/ (* m n) p))
            (fl-prods (1- n) m p))))

(defthm fl-mod-plus-list
    (implies (and (integerp p)
		  (integerp m))
	     (equal (* m (plus-list (positives n)))
		    (+ (* p (plus-list (fl-prods n m p)))
		       (plus-list (mod-prods n m p)))))
  :rule-classes ()
  :hints (("Subgoal *1/2''" :use ((:instance mod-def (x (* m n)) (y p))))))

;; Reducing the above equation mod 2 yields the desired result::

(defthm fl-mod-plus-list-evenp
    (implies (and (integerp p)
		  (integerp m)
		  (oddp m)
		  (oddp p))
	     (equal (evenp (plus-list (positives n)))
		    (equal (evenp (plus-list (fl-prods n m p)))
			   (evenp (plus-list (mod-prods n m p))))))
  :rule-classes ()
  :hints (("Goal" :use (fl-mod-plus-list
			(:instance evenp-iff-evenp-plus
				   (x (* p (plus-list (fl-prods n m p))))
				   (y (plus-list (mod-prods n m p))))))))

(defthm residue-quotients
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (oddp m))
	     (equal (residue m p)
		    (evenp (plus-list (fl-prods (/ (1- p) 2) m p)))))
  :rule-classes ()
  :hints (("Goal" :use (residue-mod-prods-positives
			(:instance fl-mod-plus-list-evenp (n (/ (1- p) 2)))))))

;; We instantiate the above result with m = q and again with m = p and p = q.
;; This gives us the following:

(defthm equal-residue-even-plus
  (implies (and (primep p)
		(not (equal p 2))
		(primep q)
		(not (equal q 2))
		(not (equal p q)))
	   (iff (equal (residue q p) (residue p q))
		(evenp (+ (plus-list (fl-prods (/ (1- p) 2) q p))
			  (plus-list (fl-prods (/ (1- q) 2) p q))))))
  :hints (("Goal" :use ((:instance residue-quotients (m q))
			(:instance residue-quotients (m p) (p q))
			(:instance evenp-iff-evenp-plus
				   (x (plus-list (fl-prods (/ (1- p) 2) q p)))
				   (y (plus-list (fl-prods (/ (1- q) 2) p q))))
			(:instance primep-no-divisor (d q))
			(:instance primep-no-divisor (d p) (p q))))))

;; We shall complete the proof of quadratic reciprocity by showing that the sum in
;; the above lemma equals the product ((p-1)/2) * ((q-1)/2).  This amounts to a
;; formalization of a geometric argument of Eisenstein.  (For a detailed discussion,
;; see http://www.russinoff.com/papers/gauss.html.)

;; Given two lists of integers l and m, let wins(l,m) be the number
;; of pairs (x,y) in the cartesian product l x m such that x > y, and
;; let losses(l,m) be the number of pairs satisfying x < y.  Assume that
;; l and m are disjoint.  Then
;;   wins(l,m) + losses(l,m) = wins(l,m) + wins(m,l) = len(l)*len(m).
;; This observation is formalized by the theorem plus-wins-wins below.

(defun wins1 (x l)
  (if (consp l)
      (if (< (car l) x)
          (1+ (wins1 x (cdr l)))
        (wins1 x (cdr l)))
    0))

(defun wins (k l)
  (if (consp k)
      (+ (wins1 (car k) l) (wins (cdr k) l))
    0))

(defun losses1 (x l)
  (if (consp l)
      (if (< x (car l))
          (1+ (losses1 x (cdr l)))
        (losses1 x (cdr l)))
    0))

(defun losses (k l)
  (if (consp k)
      (+ (losses1 (car k) l) (losses (cdr k) l))
    0))

(defun all-integerp (l)
  (if (consp l)
      (and (integerp (car l))
	   (all-integerp (cdr l)))
    t))

(defthm plus-losses1-wins1
  (implies (and (not (member x l))
		(integerp x)
		(all-integerp l))
           (equal (+ (losses1 x l) (wins1 x l))
                  (len l))))

(defthm plus-wins-losses
  (implies (and (not (intersectp-equal l m))
                (all-integerp l)
		(all-integerp m))
           (equal (+ (wins l m) (losses l m))
                  (* (len l) (len m)))))

(defthm equal-wins-losses
    (equal (losses l m) (wins m l))
  :rule-classes ())

(defthm plus-wins-wins
  (implies (and (not (intersectp-equal l m))
                (all-integerp l)
		(all-integerp m))
           (equal (+ (wins l m) (wins m l))
                  (* (len l) (len m))))
  :hints (("Goal" :use (equal-wins-losses))))

;; We shall apply the above result to the two lists
;;    l = (p, 2*p, 3*p, ..., ((q-1)/2)*p)
;; and
;;    m = (q, 2*q, 3*q, ..., ((p-1)/2)*q).
;; We must first show that l and m are disjoint.

(defun mults (n p)
  (if (zp n)
      ()
    (cons (* n p) (mults (1- n) p))))

(defthm all-integerp-mults
  (implies (integerp p)
	   (all-integerp (mults n p))))

(defthm not-divides-p-mult-q
  (implies (and (primep p)
		(primep q)
		(not (= p q))
		(not (zp j))
		(< j p))
           (not (divides p (* j q))))
  :hints (("Goal" :use ((:instance euclid (a j) (b q))
			(:instance divides-leq (x p) (y j))
			(:instance primep-no-divisor (d p) (p q))))))

(defthm no-equal-mults
  (implies (and (primep p)
		(primep q)
		(not (= p q))
		(not (zp i))
		(not (zp j))
		(< j p))
           (not (equal (* i p) (* j q))))
  :hints (("Goal" :use ((:instance divides-product (x p) (y p) (z i))))))

(defthm empty-intersect-mults-lemma
  (implies (and (primep p)
		(primep q)
		(not (= p q))
		(not (zp i))
                (not (zp j))
		(< j p))
           (not (member-equal (* i p) (mults j q)))))

(defthm empty-intersect-mults
  (implies (and (primep p)
		(primep q)
		(not (= p 2))
		(not (= q 2))
		(not (= p q)))
           (not (intersectp-equal (mults i p)
				  (mults (+ -1/2 (* 1/2 p)) q)))))

;; The product of the lengths of the two lists is
;;    len(l)*len(m) = ((p-1)/2) * (q-1)/2).

(defthm len-mults
  (equal (len (mults n p))
	 (nfix n)))

;; Once we show that wins(l,m) and wins(m,l) are equal to the two sums
;; in the lemma equal-residue-even-plus, it will follow that the sum of
;; those two sums is that product, as desired.

(defthm wins1-bnd-len
    (<= (wins1 a l) (len l))
  :rule-classes ())

(defun wins1-bnd-induction (i n)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      t
    (if (> n i)
	t
      (if (= n i)
	  t
	(if (= n (1- i))
	    (wins1-bnd-induction (1- i) n)
	  (wins1-bnd-induction (1- i) n))))))

(local-defthm hack-1
  (implies (and (not (zp i))
                (not (zp n))
                (not (zp p))
                (<= n i))
           (<= (* n p) (* i p)))
  :rule-classes ())

(local-defthm hack-2
  (implies (and (not (zp i))
                (not (zp n))
                (not (zp p))
                (<= n i)
                (integerp a)
                (< a (* n p)))
           (not (< (* i p) a)))
  :hints (("goal" :use (hack-1) :in-theory (theory 'minimal-theory)))
  :rule-classes ())

(defthm wins1-upper-bnd-lemma
    (implies (and (not (zp n))
		  (not (zp p))
		  (integerp a)
		  (< a (* n p)))
	     (< (wins1 a (mults i p)) n))
  :rule-classes ()
  :hints (("Goal" :induct (wins1-bnd-induction i n))
	  ("Subgoal *1/5" :use (hack-2 (:instance wins1-bnd-len (l (mults (1- i) p)))))
	  ("Subgoal *1/3" :use ((:instance wins1-bnd-len (l (mults (1- i) p)))))
	  ("Subgoal *1/2" :use ((:instance wins1-bnd-len (l (mults (1- i) p)))))))

(local-defthm hack-3
  (implies (and (not (zp p))
		(rationalp a))
           (< (* a p) (+ p (* p (fl a)))))
  :rule-classes ())

(defthm wins1-upper-bnd
    (implies (and (not (zp p))
		  (natp a))
	     (<= (wins1 a (mults i p)) (fl (/ a p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-3 (a (/ a p)))
                        (:instance wins1-upper-bnd-lemma (n (1+ (fl (/ a p)))))))))

(defthm monotone-wins1
    (implies (and (integerp m)
		  (integerp n)
		  (<= m n))
	     (<= (wins1 a (mults m p)) (wins1 a (mults n p))))
  :rule-classes ()
  :hints (("Goal" :induct (mults n p))))

(defthm leq-n-wins1
    (implies (and (not (zp p))
		  (integerp n)
		  (integerp a)
		  (< (* n p) a))
	     (<= n (wins1 a (mults n p))))
  :rule-classes ()
  :hints (("Goal" :induct (mults n p))))

(local-defthm hack-4
  (implies (and (not (zp p))
                (not (integerp a))
		(rationalp a))
           (> (* a p) (* p (fl a))))
  :rule-classes ())

(defthm leq-fl-wins1
  (implies (and (not (zp p))
		(integerp n)
		(integerp a)
		(not (divides p a))
                (<= (fl (/ a p)) n))
           (<= (fl (/ a p)) (wins1 a (mults n p))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
		  :use ((:instance hack-4 (a (/ a p)))
                        (:instance monotone-wins1 (m (fl (/ a p))))
			(:instance leq-n-wins1 (n (fl (/ a p))))))))

(local-defthm hack-5
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (< x y)
                (> z 0))
           (< (* z x) (* z y)))
  :rule-classes ())

(local-defthm hack-6
    (implies (and (integerp a)
		  (integerp c)
		  (not (zp d))
		  (not (zp b))
		  (<= (* a b) (* c d)))
	     (<= (/ a d) (/ c b)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-5 (x (/ c b)) (y (/ a d)) (z (* b d)))))))

(defthm leq-times-fl
    (implies (and (integerp a)
		  (integerp c)
		  (not (zp d))
		  (not (zp b))
		  (<= (* a b) (* c d)))
	     (<= (fl (/ a d)) (fl (/ c b))))
  :rule-classes ()
  :hints (("Goal" :use (hack-6
                        (:instance fl-def (x (/ a d)))
			(:instance n<=fl-linear (n (fl (/ a d))) (x (/ c b)))))))

(defthm leq-fl-times
    (implies (and (integerp j)
		  (integerp q)
		  (not (zp p))
		  (not (zp q))
		  (oddp p)
		  (oddp q)
		  (<= j (/ (1- p) 2)))
	     (<= (fl (/ (* j q) p)) (/ (1- q) 2)))
  :hints (("Goal" :in-theory (enable evenp)
		  :use ((:instance leq-times-fl (a (* j q)) (b 2) (c q) (d p))))))

(defthm wins1-lower-bnd
    (implies (and (not (zp j))
		  (integerp q)
		  (primep p)
		  (primep q)
		  (not (= p q))
		  (oddp p)
		  (oddp q)
		  (<= j (/ (1- p) 2)))
	     (<= (fl (/ (* j q) p))
		 (wins1 (* j q) (mults (/ (1- q) 2) p))))
  :hints (("Goal" :in-theory (enable evenp)
                  :use (leq-fl-times
			(:instance leq-fl-wins1 (a (* j q)) (n (/ (1- q) 2)))))))

(defthm equal-fl-wins1
  (implies (and (not (zp j))
		(integerp q)
		(primep p)
		(primep q)
		(not (= p q))
		(oddp p)
		(oddp q)
		(<= j (/ (1- p) 2)))
           (equal (wins1 (* j q) (mults (+ -1/2 (* 1/2 q)) p))
                  (fl (/ (* j q) p))))
  :hints (("Goal" :use (wins1-lower-bnd
			(:instance wins1-upper-bnd (a (* j q)) (i (/ (1- q) 2)))))))

(defthm equal-wins-plus-list
  (implies (and (not (zp j))
		(integerp q)
		(primep p)
		(primep q)
		(not (= p q))
		(oddp p)
		(oddp q)
		(<= j (/ (1- p) 2)))
           (equal (plus-list (fl-prods j q p))
                  (wins (mults j q) (mults (/ (1- q) 2) p))))
  :hints (("Goal" :induct (mults j q))
          ("Subgoal *1/3" :use equal-fl-wins1)))

(defthm quadratic-reciprocity
  (implies (and (primep p)
		(not (= p 2))
                (primep q)
		(not (= q 2))
                (not (= p q)))
           (iff (equal (residue q p) (residue p q))
                (evenp (* (/ (1- p) 2) (/ (1- q) 2))))))
