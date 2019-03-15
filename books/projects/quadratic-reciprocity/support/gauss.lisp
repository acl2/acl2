(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system)) ;; It's hard to do any arithmetic without something like this

;; This book contains a proof of Gauss's Lemma:  Let p be prime and assume that
;; m is not divisible by p.  Let mu be the number of elements of the set
;;    {mod(m,p), mod(2*m,p), ..., mod(((p-1)/2)*m}
;; that exceed (p-1)/2.  Then m is a quadratic residue mod p iff mu is even.

;; As a corollary, we also prove the Second Supplement to the Law of Quadratic
;; Reciprocity: 2 is a quadratic residue mod p iff mod(p,8) is either 1 or 7.

;; The proof depends on euler's criterion::

(include-book "euler")

(defun mu (n m p)
  (if (zp n)
      0
    (if (> (mod (* m n) p) (/ (1- p) 2))
	(1+ (mu (1- n) m p))
      (mu (1- n) m p))))

(defun reflections (n m p)
  (if (zp n)
      ()
    (if (> (mod (* m n) p) (/ (1- p) 2))
        (cons (- p (mod (* m n) p))
              (reflections (1- n) m p))
      (cons (mod (* m n) p)
	    (reflections (1- n) m p)))))

;; We shall show that reflections((p-1)/2,m,p) is a list of length (p-1)/2 of distinct
;; integers between 1 and (p-1)/2, and therefore a permutation of (1, 2, ..., (p-1)/2),
;; which implies that the product of its elements is ((p-1)/2)!.

(defthm len-reflections
    (implies (natp n)
	     (equal (len (reflections n m p)) n)))

(defthm mod-distinct-reflect
    (implies (and (primep p)
		  (not (zp i))
		  (< i (/ p 2))
		  (not (zp j))
		  (< j (/ p 2))
		  (not (= j i))
		  (integerp m)
		  (not (divides p m)))
	     (not (equal (+ (mod (* m i) p) (mod (* m j) p)) p)))
  :hints (("Goal" :use ((:instance divides-leq (x p) (y (+ i j)))
			(:instance divides-mod-0 (a (+ (* m i) (* m j))) (n p))
			(:instance divides-mod-0 (a (+ (mod (* m i) p) (mod (* m j) p))) (n p))
			(:instance euclid (a (+ i j)) (b m))))))

(defthm reflections-distinct-positives-lemma-1
    (implies (and (primep p)
		  (not (= p 2))
		  (not (zp n))
		  (< n (/ p 2))
		  (integerp r)
		  (< r n)
		  (integerp m)
		  (not (divides p m)))
	     (not (member (mod (* m n) p) (reflections r m p)))))

(defthm reflections-distinct-positives-lemma-2
    (implies (and (primep p)
		  (not (= p 2))
		  (not (zp n))
		  (< n (/ p 2))
		  (integerp r)
		  (< r n)
		  (integerp m)
		  (not (divides p m)))
	     (not (member (+ p (- (mod (* m n) p))) (reflections r m p))))
  :hints (("Subgoal *1/4" :in-theory (disable mod-distinct)
			  :use ((:instance mod-distinct (i n) (j r))))))

(defthm p-1-even-cor
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp n)
		  (> n (/ (1- p) 2)))
	     (>= n (/ (1+ p) 2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable p-1-even)
		  :use (p-1-even))))

(defthm reflections-distinct-positives
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (integerp n)
		  (< n (/ p 2)))
	     (distinct-positives (reflections n m p) (/ (1- p) 2)))
  :rule-classes ()
  :hints (("Subgoal *1/7" :use ((:instance mod-p-bnds (i n))))
	  ("Subgoal *1/4" :use ((:instance p-1-even-cor (n (mod (* m n) p)))))))

;; This result allows us to compute the product of the elements of
;; reflections((p-1)/2,m,p):

(defthm perm-reflections
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (perm (positives (/ (1- p) 2))
		   (reflections (/ (1- p) 2) m p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance reflections-distinct-positives (n (/ (1- p) 2)))
			(:instance pigeonhole-principle (l (reflections (/ (1- p) 2) m p)))))))

(defthm times-list-reflections
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
           (equal (times-list (reflections (+ -1/2 (* 1/2 p)) m p))
                  (fact (/ (1- p) 2))))
  :hints (("Goal" :use (perm-reflections
			(:instance perm-times-list
				   (l1 (positives (/ (1- p) 2)))
				   (l2 (reflections (/ (1- p) 2) m p)))))))

;;  We have an alternative method for computing the same product:

(defthm mod-mult-2
    (implies (and (integerp n)
		  (integerp m)
		  (integerp a))
	     (equal (mod (+ (* n a) m) n)
		    (mod m n)))
  :hints (("Goal" :use (mod-mult))))

(defthm times-list-reflection-mod-prods
    (implies (and (not (zp p))
		  (integerp m)
		  (integerp n))
	     (equal (mod (times-list (reflections n m p)) p)
		    (if (evenp (mu n m p))
			(mod (times-list (mod-prods n m p)) p)
		      (mod (- (times-list (mod-prods n m p))) p))))
  :rule-classes ()
  :hints (("Subgoal *1/3" :use ((:instance mod-times-mod
					   (a (times-list (reflections (1- n) m p)))
					   (b (times-list (mod-prods (1- n) m p)))
					   (c (mod (* m n) p))
					   (n p))
				(:instance mod-times-mod
					   (a (times-list (reflections (1- n) m p)))
					   (b (- (times-list (mod-prods (1- n) m p))))
					   (c (mod (* m n) p))
					   (n p))))
	  ("Subgoal *1/2" :use ((:instance evenp-oddp (m (mu (1- n) m p)))
				(:instance mod-times-mod
					   (a (times-list (reflections (1- n) m p)))
					   (b (times-list (mod-prods (1- n) m p)))
					   (c (- (mod (* m n) p)))
					   (n p))
				(:instance mod-times-mod
					   (a (times-list (reflections (1- n) m p)))
					   (b (- (times-list (mod-prods (1- n) m p))))
					   (c (- (mod (* m n) p)))
					   (n p))))))

;; Gauss's Lemma follows from the equation of the two expressions
;; for the product.  We consider two cases according to the parity
;; of mu:

(defthm euler-mu-even
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (evenp (mu (/ (1- p) 2) m p)))
	     (= (mod (expt m (/ (1- p) 2)) p) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance times-list-reflection-mod-prods (n (/ (1- p) 2)))
			(:instance mod-mod-prods (n (/ (1- p) 2)))
			(:instance not-divides-p-fact (n (/ (1- p) 2)))
			(:instance mod-times-prime (a (fact (/ (1- p) 2))) (b (expt m (/ (1- p) 2))) (c 1))))))

(defthm euler-mu-odd
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (oddp (mu (/ (1- p) 2) m p)))
	     (= (mod (expt m (/ (1- p) 2)) p) (- p 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance times-list-reflection-mod-prods (n (/ (1- p) 2)))
			(:instance mod-mod-prods (n (/ (1- p) 2)))
			(:instance not-divides-p-fact (n (/ (1- p) 2)))
			(:instance mod-times-prime
				   (a (- (fact (/ (1- p) 2)))) (b (expt m (/ (1- p) 2))) (c -1))
			(:instance mod-mult (m -1) (a 1) (n p))
			(:instance divides-product (x p) (y (- (fact (/ (1- p) 2)))) (z -1))
			(:instance mod-times-mod
				   (a (times-list (mod-prods (/ (1- p) 2) m p)))
				   (b (* (fact (/ (1- p) 2)) (expt m (/ (1- p) 2))))
				   (c -1)
				   (n p))))))

(defthm gauss-lemma
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (iff (evenp (mu (/ (1- p) 2) m p))
		  (residue m p)))
  :rule-classes ()
  :hints (("Goal" :use (euler-mu-even
			euler-mu-odd
			euler-criterion))))

;; For the proof of the Second Supplement, we show first that
;;   mu((p-1)/2,2,p) = (p-1)/2 - fl((p-1)/4):

(defthm mu-0-rewrite
    (implies (and (not (zp p))
		  (natp n)
		  (<= (* 2 n) (/ (1- p) 2)))
	     (equal (mu n 2 p) 0)))

(defthm mu-rewrite-lemma-1
    (implies (and (primep p)
		  (not (= p 2))
		  (natp k)
		  (<= (* 2 k) (/ (1- p) 2))
		  (< (/ (1- p) 2) (* 2 (1+ k)))
		  (integerp n)
		  (<= k n)
		  (<= n (/ (1- p) 2)))
	     (= (mu n 2 p) (- n k)))
  :rule-classes ())

(defthm mu-rewrite-lemma-2
    (implies (and (primep p)
		  (not (= p 2)))
	     (equal (mu (+ -1/2 (* 1/2 p)) 2 p)
		    (- (/ (1- p) 2) (fl (/ (1- p) 4)))))
  :hints (("Goal" :use ((:instance mu-rewrite-lemma-1
				   (k (fl (/ (1- p) 4)))
				   (n (/ (1- p) 2)))))))

;; Let k = fl(p/8) and m = mod(p,8).  Then p = 8*k + m.  It follows that
;;   mu((p-1)/2,2,p) = 2*k + (m-1)/2 - fl((m-1)/4):

(defthmd mu-rewrite-lemma-3
    (implies (and (primep p)
		  (not (= p 2)))
	     (equal (mod p 8)
		    (- p (* 8 (fl (/ p 8))))))
  :hints (("Goal" :use ((:instance mod-def (x p) (y 8))))))

(defthm mu-rewrite
    (implies (and (primep p)
		  (not (= p 2)))
	     (equal (mu (+ -1/2 (* 1/2 p)) 2 p)
		    (+ (* 2 (fl (/ p 8))) (- (/ (1- (mod p 8)) 2) (fl (/ (1- (mod p 8)) 4))))))
  :hints (("Goal" :in-theory (enable mu-rewrite-lemma-3))))

;; The desired result now follows by a simple case analysis:

(defthm no-integer-7-8
    (implies (and (integerp m)
		  (< 7 m))
	     (not (< m 8))))

(defthm mod-p-8-choices
    (implies (and (primep p)
		  (not (= p 2)))
	     (member (mod p 8) '(1 3 5 7)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
		  :use ((:instance mod-def (x p) (y 8))
			(:instance primep-no-divisor (d 2))
			(:instance primep-no-divisor (d 8))
			(:instance mod-bnd-1 (m p) (n 8))
			(:instance member-positives (x (mod p 8)) (n 7))
			(:instance divides-mod-0 (n 8) (a p))))))

(defthm second-supplement
    (implies (and (primep p)
		  (not (= p 2)))
	     (iff (residue 2 p)
		  (or (= (mod p 8) 1)
		      (= (mod p 8) 7))))
  :rule-classes ()
  :hints (("Goal" :use (mod-p-8-choices
			(:instance gauss-lemma (m 2))
			(:instance divides-leq (x p) (y 2))))))
