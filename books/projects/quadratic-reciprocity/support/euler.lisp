(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system)) ;; It's hard to do any arithmetic without something like this

;; This book contains a proof of Euler's Criterion for quadratic residues:
;; If p is an odd prime and m is not divisible by p, then

;;   mod(m^((p-1)/2),p) = 1 if m is a quadratic residue mod p
;;                        p-1 if not.

;; Along the way, we also prove Wilson's Theorem: If p is prime, then
;; mod((p-1)!,p) = p-1.

;; Finally, as a consequence of Euler's Criterion, we derive the First
;; Supplement to the Law of Quadratic Reciprocity: -1 is a quadratic
;; residue mod p iff mod(p,4) = 1.

;; The proof depends on Fermat's Theorem:

(include-book "fermat")

;; Let p be a prime, let m be relatively prime to p, and let 0 < j < p.
;; Then there exists a unique j' such that 0 < j' < p and
;;         mod(j*j',p) = mod(m,p),
;; called the associate of j w.r.t. a mod p.

(defund associate (j m p)
  (mod (* m (expt j (- p 2))) p))

(local-in-theory (disable acl2::floor-mod-elim acl2::mod-theorem-one-b))

(defthm associate-property
    (implies (and (primep p)
		  (integerp m)
		  (not (zp j))
		  (< j p)
		  (not (divides p m)))
	     (equal (mod (* (associate j m p) j) p)
		    (mod m p)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable associate)
		  :use ((:instance mod-mod-times (n p) (a (* m (expt j (- p 2)))) (b j))
			(:instance mod-mod-times (n p) (a (expt j (1- p))) (b m))
			(:instance divides-leq (x p) (y j))
			(:instance fermat (m j))))))

(defthm associate-bnds
    (implies (and (primep p)
		  (integerp m)
		  (not (zp j))
		  (< j p)
		  (not (divides p m)))
	     (and (not (zp (associate j m p)))
		  (< (associate j m p) p)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable associate)
		  :use (associate-property
			(:instance divides-mod-0 (a m) (n p))
			(:instance divides-leq (x p) (y j))
			(:instance natp-mod-2 (m (* m (expt j (- p 2)))) (n p))))))

(defthm associate-is-unique
    (implies (and (primep p)
		  (integerp m)
		  (not (zp j))
		  (< j p)
		  (not (divides p m))
		  (integerp x)
		  (equal (mod m p) (mod (* j x)	p)))
	     (equal (associate j m p) (mod x p)))
  :rule-classes ()
  :hints (("Goal" :use (associate-bnds
			associate-property
			(:instance divides-leq (x p) (y j))
			(:instance divides-mod-equal (n p) (a (* j x)) (b (* j (associate j m p))))
			(:instance euclid (a j) (b (- x (associate j m p))))
			(:instance divides-mod-equal (n p) (a x) (b (associate j m p)))))))

(defthm associate-of-associate
    (implies (and (primep p)
		  (integerp m)
		  (not (zp j))
		  (< j p)
		  (not (divides p m)))
	     (equal (associate (associate j m p) m p)
		    (mod j p)))
  :hints (("Goal" :use (associate-property
			associate-bnds
			(:instance divides-leq (x p) (y j))
			(:instance divides-leq (x p) (y (associate j m p)))
			(:instance associate-is-unique (x j) (j (associate j m p)))))))

(defthm associate-equal
    (implies (and (primep p)
		  (integerp m)
		  (integerp j)
		  (not (divides p m))
		  (not (zp j))
		  (< j p)
		  (not (zp i))
		  (< i p))
	     (equal (equal (associate j m p) (associate i m p))
		    (equal i j)))
  :hints (("Goal" :in-theory (disable associate-of-associate)
		  :use (associate-of-associate
			(:instance associate-of-associate (j i))))))

(defthm associate-square
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (not (zp j))
		  (< j p))
	     (iff (= (associate j m p) j)
		  (= (mod (* j j) p) (mod m p))))
  :rule-classes ()
  :hints (("Goal" :use (associate-property
			(:instance divides-leq (x p) (y j))
			(:instance associate-is-unique (x j))))))

;; If there exists x such that mod(x*x,p) = mod(m,p), then m is said to be
;; a (quadratic) residue mod p.

(defun find-root (n m p)
  (if (zp n)
      ()
    (if (= (mod (* n n) p) (mod m p))
	n
      (find-root (1- n) m p))))

(defund residue (m p)
  (not (null (find-root (1- p) m p))))

(defthm not-res-no-root-lemma
    (implies (and (not (find-root n m p))
                  (integerp m)
		  (not (zp n))
		  (not (zp j))
		  (<= j n))
	     (not (equal (mod (* j j) p) (mod m p))))
  :rule-classes ())

(defthm not-res-no-root
    (implies (and (primep p)
                  (integerp m)
		  (not (residue m p))
		  (not (zp j))
		  (< j p))
	     (not (equal (mod (* j j) p) (mod m p))))
  :hints (("Goal" :in-theory (enable residue)
		  :use ((:instance not-res-no-root-lemma (n (1- p)))))))

(defthm not-res-no-self-associate
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (not (residue m p))
		  (not (zp j))
		  (< j p))
	     (not (equal (associate j m p) j)))
  :rule-classes ()
  :hints (("Goal" :use (not-res-no-root
			associate-square))))

;; If m is a residue mod p, then there are exactly 2 roots of
;; mod(x*x,p) = mod(m,p) in the range 0 < x < p.

(defun root1 (m p)
  (find-root (1- p) m p))

(defthm res-root1-lemma
    (implies (and (find-root n m p)
		  (not (zp n)))
	     (and (not (zp (find-root n m p)))
		  (<= (find-root n m p) n)
		  (equal (mod (* (find-root n m p) (find-root n m p)) p) (mod m p))))
  :rule-classes ())

(defthm res-root1
    (implies (and (primep p)
		  (residue m p))
	     (and (not (zp (root1 m p)))
		  (< (root1 m p) p)
		  (equal (mod (* (root1 m p) (root1 m p)) p) (mod m p))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable residue)
		  :use ((:instance res-root1-lemma (n (1- p)))))))

(in-theory (disable root1))

(defun root2 (m p)
  (- p (root1 m p)))

(defthm res-root2
    (implies (and (primep p)
		  (residue m p))
	     (and (not (zp (root2 m p)))
		  (< (root2 m p) p)
		  (equal (mod (* (root2 m p) (root2 m p)) p) (mod m p))))
  :rule-classes ()
  :hints (("Goal" :use (res-root1
			(:instance mod-mult
				   (m (* (root1 m p) (root1 m p)))
				   (a (- p (* 2 (root1 m p))))
				   (n p))))))

(defthm root1-root2
    (implies (and (primep p)
		  (integerp m)
		  (residue m p))
	     (equal (mod (* (root1 m p) (root2 m p)) p)
		    (mod (- m) p)))
  :hints (("Goal" :use (res-root1
			(:instance mod-mult (n p) (m (- (* (root1 m p) (root1 m p)))) (a (root1 m p)))
			(:instance mod-mod-times (a (- (root1 m p))) (b (root1 m p)) (n p))
			(:instance mod-times-mod (a (* (root1 m p) (root1 m p))) (b m) (c -1) (n p))))))

(defthm associate-roots
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (residue m p))
	     (and (equal (associate (root1 m p) m p) (root1 m p))
		  (equal (associate (root2 m p) m p) (root2 m p))))
  :rule-classes ()
  :hints (("Goal" :use (res-root1
			res-root2
			(:instance associate-square (j (root1 m p)))
			(:instance associate-square (j (root2 m p)))))))

(defthm only-2-roots-lemma-1
    (implies (and (primep p)
		  (integerp r)
		  (integerp j)
		  (= (mod (* j j) p) (mod (* r r) p)))
	     (or (= (mod j p) (mod r p))
		 (= (mod j p) (mod (- r) p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance divides-mod-equal (n p) (a (* j j)) (b (* r r)))
			(:instance euclid (a (- j r)) (b (+ j r)))
			(:instance divides-mod-equal (n p) (a j) (b r))
			(:instance divides-mod-equal (n p) (a j) (b (- r)))))))

(defthm only-2-roots-lemma-2
    (implies (and (primep p)
		  (not (zp r))
		  (< r p)
		  (not (zp j))
		  (< j p)
		  (= (mod (* j j) p) (mod (* r r) p)))
	     (or (= j r)
		 (= j (- p r))))
  :rule-classes ()
  :hints (("Goal" :use (only-2-roots-lemma-1
			(:instance mod-mult (n p) (m (- r)) (a 1))))))

(defthm only-2-roots
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (residue m p)
		  (not (zp j))
		  (< j p)
		  (= (associate j m p) j))
	     (or (= j (root1 m p))
		 (= j (root2 m p))))
  :rule-classes ()
  :hints (("Goal" :use (res-root1
			associate-square
			res-root2
			(:instance only-2-roots-lemma-2 (r (root1 m p)))))))

(defthm roots-distinct
    (implies (and (primep p)
		  (not (= p 2))
		  (residue m p))
	     (not (= (root1 m p) (root2 m p))))
  :rule-classes ()
  :hints (("Goal" :use (res-root1
			associate-bnds
			(:instance euclid (a 2) (b (root1 m p)))
			(:instance divides-leq (x p) (y 2))
			(:instance divides-leq (x p) (y (root1 m p)))))))

(in-theory (disable root2))

;; For 0 <= n < p, we construct a list associates(n,m,p) of distinct integers 
;; between 1 and p-1 with the following properties:
;; (a) If 1 <= j <= n, then j is in associates(n,m,p).
;; (b) If j is in associates(n,m,p), then so is associate(j,m,p).

(defun associates (n m p)
  (if (zp n)
      (if (residue m p)
	  (cons (root2 m p)
		(cons (root1 m p) ()))
	())
    (if (member n (associates (1- n) m p))
	(associates (1- n) m p)
      (cons (associate n m p)
	    (cons n (associates (1- n) m p))))))

(defthm member-associates
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (integerp n)
		  (< n p)
		  (not (zp j))
		  (< j p))
	     (iff (member (associate j m p) (associates n m p))
		  (member j (associates n m p))))
  :hints (("Subgoal *1/1" :use (associate-roots))
	  ("Subgoal *1/1.8" :in-theory (disable associate-of-associate)
			    :use (associate-roots associate-of-associate))
	  ("Subgoal *1/1.5" :in-theory (disable associate-of-associate)
			    :use (associate-roots associate-of-associate))))

;; We shall show that associates(p-1,m,p) is a permutation of positives(p-1).

(defthm subset-positives-associates
    (subsetp (positives n) (associates n m p)))

(defthm member-self-associate
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (not (zp j))
		  (< j p)
		  (equal (associate j m p) j))
	     (member j (associates n m p)))
  :hints (("Subgoal *1/2" :use not-res-no-self-associate)
	  ("Subgoal *1/1" :use only-2-roots)))

(defthm distinct-positives-associates-lemma
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (integerp n)
		  (< n p))
	     (distinct-positives (associates n m p) (1- p)))
  :rule-classes ()
  :hints (("Subgoal *1/1" :use (res-root1
				res-root2
				roots-distinct))))

(defthm distinct-positives-associates
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (distinct-positives (associates (1- p) m p) (1- p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance distinct-positives-associates-lemma (n (1- p)))))))

;; We shall require a variation of the pigeonhole principle.

(defun ldpu-induction (l n)
  (if (zp n)
      t
    (if (member n l)
	(ldpu-induction (remove1 n l) (1- n))
      (ldpu-induction l (1- n)))))

(defthm len-distinct-positives-upper
    (implies (and (natp n)
		  (distinct-positives l n))
	     (<= (len l) n))
  :rule-classes ()
  :hints (("Goal" :induct (ldpu-induction l n))))

(defthm len-remove
    (implies (member n l)
	     (equal (len (remove1 n l))
		    (1- (len l)))))

(defthm subsetp-remove
    (implies (and (subsetp m l)
		  (not (member x m)))
	     (subsetp m (remove1 x l))))

(defthm len-subsetp-positives
    (implies (and (natp n)
		  (subsetp (positives n) l))
	     (>= (len l) n))
  :rule-classes ()
  :hints (("Goal" :induct (ldpu-induction l n))))

(defthm pigeonhole-principle-2
    (implies (and (natp n)
		  (distinct-positives l n)
		  (subsetp (positives n) l))
	     (perm (positives n) l))
  :rule-classes ()
  :hints (("Goal" :use (pigeonhole-principle
			len-subsetp-positives
			len-distinct-positives-upper))))

(defthm perm-associates-positives
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (perm (positives (1- p))
		   (associates (1- p) m p)))
  :rule-classes ()
  :hints (("Goal" :use (distinct-positives-associates
			(:instance pigeonhole-principle-2
				   (n (1- p))
				   (l (associates (1- p) m p)))))))

;; It follows that the product of associates(p-1,m,p) is (p-1)! and its
;; length is p-1.

(defthm times-list-associates-fact
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (times-list (associates (1- p) m p))
		    (fact (1- p))))
  :rule-classes ()
  :hints (("Goal" :use (perm-associates-positives
			(:instance perm-times-list
				   (l2 (associates (1- p) m p))
				   (l1 (positives (1- p))))))))

(defthm perm-len
    (implies (perm l1 l2)
	     (= (len l1) (len l2)))
  :rule-classes ())

(defthm len-positives
    (equal (len (positives n))
	   (nfix n)))

(defthm len-associates
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (len (associates (+ -1 p) m p))
		    (1- p)))
  :hints (("Goal" :use (perm-associates-positives
			(:instance perm-len
				   (l2 (associates (1- p) m p))
				   (l1 (positives (1- p))))))))

(defthm len-associates-even
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (integerp n)
		  (< n p))
	     (integerp (* 1/2 (len (associates n m p)))))
  :rule-classes (:type-prescription)
  :hints (("Subgoal *1/1" :use (res-root1
				res-root2
				roots-distinct))))

;; On the other hand, we can compute the product of associates(p-1,a,p) as
;; follows.

(defthm times-list-associates-lemma-1
    (implies (and (integerp tl)
		  (integerp s)
		  (integerp m)
		  (integerp b)
		  (natp l)
		  (not (zp n))
		  (= (mod tl n) (mod (* s (expt m l)) n))
		  (= (mod b n) (mod m n)))
	     (= (mod (* tl b) n) (mod (* s (expt m (1+ l))) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-mod-times (a tl))
			(:instance mod-mod-times (a (* s (expt m l))))
			(:instance mod-mod-times (a b) (b (* s (expt m l))))
			(:instance mod-mod-times (a m) (b (* s (expt m l))))))))

(defthm times-list-associates-lemma-2
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (not (zp n))
		  (< n p)
		  (not (member n (associates (1- n) m p)))
		  (equal (mod (times-list (associates (+ -1 n) m p)) p)
			 (mod (- (expt m (/ (len (associates (1- n) m p)) 2))) p)))
             (equal (mod (* n (associate n m p) (times-list (associates (+ -1 n) m p))) p)
		    (mod (- (expt m (/ (len (associates n m p)) 2))) p)))
  :hints (("Goal" :use ((:instance times-list-associates-lemma-1
				   (tl (times-list (associates (+ -1 n) m p)))
				   (s -1)
				   (b (* n (associate n m p)))
				   (l (/ (len (associates (1- n) m p)) 2))
				   (n p))
			(:instance associate-property (j n))
			(:instance associate-bnds (j n))))))

(defthm times-list-associates-lemma-3
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (not (zp n))
		  (< n p)
		  (not (member n (associates (1- n) m p)))
		  (equal (mod (times-list (associates (+ -1 n) m p)) p)
			 (mod (expt m (/ (len (associates (1- n) m p)) 2)) p)))
             (equal (mod (* n (associate n m p) (times-list (associates (+ -1 n) m p))) p)
		    (mod (expt m (/ (len (associates n m p)) 2)) p)))
  :hints (("Goal" :use ((:instance times-list-associates-lemma-1
				   (tl (times-list (associates (+ -1 n) m p)))
				   (s 1)
				   (b (* n (associate n m p)))
				   (l (/ (len (associates (1- n) m p)) 2))
				   (n p))
			(:instance associate-property (j n))
			(:instance associate-bnds (j n))))))

(defthm first-power
    (implies (integerp m)
	     (equal (expt m 1) m))
  :hints (("Goal" :expand ((expt m 1)))))

(local-defthmd hack-1
  (implies (and (integerp m) (natp n))
           (equal (expt m (+ 1 n))
                  (* m (expt m n)))))

(local-defthm hack-2
  (implies (and (integerp m) (natp n) (rationalp p))
           (equal (* p (expt m (+ 1 n)))
                  (* m p (expt m n))))
  :rule-classes ()
  :hints (("Goal" :use (hack-1) :in-theory (disable ACL2::|(* x (expt x n))|))))

(local-defthm hack-3
  (implies (and (integerp m) (natp n) (rationalp p) (integerp (* p (expt m n))))
           (integerp (* p (expt m (+ 1 n)))))
  :hints (("Goal" :use (hack-2))))

(defthm times-list-associates
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (< n p))
	     (equal (mod (times-list (associates n m p)) p)
		    (if (residue m p)
			(mod (- (expt m (/ (len (associates n m p)) 2))) p)
		      (mod (expt m (/ (len (associates n m p)) 2)) p))))
  :rule-classes ()
  :hints (("Subgoal *1/1" :use (res-root1 res-root2))))

;; Both Wilson's Theorem and Euler's Criterion now follow easily.

(defthm euler-lemma
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (mod (fact (1- p)) p)
		    (if (residue m p)
			(mod (- (expt m (/ (1- p) 2))) p)
		      (mod (expt m (/ (1- p) 2)) p))))
  :rule-classes ()
  :hints (("Goal" :use (times-list-associates-fact
			(:instance times-list-associates (n (1- p)))))))

(defthm find-root-1
    (implies (not (zp n))
	     (find-root n 1 p)))

(defthm residue-1
    (implies (primep p)
	     (residue 1 p))
  :hints (("Goal" :in-theory (enable residue))))

(defthm power-of-1
    (equal (expt 1 x) 1))

(defthm mod-minus-1
    (implies (not (zp n))
	     (equal (mod -1 n) (- n 1)))
  :hints (("Goal" :use ((:instance mod-mult (m -1) (a 1))))))

(defthm wilson
  (implies (primep p)
	   (equal (mod (fact (1- p)) p)
		  (1- p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance euler-lemma (m 1))
			(:instance divides-leq (x p) (y 1))))))

(defthm p-1-even
    (implies (and (primep p)
		  (not (= p 2)))
	     (integerp (+ -1/2 (* 1/2 p))))
  :hints (("Goal" :use ((:instance primep-no-divisor (d 2))
			(:instance divides-mod-0 (a p) (n 2))
			(:instance mod012 (m p))
			(:instance mod-equal-int (a p) (b 1) (n 2))))))

(defthm euler-criterion
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (mod (expt m (/ (1- p) 2)) p)
		    (if (residue m p)
			1
		      (1- p))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable p-1-even)
		  :use (euler-lemma
			p-1-even
			wilson
			(:instance mod-times-mod
				   (a (- (expt m (/ (1- p) 2)))) (b -1) (c -1) (n p))))))

;;  The "First Supplement" is the case a = 1:

(defthm evenp-oddp
    (implies (integerp m)
	     (iff (evenp m)
		  (oddp (1+ m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod012 (m (1+ m)))
			(:instance mod-equal-int (a (1+ m)) (b 0) (n 2))
			(:instance mod-equal-int (a (1+ m)) (b 1) (n 2))))))

(defthm expt-minus-1
    (implies (natp n)
	     (equal (expt -1 n)
		    (if (evenp n)
			1
		      -1)))
  :hints (("Goal" :induct (positives n))
	  ("Subgoal *1/2" :use ((:instance evenp-oddp (m (1- n)))))))

(defthm first-supplement
    (implies (and (primep p)
		  (not (= p 2)))
	     (iff (residue -1 p)
		  (= (mod p 4) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-minus-1 (n (/ (1- p) 2)))
			(:instance euler-criterion (m -1))
			(:instance divides-leq (x p) (y 1))
			(:instance divides-minus (x p) (y -1))
			(:instance mod-equal-int (a p) (b 1) (n 4))
			(:instance mod-equal-int-reverse (a p) (b 1) (n 4))))))
