(in-package "RTL")

(local (include-book "arithmetic-5/top" :dir :system)) ;; It's hard to do any arithmetic without something like this

;; In this book, we establish a method of certifying primes due to Vaughn Pratt,
;; based on the following theorem of Lucas:

;; Given 0 < r < p, if r^(p-1) mod p = 1 and for each prime factor q of p-1,
;; r^((p-1)/q) mod p <> 1, then p is prime.

;; A certificate for p is a tree.  The root contains a primitive root of p and a 
;; prime factorization of p-1, with subnodes corresponding to the distinct prime 
;; factors of p-1.  If a prime factor q is small enough to be certified by direct
;; computation, then its node is a leaf; otherwise it is a certificate for q.

;; To certify p is to establish the hypotheses of Lucas's theorem and to certify
;; each of its prime factors recursively.

;; Note that the source of a certificate need not be trusted, since its validity 
;; is established through the certification process.

;; Since we are interested in efficient computation, we include the following:

(include-book "mersenne")

;; If r is relatively prime to p, then the order of r mod p is the least k
;; such that r^k mod p = 1:

(defun find-order (r k p)
  (declare (xargs :measure (nfix (- p k))))
  (if (or (zp k) (zp p) (>= k p))
      ()
    (if (= (mod-expt r k p) 1)
        k
      (find-order r (1+ k) p))))

(defun order (r p)
  (find-order r 1 p))

(local-defthmd rootp-find-order
  (implies (and (not (zp p)) 
                (not (zp j))
                (<= j p)
                (not (zp k))
                (<= j k)
                (< k p)
                (= (mod-expt r k p) 1))
           (find-order r j p))
  :hints (("Goal" :induct (find-order r j p))))

(local-defthmd rootp-order
  (implies (and (not (zp p)) 
                (not (zp k))
                (< k p)
                (= (mod-expt r k p) 1))
           (order r p))
  :hints (("Goal" :in-theory (enable order) :use ((:instance rootp-find-order (j 1))))))

(local-defthmd find-order-1
  (implies (and (not (zp p)) 
                (not (zp j))
                (<= j p)
                (find-order r j p))
           (equal (mod (expt r (find-order r j p)) p) 1))
  :hints (("Goal" :induct (find-order r j p))))

(defthmd order-1
  (implies (and (not (zp p)) 
                (order r p))
           (equal (mod-expt r (order r p) p) 1))
  :hints (("Goal" :in-theory (enable order) :use ((:instance find-order-1 (j 1))))))

(local-defthmd find-order-bounds
  (implies (and (not (zp p)) 
                (not (zp j))
                (find-order r j p))
           (and (not (zp (find-order r j p)))
                (< (find-order r j p) p)))
  :hints (("Goal" :induct (find-order r j p))))

(defthmd order-bounds
  (implies (and (not (zp p))
                (order r p))
           (and (not (zp (order r p)))
                (< (order r p) p)))
  :hints (("Goal" :use ((:instance find-order-bounds (j 1))))))

(local-defthmd find-order-minimal
  (implies (and (not (zp p)) 
                (not (zp k))
                (< k p)
                (not (zp i))
                (<= i k)
                (= (mod-expt r k p) 1)
                (not (zp j))
                (<= i j)
                (< j (find-order r i p)))
           (not (equal (mod-expt r j p) 1)))
  :hints (("Goal" :induct (find-order r i p))))

(defthmd order-minimal
  (implies (and (not (zp p))
                (order r p)
                (not (zp j))
                (< j (order r p)))
           (not (equal (mod-expt r j p) 1)))
  :hints (("Goal" :use (order-bounds order-1 (:instance find-order-minimal (k (order r p)) (i 1))))))

(defun mod-power-induct (j r s)
  (if (zp j)
      j
    (* j r s (mod-power-induct (1- j) r (* s r)))))

(local-defthmd mod-power-1
  (implies (and (not (zp p))
                (integerp r)
                (integerp s)
                (natp j))
           (equal (mod (* (expt (mod r p) j) s) p)
                  (mod (* (expt r j) s) p)))
  :hints (("Goal" :induct (mod-power-induct j r s))
          ("Subgoal *1/2" :use ((:instance mod-mod-times (n p) (a r) (b (* (expt (mod r p) (1- j)) s)))))))

;; We shall show that if k is the (non-nil) order of r mod p, then for any natural m,
;; r^m mod p = 1 iff k divides m:

(defthmd mod-power
  (implies (and (natp p)
                (> p 1)
                (natp r)
                (natp i)
                (natp j))
           (equal (mod (expt (mod (expt r i) p) j) p)
                  (mod (expt r (* i j)) p)))
  :hints (("Goal" :use ((:instance mod-power-1 (r (expt r i)) (s 1))))))

(local-defthmd order-divides-1
  (implies (and (not (zp p))
                (> p 1)
                (natp r)
                (order r p)
                (natp m)
                (divides (order r p) m))
           (equal (mod (expt r m) p) 1))
  :hints (("Goal" :in-theory (enable divides)
                  :use (order-1 order-bounds (:instance mod-power (i (order r p)) (j (/ m (order r p))))))))

(local-defthmd order-divides-2
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (natp m))
           (equal (mod (expt r m) p)
                  (mod (expt r (mod m (order r p))) p)))
  :hints (("Goal" :in-theory (enable divides)
                  :use (order-1 order-bounds 
                        (:instance order-divides-1 (m (* (order r p) (fl (/ m (order r p))))))
                        (:instance mod-def (x m) (y (order r p)))
                        (:instance mod-mod-times (n p) (a (expt r (* (order r p) (fl (/ m (order r p)))))) (b (expt r (mod m (order r p)))))))))

(local-defthmd order-divides-3
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (natp m)
                (= (mod-expt r m p) 1))
          (divides (order r p) m))           
  :hints (("Goal" :in-theory (enable divides)
                  :use (order-bounds order-divides-2
                        (:instance order-minimal (j (mod m (order r p))))
                        (:instance mod-0-int (n (order r p)))))))

(defthmd order-divides
  (implies (and (natp p)
                (> p 1)
                (natp r)
                (order r p)
                (natp m))
           (iff (equal (mod-expt r m p) 1)
                (divides (order r p) m)))
  :hints (("Goal" :use (order-divides-1 order-divides-3))))

;; The maximum order mod p is p-1:

(defun max-order-p (r p) 
  (and (not (zp r))
            (< r p)
            (= (order r p) (1- p))))

;; If r has order p-1, then (r mod p, r^2 mod p, ..., r^(p-1) mod p)
;; is a sequence of distinct integers between 1 and p-1, and therefore,
;; by the pigeonhole principle, a permutation of (1, 2, ..., p-1): 

(defun mod-powers (r p n)
  (if (zp n)
      ()
    (cons (mod (expt r n) p)
          (mod-powers r p (1- n)))))

(local-defthmd powers-distinct-1
  (implies (and (not (zp p))
                (> p 1)
                (natp r)
                (order r p)
                (natp i)
                (natp j)
                (< i (order r p))
                (< j (order r p))
                (> i j)
                (= (mod (expt r i) p) (mod (expt r j) p)))
           (equal (mod (expt r (- i j)) p)
                  (mod (expt r (+ i (* (1- (order r p)) j))) p)))
  :hints (("Goal" :in-theory (enable divides)
                  :cases ((= r 0))
                  :use (order-bounds
                        (:instance order-divides (m (* (order r p) j)))
                        (:instance mod-mod-times (n p) (a (expt r (* (order r p) j))) (b (expt r (- i j))))))))

(in-theory (disable order))

(local-defthmd powers-distinct-2
  (implies (and (not (zp p))
                (> p 1)
                (natp r)
                (order r p)
                (natp j)
                (< j (order r p)))
           (integerp (expt r (* (1- (order r p)) j))))
  :hints (("Goal" :use (order-bounds))))

(local-defthmd powers-distinct-3
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (not (zp i))
                (not (zp j))
                (< i (order r p))
                (< j (order r p))
                (> i j)
                (= (mod (expt r i) p) (mod (expt r j) p)))
           (equal (mod (expt r (+ i (* (1- (order r p)) j))) p)
                  (mod (* (mod (expt r j) p) (expt r (* (1- (order r p)) j))) p)))
  :hints (("Goal" :use (order-bounds powers-distinct-2
                        (:instance mod-mod-times (n p) (a (expt r i)) (b (expt r (* (1- (order r p)) j))))))))

(local-defthmd powers-distinct-4
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (not (zp i))
                (not (zp j))
                (< i (order r p))
                (< j (order r p))
                (> i j)
                (= (mod (expt r i) p) (mod (expt r j) p)))
           (equal (mod (* (mod (expt r j) p) (expt r (* (1- (order r p)) j))) p)
                  1))
  :hints (("Goal" :in-theory (enable divides)
                  :use (order-bounds powers-distinct-2
                        (:instance order-divides (m (* (order r p) j)))
                        (:instance mod-mod-times (n p) (a (expt r j)) (b (expt r (* (1- (order r p)) j))))))))

(local-defthmd powers-distinct-5
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (not (zp i))
                (not (zp j))
                (< i (order r p))
                (< j (order r p))
                (> i j)
                (= (mod (expt r i) p) (mod (expt r j) p)))
           (equal (mod (expt r (- i j)) p)
                  1))
  :hints (("Goal" :use (powers-distinct-1 powers-distinct-2 powers-distinct-3 powers-distinct-4))))

(local-defthmd powers-distinct-6
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (not (zp i))
                (not (zp j))
                (< i (order r p))
                (< j (order r p))
                (> i j)
                (= (mod (expt r i) p) (mod (expt r j) p)))
           (not (divides (order r p) (- i j))))
  :hints (("Goal" :use ((:instance divides-leq (x (order r p)) (y (- i j)))))))

(local-defthmd powers-distinct-7
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (not (zp i))
                (not (zp j))
                (< i (order r p))
                (< j (order r p))
                (> i j))
           (not (= (mod (expt r i) p) (mod (expt r j) p))))
  :hints (("Goal" :use (powers-distinct-5 powers-distinct-6 (:instance order-divides (m (- i j)))))))

(local-defthmd powers-distinct-8
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (not (zp i))
                (not (zp j))
                (<= i (order r p))
                (< j (order r p))
                (> i j))
           (not (= (mod (expt r i) p) (mod (expt r j) p))))
  :hints (("Goal" :use (powers-distinct-7 order-minimal order-1)))) 

(local-defthmd powers-distinct-9
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (not (zp i))
                (not (zp j))
                (<= i (order r p))
                (<= j (order r p))
                (not (= i j)))
           (not (= (mod (expt r i) p) (mod (expt r j) p))))
  :hints (("Goal" :use (powers-distinct-8 (:instance powers-distinct-8 (i j) (j i))))))

(local-defthmd powers-distinct-10
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (= (order r p) (1- p))
                (not (zp m))
                (not (zp n))
                (< n m)
                (< m p))
           (not (member-equal (mod (expt r m) p) (mod-powers r p n))))
  :hints (("Goal" :induct (mod-powers r p n))
          ("Subgoal *1/" :use ((:instance powers-distinct-9 (i n) (j m))))))

(local-defthmd powers-distinct-11
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (order r p)
                (not (zp m)))
           (not (= (mod (expt r m) p) 0)))
  :hints (("Goal" :in-theory (enable divides)
                  :use (order-bounds 
                        (:instance order-divides (m (* (order r p) m)))
                        (:instance mod-power (i m) (j (order r p)))))))

(defthmd powers-distinct
  (implies (and (natp p)
                (> p 1)
                (max-order-p r p)
                (natp m)
                (< m p))
           (distinct-positives (mod-powers r p m) (1- p)))
  :hints (("Goal" :induct (mod-powers r p m))
          ("Subgoal *1/2" :use (powers-distinct-11 (:instance powers-distinct-10 (n (1- m)))))))

(defthm len-mod-powers
  (implies (natp n)
           (equal (len (mod-powers r p n))
                  n)))

(defthmd perm-powers
  (implies (and (natp p)
                (> p 1)
                (max-order-p r p))
           (perm (positives (1- p))
                 (mod-powers r p (1- p))))                 
  :hints (("Goal" :use ((:instance powers-distinct (m (1- p)))
                        (:instance pigeonhole-principle (l (mod-powers r p (1- p))))))))

;; If q divides p, then q divides q^k mod p:

(defthmd divides-mod-prod
  (implies (and (integerp p)
                (integerp a)
                (integerp b)
                (not (zp q))
                (divides q p)
                (divides q a))
           (divides q (mod (* a b) p)))
  :hints (("Goal" :use ((:instance mod-def (x (* a b)) (y p))
                        (:instance divides-product (x q) (y a) (z b))
                        (:instance divides-product (x q) (y p) (z (- (fl (/ (* a b) p)))))
                        (:instance divides-sum (x q) (y (* a b)) (z (- (* p (fl (/ (* a b) p))))))))))

(defthmd divides-mod-power
  (implies (and (not (zp p))
                (not (zp q))
                (not (zp k))
                (divides q p))
           (divides q (mod (expt q k) p)))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :cases ((= q p))
                          :use ((:instance divides-leq (x q) (y p))
                                (:instance mod-def (x p) (y p))))
          ("Subgoal *1/1" :use ((:instance divides-mod-prod (a (mod (expt q (1- k)) p)) (b q))
                                (:instance mod-mod-times (a (expt q (1- k))) (b q) (n p))))))

;; It follows that if q divides p and r has order p-1 mod p, 
;; then since q = r^j mod p, q must divide
;;    (r^j mod p)^p-1 mod p = (r^p-1 mod p)^j mod p = 1,
;; and therefore q = 1:

(local-defthmd must-be-1-1
  (implies (and (natp p)
                (> p 1)
                (not (zp r))
                (< r p)
                (order r p)
                (not (zp m))
                (divides (mod (expt r m) p) p))
           (divides (mod (expt r m) p)
                    (mod (expt r (* m (order r p))) p)))
  :hints (("Goal" :use (order-bounds powers-distinct-11
                        (:instance divides-mod-power (k (order r p)) (q (mod (expt r m) p)))
                        (:instance mod-power (i m) (j (order r p)))))))

(local-defthmd must-be-1-2
  (implies (and (natp p)
                (> p 1)
                (not (zp r))
                (< r p)
                (order r p)
                (not (zp m))
                (divides (mod (expt r m) p) p))
           (equal (mod-expt r m p) 1))
  :hints (("Goal" :in-theory (enable divides)
                  :use (must-be-1-1 order-bounds
                        (:instance divides-leq (x (mod (expt r m) p)) (y 1))
                        (:instance order-divides (m (* m (order r p))))))))

(defun loc (x l)
  (if (consp l)
      (if (equal x (car l))
          0
        (1+ (loc x (cdr l))))
    ()))

(local-defthm member-mod-powers
  (implies (and (natp n)
                (not (zp p))
                (not (zp r))
                (member-equal x (mod-powers r p n)))
           (equal x (mod (expt r (- n (loc x (mod-powers r p n)))) p)))
  :rule-classes ()
  :hints (("Goal" :induct (mod-powers r p n))))

(defthm loc-bounds
  (implies (member x l)
           (and (natp (loc x l))
                (< (loc x l) (len l))))
  :rule-classes ())
                                
(defthm mod-power-must-be-1
  (implies (and (not (zp p))
                (> p 1)
                (not (zp r))
                (< r p)
                (order r p)
                (member x (mod-powers r p (1- p)))
                (divides x p))
           (equal x 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance must-be-1-2 (m (- (1- p) (loc x (mod-powers r p (1- p))))))
                        (:instance member-mod-powers (n (1- p)))
                        (:instance loc-bounds (l (mod-powers r p (1- p))))))))

(defthm divisor-must-be-1
  (implies (and (natp p)
                (> p 1)
                (max-order-p r p)
                (not (zp x))
                (< x p)
                (divides x p))
           (equal x 1))
  :rule-classes ()
  :hints (("Goal" :use (mod-power-must-be-1 perm-powers (:instance perm-member (a (positives (1- p))) (b (mod-powers r p (1- p))))))))

(defthm max-order-p-prime
  (implies (and (not (zp p))
                (> p 1)
                (max-order-p r p))
           (primep p))
  :rule-classes ()
  :hints (("Goal" :use (order-1
                        (:instance divisor-must-be-1 (x (least-divisor 2 p)))
                        (:instance least-divisor-divides (k 2) (n p))))))

;; Thus, to establish that p is prime, it suffices to show that some r has order p-1.
;; We need a way to do this quickly.  We shall define a function fast-mod-expt that 
;; computes b^e mod n with execution time that is logarithmic in e.  This will allow us
;; to compute r^(p-1) quickly, but we clearly cannot compute r^e for all e < p-1. 
;; We need another trick.

;; A factorization of n consists of two lists,
;;   f = (f1 f2 ... fk), where fi > 1
;;   e = (e1 e2 ... ek), where ei > 0
;; such that n = f1^e1 * f2*e2 * ... * fk*ek.

(defun prod-powers (f e)
  (if (consp f)
      (* (expt (car f) (car e))
         (prod-powers (cdr f) (cdr e)))
    1))

(defun distinct-factors (f)
  (if (consp f)
      (and (natp (car f))
           (> (car f) 1)
           (not (member (car f) (cdr f)))
           (distinct-factors (cdr f)))
    t))

(defun all-positive (e)
  (if (consp e)
      (and (not (zp (car e)))
           (all-positive (cdr e)))
    t))

(defun factorization (n f e)
  (and (distinct-factors f)
       (all-positive e)
       (= (len f) (len e))
       (= n (prod-powers f e))))

(defthm factor-divides-1
  (implies (and (not (zp f)) (not (zp e)))
           (divides f (expt f e)))
  :hints (("Goal" :induct (fact e))
          ("Subgoal *1/1" :use ((:instance divides-product (x f) (y (expt f (1- e))) (z f))))))

(defthm factor-divides-2
  (implies (and (distinct-factors f)
                (or (zp x) (<= x 1)))
           (not (member x f))))

(defthm integerp-prod-powers
  (implies (and (distinct-factors f)
                (all-positive e))
           (integerp (prod-powers f e)))
  :rule-classes (:type-prescription :rewrite))

(defthm positive-prod-powers
  (implies (and (distinct-factors f)
                (all-positive e))
           (> (prod-powers f e) 0))
  :rule-classes ())

(defthm factor-divides-3
  (implies (and (distinct-factors f)
                (all-positive e)
                (= (len f) (len e))
                (member q f))
           (divides q (prod-powers f e)))
  :hints (("Subgoal *1/5" :use ((:instance divides-product (x q) (z (expt (car f) (car e))) (y (prod-powers (cdr f) (cdr e))))))
          ("Subgoal *1/4" :use ((:instance divides-product (x (car f)) (y (expt (car f) (car e))) (z (prod-powers (cdr f) (cdr e))))))))          

(defthm factor-divides
  (implies (and (factorization n f e)
                (member q f))
           (divides q n)))

;; We are particularly interested in prime factorizations:

(defun all-prime (f)
  (if (consp f)
      (and (primep (car f))
           (all-prime (cdr f)))
    t))

(defun prime-factorization (n f e)
  (and (factorization n f e)
       (all-prime f)))

;; We apply Euclid's Theorem: If a prime divides a product, then it 
;; divides one of the factors:

(local-defthm all-prime-factors-1
  (implies (and (primep p)
                (primep q)
                (natp k)
                (divides p (expt q k)))
           (= p q))
  :rule-classes ()
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/1" :use ((:instance divides-leq (x p) (y 1))))
          ("Subgoal *1/2" :use ((:instance primep-no-divisor (d p) (p q))
                                (:instance euclid (a q) (b (expt q (1- k))))))))

(local-defthmd all-prime-factors-2
  (implies (and (distinct-factors f)
                (all-prime f)
                (all-positive e)
                (= (len f) (len e))
                (primep p)
                (divides p (prod-powers f e)))
           (member p f))
  :hints (("Subgoal *1/3" :use ((:instance euclid (a (expt (car f) (car e))) (b (prod-powers (cdr f) (cdr e))))
                                (:instance all-prime-factors-1 (q (car f)) (k (car e)))))
          ("Subgoal *1/1" :use ((:instance divides-leq (x p) (y 1))))))

(defthmd all-prime-factors
  (implies (and (prime-factorization n f e)
                (primep q)
                (divides q n))
           (member q f))
  :hints (("Goal" :use ((:instance all-prime-factors-2 (p q))))))
             
;; If r^p-1 mod p = 1 but r is not of order p-1, then the order of r
;; must divide (p-1)/q for some prime factor q of p-1.  This observation
;; leads to Lucas's Theorem, which is the basis of Pratt certification:
             
(defund prime-witness (a n)
  (least-divisor 2 (/ n a)))

(local-defthmd divides-factor-1
  (implies (and (not (zp a))
                (< a n)
                (divides a n))
           (and (primep (prime-witness a n))
                (divides a (/ n (prime-witness a n)))
                (divides (prime-witness a n) (/ n a))))
  :hints (("Goal" :in-theory (enable prime-witness divides)
                  :use ((:instance least-divisor-divides (k 2) (n (/ n a)))
                        (:instance primep-least-divisor (n (/ n a)))))))

(local-defthmd divides-factor-2
  (implies (and (not (zp a))
                (< a n)
                (divides a n))
           (and (divides (prime-witness a n) n)
                (integerp (/ n (prime-witness a n)))))
  :hints (("Goal" :in-theory (enable divides)
                  :use (divides-factor-1 (:instance divides-product (x (prime-witness a n)) (y (/ n a)) (z a)))))) 

(local-defthmd divides-factor-3
  (implies (and (prime-factorization n f e)
                (not (zp a))
                (< a n)
                (divides a n))
           (and (integerp (/ n (prime-witness a n)))
                (divides a (/ n (prime-witness a n)))
                (member (prime-witness a n) f)))
  :hints (("Goal" :use (divides-factor-1 divides-factor-2
                        (:instance all-prime-factors (q (prime-witness a n)))))))

(local-defthm divides-factor-4
  (implies (and (not (zp a))
                (not (zp n))
                (divides a n)
                (not (= a n)))
           (< a n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance divides-leq (x a) (y n))))))

(defthmd divides-factor
  (implies (and (prime-factorization n f e)
                (not (zp a))
                (not (= a n))
                (divides a n))
           (and (integerp (/ n (prime-witness a n)))
                (divides a (/ n (prime-witness a n)))
                (member (prime-witness a n) f)))
  :hints (("Goal" :use (positive-prod-powers divides-factor-3 divides-factor-4))))

(defun max-order-by-factorization (r p f)
  (if (consp f)
      (and (not (= (mod-expt r (/ (1- p) (car f)) p) 1))
           (max-order-by-factorization r p (cdr f)))
    t))

(local-defthm max-order-by-factorization-rootp
  (implies (and (member q f)
                (max-order-by-factorization r p f))
           (not (= (mod-expt r (/ (1- p) q) p) 1)))
  :rule-classes ())

(defthmd max-order-by-factorization-max-order-p
  (implies (and (natp p)
                (> p 1)
                (not (zp r))
                (< r p)
                (= (mod-expt r (1- p) p) 1)
                (prime-factorization (1- p) f e)
                (max-order-by-factorization r p f))
           (max-order-p r p))
  :hints (("Goal" :use (order-bounds
                        (:instance rootp-order (k (1- p)))
                        (:instance max-order-by-factorization-rootp (q (prime-witness (order r p) (1- p))))
                        (:instance order-divides (m (/ (1- p) (prime-witness (order r p) (1- p)))))
                        (:instance order-divides (m (1- p)))
                        (:instance divides-factor (n (1- p)) (a (order r p)))))))

(defthmd lucas
  (implies (and (natp p)
                (> p 1)
                (prime-factorization (1- p) f e)                
                (not (zp r))
                (< r p)
                (= (mod-expt r (1- p) p) 1)
                (max-order-by-factorization r p f))
           (primep p))
  :hints (("Goal" :use (max-order-p-prime max-order-by-factorization-max-order-p))))

;; Thus, given a prime factorization of p-1 with k distinct prime factors and a candidate
;; primitive root r, we may establish primality of p by computing k+1 powers of r.

;; We define fast-mod-expt, which computes b^e mod n by binary exponentiation using 
;; the tail-recursive auxiliary function fast-mod-expt-mul, which computes (b^e * r) mod n.

(defun fast-mod-expt-mul (b e n r)
  (if (zp e)
      r
    (if (zp (mod e 2))
        (fast-mod-expt-mul (mod (* b b) n) (fl (/ e 2)) n r)
      (fast-mod-expt-mul (mod (* b b) n) (fl (/ e 2)) n (mod (* r b) n)))))

(defun fast-mod-expt (b e n) (fast-mod-expt-mul b e n 1))

(local-defthmd emm-1
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (expt (mod (* b b) n) q) r) n)
                  (mod (* (mod (expt (mod (* b b) n) q) n) r) n)))
  :hints (("Goal" :use ((:instance mod-mod-times (a (expt (mod (* b b) n) q)) (b r))))))

(local-defthmd emm-2
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (mod (expt (mod (* b b) n) q) n) r) n)
                  (mod (* (mod (expt b (* 2 q)) n) r) n)))
  :hints (("Goal" :use ((:instance mod-power (p n) (r b) (i 2) (j q))))))

(local-defthmd emm-3
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (mod (expt b (* 2 q)) n) r) n)
                  (mod (* (expt b (* 2 q)) r) n)))
  :hints (("Goal" :use ((:instance mod-mod-times (a (expt b (* 2 q))) (b r))))))

(local-defthmd emm-4
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (expt (mod (* b b) n) q) r) n)
                  (mod (* (expt b (* 2 q)) r) n)))
  :hints (("Goal" :use (emm-1 emm-2 emm-3))))

(local-defthmd emm-5
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (expt (mod (* b b) n) q) (mod (* r b) n)) n)
                  (mod (* (expt (mod (* b b) n) q) r b) n)))
  :hints (("Goal" :use ((:instance mod-mod-times (a (* r b)) (b (expt (mod (* b b) n) q)))))))

(local-defthmd emm-6
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (expt (mod (* b b) n) q) r b) n)
                  (mod (* (mod (expt (mod (* b b) n) q) n) r b) n)))
  :hints (("Goal" :use ((:instance mod-mod-times (a (expt (mod (* b b) n) q)) (b (* r b)))))))

(local-defthmd emm-7
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (mod (expt (mod (* b b) n) q) n) r b) n)
                  (mod (* (mod (expt b (* 2 q)) n) r b) n)))
  :hints (("Goal" :use ((:instance mod-power (p n) (r b) (i 2) (j q))))))

(local-defthmd emm-8
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (mod (expt b (* 2 q)) n) r b) n)
                  (mod (* (expt b (* 2 q)) r b) n)))
  :hints (("Goal" :use ((:instance mod-mod-times (a (expt b (* 2 q))) (b (* r b)))))))

(local-defthmd emm-9
  (implies (and (natp n)
                (> n 1)
                (natp b)
                (natp r)
                (natp q))
           (equal (mod (* (expt (mod (* b b) n) q) (mod (* r b) n)) n)
                  (mod (* (expt b (1+ (* 2 q))) r) n)))
  :hints (("Goal" :use (emm-5 emm-6 emm-7 emm-8))))

(defthm fast-mod-expt-mul-rewrite
  (implies (and (natp b)
                (natp e)
                (not (zp n))
                (> n 1)
                (natp r)
                (< r n))
           (equal (fast-mod-expt-mul b e n r)
                  (mod (* (expt b e) r) n)))
  :hints (("Goal" :induct (fast-mod-expt-mul b e n r))
          ("Subgoal *1/3" :expand ((fast-mod-expt-mul b e n r))
                          :use (fast-mod-expt-mul 
                                (:instance emm-9 (q (fl (/ e 2))))
                                (:instance mod012 (m e))
                                (:instance mod-def (x e) (y 2))))
          ("Subgoal *1/2" :expand ((fast-mod-expt-mul b e n r))
                          :use (fast-mod-expt-mul 
                                (:instance emm-4 (q (fl (/ e 2))))
                                (:instance mod012 (m e))
                                (:instance mod-def (x e) (y 2))))))

(defthm fast-mod-expt-rewrite
  (implies (and (natp b)
                (natp e)
                (not (zp n))
                (> n 1))
           (equal (fast-mod-expt b e n)
                  (mod (expt b e) n)))
  :hints (("Goal" :use ((:instance fast-mod-expt-mul-rewrite (r 2))))))

(in-theory (disable fast-mod-expt))

;; We also have a fast version of max-order-by-factorization:

(defund fast-max-fact (r p f)
  (if (consp f)
      (and (not (= (fast-mod-expt r (/ (1- p) (car f)) p) 1))
           (fast-max-fact r p (cdr f)))
    t))

(local-defthm fpfr-1
  (implies (and (not (zp n))
                (factorization n f e)
                (member q f))
           (integerp (/ n q)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (divides) (factor-divides factor-divides-3)) :use (factor-divides))))

(local-defthm fpfr-2
  (implies (and (distinct-factors f)
                (member q f))
           (> q 1))
  :rule-classes ())

(local-defthm fpfr-3
  (implies (and (not (zp n))
                (factorization n f e)
                (member q f))
           (natp (/ n q)))
  :rule-classes ()
  :hints (("Goal" :use (fpfr-1 fpfr-2))))

(local-defthm fpfr-4
  (implies (and (not (zp p))
                (> p 1)
                (factorization (1- p) f e)
                (member q f))
           (natp (/ (1- p) q)))
  :rule-classes ()
  :hints (("Goal" :use (:instance fpfr-3 (n (1- p))))))

(local-defthmd subsetp-member
  (implies (and (subsetp x y)
                (member q x))
           (member q y)))

(local-defthm subsetp-cons
  (implies (subsetp x y)
           (subsetp x (cons q y))))

(local-defthm subsetp-self
  (subsetp x x))

(in-theory (disable factorization))

(local-defthm fpfr-5
  (implies (and (natp r)
                (natp p)
                (> p 1)
                (factorization (1- p) f e)
                (subsetp x f))
           (equal (fast-max-fact r p x)
                  (max-order-by-factorization r p x)))
  :hints (("Goal" :in-theory (enable fast-max-fact))
          ("Subgoal *1/3" :use (:instance fpfr-4 (q (car x))))
          ("Subgoal *1/2" :use (:instance fpfr-4 (q (car x))))))

(defthm fast-max-fact-rewrite
  (implies (and (natp r)
                (natp p)
                (> p 1)
                (factorization (1- p) f e))
           (equal (fast-max-fact r p f)
                  (max-order-by-factorization r p f)))
  :hints (("Goal" :use (;(:instance subset-self (x f))
                        (:instance fpfr-5 (x f))))))

;; In order to apply Lucas's Theorem, we must be able to factor p-1 into primes and
;; find a primitive root of p.  Since the primality of the factors will be proved recursively,
;; we can use an untrusted factorization tool (e.g., www.alpertron.ar/ecm.htm).  It seems
;; that even large primes generally have small primitive roots, so that the following may be 
;; expected to find one quickly:

(defun find-prim-root (p f k)
  (declare (xargs :measure (nfix (- p k))))
  (if (and (not (zp p)) (not (zp k)) (< k p))
      (if (and (= (fast-mod-expt k (1- p) p)1) 
               (fast-max-fact k p f))
          k
        (find-prim-root p f (1+ k)))
    ()))

;; A certificate for a prime p is either (), indicating thet p is small enough to be 
;; certified by direct computation, or a list (r f e c), where
;;   r is a primitive root of p
;;   f is a list of the prime factors of p-1
;;   e is a list of the exponents corresponding to f
;;   c is a list of certificates for the members of f

;; Here is a certificate for a pretty big prime, p = 31757755568855353, where p-1 has only small 
;; prime factors:

;;  (10 (2 3 31 107 223 4153 430751) (3 1 1 1 1 1 1) (() () () () () () ()))

;; A certificate for 2^255 - 19:

(defun certificate-25519 ()
  '(2 (2 3 65147 74058212732561358302231226437062788676166966415465897661863160754340907) (2 1 1 1)
    (() () ()
     (2 (2 3 353 57467 132049 1923133 31757755568855353 75445702479781427272750846543864801) (1 1 1 1 1 1 1 1)
      (() () () () () ()
       (10 (2 3 31 107 223 4153 430751) (3 1 1 1 1 1 1) (() () () () () () ()))
       (7 (2 3 5 75707 72106336199 1919519569386763) (5 2 2 1 1 1)
        (() () () () () (2 (2 3 7 19 47 127 8574133) (1 1 1 1 2 1 1) (() () () () () () ())))))))))

;; A prime certificate is validated by the predicate certify-prime:

(defun certify-primes (listp p c)
  (if listp ;p is a list of primes
      (if (consp c)
          (and (consp p)
               (certify-primes () (car p) (car c))
               (certify-primes t (cdr p) (cdr c)))
        (null p))
    (if (consp c) ;p is a single prime
        (let ((r (car c))
              (f (cadr c))
              (e (caddr c))
              (c (cadddr c)))
          (and (natp p)
               (> p 1)
               (factorization (1- p) f e)
               (not (zp r))
               (< r p)
               (= (fast-mod-expt r (1- p) p) 1)
               (fast-max-fact r p f)
               (certify-primes t f c)))
      (primep p))))

(defun certify-prime (p c) (certify-primes () p c))

;; This is needed to prevent execution of the executable counterpart of primep, which is
;; horribly inefficient:

(in-theory (disable (certify-primes) (certify-prime)))

;; This is proved quite easily:

(defthmd certify-25519
  (certify-prime (- (expt 2 255) 19) (certificate-25519)))

(in-theory (disable primep))

(in-theory (enable prime-factorization))

(defthm certification-lemma
  (implies (certify-primes listp p c)
           (if listp (all-prime p) (primep p)))
  :rule-classes ()
  :hints (("Goal" :induct (certify-primes listp p c))
          ("Subgoal *1/5" :use ((:instance lucas (r (car c)) (f (cadr c)) (e (caddr c)))))))

(defthmd certification-theorem
  (implies (certify-prime p c)
           (primep p))
  :hints (("Goal" :use ((:instance certification-lemma (listp ()))))))

(defthm primep-25519
  (primep (- (expt 2 255) 19))
  :hints (("Goal" :use (certify-25519
                        (:instance certification-theorem (p (- (expt 2 255) 19)) (c (certificate-25519)))))))
