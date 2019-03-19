;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "RTL")

(include-book "euclid")
(include-book "fermat")

(local (include-book "support/pratt"))

;; Also defined in the RTL library.
(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(set-enforce-redundancy t)
(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; This book contains a proof of correctness of Vaughn Pratt's method of prime
;; certification.  For documentation see www.russinoff.com/papers/pratt.pdf.

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

(defthmd order-bounds
  (implies (and (not (zp p))
                (order r p))
           (and (not (zp (order r p)))
                (< (order r p) p))))

(defthmd order-1
  (implies (and (not (zp p))
                (order r p))
           (equal (mod-expt r (order r p) p) 1)))

(defthmd order-minimal
  (implies (and (not (zp p))
                (order r p)
                (not (zp j))
                (< j (order r p)))
           (not (equal (mod-expt r j p) 1))))

;; If k is the (non-nil) order of r mod p, then for any natural m,
;; r^m mod p = 1 iff k divides m:

(defthmd order-divides
  (implies (and (natp p)
                (> p 1)
                (natp r)
                (order r p)
                (natp m))
           (iff (equal (mod-expt r m p) 1)
                (divides (order r p) m))))

;; The maximum order mod p is p-1:

(defun max-order-p (r p)
  (and (not (zp r))
            (< r p)
            (= (order r p) (1- p))))

;; If r as order p-1, then (r mod p, r^2 mod p, ..., r^(p-1) mod p)
;; is a sequence of distinct integers between 1 and p-1, and therefore,
;; by the pigeonhole principle, a permutation of (1, 2, ..., p-1):

(defun mod-powers (r p n)
  (if (zp n)
      ()
    (cons (mod (expt r n) p)
          (mod-powers r p (1- n)))))

(defthmd powers-distinct
  (implies (and (natp p)
                (> p 1)
                (max-order-p r p)
                (natp m)
                (< m p))
           (distinct-positives (mod-powers r p m) (1- p))))

(defthmd perm-powers
  (implies (and (natp p)
                (> p 1)
                (max-order-p r p))
           (perm (positives (1- p))
                 (mod-powers r p (1- p)))))

;; If q divides p, then q divides q^k mod p:

(defthmd divides-mod-power
  (implies (and (not (zp p))
                (not (zp q))
                (not (zp k))
                (divides q p))
           (divides q (mod (expt q k) p))))

;; It follows that if q divides p and r has order p-1 mod p,
;; then since q = r^j mod p, q must divide
;;    (r^j mod p)^p-1 mod p = (r^p-1 mod p) mod p = 1,
;; and therefore q = 1:

(defthm max-order-p-prime
  (implies (and (not (zp p))
                (> p 1)
                (max-order-p r p))
           (primep p))
  :rule-classes ())

;; Thus, to establish that p is prime, it suffices to show that some r has order p-1.
;; We need a way to do this quickly

;; The function fast-mod-expt computes b^e mod n by binary exponentiation, using the
;; tail-recursive auxiliary function fast-mod-expt-mul, which computes (b^e * r) mod n:

(defun fast-mod-expt-mul (b e n r)
  (if (zp e)
      r
    (if (zp (mod e 2))
        (fast-mod-expt-mul (mod (* b b) n) (fl (/ e 2)) n r)
      (fast-mod-expt-mul (mod (* b b) n) (fl (/ e 2)) n (mod (* r b) n)))))

(defun fast-mod-expt (b e n) (fast-mod-expt-mul b e n 1))

(defthm fast-mod-expt-rewrite
  (implies (and (natp b)
                (natp e)
                (not (zp n))
                (> n 1))
           (equal (fast-mod-expt b e n)
                  (mod (expt b e) n))))

;; The execution time of fast-mod-expt is logarithmic in e.  Even so, we
;; can't compute (fast-mod-expt r k p) for k = 1, 2, ..., p-1.
;; We need one more trick.

;; A factorization of n consistes of two lists,
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

;; This follows from Euclid's Theorem, which states that if a prime
;; divides a product, then it divides one of the factors:

(defthmd all-prime-factors
  (implies (and (prime-factorization n f e)
                (primep q)
                (divides q n))
           (member q f)))

;; If r^p-1 mod p = 1 but r is not of order p-1, then the order of r
;; must divide (p-1)/q for some prime factor q of p-1:

(defun max-order-by-factorization (r p f)
  (if (consp f)
      (and (not (= (mod-expt r (/ (1- p) (car f)) p) 1))
           (max-order-by-factorization r p (cdr f)))
    t))

;; Lucas's Theorem is the basis of Pratt certification:

(defthmd lucas
  (implies (and (natp p)
                (> p 1)
                (prime-factorization (1- p) f e)
                (not (zp r))
                (< r p)
                (= (mod-expt r (1- p) p) 1)
                (max-order-by-factorization r p f))
           (primep p)))

;; Fast version of max-order-by-factorization:

(defund fast-max-fact (r p f)
  (if (consp f)
      (and (not (= (fast-mod-expt r (/ (1- p) (car f)) p) 1))
           (fast-max-fact r p (cdr f)))
    t))

(defthm fast-max-fact-rewrite
  (implies (and (natp r)
                (natp p)
                (> p 1)
                (factorization (1- p) f e))
           (equal (fast-max-fact r p f)
                  (max-order-by-factorization r p f))))

;; In order to apply Lucas's Theorem, we must be able to factor p-1 and
;; find a primitive root of p.  Primes generally have small primitive
;; roots, so that the following may be expected to find one quickly:

(defun find-prim-root (p f k)
  (declare (xargs :measure (nfix (- p k))))
  (if (and (not (zp p)) (not (zp k)) (< k p))
      (if (and (= (fast-mod-expt k (1- p) p) 1)
               (fast-max-fact k p f))
          k
        (find-prim-root p f (1+ k)))
    ()))

;; A certificate for a prime p is either (), indicating thet p is small
;; enough to be certified by direct computation, or a list (r f e c), where
;;   r is a primitive root of p
;;   f is a list of the prime factors of p-1
;;   e is a list of the exponents corresponding to f
;;   c is a list of certificates for the members of f

;; Here is a certificate for a pretty big prime, p = 31757755568855353, where p-1 has only small
;; prime factors:

;;  (10 (2 3 31 107 223 4153 430751) (3 1 1 1 1 1 1) (() () () () () () ()))

;; Here is a certificate for 2^255 - 19:

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

(defthm certification-lemma
  (implies (certify-primes listp p c)
           (if listp (all-prime p) (primep p)))
  :rule-classes ())

(defthmd certification-theorem
  (implies (certify-prime p c)
           (primep p)))

;; This is proved quite easily:

(defthmd primep-25519
  (primep (- (expt 2 255) 19))
  :hints (("Goal" :use (:instance certification-theorem
                          (p (- (expt 2 255) 19))
                          (c (certificate-25519))))))
