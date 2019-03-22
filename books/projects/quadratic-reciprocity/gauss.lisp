;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "RTL")

(local (include-book "support/gauss"))

;; Also defined in the RTL library.
(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(set-enforce-redundancy t)
(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

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
	     (not (equal (+ (mod (* m i) p) (mod (* m j) p)) p))))

(defthm reflections-distinct-positives
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (integerp n)
		  (< n (/ p 2)))
	     (distinct-positives (reflections n m p) (/ (1- p) 2)))
  :rule-classes ())

;; This result allows us to compute the product of the elements of
;; reflections((p-1)/2,m,p):

(defthm perm-reflections
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (perm (positives (/ (1- p) 2))
		   (reflections (/ (1- p) 2) m p)))
  :rule-classes ())

(defthm times-list-reflections
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
           (equal (times-list (reflections (+ -1/2 (* 1/2 p)) m p))
                  (fact (/ (1- p) 2)))))

;;  We have an alternative method for computing the same product:

(defthm times-list-reflection-mod-prods
    (implies (and (not (zp p))
		  (integerp m)
		  (integerp n))
	     (equal (mod (times-list (reflections n m p)) p)
		    (if (evenp (mu n m p))
			(mod (times-list (mod-prods n m p)) p)
		      (mod (- (times-list (mod-prods n m p))) p))))
  :rule-classes ())

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
  :rule-classes ())

(defthm euler-mu-odd
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (oddp (mu (/ (1- p) 2) m p)))
	     (= (mod (expt m (/ (1- p) 2)) p) (- p 1)))
  :rule-classes ())

(defthm gauss-lemma
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (iff (evenp (mu (/ (1- p) 2) m p))
		  (residue m p)))
  :rule-classes ())

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
		    (- (/ (1- p) 2) (fl (/ (1- p) 4))))))

;; Let k = fl(p/8) and m = mod(p,8).  Then p = 8*k + m.  It follows that
;;   mu((p-1)/2,2,p) = 2*k + (m-1)/2 - fl((m-1)/4):

(defthmd mu-rewrite-lemma-3
    (implies (and (primep p)
		  (not (= p 2)))
	     (equal (mod p 8)
		    (- p (* 8 (fl (/ p 8)))))))

(defthm mu-rewrite
    (implies (and (primep p)
		  (not (= p 2)))
	     (equal (mu (+ -1/2 (* 1/2 p)) 2 p)
		    (+ (* 2 (fl (/ p 8))) (- (/ (1- (mod p 8)) 2) (fl (/ (1- (mod p 8)) 4)))))))

;; The desired result now follows by a simple case analysis:

(defthm second-supplement
    (implies (and (primep p)
		  (not (= p 2)))
	     (iff (residue 2 p)
		  (or (= (mod p 8) 1)
		      (= (mod p 8) 7))))
  :rule-classes ())
