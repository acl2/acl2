; x-mmt.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/mmt.lisp
; produced by rename.py in this directory; do not edit by hand.
; mmt.lisp -- The matrix multiplication tensor M^(n) over F_2.
;
; Matrices are bit vectors of length n*n with entry (i,j) at index i*n+j.
; The tensor is a bit vector of length (n*n)^3 = n^6.
;
; We define M^(n) as the sum over i,j,k of E_ij (x) E_jk (x) E_ik (the
; formula of Lemma 4.1 of the paper, and also the "naive" rank-n^3
; scheme from which all searches start), and then prove the coordinate
; formula M_{g,h,i,j,k,l} = delta_{g,k} delta_{h,i} delta_{j,l} from
; Definition 2.1 / Lemma 4.1.  The characterization of Definition 2.1
; through bilinear evaluation on matrices is in mmt-def.lisp.

(in-package "ACL2")

(include-book "x-outer")

;;; ------------------------------------------------------------------
;;; Index arithmetic
;;; ------------------------------------------------------------------

;; Length of an n x n matrix vector.  Kept disabled so that (sq n) is not
;; normalized to (expt n 2) inside rules.
(defun x-sq (n)
  (declare (xargs :guard (natp n)))
  (* n n))

(defthm x-natp-of-sq (implies (natp n) (natp (x-sq n))) :rule-classes :type-prescription)
(defthm x-posp-of-sq (implies (posp n) (posp (x-sq n))) :rule-classes :type-prescription)

(defun x-midx (n i j)
  (declare (xargs :guard (and (natp n) (natp i) (natp j))))
  (+ (* i n) j))

(defthm x-floor-of-midx
  (implies (and (natp i) (natp j) (natp n) (< j n))
           (equal (floor (x-midx n i j) n) i)))

(defthm x-mod-of-midx
  (implies (and (natp i) (natp j) (natp n) (< j n))
           (equal (mod (x-midx n i j) n) j)))

(defthm x-floor-mod-decompose
  (implies (and (natp a) (posp n))
           (equal (+ (* (floor a n) n) (mod a n)) a))
  :rule-classes nil)

(defthm x-mod-bound
  (implies (and (natp a) (posp n))
           (< (mod a n) n))
  :rule-classes :linear)

(defthm x-floor-bound
  (implies (and (natp a) (posp n) (< a (x-sq n)))
           (< (floor a n) n))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm x-natp-of-floor
  (implies (and (natp a) (posp n)) (natp (floor a n)))
  :rule-classes :type-prescription)

(defthm x-natp-of-mod
  (implies (and (natp a) (posp n)) (natp (mod a n)))
  :rule-classes :type-prescription)

(defthm x-midx-bound
  (implies (and (natp i) (natp j) (natp n) (< i n) (< j n))
           (< (x-midx n i j) (x-sq n)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm x-midx-equal-iff
  (implies (and (natp b) (posp n) (natp j) (natp k) (< k n))
           (equal (equal b (x-midx n j k))
                  (and (equal (floor b n) j) (equal (mod b n) k))))
  :hints (("Goal" :use x-floor-mod-decompose)))

(defthm x-natp-of-midx
  (implies (and (natp n) (natp i) (natp j)) (natp (x-midx n i j)))
  :rule-classes :type-prescription)

(in-theory (disable x-midx x-sq))

;; Keep n^2 in the canonical form (sq n).
(defthm x-expt-2-is-sq
  (implies (integerp n) (equal (expt n 2) (x-sq n)))
  :hints (("Goal" :in-theory (enable x-sq))))

;;; ------------------------------------------------------------------
;;; Standard basis matrices, triples, and sums of rank-one tensors
;;; ------------------------------------------------------------------

;; E_ij: the n x n matrix with a single 1 at (i,j).
(defun x-E (n i j)
  (declare (xargs :guard (and (natp n) (natp i) (natp j))))
  (x-unit (x-sq n) (x-midx n i j)))

(defthm x-bvp-of-E (x-bvp (x-E n i j)))
(defthm x-len-of-E (implies (natp n) (equal (len (x-E n i j)) (x-sq n))))
(defthm x-nth-of-E
  (implies (and (natp n) (natp a) (< a (x-sq n)) (natp i) (natp j) (< i n) (< j n))
           (equal (nth a (x-E n i j)) (if (equal a (x-midx n i j)) 1 0))))
(defthm x-E-nonzero
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (not (equal (x-E n i j) (x-bv-zero (x-sq n))))))
(in-theory (disable x-E))

;; Length of an order-3 tensor whose factors have length L.
(defun x-tlen (L)
  (declare (xargs :guard (natp L)))
  (* (nfix L) (* (nfix L) (nfix L))))

;; A summand is a list (A B C) of three bit vectors of length L.
(defun x-triplep (L s)
  (declare (xargs :guard (natp L)))
  (and (true-listp s) (equal (len s) 3)
       (x-bvp (car s)) (equal (len (car s)) (nfix L))
       (x-bvp (cadr s)) (equal (len (cadr s)) (nfix L))
       (x-bvp (caddr s)) (equal (len (caddr s)) (nfix L))))

(defun x-triple-listp (L lst)
  (declare (xargs :guard (natp L)))
  (if (atom lst) (null lst)
    (and (x-triplep L (car lst)) (x-triple-listp L (cdr lst)))))

(defun x-rank1 (s)
  (declare (xargs :guard (and (true-listp s) (x-bvp (car s)) (x-bvp (cadr s)) (x-bvp (caddr s)))))
  (x-outer3 (car s) (cadr s) (caddr s)))

;; The tensor represented by a list of summands.
(defun x-triple-sum (L lst)
  (declare (xargs :guard (and (natp L) (x-triple-listp L lst))))
  (if (atom lst)
      (x-bv-zero (x-tlen L))
    (x-bv+ (x-rank1 (car lst)) (x-triple-sum L (cdr lst)))))

(defthm x-bvp-of-rank1
  (implies (and (x-bvp (car s)) (x-bvp (cadr s)) (x-bvp (caddr s)))
           (x-bvp (x-rank1 s))))
(defthm x-len-of-rank1
  (equal (len (x-rank1 s)) (* (len (car s)) (* (len (cadr s)) (len (caddr s))))))
(defthm x-nfix-of-len (equal (nfix (len x)) (len x)))

(in-theory (disable x-outer3 x-rank1))

(defthm x-bvp-of-triple-sum (x-bvp (x-triple-sum L lst)))
(defthm x-len-of-triple-sum
  (implies (x-triple-listp L lst) (equal (len (x-triple-sum L lst)) (x-tlen L))))

(defthm x-triple-listp-of-append
  (implies (true-listp x)
           (equal (x-triple-listp L (append x y))
                  (and (x-triple-listp L x) (x-triple-listp L y))))
  :hints (("Goal" :induct (x-triple-listp L x))))

(defthm x-triple-listp-forward-to-true-listp
  (implies (x-triple-listp L x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm x-triple-sum-of-append
  (implies (and (x-triple-listp L x) (x-triple-listp L y))
           (equal (x-triple-sum L (append x y))
                  (x-bv+ (x-triple-sum L x) (x-triple-sum L y))))
  :hints (("Goal" :induct (x-triple-listp L x)
                  :in-theory (disable x-bv+-commutative x-bv+-commutative-2))))

(defthm x-triple-listp-member
  (implies (and (x-triple-listp L x) (member-equal s x))
           (x-triplep L s))
  :hints (("Goal" :induct (x-triple-listp L x))))

(defthm x-triple-listp-member-facts
  (implies (and (member-equal s x) (x-triple-listp L x))
           (and (x-bvp (car s)) (x-bvp (cadr s)) (x-bvp (caddr s))
                (true-listp s) (equal (len s) 3)
                (equal (len (car s)) (nfix L))
                (equal (len (cadr s)) (nfix L))
                (equal (len (caddr s)) (nfix L))))
  :hints (("Goal" :induct (x-triple-listp L x))))

(defthm x-triple-listp-of-remove1
  (implies (x-triple-listp L x) (x-triple-listp L (remove1-equal s x)))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal s x))))

(defthm x-triple-listp-of-remove1-converse
  (implies (and (member-equal s y) (x-triplep L s) (true-listp y)
                (x-triple-listp L (remove1-equal s y)))
           (x-triple-listp L y))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal s y))))

(defthm x-triple-sum-of-remove1
  (implies (and (x-triple-listp L x) (member-equal s x))
           (equal (x-triple-sum L (remove1-equal s x))
                  (x-bv+ (x-rank1 s) (x-triple-sum L x))))
  :hints (("Goal" :in-theory (e/d (remove1-equal) (x-bv+-commutative))
                  :induct (remove1-equal s x))))

(defthm x-triple-listp-when-perm
  (implies (and (perm x y) (x-triple-listp L x) (true-listp y))
           (x-triple-listp L y))
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

(defthm x-triple-sum-when-perm
  (implies (and (perm x y) (x-triple-listp L x) (x-triple-listp L y))
           (equal (x-triple-sum L x) (x-triple-sum L y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

(defthm x-triple-listp-of-cons
  (equal (x-triple-listp L (cons s x))
         (and (x-triplep L s) (x-triple-listp L x))))

;;; ------------------------------------------------------------------
;;; The naive scheme and the tensor M^(n)
;;; ------------------------------------------------------------------

;; Summands E_ij (x) E_jk' (x) E_ik' for k' = k, ..., n-1.
(defun x-naive-k (n i j k)
  (declare (xargs :guard (and (natp n) (natp i) (natp j) (natp k))
                  :measure (nfix (- n k))))
  (if (or (not (natp n)) (not (natp k)) (>= k n))
      nil
    (cons (list (x-E n i j) (x-E n j k) (x-E n i k))
          (x-naive-k n i j (1+ k)))))

(defun x-naive-j (n i j)
  (declare (xargs :guard (and (natp n) (natp i) (natp j))
                  :measure (nfix (- n j))))
  (if (or (not (natp n)) (not (natp j)) (>= j n))
      nil
    (append (x-naive-k n i j 0) (x-naive-j n i (1+ j)))))

(defun x-naive-i (n i)
  (declare (xargs :guard (and (natp n) (natp i))
                  :measure (nfix (- n i))))
  (if (or (not (natp n)) (not (natp i)) (>= i n))
      nil
    (append (x-naive-j n i 0) (x-naive-i n (1+ i)))))

;; The trivial rank-n^3 scheme {E_ij (x) E_jk (x) E_ik : i,j,k in [n]}.
(defun x-naive-scheme (n)
  (declare (xargs :guard (natp n)))
  (x-naive-i n 0))

(defthm x-triple-listp-of-naive-k
  (implies (natp n) (x-triple-listp (x-sq n) (x-naive-k n i j k))))
(defthm x-triple-listp-of-naive-j
  (implies (natp n) (x-triple-listp (x-sq n) (x-naive-j n i j))))
(defthm x-triple-listp-of-naive-i
  (implies (natp n) (x-triple-listp (x-sq n) (x-naive-i n i))))
(defthm x-triple-listp-of-naive-scheme
  (implies (natp n) (x-triple-listp (x-sq n) (x-naive-scheme n))))

;; The matrix multiplication tensor (Lemma 4.1 of the paper).
(defun x-mmt (n)
  (declare (xargs :guard (natp n)))
  (x-triple-sum (x-sq n) (x-naive-scheme n)))


(defthm x-len-of-naive-k
  (implies (and (natp n) (natp k) (<= k n)) (equal (len (x-naive-k n i j k)) (- n k))))
(defthm x-len-of-naive-j
  (implies (and (natp n) (natp j) (<= j n)) (equal (len (x-naive-j n i j)) (* (- n j) n))))
(defthm x-len-of-naive-i
  (implies (and (natp n) (natp i) (<= i n)) (equal (len (x-naive-i n i)) (* (- n i) (x-sq n)))))
(defthm x-len-of-naive-scheme
  (implies (natp n) (equal (len (x-naive-scheme n)) (* n n n))))

(defthm x-bvp-of-mmt (x-bvp (x-mmt n)))
(defthm x-len-of-mmt (implies (natp n) (equal (len (x-mmt n)) (x-tlen (x-sq n)))))

;;; ------------------------------------------------------------------
;;; The coordinate formula (Definition 2.1 / Lemma 4.1)
;;; ------------------------------------------------------------------

;; For a = (g,h), b = (i,j), c = (k,l):  M_{a,b,c} = [g=k][h=i][j=l].
(defun x-mmt-coeff (n a b c)
  (declare (xargs :guard (and (posp n) (natp a) (natp b) (natp c))))
  (if (and (equal (floor a n) (floor c n))
           (equal (mod a n) (floor b n))
           (equal (mod b n) (mod c n)))
      1 0))

;; Partial-sum coefficient functions used for the three nested inductions.
(defun x-coeff-k (n a b c i j k)
  (if (and (equal a (x-midx n i j))
           (equal (floor b n) j)
           (equal (floor c n) i)
           (equal (mod b n) (mod c n))
           (<= k (mod b n)))
      1 0))

(defun x-coeff-j (n a b c i j)
  (if (and (equal (floor a n) i)
           (<= j (mod a n))
           (equal (floor b n) (mod a n))
           (equal (floor c n) i)
           (equal (mod b n) (mod c n)))
      1 0))

(defun x-coeff-i (n a b c i)
  (if (and (<= i (floor a n))
           (equal (floor b n) (mod a n))
           (equal (floor c n) (floor a n))
           (equal (mod b n) (mod c n)))
      1 0))

(defthm x-tidx3-bound-sq
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n)))
           (< (x-tidx3 (x-sq n) (x-sq n) a b c) (x-tlen (x-sq n))))
  :hints (("Goal" :in-theory (disable x-tidx3-bound)
                  :use ((:instance x-tidx3-bound (LA (x-sq n)) (LB (x-sq n)) (LC (x-sq n))))))
  :rule-classes :linear)

(defthm x-natp-of-tidx3
  (implies (and (natp a) (natp b) (natp c) (natp LB) (natp LC))
           (natp (x-tidx3 LB LC a b c)))
  :rule-classes :type-prescription)

(in-theory (disable x-tidx3))

(defthm x-nth-of-rank1-of-units
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (nth (x-tidx3 (x-sq n) (x-sq n) a b c)
                       (x-rank1 (list (x-E n i j) (x-E n j k) (x-E n i k))))
                  (if (and (equal a (x-midx n i j))
                           (equal b (x-midx n j k))
                           (equal c (x-midx n i k)))
                      1 0)))
  :hints (("Goal" :in-theory (e/d (x-rank1) (x-nth-of-outer3))
                  :use ((:instance x-nth-of-outer3
                                   (A (x-E n i j)) (B (x-E n j k)) (C (x-E n i k))
                                   (ia a) (ib b) (ic c))))))

(defthm x-coeff-k-step
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (x-coeff-k n a b c i j k)
                  (x-bxor (if (and (equal a (x-midx n i j))
                                 (equal b (x-midx n j k))
                                 (equal c (x-midx n i k)))
                            1 0)
                        (x-coeff-k n a b c i j (1+ k))))))

(defthm x-nth-of-naive-k
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (<= k n))
           (equal (nth (x-tidx3 (x-sq n) (x-sq n) a b c)
                       (x-triple-sum (x-sq n) (x-naive-k n i j k)))
                  (x-coeff-k n a b c i j k)))
  :hints (("Goal" :induct (x-naive-k n i j k)
                  :in-theory (disable x-coeff-k x-rank1 x-coeff-k-step))
          ("Subgoal *1/2" :use (x-coeff-k-step
                                (:instance x-nth-of-bv+
                                           (i (x-tidx3 (x-sq n) (x-sq n) a b c))
                                           (x (x-rank1 (list (x-E n i j) (x-E n j k) (x-E n i k))))
                                           (y (x-triple-sum (x-sq n) (x-naive-k n i j (1+ k)))))))
          ("Subgoal *1/1" :in-theory (enable x-coeff-k))))

(defthm x-coeff-j-step
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n))
                (natp i) (natp j) (< i n) (< j n))
           (equal (x-coeff-j n a b c i j)
                  (x-bxor (x-coeff-k n a b c i j 0)
                        (x-coeff-j n a b c i (1+ j)))))
  :hints (("Goal" :in-theory (enable x-midx-equal-iff))))

(defthm x-nth-of-naive-j
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n))
                (natp i) (natp j) (< i n) (<= j n))
           (equal (nth (x-tidx3 (x-sq n) (x-sq n) a b c)
                       (x-triple-sum (x-sq n) (x-naive-j n i j)))
                  (x-coeff-j n a b c i j)))
  :hints (("Goal" :induct (x-naive-j n i j)
                  :in-theory (disable x-coeff-k x-coeff-j x-rank1 x-coeff-j-step))
          ("Subgoal *1/2" :use (x-coeff-j-step
                                (:instance x-nth-of-bv+
                                           (i (x-tidx3 (x-sq n) (x-sq n) a b c))
                                           (x (x-triple-sum (x-sq n) (x-naive-k n i j 0)))
                                           (y (x-triple-sum (x-sq n) (x-naive-j n i (1+ j)))))))
          ("Subgoal *1/1" :in-theory (enable x-coeff-j))))

(defthm x-coeff-i-step
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n))
                (natp i) (< i n))
           (equal (x-coeff-i n a b c i)
                  (x-bxor (x-coeff-j n a b c i 0)
                        (x-coeff-i n a b c (1+ i))))))

(defthm x-nth-of-naive-i
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n))
                (natp i) (<= i n))
           (equal (nth (x-tidx3 (x-sq n) (x-sq n) a b c)
                       (x-triple-sum (x-sq n) (x-naive-i n i)))
                  (x-coeff-i n a b c i)))
  :hints (("Goal" :induct (x-naive-i n i)
                  :in-theory (disable x-coeff-j x-coeff-i x-rank1 x-coeff-i-step))
          ("Subgoal *1/2" :use (x-coeff-i-step
                                (:instance x-nth-of-bv+
                                           (i (x-tidx3 (x-sq n) (x-sq n) a b c))
                                           (x (x-triple-sum (x-sq n) (x-naive-j n i 0)))
                                           (y (x-triple-sum (x-sq n) (x-naive-i n (1+ i)))))))
          ("Subgoal *1/1" :in-theory (enable x-coeff-i))))

;; The coordinate formula for M^(n).
(defthm x-coeff-i-0-is-mmt-coeff
  (implies (and (posp n) (natp a))
           (equal (x-coeff-i n a b c 0) (x-mmt-coeff n a b c))))

(defthm x-nth-of-mmt
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (x-sq n)) (< b (x-sq n)) (< c (x-sq n)))
           (equal (nth (x-tidx3 (x-sq n) (x-sq n) a b c) (x-mmt n))
                  (x-mmt-coeff n a b c)))
  :hints (("Goal" :in-theory (e/d (x-mmt x-naive-scheme)
                                  (x-coeff-i x-mmt-coeff x-nth-of-naive-i x-triple-sum))
                  :use ((:instance x-nth-of-naive-i (i 0))))))

(in-theory (disable x-mmt x-naive-scheme))

;; Consequences used by the span lemma: fixing the B and C coordinates to
;; (j,k) and (i,k) picks out exactly the A coordinate (i,j).
(defthm x-mmt-coeff-slice-A
  (implies (and (posp n) (natp a) (< a (x-sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (x-mmt-coeff n a (x-midx n j k) (x-midx n i k))
                  (if (equal a (x-midx n i j)) 1 0)))
  :hints (("Goal" :in-theory (enable x-midx-equal-iff))))

(defthm x-mmt-coeff-slice-B
  (implies (and (posp n) (natp b) (< b (x-sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (x-mmt-coeff n (x-midx n i j) b (x-midx n i k))
                  (if (equal b (x-midx n j k)) 1 0)))
  :hints (("Goal" :in-theory (enable x-midx-equal-iff))))

(defthm x-mmt-coeff-slice-C
  (implies (and (posp n) (natp c) (< c (x-sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (x-mmt-coeff n (x-midx n i j) (x-midx n j k) c)
                  (if (equal c (x-midx n i k)) 1 0)))
  :hints (("Goal" :in-theory (enable x-midx-equal-iff))))
