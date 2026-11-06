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

(include-book "outer")

;;; ------------------------------------------------------------------
;;; Index arithmetic
;;; ------------------------------------------------------------------

;; Length of an n x n matrix vector.  Kept disabled so that (sq n) is not
;; normalized to (expt n 2) inside rules.
(defun sq (n)
  (declare (xargs :guard (natp n)))
  (* n n))

(defthm natp-of-sq (implies (natp n) (natp (sq n))) :rule-classes :type-prescription)
(defthm posp-of-sq (implies (posp n) (posp (sq n))) :rule-classes :type-prescription)

(defun midx (n i j)
  (declare (xargs :guard (and (natp n) (natp i) (natp j))))
  (+ (* i n) j))

(defthm floor-of-midx
  (implies (and (natp i) (natp j) (natp n) (< j n))
           (equal (floor (midx n i j) n) i)))

(defthm mod-of-midx
  (implies (and (natp i) (natp j) (natp n) (< j n))
           (equal (mod (midx n i j) n) j)))

(defthm floor-mod-decompose
  (implies (and (natp a) (posp n))
           (equal (+ (* (floor a n) n) (mod a n)) a))
  :rule-classes nil)

(defthm mod-bound
  (implies (and (natp a) (posp n))
           (< (mod a n) n))
  :rule-classes :linear)

(defthm floor-bound
  (implies (and (natp a) (posp n) (< a (sq n)))
           (< (floor a n) n))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm natp-of-floor
  (implies (and (natp a) (posp n)) (natp (floor a n)))
  :rule-classes :type-prescription)

(defthm natp-of-mod
  (implies (and (natp a) (posp n)) (natp (mod a n)))
  :rule-classes :type-prescription)

(defthm midx-bound
  (implies (and (natp i) (natp j) (natp n) (< i n) (< j n))
           (< (midx n i j) (sq n)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm midx-equal-iff
  (implies (and (natp b) (posp n) (natp j) (natp k) (< k n))
           (equal (equal b (midx n j k))
                  (and (equal (floor b n) j) (equal (mod b n) k))))
  :hints (("Goal" :use floor-mod-decompose)))

(defthm natp-of-midx
  (implies (and (natp n) (natp i) (natp j)) (natp (midx n i j)))
  :rule-classes :type-prescription)

(in-theory (disable midx sq))

;; Keep n^2 in the canonical form (sq n).
(defthm expt-2-is-sq
  (implies (integerp n) (equal (expt n 2) (sq n)))
  :hints (("Goal" :in-theory (enable sq))))

;;; ------------------------------------------------------------------
;;; Standard basis matrices, triples, and sums of rank-one tensors
;;; ------------------------------------------------------------------

;; E_ij: the n x n matrix with a single 1 at (i,j).
(defun E (n i j)
  (declare (xargs :guard (and (natp n) (natp i) (natp j))))
  (unit (sq n) (midx n i j)))

(defthm bvp-of-E (bvp (E n i j)))
(defthm len-of-E (implies (natp n) (equal (len (E n i j)) (sq n))))
(defthm nth-of-E
  (implies (and (natp n) (natp a) (< a (sq n)) (natp i) (natp j) (< i n) (< j n))
           (equal (nth a (E n i j)) (if (equal a (midx n i j)) 1 0))))
(defthm E-nonzero
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (not (equal (E n i j) (bv-zero (sq n))))))
(in-theory (disable E))

;; Length of an order-3 tensor whose factors have length L.
(defun tlen (L)
  (declare (xargs :guard (natp L)))
  (* (nfix L) (* (nfix L) (nfix L))))

;; A summand is a list (A B C) of three bit vectors of length L.
(defun triplep (L s)
  (declare (xargs :guard (natp L)))
  (and (true-listp s) (equal (len s) 3)
       (bvp (car s)) (equal (len (car s)) (nfix L))
       (bvp (cadr s)) (equal (len (cadr s)) (nfix L))
       (bvp (caddr s)) (equal (len (caddr s)) (nfix L))))

(defun triple-listp (L lst)
  (declare (xargs :guard (natp L)))
  (if (atom lst) (null lst)
    (and (triplep L (car lst)) (triple-listp L (cdr lst)))))

(defun rank1 (s)
  (declare (xargs :guard (and (true-listp s) (bvp (car s)) (bvp (cadr s)) (bvp (caddr s)))))
  (outer3 (car s) (cadr s) (caddr s)))

;; The tensor represented by a list of summands.
(defun triple-sum (L lst)
  (declare (xargs :guard (and (natp L) (triple-listp L lst))))
  (if (atom lst)
      (bv-zero (tlen L))
    (bv+ (rank1 (car lst)) (triple-sum L (cdr lst)))))

(defthm bvp-of-rank1
  (implies (and (bvp (car s)) (bvp (cadr s)) (bvp (caddr s)))
           (bvp (rank1 s))))
(defthm len-of-rank1
  (equal (len (rank1 s)) (* (len (car s)) (* (len (cadr s)) (len (caddr s))))))
(defthm nfix-of-len (equal (nfix (len x)) (len x)))

(in-theory (disable outer3 rank1))

(defthm bvp-of-triple-sum (bvp (triple-sum L lst)))
(defthm len-of-triple-sum
  (implies (triple-listp L lst) (equal (len (triple-sum L lst)) (tlen L))))

(defthm triple-listp-of-append
  (implies (true-listp x)
           (equal (triple-listp L (append x y))
                  (and (triple-listp L x) (triple-listp L y))))
  :hints (("Goal" :induct (triple-listp L x))))

(defthm triple-listp-forward-to-true-listp
  (implies (triple-listp L x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm triple-sum-of-append
  (implies (and (triple-listp L x) (triple-listp L y))
           (equal (triple-sum L (append x y))
                  (bv+ (triple-sum L x) (triple-sum L y))))
  :hints (("Goal" :induct (triple-listp L x)
                  :in-theory (disable bv+-commutative bv+-commutative-2))))

(defthm triple-listp-member
  (implies (and (triple-listp L x) (member-equal s x))
           (triplep L s))
  :hints (("Goal" :induct (triple-listp L x))))

(defthm triple-listp-member-facts
  (implies (and (member-equal s x) (triple-listp L x))
           (and (bvp (car s)) (bvp (cadr s)) (bvp (caddr s))
                (true-listp s) (equal (len s) 3)
                (equal (len (car s)) (nfix L))
                (equal (len (cadr s)) (nfix L))
                (equal (len (caddr s)) (nfix L))))
  :hints (("Goal" :induct (triple-listp L x))))

(defthm triple-listp-of-remove1
  (implies (triple-listp L x) (triple-listp L (remove1-equal s x)))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal s x))))

(defthm triple-listp-of-remove1-converse
  (implies (and (member-equal s y) (triplep L s) (true-listp y)
                (triple-listp L (remove1-equal s y)))
           (triple-listp L y))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal s y))))

(defthm triple-sum-of-remove1
  (implies (and (triple-listp L x) (member-equal s x))
           (equal (triple-sum L (remove1-equal s x))
                  (bv+ (rank1 s) (triple-sum L x))))
  :hints (("Goal" :in-theory (e/d (remove1-equal) (bv+-commutative))
                  :induct (remove1-equal s x))))

(defthm triple-listp-when-perm
  (implies (and (perm x y) (triple-listp L x) (true-listp y))
           (triple-listp L y))
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

(defthm triple-sum-when-perm
  (implies (and (perm x y) (triple-listp L x) (triple-listp L y))
           (equal (triple-sum L x) (triple-sum L y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

(defthm triple-listp-of-cons
  (equal (triple-listp L (cons s x))
         (and (triplep L s) (triple-listp L x))))

;;; ------------------------------------------------------------------
;;; The naive scheme and the tensor M^(n)
;;; ------------------------------------------------------------------

;; Summands E_ij (x) E_jk' (x) E_ik' for k' = k, ..., n-1.
(defun naive-k (n i j k)
  (declare (xargs :guard (and (natp n) (natp i) (natp j) (natp k))
                  :measure (nfix (- n k))))
  (if (or (not (natp n)) (not (natp k)) (>= k n))
      nil
    (cons (list (E n i j) (E n j k) (E n i k))
          (naive-k n i j (1+ k)))))

(defun naive-j (n i j)
  (declare (xargs :guard (and (natp n) (natp i) (natp j))
                  :measure (nfix (- n j))))
  (if (or (not (natp n)) (not (natp j)) (>= j n))
      nil
    (append (naive-k n i j 0) (naive-j n i (1+ j)))))

(defun naive-i (n i)
  (declare (xargs :guard (and (natp n) (natp i))
                  :measure (nfix (- n i))))
  (if (or (not (natp n)) (not (natp i)) (>= i n))
      nil
    (append (naive-j n i 0) (naive-i n (1+ i)))))

;; The trivial rank-n^3 scheme {E_ij (x) E_jk (x) E_ik : i,j,k in [n]}.
(defun naive-scheme (n)
  (declare (xargs :guard (natp n)))
  (naive-i n 0))

(defthm triple-listp-of-naive-k
  (implies (natp n) (triple-listp (sq n) (naive-k n i j k))))
(defthm triple-listp-of-naive-j
  (implies (natp n) (triple-listp (sq n) (naive-j n i j))))
(defthm triple-listp-of-naive-i
  (implies (natp n) (triple-listp (sq n) (naive-i n i))))
(defthm triple-listp-of-naive-scheme
  (implies (natp n) (triple-listp (sq n) (naive-scheme n))))

;; The matrix multiplication tensor (Lemma 4.1 of the paper).
(defun mmt (n)
  (declare (xargs :guard (natp n)))
  (triple-sum (sq n) (naive-scheme n)))


(defthm len-of-naive-k
  (implies (and (natp n) (natp k) (<= k n)) (equal (len (naive-k n i j k)) (- n k))))
(defthm len-of-naive-j
  (implies (and (natp n) (natp j) (<= j n)) (equal (len (naive-j n i j)) (* (- n j) n))))
(defthm len-of-naive-i
  (implies (and (natp n) (natp i) (<= i n)) (equal (len (naive-i n i)) (* (- n i) (sq n)))))
(defthm len-of-naive-scheme
  (implies (natp n) (equal (len (naive-scheme n)) (* n n n))))

(defthm bvp-of-mmt (bvp (mmt n)))
(defthm len-of-mmt (implies (natp n) (equal (len (mmt n)) (tlen (sq n)))))

;;; ------------------------------------------------------------------
;;; The coordinate formula (Definition 2.1 / Lemma 4.1)
;;; ------------------------------------------------------------------

;; For a = (g,h), b = (i,j), c = (k,l):  M_{a,b,c} = [g=k][h=i][j=l].
(defun mmt-coeff (n a b c)
  (declare (xargs :guard (and (posp n) (natp a) (natp b) (natp c))))
  (if (and (equal (floor a n) (floor c n))
           (equal (mod a n) (floor b n))
           (equal (mod b n) (mod c n)))
      1 0))

;; Partial-sum coefficient functions used for the three nested inductions.
(defun coeff-k (n a b c i j k)
  (if (and (equal a (midx n i j))
           (equal (floor b n) j)
           (equal (floor c n) i)
           (equal (mod b n) (mod c n))
           (<= k (mod b n)))
      1 0))

(defun coeff-j (n a b c i j)
  (if (and (equal (floor a n) i)
           (<= j (mod a n))
           (equal (floor b n) (mod a n))
           (equal (floor c n) i)
           (equal (mod b n) (mod c n)))
      1 0))

(defun coeff-i (n a b c i)
  (if (and (<= i (floor a n))
           (equal (floor b n) (mod a n))
           (equal (floor c n) (floor a n))
           (equal (mod b n) (mod c n)))
      1 0))

(defthm tidx3-bound-sq
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n)))
           (< (tidx3 (sq n) (sq n) a b c) (tlen (sq n))))
  :hints (("Goal" :in-theory (disable tidx3-bound)
                  :use ((:instance tidx3-bound (LA (sq n)) (LB (sq n)) (LC (sq n))))))
  :rule-classes :linear)

(defthm natp-of-tidx3
  (implies (and (natp a) (natp b) (natp c) (natp LB) (natp LC))
           (natp (tidx3 LB LC a b c)))
  :rule-classes :type-prescription)

(in-theory (disable tidx3))

(defthm nth-of-rank1-of-units
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (nth (tidx3 (sq n) (sq n) a b c)
                       (rank1 (list (E n i j) (E n j k) (E n i k))))
                  (if (and (equal a (midx n i j))
                           (equal b (midx n j k))
                           (equal c (midx n i k)))
                      1 0)))
  :hints (("Goal" :in-theory (e/d (rank1) (nth-of-outer3))
                  :use ((:instance nth-of-outer3
                                   (A (E n i j)) (B (E n j k)) (C (E n i k))
                                   (ia a) (ib b) (ic c))))))

(defthm coeff-k-step
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (coeff-k n a b c i j k)
                  (bxor (if (and (equal a (midx n i j))
                                 (equal b (midx n j k))
                                 (equal c (midx n i k)))
                            1 0)
                        (coeff-k n a b c i j (1+ k))))))

(defthm nth-of-naive-k
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (<= k n))
           (equal (nth (tidx3 (sq n) (sq n) a b c)
                       (triple-sum (sq n) (naive-k n i j k)))
                  (coeff-k n a b c i j k)))
  :hints (("Goal" :induct (naive-k n i j k)
                  :in-theory (disable coeff-k rank1 coeff-k-step))
          ("Subgoal *1/2" :use (coeff-k-step
                                (:instance nth-of-bv+
                                           (i (tidx3 (sq n) (sq n) a b c))
                                           (x (rank1 (list (E n i j) (E n j k) (E n i k))))
                                           (y (triple-sum (sq n) (naive-k n i j (1+ k)))))))
          ("Subgoal *1/1" :in-theory (enable coeff-k))))

(defthm coeff-j-step
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n))
                (natp i) (natp j) (< i n) (< j n))
           (equal (coeff-j n a b c i j)
                  (bxor (coeff-k n a b c i j 0)
                        (coeff-j n a b c i (1+ j)))))
  :hints (("Goal" :in-theory (enable midx-equal-iff))))

(defthm nth-of-naive-j
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n))
                (natp i) (natp j) (< i n) (<= j n))
           (equal (nth (tidx3 (sq n) (sq n) a b c)
                       (triple-sum (sq n) (naive-j n i j)))
                  (coeff-j n a b c i j)))
  :hints (("Goal" :induct (naive-j n i j)
                  :in-theory (disable coeff-k coeff-j rank1 coeff-j-step))
          ("Subgoal *1/2" :use (coeff-j-step
                                (:instance nth-of-bv+
                                           (i (tidx3 (sq n) (sq n) a b c))
                                           (x (triple-sum (sq n) (naive-k n i j 0)))
                                           (y (triple-sum (sq n) (naive-j n i (1+ j)))))))
          ("Subgoal *1/1" :in-theory (enable coeff-j))))

(defthm coeff-i-step
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n))
                (natp i) (< i n))
           (equal (coeff-i n a b c i)
                  (bxor (coeff-j n a b c i 0)
                        (coeff-i n a b c (1+ i))))))

(defthm nth-of-naive-i
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n))
                (natp i) (<= i n))
           (equal (nth (tidx3 (sq n) (sq n) a b c)
                       (triple-sum (sq n) (naive-i n i)))
                  (coeff-i n a b c i)))
  :hints (("Goal" :induct (naive-i n i)
                  :in-theory (disable coeff-j coeff-i rank1 coeff-i-step))
          ("Subgoal *1/2" :use (coeff-i-step
                                (:instance nth-of-bv+
                                           (i (tidx3 (sq n) (sq n) a b c))
                                           (x (triple-sum (sq n) (naive-j n i 0)))
                                           (y (triple-sum (sq n) (naive-i n (1+ i)))))))
          ("Subgoal *1/1" :in-theory (enable coeff-i))))

;; The coordinate formula for M^(n).
(defthm coeff-i-0-is-mmt-coeff
  (implies (and (posp n) (natp a))
           (equal (coeff-i n a b c 0) (mmt-coeff n a b c))))

(defthm nth-of-mmt
  (implies (and (posp n) (natp a) (natp b) (natp c)
                (< a (sq n)) (< b (sq n)) (< c (sq n)))
           (equal (nth (tidx3 (sq n) (sq n) a b c) (mmt n))
                  (mmt-coeff n a b c)))
  :hints (("Goal" :in-theory (e/d (mmt naive-scheme)
                                  (coeff-i mmt-coeff nth-of-naive-i triple-sum))
                  :use ((:instance nth-of-naive-i (i 0))))))

(in-theory (disable mmt naive-scheme))

;; Consequences used by the span lemma: fixing the B and C coordinates to
;; (j,k) and (i,k) picks out exactly the A coordinate (i,j).
(defthm mmt-coeff-slice-A
  (implies (and (posp n) (natp a) (< a (sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (mmt-coeff n a (midx n j k) (midx n i k))
                  (if (equal a (midx n i j)) 1 0)))
  :hints (("Goal" :in-theory (enable midx-equal-iff))))

(defthm mmt-coeff-slice-B
  (implies (and (posp n) (natp b) (< b (sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (mmt-coeff n (midx n i j) b (midx n i k))
                  (if (equal b (midx n j k)) 1 0)))
  :hints (("Goal" :in-theory (enable midx-equal-iff))))

(defthm mmt-coeff-slice-C
  (implies (and (posp n) (natp c) (< c (sq n))
                (natp i) (natp j) (natp k) (< i n) (< j n) (< k n))
           (equal (mmt-coeff n (midx n i j) (midx n j k) c)
                  (if (equal c (midx n i k)) 1 0)))
  :hints (("Goal" :in-theory (enable midx-equal-iff))))
