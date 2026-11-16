; mmt-def.lisp -- Definition 2.1 of the paper.
;
; The matrix multiplication tensor is "the unique tensor M satisfying,
; for all n x n matrices D and F,
;      (DF)_{k,l} = sum_{g,h,i,j} M_{g,h,i,j,k,l} D_{g,h} F_{i,j}."
;
; We define matrix multiplication over F_2 and the bilinear evaluation of
; an order-3 tensor on two matrices, prove that (mmt n) satisfies the
; equation for all D, F, and prove that any tensor satisfying it equals
; (mmt n).

(in-package "ACL2")

(include-book "mmt")

;;; ------------------------------------------------------------------
;;; Matrix multiplication over F_2
;;; ------------------------------------------------------------------

;; xor_{h >= h0} D[k,h] F[h,l]
(defun mm-entry (n D F k l h)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- n h))))
  (if (or (not (natp n)) (not (natp h)) (>= h n))
      0
    (bxor (band (nth (midx n k h) D) (nth (midx n h l) F))
          (mm-entry n D F k l (1+ h)))))

;; The product matrix, entries listed in index order idx = k*n + l.
(defun matmul-from (n D F idx)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (sq n) idx))))
  (if (or (not (natp n)) (not (natp idx)) (>= idx (sq n)))
      nil
    (cons (mm-entry n D F (floor idx n) (mod idx n) 0)
          (matmul-from n D F (1+ idx)))))

(defun matmul (n D F)
  (declare (xargs :guard t :verify-guards nil))
  (matmul-from n D F 0))

;;; ------------------------------------------------------------------
;;; Bilinear evaluation of an order-3 tensor
;;; ------------------------------------------------------------------

;; xor_{b >= b0} T[a,b,c] D[a] F[b]
(defun teval-b (n T3 D F a c b)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (sq n) b))))
  (if (or (not (natp n)) (not (natp b)) (>= b (sq n)))
      0
    (bxor (band (nth (tidx3 (sq n) (sq n) a b c) T3) (band (nth a D) (nth b F)))
          (teval-b n T3 D F a c (1+ b)))))

;; xor_{a >= a0} xor_b T[a,b,c] D[a] F[b]
(defun teval-a (n T3 D F c a)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (sq n) a))))
  (if (or (not (natp n)) (not (natp a)) (>= a (sq n)))
      0
    (bxor (teval-b n T3 D F a c 0)
          (teval-a n T3 D F c (1+ a)))))

(defun teval-from (n T3 D F idx)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (sq n) idx))))
  (if (or (not (natp n)) (not (natp idx)) (>= idx (sq n)))
      nil
    (cons (teval-a n T3 D F idx 0)
          (teval-from n T3 D F (1+ idx)))))

;; The matrix whose (k,l) entry is sum_{a,b} T[a,b,(k,l)] D[a] F[b].
(defun tensor-eval (n T3 D F)
  (declare (xargs :guard t :verify-guards nil))
  (teval-from n T3 D F 0))

;;; ------------------------------------------------------------------
;;; M^(n) satisfies the defining equation
;;; ------------------------------------------------------------------

(defthm midx-of-floor-mod-local
  (implies (and (natp k) (posp n))
           (equal (midx n (floor k n) (mod k n)) k))
  :hints (("Goal" :in-theory (enable midx) :use floor-mod-decompose)))

;; Inner sum for M: for fixed a = (k',h) and c = (k,l), the only b with
;; a nonzero coefficient is b = (h,l), and it needs k' = k.
(defthm teval-b-of-mmt
  (implies (and (posp n) (natp a) (< a (sq n)) (natp c) (< c (sq n))
                (natp b) (<= b (sq n))
                (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (teval-b n (mmt n) D F a c b)
                  (if (and (equal (floor a n) (floor c n))
                           (<= b (midx n (mod a n) (mod c n))))
                      (band (nth a D) (nth (midx n (mod a n) (mod c n)) F))
                    0)))
  :hints (("Goal" :induct (teval-b n (mmt n) D F a c b)
                  :in-theory (e/d (midx-equal-iff) (nth-of-mmt mmt-coeff)))
          ("Subgoal *1/2" :use ((:instance nth-of-mmt))
                          :expand ((mmt-coeff n a b c)))))

;; The inner sum from b = 0.
(defthm teval-b0-of-mmt
  (implies (and (posp n) (natp a) (< a (sq n)) (natp c) (< c (sq n))
                (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (teval-b n (mmt n) D F a c 0)
                  (if (equal (floor a n) (floor c n))
                      (band (nth a D) (nth (midx n (mod a n) (mod c n)) F))
                    0)))
  :hints (("Goal" :use ((:instance teval-b-of-mmt (b 0))))))

(in-theory (disable teval-b-of-mmt))

;; Outer sum for M.  Rows above k = floor(c/n) contribute nothing ...
(defthm teval-a-of-mmt-above
  (implies (and (posp n) (natp c) (< c (sq n)) (natp a) (<= a (sq n))
                (< (floor c n) (floor a n))
                (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (teval-a n (mmt n) D F c a) 0))
  :hints (("Goal" :induct (teval-a n (mmt n) D F c a))))

(defthm midx-plus-1
  (implies (and (natp n) (natp k) (natp h))
           (equal (+ 1 (midx n k h)) (midx n k (1+ h))))
  :hints (("Goal" :in-theory (enable midx))))

(defthm midx-n-is-next-row
  (implies (and (natp n) (natp k))
           (equal (midx n k n) (midx n (1+ k) 0)))
  :hints (("Goal" :in-theory (enable midx))))

(defthm midx-row-n-is-sq
  (implies (natp n) (equal (midx n n 0) (sq n)))
  :hints (("Goal" :in-theory (enable midx sq))))

;; At the end of row k (a = (k+1) n) the sum is zero: either a = n^2, or
;; a starts row k+1 > k.
(defthm teval-a-of-mmt-row-end
  (implies (and (posp n) (natp c) (< c (sq n))
                (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (teval-a n (mmt n) D F c (midx n (floor c n) n)) 0))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (midx sq) (teval-a-of-mmt-above midx-row-n-is-sq expt-2-is-sq
                                             midx-n-is-next-row))
                  :cases ((equal (1+ (floor c n)) n))
                  :use ((:instance floor-bound (a c))
                        (:instance teval-a-of-mmt-above (a (midx n (1+ (floor c n)) 0)))))))

;; ... within row k the sum from column h is the product entry from h ...
(defthm teval-a-of-mmt-in-row
  (implies (and (posp n) (natp c) (< c (sq n)) (natp h) (<= h n)
                (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (teval-a n (mmt n) D F c (midx n (floor c n) h))
                  (mm-entry n D F (floor c n) (mod c n) h)))
  :hints (("Goal" :induct (mm-entry n D F (floor c n) (mod c n) h)
                  :in-theory (disable teval-a-of-mmt-above midx-plus-1 midx-n-is-next-row
                                      midx-row-n-is-sq teval-a-of-mmt-row-end))
          ("Subgoal *1/2" :expand ((teval-a n (mmt n) D F c (midx n (floor c n) h)))
                          :use ((:instance midx-plus-1 (k (floor c n)))
                                (:instance floor-bound (a c))))
          ("Subgoal *1/1" :in-theory (disable midx-equal-iff teval-a-of-mmt-above midx-plus-1
                                              midx-n-is-next-row midx-row-n-is-sq)
                          :use ((:instance teval-a-of-mmt-row-end))
                          :expand ((mm-entry n D F (floor c n) (mod c n) h)))))

;; ... and rows below k contribute nothing either.
(defthm floor-lt-when-lt-mult
  (implies (and (natp a) (posp n) (natp k) (< a (* k n)))
           (< (floor a n) k))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

(defthm teval-a-of-mmt-below
  (implies (and (posp n) (natp c) (< c (sq n)) (natp a) (<= a (midx n (floor c n) 0))
                (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (teval-a n (mmt n) D F c a)
                  (teval-a n (mmt n) D F c (midx n (floor c n) 0))))
  :hints (("Goal" :induct (teval-a n (mmt n) D F c a)
                  :in-theory (e/d (midx) (floor-lt-when-lt-mult)))
          ("Subgoal *1/2" :use ((:instance floor-lt-when-lt-mult (k (floor c n)))))))

(defthm teval-a0-of-mmt
  (implies (and (posp n) (natp c) (< c (sq n))
                (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (teval-a n (mmt n) D F c 0)
                  (mm-entry n D F (floor c n) (mod c n) 0)))
  :hints (("Goal" :in-theory (disable teval-a-of-mmt-in-row teval-a-of-mmt-below)
                  :use ((:instance teval-a-of-mmt-below (a 0))
                        (:instance teval-a-of-mmt-in-row (h 0))))))

(defthm teval-from-of-mmt
  (implies (and (posp n) (natp idx)
                (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (teval-from n (mmt n) D F idx) (matmul-from n D F idx)))
  :hints (("Goal" :induct (teval-from n (mmt n) D F idx))))

;; Definition 2.1, existence: M^(n) satisfies (DF) = sum M D F for all D, F.
(defthm mmt-satisfies-definition
  (implies (and (posp n) (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
           (equal (tensor-eval n (mmt n) D F) (matmul n D F))))

;;; ------------------------------------------------------------------
;;; Definition 2.1, uniqueness
;;; ------------------------------------------------------------------

;; Evaluating any tensor on the basis matrices E_a0, E_b0 reads off its
;; coefficients.
(defthm teval-b-on-units
  (implies (and (posp n) (natp a) (< a (sq n)) (natp c) (< c (sq n))
                (natp a0) (< a0 (sq n)) (natp b0) (< b0 (sq n))
                (natp b) (<= b (sq n))
                (bvp T3) (equal (len T3) (tlen (sq n))))
           (equal (teval-b n T3 (unit (sq n) a0) (unit (sq n) b0) a c b)
                  (if (and (equal a a0) (<= b b0))
                      (nth (tidx3 (sq n) (sq n) a0 b0 c) T3)
                    0)))
  :hints (("Goal" :induct (teval-b n T3 (unit (sq n) a0) (unit (sq n) b0) a c b))))

(defthm teval-a-on-units
  (implies (and (posp n) (natp c) (< c (sq n))
                (natp a0) (< a0 (sq n)) (natp b0) (< b0 (sq n))
                (natp a) (<= a (sq n))
                (bvp T3) (equal (len T3) (tlen (sq n))))
           (equal (teval-a n T3 (unit (sq n) a0) (unit (sq n) b0) c a)
                  (if (<= a a0)
                      (nth (tidx3 (sq n) (sq n) a0 b0 c) T3)
                    0)))
  :hints (("Goal" :induct (teval-a n T3 (unit (sq n) a0) (unit (sq n) b0) c a)
                  :in-theory (disable teval-b-on-units unit nth-of-unit teval-b))
          ("Subgoal *1/2" :use ((:instance teval-b-on-units (b 0))))))

(defun ind-idx-i (n idx i)
  (declare (xargs :measure (nfix (- (sq n) idx))))
  (if (or (not (natp n)) (not (natp idx)) (>= idx (sq n)))
      (list n idx i)
    (ind-idx-i n (1+ idx) (1- i))))

(defthm nth-of-teval-from
  (implies (and (posp n) (natp idx) (natp i) (< (+ idx i) (sq n)))
           (equal (nth i (teval-from n T3 D F idx))
                  (teval-a n T3 D F (+ idx i) 0)))
  :hints (("Goal" :induct (ind-idx-i n idx i)
                  :in-theory (disable teval-a))))

(defthm nth-of-tensor-eval-on-units
  (implies (and (posp n) (natp c) (< c (sq n))
                (natp a0) (< a0 (sq n)) (natp b0) (< b0 (sq n))
                (bvp T3) (equal (len T3) (tlen (sq n))))
           (equal (nth c (tensor-eval n T3 (unit (sq n) a0) (unit (sq n) b0)))
                  (nth (tidx3 (sq n) (sq n) a0 b0 c) T3)))
  :hints (("Goal" :in-theory (disable nth-of-teval-from)
                  :use ((:instance nth-of-teval-from (idx 0) (i c) (D (unit (sq n) a0)) (F (unit (sq n) b0)))))))

;; "T satisfies the defining equation for all D, F"
(defun-sk satisfies-mm-equation (n T3)
  (forall (D F)
          (implies (and (bvp D) (equal (len D) (sq n)) (bvp F) (equal (len F) (sq n)))
                   (equal (tensor-eval n T3 D F) (matmul n D F)))))

;; Coefficient (a0,b0,c) of any such T equals that of M^(n).
(defthm satisfies-mm-equation-coefficient
  (implies (and (posp n) (satisfies-mm-equation n T3)
                (bvp T3) (equal (len T3) (tlen (sq n)))
                (natp a0) (< a0 (sq n)) (natp b0) (< b0 (sq n)) (natp c) (< c (sq n)))
           (equal (nth (tidx3 (sq n) (sq n) a0 b0 c) T3)
                  (nth (tidx3 (sq n) (sq n) a0 b0 c) (mmt n))))
  :hints (("Goal" :in-theory (disable satisfies-mm-equation nth-of-tensor-eval-on-units
                                      mmt-satisfies-definition tensor-eval matmul)
                  :use ((:instance satisfies-mm-equation-necc (D (unit (sq n) a0)) (F (unit (sq n) b0)))
                        (:instance nth-of-tensor-eval-on-units)
                        (:instance nth-of-tensor-eval-on-units (T3 (mmt n)))
                        (:instance mmt-satisfies-definition (D (unit (sq n) a0)) (F (unit (sq n) b0)))))))

;; Decoding a tensor index into its three coordinates.
(defun tidx-a (L idx) (floor idx (* L L)))
(defun tidx-b (L idx) (floor (mod idx (* L L)) L))
(defun tidx-c (L idx) (mod (mod idx (* L L)) L))

(defthm tidx3-decode
  (implies (and (posp L) (natp idx) (< idx (tlen L)))
           (and (natp (tidx-a L idx)) (< (tidx-a L idx) L)
                (natp (tidx-b L idx)) (< (tidx-b L idx) L)
                (natp (tidx-c L idx)) (< (tidx-c L idx) L)
                (equal (tidx3 L L (tidx-a L idx) (tidx-b L idx) (tidx-c L idx)) idx)))
  :hints (("Goal" :in-theory (e/d (tidx3) (floor-lt-when-lt-mult mod-bound))
                  :do-not-induct t
                  :use ((:instance floor-mod-decompose (a idx) (n (* L L)))
                        (:instance floor-mod-decompose (a (mod idx (* L L))) (n L))
                        (:instance floor-lt-when-lt-mult (a idx) (n (* L L)) (k L))
                        (:instance floor-lt-when-lt-mult (a (mod idx (* L L))) (n L) (k L))
                        (:instance mod-bound (a idx) (n (* L L)))
                        (:instance mod-bound (a (mod idx (* L L))) (n L))))))

(in-theory (disable tidx-a tidx-b tidx-c))

;; Definition 2.1, uniqueness: any tensor satisfying the equation is M^(n).
(defthm mmt-unique
  (implies (and (posp n) (bvp T3) (equal (len T3) (tlen (sq n)))
                (satisfies-mm-equation n T3))
           (equal T3 (mmt n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable satisfies-mm-equation-coefficient tidx3-decode
                                      bv-diff-index-witness satisfies-mm-equation)
                  :use ((:instance bv-extensionality (x T3) (y (mmt n)))
                        (:instance bv-diff-index-witness (x T3) (y (mmt n)))
                        (:instance tidx3-decode (L (sq n)) (idx (bv-diff-index T3 (mmt n))))
                        (:instance satisfies-mm-equation-coefficient
                                   (a0 (tidx-a (sq n) (bv-diff-index T3 (mmt n))))
                                   (b0 (tidx-b (sq n) (bv-diff-index T3 (mmt n))))
                                   (c (tidx-c (sq n) (bv-diff-index T3 (mmt n)))))))))
