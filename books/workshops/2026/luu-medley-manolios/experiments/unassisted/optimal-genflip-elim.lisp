; optimal-genflip-elim.lisp -- Appendix B, part 4: the elimination that
; realizes the optimal generalized flip.
;
; Part 4a (this section): elementary pair flips
;     flip(i,j):  X_j += X_i,  Y_i += Y_j
; preserve the order-2 tensor, commute with changes of basis (so a whole
; sequence of flips applied to (B, C) equals a single change of basis
; (BG, G^{-1}C) where (G, G^{-1}) are obtained by applying the same
; sequence to (I, I)), and the resulting (G, G^{-1}) is invertible in the
; sense of genflip-basis.lisp (sum_j g_j (x) h_j = I).

(in-package "ACL2")

(include-book "optimal-genflip")

;;; ------------------------------------------------------------------
;;; update-nth bookkeeping
;;; ------------------------------------------------------------------

(defthm nth-of-update-nth-diff-local
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (nth i (update-nth j v x)) (nth i x))))

(defthm nth-of-update-nth-same-local
  (implies (natp j)
           (equal (nth j (update-nth j v x)) v)))

(defthm update-nth-of-update-nth-same-local
  (implies (natp j)
           (equal (update-nth j a (update-nth j b x)) (update-nth j a x))))

(defthm update-nth-of-update-nth-diff-local
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (update-nth i a (update-nth j b x))
                  (update-nth j b (update-nth i a x))))
  :rule-classes nil)

;;; ------------------------------------------------------------------
;;; A flip preserves the tensor
;;; ------------------------------------------------------------------

;; Peeling one pair out of T2 (zeroing both entries).
(defthm T2-peel
  (implies (and (natp LB) (natp LC) (bv-listp LB Xs) (bv-listp LC Ys) (equal (len Xs) (len Ys))
                (natp k) (< k (len Xs)))
           (equal (T2 LB LC Xs Ys)
                  (bv+ (outer (nth k Xs) (nth k Ys))
                       (T2 LB LC (update-nth k (bv-zero LB) Xs) (update-nth k (bv-zero LC) Ys)))))
  :rule-classes nil
  :hints (("Goal" :induct (ind-2lists-nat2 Xs Ys k))))

(defthm bvp-facts-T2
  (implies (and (natp LB) (natp LC) (bv-listp LB Xs) (bv-listp LC Ys) (equal (len Xs) (len Ys)))
           (and (bvp (T2 LB LC Xs Ys)) (equal (len (T2 LB LC Xs Ys)) (* LB LC)))))

;; flip(i,j) leaves sum_k X_k (x) Y_k unchanged:
;;   X_i (x) (Y_i + Y_j) + (X_j + X_i) (x) Y_j = X_i (x) Y_i + X_j (x) Y_j.
(defthm T2-of-flip
  (implies (and (natp L) (bv-listp L Xs) (bv-listp L Ys) (equal (len Xs) (len Ys))
                (natp i) (natp j) (not (equal i j)) (< i (len Xs)) (< j (len Xs)))
           (equal (T2 L L (flipX i j Xs) (flipY i j Ys))
                  (T2 L L Xs Ys)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable bv-listp-member)
                  :use ((:instance T2-peel (LB L) (LC L) (k i))
                        (:instance T2-peel (LB L) (LC L) (k j)
                                   (Xs (update-nth i (bv-zero L) Xs))
                                   (Ys (update-nth i (bv-zero L) Ys)))
                        (:instance T2-peel (LB L) (LC L) (k i)
                                   (Xs (flipX i j Xs)) (Ys (flipY i j Ys)))
                        (:instance T2-peel (LB L) (LC L) (k j)
                                   (Xs (update-nth i (bv-zero L) (flipX i j Xs)))
                                   (Ys (update-nth i (bv-zero L) (flipY i j Ys))))
                        (:instance update-nth-of-update-nth-diff-local
                                   (a (bv-zero L)) (b (bv+ (nth j Xs) (nth i Xs))) (x Xs))
                        (:instance update-nth-of-update-nth-diff-local
                                   (a (bv-zero L)) (b (bv-zero L)) (x Xs))
                        (:instance update-nth-of-update-nth-diff-local
                                   (a (bv-zero L)) (b (bv-zero L)) (x Ys))))))

;;; ------------------------------------------------------------------
;;; Flips commute with changes of basis
;;; ------------------------------------------------------------------

(defthm nth-of-new-facs
  (implies (and (natp j) (< j (len gs)))
           (equal (nth j (new-facs L Vs gs)) (col-comb L Vs (nth j gs))))
  :hints (("Goal" :induct (ind-xk gs j))))

(defthm new-facs-of-update-nth
  (implies (and (natp j) (< j (len gs)))
           (equal (new-facs L Vs (update-nth j w gs))
                  (update-nth j (col-comb L Vs w) (new-facs L Vs gs))))
  :hints (("Goal" :induct (ind-xk gs j))))

;; flip(i,j) on (BG) equals (B G') where G' is flip(i,j) applied to the
;; columns of G; likewise for the rows of G^{-1}.
(defthm flipX-of-new-facs
  (implies (and (natp L) (bv-listp L Vs) (bv-listp (len Vs) gs)
                (natp i) (natp j) (< i (len gs)) (< j (len gs)))
           (equal (flipX i j (new-facs L Vs gs))
                  (new-facs L Vs (flipX i j gs))))
  :hints (("Goal" :in-theory (disable col-comb-of-bv+ bv-listp-member)
                  :use ((:instance col-comb-of-bv+ (Cs Vs) (m (nth j gs)) (m2 (nth i gs)))
                        (:instance bv-listp-nth (L (len Vs)) (Xs gs) (j i))
                        (:instance bv-listp-nth (L (len Vs)) (Xs gs) (j j))))))

(defthm flipY-of-new-facs
  (implies (and (natp L) (bv-listp L Vs) (bv-listp (len Vs) hs)
                (natp i) (natp j) (< i (len hs)) (< j (len hs)))
           (equal (flipY i j (new-facs L Vs hs))
                  (new-facs L Vs (flipY i j hs))))
  :hints (("Goal" :in-theory (disable col-comb-of-bv+ bv-listp-member)
                  :use ((:instance col-comb-of-bv+ (Cs Vs) (m (nth i hs)) (m2 (nth j hs)))
                        (:instance bv-listp-nth (L (len Vs)) (Xs hs) (j i))
                        (:instance bv-listp-nth (L (len Vs)) (Xs hs) (j j))))))

;;; ------------------------------------------------------------------
;;; The identity change of basis
;;; ------------------------------------------------------------------

(defun ind-up (N i)
  (declare (xargs :measure (nfix (- N i))))
  (if (or (not (natp N)) (not (natp i)) (>= i N)) (list N i) (ind-up N (1+ i))))

(defthm new-facs-of-id-rows-from
  (implies (and (natp L) (bv-listp L Vs) (natp i) (<= i (len Vs)))
           (equal (new-facs L Vs (id-rows-from (len Vs) i)) (nthcdr i Vs)))
  :hints (("Goal" :induct (ind-up (len Vs) i)
                  :in-theory (disable col-comb-of-unit))
          ("Subgoal *1/2" :expand ((id-rows-from (len Vs) i))
                          :use ((:instance col-comb-of-unit (Cs Vs) (N (len Vs)))))
          ("Subgoal *1/1" :expand ((id-rows-from (len Vs) i)))))

(defthm new-facs-of-identity-rows
  (implies (and (natp L) (bv-listp L Vs))
           (equal (new-facs L Vs (identity-rows (len Vs))) Vs))
  :hints (("Goal" :use ((:instance new-facs-of-id-rows-from (i 0))))))

;;; ------------------------------------------------------------------
;;; Invertibility, entry by entry
;;; ------------------------------------------------------------------

;; Row k of sum_j g_j (x) h_j is sum_j (g_j)_k h_j.
(defthm len-of-rows-outer-local (equal (len (rows-outer g h)) (len g)))

(defthm nth-of-rows+
  (implies (and (natp k) (< k (len M1)))
           (equal (nth k (rows+ M1 M2)) (bv+ (nth k M1) (nth k M2))))
  :hints (("Goal" :induct (ind-2lists-nat2 M1 M2 k))))

(defthm nth-of-rows-outer
  (implies (and (natp k) (< k (len g)))
           (equal (nth k (rows-outer g h)) (bv-scale (nth k g) h)))
  :hints (("Goal" :induct (ind-xk g k))))

(defun ind-nat-nat (a b) (if (zp a) (list a b) (ind-nat-nat (1- a) (1- b))))

(defthm nth-of-zero-rows-of
  (implies (and (natp k) (< k (nfix NB)))
           (equal (nth k (zero-rows-of NB NC)) (bv-zero NC)))
  :hints (("Goal" :induct (ind-nat-nat NB k))))

(defthm nth-of-rows-sum2
  (implies (and (natp NB) (natp NC) (bv-listp NB gs) (bv-listp NC hs) (equal (len gs) (len hs))
                (natp k) (< k NB))
           (equal (nth k (rows-sum2 NB NC gs hs))
                  (col-comb NC hs (coords-at k gs))))
  :hints (("Goal" :induct (ind-2lists gs hs)
                  :in-theory (disable bv-listp-member))))

;; Entry (k,q) of sum_j g_j (x) h_j (rows form) is coordinate (k,q) of the
;; flat tensor T2.
(defthm entry-of-rows-sum2
  (implies (and (natp N) (bv-listp N gs) (bv-listp N hs) (equal (len gs) (len hs))
                (natp k) (< k N) (natp q) (< q N))
           (equal (nth q (nth k (rows-sum2 N N gs hs)))
                  (nth (+ (* k N) q) (T2 N N gs hs))))
  :hints (("Goal" :in-theory (disable nth-of-rows-sum2 nth-of-col-comb-coords nth-of-T2)
                  :use ((:instance nth-of-rows-sum2 (NB N) (NC N))
                        (:instance nth-of-col-comb-coords (L N) (Us gs) (Vs hs) (p k))
                        (:instance nth-of-T2 (L N) (Us gs) (Vs hs) (p k))))))

;; Entries of the identity rows.
(defun ind-up-down (i k) (if (zp k) (list i k) (ind-up-down (1+ i) (1- k))))

(defthm nth-of-id-rows-from
  (implies (and (natp N) (natp i) (natp k) (< (+ i k) N))
           (equal (nth k (id-rows-from N i)) (unit N (+ i k))))
  :hints (("Goal" :induct (ind-up-down i k))
          ("Subgoal *1/2" :expand ((id-rows-from N i)))
          ("Subgoal *1/1" :expand ((id-rows-from N i)))))
