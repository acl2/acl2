; optimal-genflip-phaseB.lisp -- Appendix B, part 4b: Gauss-Jordan
; elimination on the B side by pair flips.
;
; State: (Xs Ys gs hs), all lists of N vectors, with the invariants
;   Xs = (new-facs L Bs gs), Ys = (new-facs L Cs hs), T2(gs,hs) = T2(I,I)
; maintained by every flip (optimal-genflip-elim.lisp).  Phase B walks
; k = 0..N-1; if X_k /= 0 it takes the pivot p_k = first set bit of X_k
; and flips (k -> j) for every j /= k with X_j[p_k] = 1.  Afterwards,
; column p_k of the X-matrix, i.e. (coords-at p_k Xs), is the unit
; vector e_k, and this stays true for all later steps.

(in-package "ACL2")

(include-book "optimal-genflip-elim")

;;; ------------------------------------------------------------------
;;; Columns of the X matrix under flips
;;; ------------------------------------------------------------------

(defthm coords-at-of-update-nth
  (implies (and (natp j) (< j (len Xs)))
           (equal (coords-at p (update-nth j v Xs))
                  (update-nth j (nth p v) (coords-at p Xs))))
  :hints (("Goal" :induct (ind-xk Xs j))))

(defthm nth-of-coords-at
  (implies (and (natp j) (< j (len Xs)))
           (equal (nth j (coords-at p Xs)) (nth p (nth j Xs))))
  :hints (("Goal" :induct (ind-xk Xs j))))

;; Column p after flip(k,j): coordinate j gets X_j[p] + X_k[p].
(defthm coords-at-of-flipX
  (implies (and (natp L) (bv-listp L Xs) (natp k) (natp j) (< k (len Xs)) (< j (len Xs))
                (natp p) (< p L))
           (equal (coords-at p (flipX k j Xs))
                  (update-nth j (bxor (nth p (nth j Xs)) (nth p (nth k Xs))) (coords-at p Xs))))
  :hints (("Goal" :in-theory (disable bv-listp-member)
                  :use ((:instance bv-listp-nth (j j)) (:instance bv-listp-nth (j k))))))

;; A column that is e_i with i /= k is unchanged by flip(k,j).
(defthm coords-at-of-flipX-other-pivot
  (implies (and (natp L) (bv-listp L Xs) (natp k) (natp j) (< k (len Xs)) (< j (len Xs))
                (natp p) (< p L) (natp i) (not (equal i k)) (< i (len Xs))
                (equal (coords-at p Xs) (unit (len Xs) i)))
           (equal (coords-at p (flipX k j Xs)) (coords-at p Xs)))
  :hints (("Goal" :in-theory (disable coords-at-of-flipX nth-of-coords-at)
                  :use (coords-at-of-flipX
                        (:instance nth-of-coords-at (j k))
                        (:instance nth-of-coords-at (j j))))))

;; Rows other than j are unchanged by flip(k,j); row k in particular.
(defthm nth-of-flipX-other
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (nth i (flipX k j Xs)) (nth i Xs))))

;;; ------------------------------------------------------------------
;;; Eliminating pivot p of row k from all other rows
;;; ------------------------------------------------------------------

;; For j = j0, ..., N-1: if j /= k and X_j[p] = 1 then flip(k,j).
(defun elim-col (k p j Xs Ys gs hs N)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- N j))))
  (if (or (not (natp N)) (not (natp j)) (>= j N))
      (mv Xs Ys gs hs)
    (if (and (not (equal j k)) (equal (nth p (nth j Xs)) 1))
        (elim-col k p (1+ j) (flipX k j Xs) (flipY k j Ys) (flipX k j gs) (flipY k j hs) N)
      (elim-col k p (1+ j) Xs Ys gs hs N))))

;; (agrees-below col k j) : for all i < j, col_i = [i = k].
(defun agrees-below (col k j)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp j) t
    (and (equal (nth (1- j) col) (if (equal (1- j) k) 1 0))
         (agrees-below col k (1- j)))))

(defthm agrees-below-nth
  (implies (and (agrees-below col k j) (natp j) (natp i) (< i j))
           (equal (nth i col) (if (equal i k) 1 0)))
  :hints (("Goal" :induct (agrees-below col k j))))

(defthm agrees-below-all-is-unit
  (implies (and (bvp col) (equal (len col) N) (natp N) (natp k) (< k N)
                (agrees-below col k N))
           (equal col (unit N k)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable agrees-below-nth bv-diff-index-witness)
                  :use ((:instance bv-extensionality (x col) (y (unit N k)))
                        (:instance bv-diff-index-witness (x col) (y (unit N k)))
                        (:instance agrees-below-nth (i (bv-diff-index col (unit N k))) (j N))))))

(defthm agrees-below-of-update-nth-above
  (implies (and (natp j) (natp j2) (<= j j2))
           (equal (agrees-below (update-nth j2 v col) k j)
                  (agrees-below col k j)))
  :hints (("Goal" :induct (agrees-below col k j))))

(defthm agrees-below-step
  (implies (natp j)
           (equal (agrees-below col k (1+ j))
                  (and (equal (nth j col) (if (equal j k) 1 0))
                       (agrees-below col k j)))))

(in-theory (disable agrees-below))

;;; ------------------------------------------------------------------
;;; Invariants of elim-col
;;; ------------------------------------------------------------------

;; Lists stay well formed.
(defthm elim-col-shape
  (implies (and (natp L) (natp N) (natp k) (< k N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))
           (mv-let (Xs2 Ys2 gs2 hs2) (elim-col k p j Xs Ys gs hs N)
             (and (bv-listp L Xs2) (bv-listp L Ys2) (bv-listp N gs2) (bv-listp N hs2)
                  (equal (len Xs2) N) (equal (len Ys2) N) (equal (len gs2) N) (equal (len hs2) N))))
  :hints (("Goal" :induct (elim-col k p j Xs Ys gs hs N)
                  :in-theory (disable bv-listp-member flipX flipY))))

;; Row k is never changed.
(defthm elim-col-row-k
  (implies (and (natp N) (natp k) (< k N))
           (equal (nth k (mv-nth 0 (elim-col k p j Xs Ys gs hs N))) (nth k Xs)))
  :hints (("Goal" :induct (elim-col k p j Xs Ys gs hs N)
                  :in-theory (disable flipX flipY))))

;; A zero row stays zero.
(defthm elim-col-zero-row
  (implies (and (natp L) (natp N) (natp k) (< k N) (natp i) (< i N) (natp p) (< p L)
                (bv-listp L Xs) (equal (len Xs) N)
                (equal (nth i Xs) (bv-zero L)))
           (equal (nth i (mv-nth 0 (elim-col k p j Xs Ys gs hs N))) (bv-zero L)))
  :hints (("Goal" :induct (elim-col k p j Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member))
          ("Subgoal *1/2" :cases ((equal i j)))))

;; The pivot column becomes e_k.
(defthm elim-col-pivot-column
  (implies (and (natp L) (natp N) (natp k) (< k N) (natp p) (< p L) (natp j) (<= j N)
                (bv-listp L Xs) (equal (len Xs) N)
                (equal (nth p (nth k Xs)) 1)
                (agrees-below (coords-at p Xs) k j))
           (agrees-below (coords-at p (mv-nth 0 (elim-col k p j Xs Ys gs hs N))) k N))
  :hints (("Goal" :induct (elim-col k p j Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member coords-at-of-flipX))
          ("Subgoal *1/2" :use ((:instance coords-at-of-flipX)))))

;; Other unit columns are preserved.
(defthm elim-col-other-column
  (implies (and (natp L) (natp N) (natp k) (< k N) (natp p2) (< p2 L)
                (natp i) (not (equal i k)) (< i N)
                (bv-listp L Xs) (equal (len Xs) N)
                (equal (coords-at p2 Xs) (unit N i)))
           (equal (coords-at p2 (mv-nth 0 (elim-col k p j Xs Ys gs hs N))) (unit N i)))
  :hints (("Goal" :induct (elim-col k p j Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member coords-at-of-flipX-other-pivot))
          ("Subgoal *1/2" :use ((:instance coords-at-of-flipX-other-pivot (p p2))))))

;; Simulation: the state is always a change of basis of the original.
(defthm elim-col-simulation
  (implies (and (natp L) (natp N) (natp k) (< k N)
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) N) (equal (len Cs) N)
                (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N)
                (equal Xs (new-facs L Bs gs)) (equal Ys (new-facs L Cs hs)))
           (mv-let (Xs2 Ys2 gs2 hs2) (elim-col k p j Xs Ys gs hs N)
             (and (equal Xs2 (new-facs L Bs gs2))
                  (equal Ys2 (new-facs L Cs hs2)))))
  :hints (("Goal" :induct (elim-col k p j Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member flipX-of-new-facs flipY-of-new-facs))
          ("Subgoal *1/2" :use ((:instance flipX-of-new-facs (Vs Bs) (i k))
                                (:instance flipY-of-new-facs (Vs Cs) (i k))))))

;; The tensor T2(gs,hs) (hence invertibility) and T2(Xs,Ys) are preserved.
(defthm elim-col-T2
  (implies (and (natp L) (natp N) (natp k) (< k N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))
           (mv-let (Xs2 Ys2 gs2 hs2) (elim-col k p j Xs Ys gs hs N)
             (and (equal (T2 N N gs2 hs2) (T2 N N gs hs))
                  (equal (T2 L L Xs2 Ys2) (T2 L L Xs Ys)))))
  :hints (("Goal" :induct (elim-col k p j Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member T2-of-flip))
          ("Subgoal *1/2" :use ((:instance T2-of-flip (i k))
                                (:instance T2-of-flip (i k) (L N) (Xs gs) (Ys hs))))))
