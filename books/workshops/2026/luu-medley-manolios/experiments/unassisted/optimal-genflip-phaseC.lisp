; optimal-genflip-phaseC.lisp -- Appendix B, part 4c: eliminating a
; dependency among the C factors.  Given a nonzero selection sel of rows
; (all live pivots) with sum_{i in sel} Y_i = 0 and r = the first selected
; row, flip(r,i) for every other selected i:  X_i += X_r, Y_r += Y_i.
; Afterwards Y_r = sum_{i in sel} Y_i = 0, so pair r is dead, while the
; pivot columns of the other live pivots are unchanged.

(in-package "ACL2")

(include-book "optimal-genflip-phaseB")

;; For i = i0..N-1 with i /= r and sel_i = 1: flip(r,i).
(defun dep-elim (r sel i Xs Ys gs hs N)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- N i))))
  (if (or (not (natp N)) (not (natp i)) (>= i N))
      (mv Xs Ys gs hs)
    (if (and (not (equal i r)) (equal (nth i sel) 1))
        (dep-elim r sel (1+ i) (flipX r i Xs) (flipY r i Ys) (flipX r i gs) (flipY r i hs) N)
      (dep-elim r sel (1+ i) Xs Ys gs hs N))))

;; xor of Y_i over i = i0..N-1 with i /= r and sel_i = 1.
(defun sel-sum-from (L Ys sel r i N)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- N i))))
  (if (or (not (natp N)) (not (natp i)) (>= i N))
      (bv-zero L)
    (if (and (not (equal i r)) (equal (nth i sel) 1))
        (bv+ (nth i Ys) (sel-sum-from L Ys sel r (1+ i) N))
      (sel-sum-from L Ys sel r (1+ i) N))))

(defthm dep-elim-shape
  (implies (and (natp L) (natp N) (natp r) (< r N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))
           (mv-let (Xs2 Ys2 gs2 hs2) (dep-elim r sel i Xs Ys gs hs N)
             (and (bv-listp L Xs2) (bv-listp L Ys2) (bv-listp N gs2) (bv-listp N hs2)
                  (equal (len Xs2) N) (equal (len Ys2) N) (equal (len gs2) N) (equal (len hs2) N))))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable bv-listp-member flipX flipY))))

(defthm dep-elim-simulation
  (implies (and (natp L) (natp N) (natp r) (< r N)
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) N) (equal (len Cs) N)
                (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N)
                (equal Xs (new-facs L Bs gs)) (equal Ys (new-facs L Cs hs)))
           (mv-let (Xs2 Ys2 gs2 hs2) (dep-elim r sel i Xs Ys gs hs N)
             (and (equal Xs2 (new-facs L Bs gs2))
                  (equal Ys2 (new-facs L Cs hs2)))))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member flipX-of-new-facs flipY-of-new-facs))
          ("Subgoal *1/2" :use ((:instance flipX-of-new-facs (Vs Bs) (i r) (j i))
                                (:instance flipY-of-new-facs (Vs Cs) (i r) (j i))))))

(defthm dep-elim-T2
  (implies (and (natp L) (natp N) (natp r) (< r N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))
           (mv-let (Xs2 Ys2 gs2 hs2) (dep-elim r sel i Xs Ys gs hs N)
             (and (equal (T2 N N gs2 hs2) (T2 N N gs hs))
                  (equal (T2 L L Xs2 Ys2) (T2 L L Xs Ys)))))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member T2-of-flip))
          ("Subgoal *1/2" :use ((:instance T2-of-flip (i r) (j i))
                                (:instance T2-of-flip (i r) (j i) (L N) (Xs gs) (Ys hs))))))

;; Row r of X and rows i /= r of Y are unchanged.
(defthm nth-of-flipY-other
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (nth i (flipY j k Ys)) (nth i Ys))))

(defthm dep-elim-row-r-X
  (implies (and (natp N) (natp r) (< r N))
           (equal (nth r (mv-nth 0 (dep-elim r sel i Xs Ys gs hs N))) (nth r Xs)))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX flipY))))

(defthm dep-elim-other-Y
  (implies (and (natp N) (natp r) (< r N) (natp i2) (not (equal i2 r)))
           (equal (nth i2 (mv-nth 1 (dep-elim r sel i Xs Ys gs hs N))) (nth i2 Ys)))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX flipY))))

;; Rows not selected (and row r) keep their X.
(defthm dep-elim-unselected-X
  (implies (and (natp N) (natp r) (< r N) (natp i2)
                (or (equal i2 r) (not (equal (nth i2 sel) 1))))
           (equal (nth i2 (mv-nth 0 (dep-elim r sel i Xs Ys gs hs N))) (nth i2 Xs)))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX flipY))
          ("Subgoal *1/2" :cases ((equal i2 i)))))

;; Rows below the loop index are untouched.
(defthm dep-elim-below
  (implies (and (natp N) (natp r) (< r N) (natp i2) (natp i) (< i2 i))
           (equal (nth i2 (mv-nth 0 (dep-elim r sel i Xs Ys gs hs N))) (nth i2 Xs)))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX flipY))))

;; Selected rows i /= r get X_i + X_r (row r never changes).
(defthm dep-elim-selected-X
  (implies (and (natp L) (natp N) (natp r) (< r N) (natp i2) (< i2 N) (natp i) (<= i i2)
                (not (equal i2 r)) (equal (nth i2 sel) 1)
                (bv-listp L Xs) (equal (len Xs) N))
           (equal (nth i2 (mv-nth 0 (dep-elim r sel i Xs Ys gs hs N)))
                  (bv+ (nth i2 Xs) (nth r Xs))))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member dep-elim-below))
          ("Subgoal *1/2" :cases ((equal i2 i))
                          :use ((:instance dep-elim-below (i (1+ i)) (i2 i)
                                           (Xs (flipX r i Xs)) (Ys (flipY r i Ys))
                                           (gs (flipX r i gs)) (hs (flipY r i hs)))))
          ("Subgoal *1/2.1" :in-theory (e/d (flipX) (flipY bv-listp-member dep-elim-below)))))

;; sel-sum-from skips row r, so updates at r do not affect it.
(defthm sel-sum-from-of-update-nth-r
  (implies (natp r)
           (equal (sel-sum-from L (update-nth r v Ys) sel r i N)
                  (sel-sum-from L Ys sel r i N)))
  :hints (("Goal" :induct (sel-sum-from L Ys sel r i N))))

(defthm bv-facts-of-sel-sum-from
  (implies (and (natp L) (bv-listp L Ys) (natp N) (equal (len Ys) N))
           (and (bvp (sel-sum-from L Ys sel r i N))
                (equal (len (sel-sum-from L Ys sel r i N)) L)))
  :hints (("Goal" :induct (sel-sum-from L Ys sel r i N) :in-theory (disable bv-listp-member))))

;; Row r of Y accumulates the selected Y's (which themselves never change).
(defthm dep-elim-row-r-Y
  (implies (and (natp L) (natp N) (natp r) (< r N)
                (bv-listp L Ys) (equal (len Ys) N))
           (equal (nth r (mv-nth 1 (dep-elim r sel i Xs Ys gs hs N)))
                  (bv+ (nth r Ys) (sel-sum-from L Ys sel r i N))))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX bv-listp-member))
          ("Subgoal *1/2" :in-theory (e/d (flipY) (flipX bv-listp-member))
                          :use ((:instance bv-listp-nth (Xs Ys) (j i))
                                (:instance bv-listp-nth (Xs Ys) (j r))))))

;; Pivot columns of pivots i' /= r are unchanged.
(defthm dep-elim-other-column
  (implies (and (natp L) (natp N) (natp r) (< r N) (natp p2) (< p2 L)
                (natp i2) (not (equal i2 r)) (< i2 N)
                (bv-listp L Xs) (equal (len Xs) N)
                (equal (coords-at p2 Xs) (unit N i2)))
           (equal (coords-at p2 (mv-nth 0 (dep-elim r sel i Xs Ys gs hs N))) (unit N i2)))
  :hints (("Goal" :induct (dep-elim r sel i Xs Ys gs hs N)
                  :in-theory (disable flipX flipY bv-listp-member coords-at-of-flipX-other-pivot))
          ("Subgoal *1/2" :use ((:instance coords-at-of-flipX-other-pivot (p p2) (k r) (j i) (i i2))))))
