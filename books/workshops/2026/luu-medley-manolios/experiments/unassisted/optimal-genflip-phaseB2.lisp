; optimal-genflip-phaseB2.lisp -- Appendix B, part 4b (end): the phase-B
; driver.  For k = 0..N-1, if X_k /= 0 take p_k = first set bit of X_k
; and eliminate it from all other rows.  Afterwards every nonzero row k
; has a pivot coordinate p_k with (coords-at p_k Xs) = e_k.

(in-package "ACL2")

(include-book "optimal-genflip-phaseB")

;; PL is a list of pivot coordinates (one per row; irrelevant for zero rows).
;; (pivots-ok L N Xs PL k): for every i < k, either X_i = 0 or p_i < L and
;; column p_i of X is e_i.
(defun pivots-ok (L N Xs PL k)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp k) t
    (and (or (equal (nth (1- k) Xs) (bv-zero L))
             (and (natp (nth (1- k) PL)) (< (nth (1- k) PL) L)
                  (equal (coords-at (nth (1- k) PL) Xs) (unit N (1- k)))))
         (pivots-ok L N Xs PL (1- k)))))

(defthm pivots-ok-nth
  (implies (and (pivots-ok L N Xs PL k) (natp k) (natp i) (< i k))
           (or (equal (nth i Xs) (bv-zero L))
               (and (natp (nth i PL)) (< (nth i PL) L)
                    (equal (coords-at (nth i PL) Xs) (unit N i)))))
  :rule-classes nil
  :hints (("Goal" :induct (pivots-ok L N Xs PL k))))

(defthm pivots-ok-step
  (implies (natp k)
           (equal (pivots-ok L N Xs PL (1+ k))
                  (and (or (equal (nth k Xs) (bv-zero L))
                           (and (natp (nth k PL)) (< (nth k PL) L)
                                (equal (coords-at (nth k PL) Xs) (unit N k))))
                       (pivots-ok L N Xs PL k)))))

(in-theory (disable pivots-ok))

(defun phaseB (k Xs Ys gs hs N PL L)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- N k))))
  (if (or (not (natp N)) (not (natp k)) (>= k N))
      (mv Xs Ys gs hs PL)
    (if (equal (nth k Xs) (bv-zero L))
        (phaseB (1+ k) Xs Ys gs hs N PL L)
      (let ((p (bv-first-one (nth k Xs))))
        (mv-let (Xs2 Ys2 gs2 hs2) (elim-col k p 0 Xs Ys gs hs N)
          (phaseB (1+ k) Xs2 Ys2 gs2 hs2 N (update-nth k p PL) L))))))

;; pivots-ok is preserved by elim-col for rows i < k (i /= k).
(defthm elim-col-preserves-pivots-ok
  (implies (and (natp L) (natp N) (natp k) (< k N) (natp p) (< p L) (natp k0) (<= k0 k)
                (bv-listp L Xs) (equal (len Xs) N)
                (pivots-ok L N Xs PL k0))
           (pivots-ok L N (mv-nth 0 (elim-col k p j Xs Ys gs hs N)) PL k0))
  :hints (("Goal" :induct (pivots-ok L N Xs PL k0)
                  :in-theory (e/d (pivots-ok) (elim-col-zero-row elim-col-other-column)))
          ("Subgoal *1/2" :use ((:instance elim-col-zero-row (i (1- k0)))
                                (:instance elim-col-other-column (i (1- k0)) (p2 (nth (1- k0) PL)))))))

(defthm pivots-ok-of-update-nth-PL
  (implies (and (natp k) (natp k0) (<= k0 k))
           (equal (pivots-ok L N Xs (update-nth k v PL) k0)
                  (pivots-ok L N Xs PL k0)))
  :hints (("Goal" :induct (pivots-ok L N Xs PL k0) :in-theory (enable pivots-ok))))

(defthm coords-at-facts
  (implies (and (natp L) (bv-listp L Xs) (natp p) (< p L))
           (and (bvp (coords-at p Xs)) (equal (len (coords-at p Xs)) (len Xs))))
  :hints (("Goal" :induct (coords-at p Xs) :in-theory (disable bv-listp-member))))

;; The new pivot column of row k becomes e_k.
(defthm elim-col-new-pivot
  (implies (and (natp L) (natp N) (natp k) (< k N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N)
                (not (equal (nth k Xs) (bv-zero L))))
           (let ((p (bv-first-one (nth k Xs))))
             (and (natp p) (< p L)
                  (equal (coords-at p (mv-nth 0 (elim-col k p 0 Xs Ys gs hs N)))
                         (unit N k)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable elim-col-pivot-column bv-first-one-witness
                                      bv-listp-member
                                      elim-col-shape coords-at-facts)
                  :use ((:instance bv-first-one-witness (x (nth k Xs)))
                        (:instance bv-listp-nth (j k))
                        (:instance elim-col-pivot-column (p (bv-first-one (nth k Xs))) (j 0))
                        (:instance elim-col-shape (p (bv-first-one (nth k Xs))) (j 0))
                        (:instance coords-at-facts (p (bv-first-one (nth k Xs)))
                                   (Xs (mv-nth 0 (elim-col k (bv-first-one (nth k Xs)) 0 Xs Ys gs hs N))))
                        (:instance agrees-below-all-is-unit
                                   (col (coords-at (bv-first-one (nth k Xs))
                                                   (mv-nth 0 (elim-col k (bv-first-one (nth k Xs)) 0 Xs Ys gs hs N))))))
                  :expand ((agrees-below (coords-at (bv-first-one (nth k Xs)) Xs) k 0)))))

;; Phase B: shape.
(defthm phaseB-shape
  (implies (and (natp L) (natp N) (natp k) (<= k N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))
           (mv-let (Xs2 Ys2 gs2 hs2 P2) (phaseB k Xs Ys gs hs N PL L)
             (declare (ignore P2))
             (and (bv-listp L Xs2) (bv-listp L Ys2) (bv-listp N gs2) (bv-listp N hs2)
                  (equal (len Xs2) N) (equal (len Ys2) N) (equal (len gs2) N) (equal (len hs2) N))))
  :hints (("Goal" :induct (phaseB k Xs Ys gs hs N PL L)
                  :in-theory (disable elim-col-shape bv-listp-member))
          ("Subgoal *1/3" :use ((:instance elim-col-shape (p (bv-first-one (nth k Xs))) (j 0))))))

;; Phase B: simulation.
(defthm phaseB-simulation
  (implies (and (natp L) (natp N) (natp k) (<= k N)
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) N) (equal (len Cs) N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N)
                (equal Xs (new-facs L Bs gs)) (equal Ys (new-facs L Cs hs)))
           (mv-let (Xs2 Ys2 gs2 hs2 P2) (phaseB k Xs Ys gs hs N PL L)
             (declare (ignore P2))
             (and (equal Xs2 (new-facs L Bs gs2)) (equal Ys2 (new-facs L Cs hs2)))))
  :hints (("Goal" :induct (phaseB k Xs Ys gs hs N PL L)
                  :in-theory (disable elim-col-shape elim-col-simulation bv-listp-member))
          ("Subgoal *1/3" :use ((:instance elim-col-shape (p (bv-first-one (nth k Xs))) (j 0))
                                (:instance elim-col-simulation (p (bv-first-one (nth k Xs))) (j 0))))))

;; Phase B: the tensors.
(defthm phaseB-T2
  (implies (and (natp L) (natp N) (natp k) (<= k N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))
           (mv-let (Xs2 Ys2 gs2 hs2 P2) (phaseB k Xs Ys gs hs N PL L)
             (declare (ignore P2))
             (and (equal (T2 N N gs2 hs2) (T2 N N gs hs))
                  (equal (T2 L L Xs2 Ys2) (T2 L L Xs Ys)))))
  :hints (("Goal" :induct (phaseB k Xs Ys gs hs N PL L)
                  :in-theory (disable elim-col-shape elim-col-T2 bv-listp-member))
          ("Subgoal *1/3" :use ((:instance elim-col-shape (p (bv-first-one (nth k Xs))) (j 0))
                                (:instance elim-col-T2 (p (bv-first-one (nth k Xs))) (j 0))))))

;; Phase B: the pivot invariant.
(defthm phaseB-pivots
  (implies (and (natp L) (natp N) (natp k) (<= k N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N)
                (pivots-ok L N Xs PL k))
           (mv-let (Xs2 Ys2 gs2 hs2 P2) (phaseB k Xs Ys gs hs N PL L)
             (declare (ignore Ys2 gs2 hs2))
             (pivots-ok L N Xs2 P2 N)))
  :hints (("Goal" :induct (phaseB k Xs Ys gs hs N PL L)
                  :in-theory (disable elim-col-shape elim-col-preserves-pivots-ok elim-col-new-pivot
                                      bv-listp-member))
          ("Subgoal *1/3" :use ((:instance elim-col-shape (p (bv-first-one (nth k Xs))) (j 0))
                                (:instance elim-col-preserves-pivots-ok
                                           (p (bv-first-one (nth k Xs))) (j 0) (k0 k))
                                (:instance elim-col-new-pivot)
                                (:instance pivots-ok-step
                                           (Xs (mv-nth 0 (elim-col k (bv-first-one (nth k Xs)) 0 Xs Ys gs hs N)))
                                           (PL (update-nth k (bv-first-one (nth k Xs)) PL)))
                                (:instance pivots-ok-of-update-nth-PL
                                           (Xs (mv-nth 0 (elim-col k (bv-first-one (nth k Xs)) 0 Xs Ys gs hs N)))
                                           (v (bv-first-one (nth k Xs))) (k0 k))))))
