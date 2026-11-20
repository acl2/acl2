; optimal-genflip-final.lisp -- Appendix B, part 4d: phase C and
; Theorem B.1 (optimal generalized flip reduction).
;
; Starting from (Bs, Cs) with (gs, hs) = (I, I), phase B puts the X
; factors into reduced echelon form and phase C removes dependencies
; among the Y factors of the live pairs, one pair per step.  The final
; (gs*, hs*) is an invertible change of basis (sum_j g_j (x) h_j = I),
; its survivors are the live pairs, and by part 3 no decomposition of
; T_BC = sum_i B_i (x) C_i is shorter.  Together with the lower bound of
; part 1 this is Theorem B.1: the minimum number of survivors over all
; generalized flips is exactly rank(T_BC).

(in-package "ACL2")

(include-book "optimal-genflip-phaseB2")
(include-book "optimal-genflip-phaseC")
(include-book "optimal-genflip-select")
(include-book "optimal-genflip-inv")

;;; ------------------------------------------------------------------
;;; Live pairs
;;; ------------------------------------------------------------------

(defun live-flags (L Xs Ys)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom Xs) nil)
        (t (cons (if (or (equal (car Xs) (bv-zero L)) (equal (car Ys) (bv-zero L))) 0 1)
                 (live-flags L (cdr Xs) (cdr Ys))))))

(defthm len-of-live-flags (equal (len (live-flags L Xs Ys)) (len Xs)))
(defthm bvp-of-live-flags (bvp (live-flags L Xs Ys)))

(defthm nth-of-live-flags
  (implies (and (natp i) (< i (len Xs)))
           (equal (nth i (live-flags L Xs Ys))
                  (if (or (equal (nth i Xs) (bv-zero L)) (equal (nth i Ys) (bv-zero L))) 0 1)))
  :hints (("Goal" :induct (ind-2lists-nat2 Xs Ys i))))

;; The survivors of part 1 are exactly the live pairs.
(defthm survivors-are-select-live
  (implies (equal (len Xs) (len Ys))
           (and (equal (mv-nth 0 (survivors L L Xs Ys)) (select (live-flags L Xs Ys) Xs))
                (equal (mv-nth 1 (survivors L L Xs Ys)) (select (live-flags L Xs Ys) Ys))))
  :hints (("Goal" :induct (ind-2lists Xs Ys))))

(defthm num-survivors-is-nflags
  (implies (equal (len Xs) (len Ys))
           (equal (num-survivors L L Xs Ys) (nflags (live-flags L Xs Ys))))
  :hints (("Goal" :in-theory (disable survivors-are-select-live)
                  :use survivors-are-select-live)))

;; sel is supported on the flags F.
(defun sel-subset (sel F)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom sel) t)
        ((eql (car sel) 1) (and (eql (car F) 1) (sel-subset (cdr sel) (cdr F))))
        (t (sel-subset (cdr sel) (cdr F)))))

(defthm sel-subset-nth
  (implies (and (sel-subset sel F) (natp i) (equal (nth i sel) 1))
           (equal (nth i F) 1))
  :hints (("Goal" :induct (ind-2lists-nat2 sel F i))))

;; A dependency among the live Y factors.
(defun-sk live-dependent (L N Xs Ys)
  (exists sel
          (and (bvp sel) (equal (len sel) N) (not (equal sel (bv-zero N)))
               (sel-subset sel (live-flags L Xs Ys))
               (equal (col-comb L Ys sel) (bv-zero L)))))

;;; ------------------------------------------------------------------
;;; Phase C
;;; ------------------------------------------------------------------

(defun phaseC (Xs Ys gs hs N L)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nflags (live-flags L Xs Ys))))
  (if (not (live-dependent L N Xs Ys))
      (mv Xs Ys gs hs)
    (let* ((sel (live-dependent-witness L N Xs Ys))
           (r (bv-first-one sel)))
      (mv-let (Xs2 Ys2 gs2 hs2) (dep-elim r sel 0 Xs Ys gs hs N)
        (if (< (nflags (live-flags L Xs2 Ys2)) (nflags (live-flags L Xs Ys)))
            (phaseC Xs2 Ys2 gs2 hs2 N L)
          (mv Xs Ys gs hs))))))

;;; ------------------------------------------------------------------
;;; Facts about one phase-C step
;;; ------------------------------------------------------------------

;; sum_{i >= i0} sel_i Y_i, by index.
(defun sum-from (L Ys sel i N)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- N i))))
  (if (or (not (natp N)) (not (natp i)) (>= i N))
      (bv-zero L)
    (if (equal (nth i sel) 1)
        (bv+ (nth i Ys) (sum-from L Ys sel (1+ i) N))
      (sum-from L Ys sel (1+ i) N))))

(defthm bv-facts-of-sum-from
  (implies (and (natp L) (bv-listp L Ys) (natp N) (equal (len Ys) N))
           (and (bvp (sum-from L Ys sel i N))
                (equal (len (sum-from L Ys sel i N)) L)))
  :hints (("Goal" :induct (sum-from L Ys sel i N) :in-theory (disable bv-listp-member))))

(defthm col-comb-as-sum-from-gen
  (implies (and (natp L) (bv-listp L Ys) (bvp sel) (equal (len sel) (len Ys))
                (natp i) (<= i (len Ys)))
           (equal (col-comb L (nthcdr i Ys) (nthcdr i sel)) (sum-from L Ys sel i (len Ys))))
  :hints (("Goal" :induct (ind-up (len Ys) i)
                  :in-theory (disable bv-listp-member))
          ("Subgoal *1/2" :expand ((col-comb L (nthcdr i Ys) (nthcdr i sel))))))

(defthm col-comb-as-sum-from
  (implies (and (natp L) (bv-listp L Ys) (bvp sel) (equal (len sel) (len Ys)))
           (equal (col-comb L Ys sel) (sum-from L Ys sel 0 (len Ys))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable bv-listp-member col-comb-as-sum-from-gen)
                  :use ((:instance col-comb-as-sum-from-gen (i 0))))))

;; sum-from = [r selected and r >= i] Y_r + sel-sum-from (which skips r).
(defthm sum-from-splits-r
  (implies (and (natp L) (bv-listp L Ys) (natp N) (equal (len Ys) N) (natp r) (< r N)
                (natp i))
           (equal (sum-from L Ys sel i N)
                  (if (and (<= i r) (equal (nth r sel) 1))
                      (bv+ (nth r Ys) (sel-sum-from L Ys sel r i N))
                    (sel-sum-from L Ys sel r i N))))
  :hints (("Goal" :induct (sum-from L Ys sel i N)
                  :in-theory (disable bv-listp-member))))

;; After dep-elim, Y_r = sum_{i in sel} Y_i.
(defthm dep-elim-Y-r-is-col-comb
  (implies (and (natp L) (natp N) (natp r) (< r N)
                (bv-listp L Ys) (equal (len Ys) N) (bvp sel) (equal (len sel) N)
                (equal (nth r sel) 1))
           (equal (nth r (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N)))
                  (col-comb L Ys sel)))
  :hints (("Goal" :in-theory (disable dep-elim-row-r-Y sum-from-splits-r bv-listp-member)
                  :use ((:instance dep-elim-row-r-Y (i 0))
                        (:instance col-comb-as-sum-from)
                        (:instance sum-from-splits-r (i 0))
                        (:instance bv-listp-nth (Xs Ys) (j r))))))


;; Live pivots: every live row i has a pivot column e_i.
(defun live-pivots-ok (L N Xs Ys PL)
  (declare (xargs :guard t :verify-guards nil))
  (all-pivots-ok L N Xs PL (live-flags L Xs Ys) 0))

;; pivots-ok for all rows implies live-pivots-ok.
(defthm car-of-nthcdr-local
  (implies (natp i) (equal (car (nthcdr i x)) (nth i x))))

(defthm pivots-ok-implies-all-pivots-ok
  (implies (and (natp L) (natp N) (natp i0) (<= i0 N) (equal (len Xs) N)
                (pivots-ok L N Xs PL N))
           (all-pivots-ok L N Xs PL (nthcdr i0 (live-flags L Xs Ys)) i0))
  :hints (("Goal" :induct (ind-up N i0)
                  :in-theory (disable nth-of-live-flags))
          ("Subgoal *1/2" :use ((:instance pivots-ok-nth (k N) (i i0))
                                (:instance nth-of-live-flags (i i0)))
                          :expand ((all-pivots-ok L N Xs PL (nthcdr i0 (live-flags L Xs Ys)) i0)))
          ("Subgoal *1/1" :expand ((all-pivots-ok L N Xs PL (nthcdr i0 (live-flags L Xs Ys)) i0)))))

;;; ------------------------------------------------------------------
;;; One phase-C step: r dies, everything else keeps its live status
;;; ------------------------------------------------------------------

;; The witness selects a live row r = first set bit.
(defthm witness-facts
  (implies (and (natp N) (equal (len Xs) N) (equal (len Ys) N)
                (live-dependent L N Xs Ys))
           (let ((sel (live-dependent-witness L N Xs Ys)))
             (and (bvp sel) (equal (len sel) N)
                  (natp (bv-first-one sel)) (< (bv-first-one sel) N)
                  (equal (nth (bv-first-one sel) sel) 1)
                  (not (equal (nth (bv-first-one sel) Xs) (bv-zero L)))
                  (not (equal (nth (bv-first-one sel) Ys) (bv-zero L)))
                  (sel-subset sel (live-flags L Xs Ys))
                  (equal (col-comb L Ys sel) (bv-zero L)))))
  :hints (("Goal" :in-theory (disable bv-first-one-witness sel-subset-nth nth-of-live-flags)
                  :use ((:instance bv-first-one-witness (x (live-dependent-witness L N Xs Ys)))
                        (:instance sel-subset-nth (sel (live-dependent-witness L N Xs Ys))
                                   (F (live-flags L Xs Ys)) (i (bv-first-one (live-dependent-witness L N Xs Ys))))
                        (:instance nth-of-live-flags (i (bv-first-one (live-dependent-witness L N Xs Ys))))))))

;; A selected row i /= r stays nonzero: its pivot bit survives.
(defthm selected-row-stays-nonzero
  (implies (and (natp L) (natp N) (natp r) (< r N) (natp i) (< i N) (not (equal i r))
                (bv-listp L Xs) (equal (len Xs) N)
                (natp p) (< p L) (equal (coords-at p Xs) (unit N i)))
           (not (equal (bv+ (nth i Xs) (nth r Xs)) (bv-zero L))))
  :hints (("Goal" :in-theory (disable nth-of-coords-at bv-listp-member)
                  :use ((:instance nth-of-coords-at (j i)) (:instance nth-of-coords-at (j r))
                        (:instance bv-listp-nth (j i)) (:instance bv-listp-nth (j r))
                        (:instance nth-of-bv+ (i p) (x (nth i Xs)) (y (nth r Xs)))))))

;; Live flag of row r after the step: 0 (Y_r became the zero sum).
(defthm live-flag-after-step-r
  (implies (and (natp L) (natp N) (natp r) (< r N)
                (bv-listp L Xs) (bv-listp L Ys) (equal (len Xs) N) (equal (len Ys) N)
                (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N)
                (bvp sel) (equal (len sel) N) (equal (nth r sel) 1)
                (equal (col-comb L Ys sel) (bv-zero L)))
           (equal (nth r (live-flags L (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N))
                                        (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N))))
                  0))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable dep-elim dep-elim-shape bv-listp-member
                                      dep-elim-Y-r-is-col-comb live-flags nth-of-live-flags)
                  :use ((:instance dep-elim-shape (i 0))
                        (:instance dep-elim-Y-r-is-col-comb)
                        (:instance nth-of-live-flags (i r)
                                   (Xs (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N)))
                                   (Ys (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N))))))))

;; An unselected row i /= r keeps its flag.
(defthm live-flag-after-step-unselected
  (implies (and (natp L) (natp N) (natp r) (< r N) (natp i) (< i N) (not (equal i r))
                (not (equal (nth i sel) 1))
                (bv-listp L Xs) (bv-listp L Ys) (equal (len Xs) N) (equal (len Ys) N)
                (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N))
           (equal (nth i (live-flags L (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N))
                                        (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N))))
                  (nth i (live-flags L Xs Ys))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable dep-elim dep-elim-shape bv-listp-member
                                      dep-elim-other-Y dep-elim-unselected-X live-flags nth-of-live-flags)
                  :use ((:instance dep-elim-shape (i 0))
                        (:instance dep-elim-other-Y (i 0) (i2 i))
                        (:instance dep-elim-unselected-X (i 0) (i2 i))
                        (:instance nth-of-live-flags)
                        (:instance nth-of-live-flags
                                   (Xs (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N)))
                                   (Ys (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N))))))))

;; A selected row i /= r stays live: its pivot bit survives X_i += X_r.
(defthm live-flag-after-step-selected
  (implies (and (natp L) (natp N) (natp r) (< r N) (natp i) (< i N) (not (equal i r))
                (equal (nth i sel) 1)
                (bv-listp L Xs) (bv-listp L Ys) (equal (len Xs) N) (equal (len Ys) N)
                (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N)
                (sel-subset sel (live-flags L Xs Ys))
                (live-pivots-ok L N Xs Ys PL))
           (equal (nth i (live-flags L (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N))
                                        (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N))))
                  (nth i (live-flags L Xs Ys))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable dep-elim dep-elim-shape bv-listp-member
                                      dep-elim-other-Y dep-elim-selected-X live-flags nth-of-live-flags
                                      sel-subset-nth all-pivots-ok-nth selected-row-stays-nonzero)
                  :use ((:instance dep-elim-shape (i 0))
                        (:instance dep-elim-other-Y (i 0) (i2 i))
                        (:instance dep-elim-selected-X (i 0) (i2 i))
                        (:instance sel-subset-nth (F (live-flags L Xs Ys)))
                        (:instance all-pivots-ok-nth (F (live-flags L Xs Ys)) (i0 0) (P PL))
                        (:instance selected-row-stays-nonzero (p (nth i PL)))
                        (:instance nth-of-live-flags)
                        (:instance nth-of-live-flags
                                   (Xs (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N)))
                                   (Ys (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N))))))))

;; Live flag of row i after the step.
(defthm live-flag-after-step-nth
  (implies (and (natp L) (natp N) (natp r) (< r N) (natp i) (< i N)
                (bv-listp L Xs) (bv-listp L Ys) (equal (len Xs) N) (equal (len Ys) N)
                (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N)
                (bvp sel) (equal (len sel) N) (equal (nth r sel) 1)
                (sel-subset sel (live-flags L Xs Ys))
                (equal (col-comb L Ys sel) (bv-zero L))
                (live-pivots-ok L N Xs Ys PL))
           (mv-let (Xs2 Ys2 gs2 hs2) (dep-elim r sel 0 Xs Ys gs hs N)
             (declare (ignore gs2 hs2))
             (equal (nth i (live-flags L Xs2 Ys2))
                    (if (equal i r) 0 (nth i (live-flags L Xs Ys))))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable dep-elim live-flags nth-of-live-flags bv-listp-member
                                      live-flag-after-step-r live-flag-after-step-unselected
                                      live-flag-after-step-selected)
                  :cases ((equal i r) (equal (nth i sel) 1))
                  :use (live-flag-after-step-r live-flag-after-step-unselected
                        live-flag-after-step-selected))))

;; Live flags after the step: bit r cleared, all others unchanged.
(defthm live-flags-after-step
  (implies (and (natp L) (natp N) (natp r) (< r N)
                (bv-listp L Xs) (bv-listp L Ys) (equal (len Xs) N) (equal (len Ys) N)
                (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N)
                (bvp sel) (equal (len sel) N) (equal (nth r sel) 1)
                (sel-subset sel (live-flags L Xs Ys))
                (equal (col-comb L Ys sel) (bv-zero L))
                (live-pivots-ok L N Xs Ys PL))
           (mv-let (Xs2 Ys2 gs2 hs2) (dep-elim r sel 0 Xs Ys gs hs N)
             (declare (ignore gs2 hs2))
             (equal (live-flags L Xs2 Ys2) (update-nth r 0 (live-flags L Xs Ys)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable dep-elim dep-elim-shape bv-listp-member nth-of-live-flags
                                      bv-diff-index-witness live-flag-after-step-nth live-flags)
                  :use ((:instance dep-elim-shape (i 0))
                        (:instance bv-extensionality
                                   (x (live-flags L (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N))
                                                  (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N))))
                                   (y (update-nth r 0 (live-flags L Xs Ys))))
                        (:instance bv-diff-index-witness
                                   (x (live-flags L (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N))
                                                  (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N))))
                                   (y (update-nth r 0 (live-flags L Xs Ys))))
                        (:instance live-flag-after-step-nth
                                   (i (bv-diff-index
                                       (live-flags L (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N))
                                                   (mv-nth 1 (dep-elim r sel 0 Xs Ys gs hs N)))
                                       (update-nth r 0 (live-flags L Xs Ys)))))))))

(defthm nflags-of-update-nth-0
  (implies (and (natp r) (< r (len F)) (equal (nth r F) 1))
           (equal (nflags (update-nth r 0 F)) (1- (nflags F))))
  :hints (("Goal" :induct (ind-xk F r))))

;; Clear the flag at index k (no change for k < 0 or k out of range).
(defun clear-at (F k)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom F) F)
        ((not (integerp k)) F)
        ((< k 0) F)
        ((equal k 0) (cons 0 (cdr F)))
        (t (cons (car F) (clear-at (cdr F) (1- k))))))

(defthm clear-at-negative
  (implies (and (integerp k) (< k 0)) (equal (clear-at F k) F)))

(defthm clear-at-is-update-nth
  (implies (and (natp r) (< r (len F)) (true-listp F))
           (equal (clear-at F r) (update-nth r 0 F)))
  :hints (("Goal" :induct (ind-xk F r))))

;; Live pivots survive the step: rows other than r keep their unit columns.
(defthm all-pivots-ok-after-step
  (implies (and (natp L) (natp N) (natp r) (< r N)
                (bv-listp L Xs) (equal (len Xs) N)
                (natp i0) (<= (+ i0 (len F)) N)
                (all-pivots-ok L N Xs PL F i0))
           (all-pivots-ok L N (mv-nth 0 (dep-elim r sel 0 Xs Ys gs hs N)) PL
                          (clear-at F (- r i0)) i0))
  :hints (("Goal" :induct (all-pivots-ok L N Xs PL F i0)
                  :in-theory (disable dep-elim dep-elim-other-column bv-listp-member))
          ("Subgoal *1/2" :use ((:instance dep-elim-other-column (i 0) (i2 i0) (p2 (nth i0 PL)))))))

;;; ------------------------------------------------------------------
;;; Phase C correctness
;;; ------------------------------------------------------------------

(defthm phaseC-shape
  (implies (and (natp L) (natp N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))
           (mv-let (Xs2 Ys2 gs2 hs2) (phaseC Xs Ys gs hs N L)
             (and (bv-listp L Xs2) (bv-listp L Ys2) (bv-listp N gs2) (bv-listp N hs2)
                  (equal (len Xs2) N) (equal (len Ys2) N) (equal (len gs2) N) (equal (len hs2) N))))
  :hints (("Goal" :induct (phaseC Xs Ys gs hs N L)
                  :expand ((phaseC Xs Ys gs hs N L))
                  :in-theory (disable dep-elim dep-elim-shape witness-facts bv-listp-member live-dependent))
          ("Subgoal *1/3" :use (witness-facts
                                (:instance dep-elim-shape (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))))
          ("Subgoal *1/2" :use (witness-facts
                                (:instance dep-elim-shape (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))))))
(defthm phaseC-simulation
  (implies (and (natp L) (natp N)
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) N) (equal (len Cs) N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N)
                (equal Xs (new-facs L Bs gs)) (equal Ys (new-facs L Cs hs)))
           (mv-let (Xs2 Ys2 gs2 hs2) (phaseC Xs Ys gs hs N L)
             (and (equal Xs2 (new-facs L Bs gs2)) (equal Ys2 (new-facs L Cs hs2)))))
  :hints (("Goal" :induct (phaseC Xs Ys gs hs N L)
                  :expand ((phaseC Xs Ys gs hs N L))
                  :in-theory (disable dep-elim dep-elim-shape dep-elim-simulation witness-facts
                                      bv-listp-member live-dependent))
          ("Subgoal *1/3" :use (witness-facts
                                (:instance dep-elim-shape (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))
                                (:instance dep-elim-simulation (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))))
          ("Subgoal *1/2" :use (witness-facts
                                (:instance dep-elim-shape (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))
                                (:instance dep-elim-simulation (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))))))
(defthm phaseC-T2
  (implies (and (natp L) (natp N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))
           (mv-let (Xs2 Ys2 gs2 hs2) (phaseC Xs Ys gs hs N L)
             (and (equal (T2 N N gs2 hs2) (T2 N N gs hs))
                  (equal (T2 L L Xs2 Ys2) (T2 L L Xs Ys)))))
  :hints (("Goal" :induct (phaseC Xs Ys gs hs N L)
                  :expand ((phaseC Xs Ys gs hs N L))
                  :in-theory (disable dep-elim dep-elim-shape dep-elim-T2 witness-facts
                                      bv-listp-member live-dependent))
          ("Subgoal *1/3" :use (witness-facts
                                (:instance dep-elim-shape (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))
                                (:instance dep-elim-T2 (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))))
          ("Subgoal *1/2" :use (witness-facts
                                (:instance dep-elim-shape (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))
                                (:instance dep-elim-T2 (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))))))
(defthm phaseC-pivots-and-independence
  (implies (and (natp L) (natp N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N)
                (live-pivots-ok L N Xs Ys PL))
           (mv-let (Xs2 Ys2 gs2 hs2) (phaseC Xs Ys gs hs N L)
             (declare (ignore gs2 hs2))
             (and (live-pivots-ok L N Xs2 Ys2 PL)
                  (not (live-dependent L N Xs2 Ys2)))))
  :hints (("Goal" :induct (phaseC Xs Ys gs hs N L)
                  :expand ((phaseC Xs Ys gs hs N L))
                  :in-theory (disable dep-elim dep-elim-shape witness-facts live-flags-after-step
                                      all-pivots-ok-after-step nflags-of-update-nth-0 clear-at-is-update-nth
                                      bv-listp-member live-dependent live-flags))
          ("Subgoal *1/3" :use (witness-facts
                                (:instance dep-elim-shape (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))
                                (:instance all-pivots-ok-after-step
                                           (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i0 0)
                                           (F (live-flags L Xs Ys)))
                                (:instance live-flags-after-step
                                           (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)))
                                (:instance clear-at-is-update-nth
                                           (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (F (live-flags L Xs Ys)))
                                (:instance nflags-of-update-nth-0
                                           (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (F (live-flags L Xs Ys)))))
          ("Subgoal *1/2" :use (witness-facts
                                (:instance dep-elim-shape (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i 0))
                                (:instance all-pivots-ok-after-step
                                           (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)) (i0 0)
                                           (F (live-flags L Xs Ys)))
                                (:instance live-flags-after-step
                                           (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (sel (live-dependent-witness L N Xs Ys)))
                                (:instance clear-at-is-update-nth
                                           (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (F (live-flags L Xs Ys)))
                                (:instance nflags-of-update-nth-0
                                           (r (bv-first-one (live-dependent-witness L N Xs Ys)))
                                           (F (live-flags L Xs Ys)))))))

(defthm phaseC-correct
  (implies (and (natp L) (natp N)
                (bv-listp L Bs) (bv-listp L Cs) (equal (len Bs) N) (equal (len Cs) N)
                (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N)
                (equal Xs (new-facs L Bs gs)) (equal Ys (new-facs L Cs hs))
                (live-pivots-ok L N Xs Ys PL))
           (mv-let (Xs2 Ys2 gs2 hs2) (phaseC Xs Ys gs hs N L)
             (and (bv-listp L Xs2) (bv-listp L Ys2) (bv-listp N gs2) (bv-listp N hs2)
                  (equal (len Xs2) N) (equal (len Ys2) N) (equal (len gs2) N) (equal (len hs2) N)
                  (equal Xs2 (new-facs L Bs gs2)) (equal Ys2 (new-facs L Cs hs2))
                  (equal (T2 N N gs2 hs2) (T2 N N gs hs))
                  (equal (T2 L L Xs2 Ys2) (T2 L L Xs Ys))
                  (live-pivots-ok L N Xs2 Ys2 PL)
                  (not (live-dependent L N Xs2 Ys2)))))
  :hints (("Goal" :in-theory (disable phaseC-shape phaseC-simulation phaseC-T2
                                      phaseC-pivots-and-independence live-dependent)
                  :use (phaseC-shape phaseC-simulation phaseC-T2 phaseC-pivots-and-independence))))

;;; ------------------------------------------------------------------
;;; Independence of the live Y's, transported to the selected list
;;; ------------------------------------------------------------------

;; Place the bits of x (over the flagged positions) into a vector over all
;; positions; zero elsewhere.
(defun expand (F x)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom F) nil)
        ((eql (car F) 1) (cons (car x) (expand (cdr F) (cdr x))))
        (t (cons 0 (expand (cdr F) x)))))

(defthm bvp-of-expand
  (implies (and (bvp x) (equal (len x) (nflags F))) (bvp (expand F x)))
  :hints (("Goal" :induct (expand F x))))
(defthm len-of-expand (equal (len (expand F x)) (len F)))
(defthm sel-subset-of-expand
  (implies (bvp F) (sel-subset (expand F x) F))
  :hints (("Goal" :induct (expand F x))))

(defun ind-expand (F Ys x)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom F) (list Ys x))
        ((eql (car F) 1) (ind-expand (cdr F) (cdr Ys) (cdr x)))
        (t (ind-expand (cdr F) (cdr Ys) x))))

(defthm col-comb-of-expand
  (implies (and (natp L) (bv-listp L Ys) (equal (len F) (len Ys)))
           (equal (col-comb L Ys (expand F x)) (col-comb L (select F Ys) x)))
  :hints (("Goal" :induct (ind-expand F Ys x) :in-theory (disable bv-listp-member))))

(defthm expand-zero-implies-zero
  (implies (and (bvp x) (equal (len x) (nflags F))
                (equal (expand F x) (bv-zero (len F))))
           (equal x (bv-zero (nflags F))))
  :rule-classes nil
  :hints (("Goal" :induct (expand F x))))

(defthm no-dependency-implies-trivial-kernel
  (implies (and (natp L) (natp N) (bv-listp L Xs) (bv-listp L Ys) (equal (len Xs) N) (equal (len Ys) N)
                (not (live-dependent L N Xs Ys)))
           (trivial-kernel L (select (live-flags L Xs Ys) Ys) (nflags (live-flags L Xs Ys))))
  :hints (("Goal" :in-theory (disable live-dependent-suff bv-listp-member)
                  :expand ((trivial-kernel L (select (live-flags L Xs Ys) Ys) (nflags (live-flags L Xs Ys))))
                  :use ((:instance live-dependent-suff
                                   (sel (expand (live-flags L Xs Ys)
                                                (trivial-kernel-witness L (select (live-flags L Xs Ys) Ys)
                                                                        (nflags (live-flags L Xs Ys))))))
                        (:instance expand-zero-implies-zero (F (live-flags L Xs Ys))
                                   (x (trivial-kernel-witness L (select (live-flags L Xs Ys) Ys)
                                                              (nflags (live-flags L Xs Ys)))))))))

;;; ------------------------------------------------------------------
;;; Theorem B.1
;;; ------------------------------------------------------------------

;; The whole elimination: phase B then phase C, starting from (I, I).
(defun pB (L N Bs Cs)
  (declare (xargs :guard t :verify-guards nil))
  (phaseB 0 Bs Cs (identity-rows N) (identity-rows N) N (bv-zero N) L))

(defun optimal-flip (L N Bs Cs)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (Xs Ys gs hs PL) (pB L N Bs Cs)
    (declare (ignore PL))
    (phaseC Xs Ys gs hs N L)))

(defthm identity-rows-facts
  (implies (natp N)
           (and (bv-listp N (identity-rows N)) (equal (len (identity-rows N)) N)))
  :hints (("Goal" :in-theory (disable len-of-id-rows-from bv-listp-of-id-rows-from)
                  :use ((:instance len-of-id-rows-from (i 0))
                        (:instance bv-listp-of-id-rows-from (i 0))))))

(defthm pivots-ok-0 (pivots-ok L N Xs PL 0)
  :hints (("Goal" :in-theory (enable pivots-ok))))

;; Facts after phase B, one property at a time.
(defthm pB-shape
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs PL) (pB L N Bs Cs)
             (declare (ignore PL))
             (and (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                  (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable phaseB-shape bv-listp-member)
                  :use ((:instance phaseB-shape (k 0) (Xs Bs) (Ys Cs) (gs (identity-rows N))
                                   (hs (identity-rows N)) (PL (bv-zero N)))))))

(defthm pB-simulation
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs PL) (pB L N Bs Cs)
             (declare (ignore PL))
             (and (equal Xs (new-facs L Bs gs)) (equal Ys (new-facs L Cs hs)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable phaseB-simulation bv-listp-member new-facs-of-identity-rows)
                  :use ((:instance new-facs-of-identity-rows (Vs Bs))
                        (:instance new-facs-of-identity-rows (Vs Cs))
                        (:instance phaseB-simulation (k 0) (Xs Bs) (Ys Cs) (gs (identity-rows N))
                                   (hs (identity-rows N)) (PL (bv-zero N)))))))

(defthm pB-T2
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs PL) (pB L N Bs Cs)
             (declare (ignore PL))
             (and (equal (T2 N N gs hs) (T2 N N (identity-rows N) (identity-rows N)))
                  (equal (T2 L L Xs Ys) (T2 L L Bs Cs)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable phaseB-T2 bv-listp-member)
                  :use ((:instance phaseB-T2 (k 0) (Xs Bs) (Ys Cs) (gs (identity-rows N))
                                   (hs (identity-rows N)) (PL (bv-zero N)))))))

(defthm pB-pivots
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs PL) (pB L N Bs Cs)
             (declare (ignore Ys gs hs))
             (pivots-ok L N Xs PL N)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable phaseB-pivots bv-listp-member)
                  :use ((:instance phaseB-pivots (k 0) (Xs Bs) (Ys Cs) (gs (identity-rows N))
                                   (hs (identity-rows N)) (PL (bv-zero N)))))))

(in-theory (disable pB))

(defthm pB-live-pivots
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs PL) (pB L N Bs Cs)
             (declare (ignore gs hs))
             (live-pivots-ok L N Xs Ys PL)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable pB-shape pB-pivots pivots-ok-implies-all-pivots-ok bv-listp-member)
                  :use (pB-shape pB-pivots
                        (:instance pivots-ok-implies-all-pivots-ok (i0 0)
                                   (Xs (mv-nth 0 (pB L N Bs Cs))) (Ys (mv-nth 1 (pB L N Bs Cs)))
                                   (PL (mv-nth 4 (pB L N Bs Cs))))))))

;; Facts after phase C (the final state), one property at a time.
(defthm optimal-flip-shape
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (and (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                  (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (union-theories (theory 'minimal-theory) '(optimal-flip))
                  :use (pB-shape
                        (:instance phaseC-shape
                                   (Xs (mv-nth 0 (pB L N Bs Cs))) (Ys (mv-nth 1 (pB L N Bs Cs)))
                                   (gs (mv-nth 2 (pB L N Bs Cs))) (hs (mv-nth 3 (pB L N Bs Cs))))))))

(defthm optimal-flip-simulation
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (and (equal Xs (new-facs L Bs gs)) (equal Ys (new-facs L Cs hs)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (union-theories (theory 'minimal-theory) '(optimal-flip))
                  :use (pB-shape pB-simulation
                        (:instance phaseC-simulation
                                   (Xs (mv-nth 0 (pB L N Bs Cs))) (Ys (mv-nth 1 (pB L N Bs Cs)))
                                   (gs (mv-nth 2 (pB L N Bs Cs))) (hs (mv-nth 3 (pB L N Bs Cs))))))))

(defthm optimal-flip-T2
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (and (equal (T2 N N gs hs) (T2 N N (identity-rows N) (identity-rows N)))
                  (equal (T2 L L Xs Ys) (T2 L L Bs Cs)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (union-theories (theory 'minimal-theory) '(optimal-flip))
                  :use (pB-shape pB-T2
                        (:instance phaseC-T2
                                   (Xs (mv-nth 0 (pB L N Bs Cs))) (Ys (mv-nth 1 (pB L N Bs Cs)))
                                   (gs (mv-nth 2 (pB L N Bs Cs))) (hs (mv-nth 3 (pB L N Bs Cs))))))))

(defthm optimal-flip-pivots-and-independence
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (declare (ignore gs hs))
             (and (live-pivots-ok L N Xs Ys (mv-nth 4 (pB L N Bs Cs)))
                  (not (live-dependent L N Xs Ys)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (union-theories (theory 'minimal-theory) '(optimal-flip))
                  :use (pB-shape pB-live-pivots
                        (:instance phaseC-pivots-and-independence
                                   (Xs (mv-nth 0 (pB L N Bs Cs))) (Ys (mv-nth 1 (pB L N Bs Cs)))
                                   (gs (mv-nth 2 (pB L N Bs Cs))) (hs (mv-nth 3 (pB L N Bs Cs)))
                                   (PL (mv-nth 4 (pB L N Bs Cs))))))))

(defthm optimal-flip-facts
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (and (bv-listp L Xs) (bv-listp L Ys) (bv-listp N gs) (bv-listp N hs)
                  (equal (len Xs) N) (equal (len Ys) N) (equal (len gs) N) (equal (len hs) N)
                  (equal Xs (new-facs L Bs gs)) (equal Ys (new-facs L Cs hs))
                  (equal (T2 N N gs hs) (T2 N N (identity-rows N) (identity-rows N)))
                  (equal (T2 L L Xs Ys) (T2 L L Bs Cs))
                  (live-pivots-ok L N Xs Ys (mv-nth 4 (pB L N Bs Cs)))
                  (not (live-dependent L N Xs Ys)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (theory 'minimal-theory)
                  :use (optimal-flip-shape optimal-flip-simulation optimal-flip-T2
                        optimal-flip-pivots-and-independence))))

(in-theory (disable optimal-flip))

;; (a) invertibility
(defthm optimal-flip-invertible
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (declare (ignore Xs Ys))
             (equal (rows-sum2 N N gs hs) (identity-rows N))))
  :hints (("Goal" :in-theory (disable optimal-flip-facts T2-eq-identity-implies-rows-sum2-identity)
                  :use (optimal-flip-facts
                        (:instance T2-eq-identity-implies-rows-sum2-identity
                                   (gs (mv-nth 2 (optimal-flip L N Bs Cs)))
                                   (hs (mv-nth 3 (optimal-flip L N Bs Cs))))))))

;; (b) the survivors decompose T_BC
(defthm optimal-flip-survivors-decompose
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (declare (ignore gs hs))
             (has-decomp L L (T2 L L Bs Cs) (num-survivors L L Xs Ys))))
  :hints (("Goal" :in-theory (disable optimal-flip-facts T2-of-survivors survivors-bv-listp
                                      survivors-are-select-live num-survivors-is-nflags)
                  :use (optimal-flip-facts
                        (:instance T2-of-survivors (LB L) (LC L)
                                   (Bs (mv-nth 0 (optimal-flip L N Bs Cs)))
                                   (Cs (mv-nth 1 (optimal-flip L N Bs Cs))))
                        (:instance survivors-bv-listp (LB L) (LC L)
                                   (Bs (mv-nth 0 (optimal-flip L N Bs Cs)))
                                   (Cs (mv-nth 1 (optimal-flip L N Bs Cs))))
                        (:instance has-decomp-suff (LB L) (LC L)
                                   (T2val (T2 L L Bs Cs))
                                   (k (num-survivors L L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                     (mv-nth 1 (optimal-flip L N Bs Cs))))
                                   (Us (mv-nth 0 (survivors L L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                            (mv-nth 1 (optimal-flip L N Bs Cs)))))
                                   (Vs (mv-nth 1 (survivors L L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                            (mv-nth 1 (optimal-flip L N Bs Cs))))))))))

;; The selected pivots are coordinates below L.
(defthm all-below-of-select-gen
  (implies (and (natp i) (all-pivots-ok L N Xs PL F i))
           (all-below (select F (nthcdr i PL)) L))
  :hints (("Goal" :induct (all-pivots-ok L N Xs PL F i)
                  :in-theory (disable nth-of-select))))

(defthm all-below-of-select
  (implies (all-pivots-ok L N Xs PL F 0)
           (all-below (select F PL) L))
  :hints (("Goal" :use ((:instance all-below-of-select-gen (i 0))))))

;; (c) no shorter decomposition exists
(defthm optimal-flip-is-shortest
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N)
                (bv-listp L Us) (bv-listp L Vs) (equal (len Us) (len Vs))
                (equal (T2 L L Us Vs) (T2 L L Bs Cs)))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (declare (ignore gs hs))
             (<= (num-survivors L L Xs Ys) (len Us))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable optimal-flip-facts T2-of-survivors survivors-are-select-live
                                      num-survivors-is-nflags
                                      pivots-from-of-nthcdr-select all-below-of-select
                                      no-dependency-implies-trivial-kernel bv-listp-member
                                      live-dependent bv-listp-of-select)
                  :use (optimal-flip-facts
                        (:instance T2-of-survivors (LB L) (LC L)
                                   (Bs (mv-nth 0 (optimal-flip L N Bs Cs)))
                                   (Cs (mv-nth 1 (optimal-flip L N Bs Cs))))
                        (:instance survivors-are-select-live
                                   (Xs (mv-nth 0 (optimal-flip L N Bs Cs)))
                                   (Ys (mv-nth 1 (optimal-flip L N Bs Cs))))
                        (:instance num-survivors-is-nflags
                                   (Xs (mv-nth 0 (optimal-flip L N Bs Cs)))
                                   (Ys (mv-nth 1 (optimal-flip L N Bs Cs))))
                        (:instance pivots-from-of-nthcdr-select (k 0)
                                   (F (live-flags L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                  (mv-nth 1 (optimal-flip L N Bs Cs))))
                                   (Xs (mv-nth 0 (optimal-flip L N Bs Cs)))
                                   (P (mv-nth 4 (pB L N Bs Cs))))
                        (:instance all-below-of-select
                                   (F (live-flags L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                  (mv-nth 1 (optimal-flip L N Bs Cs))))
                                   (Xs (mv-nth 0 (optimal-flip L N Bs Cs)))
                                   (PL (mv-nth 4 (pB L N Bs Cs))))
                        (:instance no-dependency-implies-trivial-kernel
                                   (Xs (mv-nth 0 (optimal-flip L N Bs Cs)))
                                   (Ys (mv-nth 1 (optimal-flip L N Bs Cs))))
                        (:instance bv-listp-of-select
                                   (F (live-flags L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                  (mv-nth 1 (optimal-flip L N Bs Cs))))
                                   (Xs (mv-nth 0 (optimal-flip L N Bs Cs))))
                        (:instance bv-listp-of-select
                                   (F (live-flags L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                  (mv-nth 1 (optimal-flip L N Bs Cs))))
                                   (Xs (mv-nth 1 (optimal-flip L N Bs Cs))))
                        (:instance echelon-decomp-is-shortest
                                   (Bs (select (live-flags L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                            (mv-nth 1 (optimal-flip L N Bs Cs)))
                                               (mv-nth 0 (optimal-flip L N Bs Cs))))
                                   (Cs (select (live-flags L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                            (mv-nth 1 (optimal-flip L N Bs Cs)))
                                               (mv-nth 1 (optimal-flip L N Bs Cs))))
                                   (P (select (live-flags L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                           (mv-nth 1 (optimal-flip L N Bs Cs)))
                                              (mv-nth 4 (pB L N Bs Cs)))))))))

(defthm optimal-flip-no-shorter-decomp
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (declare (ignore gs hs))
             (not (has-decomp L L (T2 L L Bs Cs) (1- (num-survivors L L Xs Ys))))))
  :hints (("Goal" :in-theory (disable optimal-flip-is-shortest)
                  :use ((:instance optimal-flip-is-shortest
                                   (Us (mv-nth 0 (has-decomp-witness L L (T2 L L Bs Cs)
                                                                     (1- (num-survivors L L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                                                          (mv-nth 1 (optimal-flip L N Bs Cs)))))))
                                   (Vs (mv-nth 1 (has-decomp-witness L L (T2 L L Bs Cs)
                                                                     (1- (num-survivors L L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                                                          (mv-nth 1 (optimal-flip L N Bs Cs))))))))))))

;; Theorem B.1.  Let (gs*, hs*) be the change of basis computed by the
;; elimination and s the number of surviving summands.  Then
;;  (a) (gs*, hs*) is invertible:  sum_j g_j (x) h_j = I;
;;  (b) the survivors are a decomposition of T_BC into s simple tensors;
;;  (c) T_BC has no decomposition into fewer than s simple tensors,
;;      i.e. s = rank(T_BC);
;;  (d) every generalized flip (any invertible G) has at least s survivors
;;      (genflip-lower-bound in optimal-genflip.lisp with r = s; restated
;;      below as theorem-B1-lower-bound).
(defthm theorem-B1
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N))
           (mv-let (Xs Ys gs hs) (optimal-flip L N Bs Cs)
             (let ((s (num-survivors L L Xs Ys)))
               (and (equal (rows-sum2 N N gs hs) (identity-rows N))
                    (equal Xs (new-facs L Bs gs))
                    (equal Ys (new-facs L Cs hs))
                    (has-decomp L L (T2 L L Bs Cs) s)
                    (not (has-decomp L L (T2 L L Bs Cs) (1- s)))))))
  :hints (("Goal" :in-theory (disable optimal-flip-facts optimal-flip-invertible
                                      optimal-flip-survivors-decompose optimal-flip-no-shorter-decomp)
                  :use (optimal-flip-facts optimal-flip-invertible
                        optimal-flip-survivors-decompose optimal-flip-no-shorter-decomp))))

(defthm theorem-B1-lower-bound
  (implies (and (natp L) (natp N) (bv-listp L Bs) (bv-listp L Cs)
                (equal (len Bs) N) (equal (len Cs) N)
                (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N)
                (equal (rows-sum2 N N gs hs) (identity-rows N)))
           (mv-let (Xs Ys gs2 hs2) (optimal-flip L N Bs Cs)
             (declare (ignore gs2 hs2))
             (<= (num-survivors L L Xs Ys)
                 (num-survivors L L (new-facs L Bs gs) (new-facs L Cs hs)))))
  :hints (("Goal" :in-theory (disable optimal-flip-no-shorter-decomp genflip-lower-bound)
                  :use (optimal-flip-no-shorter-decomp
                        (:instance genflip-lower-bound (LB L) (LC L)
                                   (r (num-survivors L L (mv-nth 0 (optimal-flip L N Bs Cs))
                                                     (mv-nth 1 (optimal-flip L N Bs Cs)))))))))
