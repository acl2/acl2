; optimal-genflip-select.lisp -- Appendix B, part 4d (helpers): selecting
; the live pairs of a decomposition and transporting the echelon and
; independence properties to the selected lists.

(in-package "ACL2")

(include-book "optimal-genflip")

;;; ------------------------------------------------------------------
;;; Selection by a flag list
;;; ------------------------------------------------------------------

(defun select (F Xs)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom F) nil)
        ((eql (car F) 1) (cons (car Xs) (select (cdr F) (cdr Xs))))
        (t (select (cdr F) (cdr Xs)))))

;; number of flags set
(defun nflags (F)
  (declare (xargs :guard t))
  (cond ((atom F) 0) ((eql (car F) 1) (1+ (nflags (cdr F)))) (t (nflags (cdr F)))))

;; number of flags set strictly below i
(defun frank (F i)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((zp i) 0) ((atom F) 0)
        ((eql (car F) 1) (1+ (frank (cdr F) (1- i))))
        (t (frank (cdr F) (1- i)))))

(defthm len-of-select (equal (len (select F Xs)) (nflags F)))

(defthm bv-listp-of-select
  (implies (and (bv-listp L Xs) (<= (len F) (len Xs))) (bv-listp L (select F Xs)))
  :hints (("Goal" :induct (select F Xs))))

(defthm coords-at-of-select
  (equal (coords-at p (select F Xs)) (select F (coords-at p Xs)))
  :hints (("Goal" :induct (select F Xs))))

(defun ind-F-i-N (F i N)
  (if (atom F) (list F i N) (ind-F-i-N (cdr F) (1- i) (1- N))))


;; Selecting from zero.
(defthm select-of-bv-zero
  (implies (and (natp N) (equal (len F) N))
           (equal (select F (bv-zero N)) (bv-zero (nflags F))))
  :hints (("Goal" :induct (ind-F-i-N F N N))))

;; Selecting from a unit vector: a unit at a flagged position, else zero.
(defthm select-of-unit
  (implies (and (natp i) (natp N) (equal (len F) N) (< i N))
           (equal (select F (unit N i))
                  (if (equal (nth i F) 1)
                      (unit (nflags F) (frank F i))
                    (bv-zero (nflags F)))))
  :hints (("Goal" :induct (ind-F-i-N F i N))))

;;; ------------------------------------------------------------------
;;; Flagged positions
;;; ------------------------------------------------------------------

;; The idx-th flagged position (0-based), as an index into F.
(defun flagged-pos (F idx)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom F) 0)
        ((eql (car F) 1) (if (zp idx) 0 (1+ (flagged-pos (cdr F) (1- idx)))))
        (t (1+ (flagged-pos (cdr F) idx)))))

(defun ind-sel (F Xs idx)
  (cond ((atom F) (list F Xs idx))
        ((eql (car F) 1) (if (zp idx) (list F Xs idx) (ind-sel (cdr F) (cdr Xs) (1- idx))))
        (t (ind-sel (cdr F) (cdr Xs) idx))))

(defthm nth-of-select
  (implies (and (natp idx) (< idx (nflags F)))
           (equal (nth idx (select F Xs)) (nth (flagged-pos F idx) Xs)))
  :hints (("Goal" :induct (ind-sel F Xs idx))))

(defthm flagged-pos-is-flagged
  (implies (and (natp idx) (< idx (nflags F)))
           (equal (nth (flagged-pos F idx) F) 1))
  :hints (("Goal" :induct (flagged-pos F idx))))

(defthm flagged-pos-below-len
  (implies (and (natp idx) (< idx (nflags F)))
           (< (flagged-pos F idx) (len F)))
  :hints (("Goal" :induct (flagged-pos F idx)))
  :rule-classes :linear)

(defthm frank-of-flagged-pos
  (implies (and (natp idx) (< idx (nflags F)))
           (equal (frank F (flagged-pos F idx)) idx))
  :hints (("Goal" :induct (flagged-pos F idx))))

(defthm natp-of-flagged-pos (natp (flagged-pos F idx)) :rule-classes :type-prescription)

;;; ------------------------------------------------------------------
;;; Transporting the echelon property
;;; ------------------------------------------------------------------

;; (all-pivots-ok L N Xs P F): every flagged row i has a pivot coordinate
;; p_i < L whose column in X is e_i.
(defun all-pivots-ok (L N Xs P F i)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom F) t
    (and (or (not (eql (car F) 1))
             (and (natp (nth i P)) (< (nth i P) L)
                  (equal (coords-at (nth i P) Xs) (unit N i))))
         (all-pivots-ok L N Xs P (cdr F) (1+ i)))))

(defthm all-pivots-ok-nth
  (implies (and (all-pivots-ok L N Xs P F i0) (natp i0) (natp i) (<= i0 i) (< i (+ i0 (len F)))
                (equal (nth (- i i0) F) 1))
           (and (natp (nth i P)) (< (nth i P) L)
                (equal (coords-at (nth i P) Xs) (unit N i))))
  :hints (("Goal" :induct (all-pivots-ok L N Xs P F i0))))

;; pivots-from on the selected lists, from index idx on.
(defun ind-pivots (Q idx) (if (atom Q) (list Q idx) (ind-pivots (cdr Q) (1+ idx))))

;; The k-th element of Plive = (select F P) is (nth (flagged-pos F k) P) and its
;; column in (select F Xs) is e_k (as a vector of length (nflags F)).
(defthm pivot-column-of-selected
  (implies (and (natp L) (natp N) (equal (len F) N) (equal (len Xs) N) (bv-listp L Xs)
                (all-pivots-ok L N Xs P F 0)
                (natp k) (< k (nflags F)))
           (and (natp (nth k (select F P)))
                (equal (coords-at (nth k (select F P)) (select F Xs))
                       (unit (nflags F) k))))
  :hints (("Goal" :in-theory (disable all-pivots-ok-nth select-of-unit nth-of-select
                                      flagged-pos-is-flagged frank-of-flagged-pos)
                  :use ((:instance nth-of-select (idx k) (Xs P))
                        (:instance flagged-pos-is-flagged (idx k))
                        (:instance frank-of-flagged-pos (idx k))
                        (:instance all-pivots-ok-nth (i0 0) (i (flagged-pos F k)))
                        (:instance select-of-unit (i (flagged-pos F k)))))))

;; pivots-from over a suffix of the selected pivot list.
(defun ind-up2 (N i)
  (declare (xargs :measure (nfix (- N i))))
  (if (or (not (natp N)) (not (natp i)) (>= i N)) (list N i) (ind-up2 N (1+ i))))

(defthm pivots-from-of-nthcdr-select
  (implies (and (natp L) (natp N) (equal (len F) N) (equal (len Xs) N) (bv-listp L Xs)
                (all-pivots-ok L N Xs P F 0)
                (natp k) (<= k (nflags F)))
           (pivots-from (nthcdr k (select F P)) (select F Xs) (nflags F) k))
  :hints (("Goal" :induct (ind-up2 (nflags F) k)
                  :in-theory (disable pivot-column-of-selected nth-of-select))
          ("Subgoal *1/2" :use ((:instance pivot-column-of-selected))
                          :expand ((pivots-from (nthcdr k (select F P)) (select F Xs) (nflags F) k)))))
