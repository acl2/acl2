; span.lisp -- Lemma 4.2 of the paper (the span lemma), constructively.
;
; For a scheme S, a position p, and a target basis matrix E_xy, we
; exhibit coordinates (b, c) for the two other positions such that the
; sum of the p-factors of the summands whose lo-factor has a 1 at b and
; whose hi-factor has a 1 at c is exactly E_xy.  This is the coefficient
; comparison in the paper's proof:
;      E_ij = sum_r A^(r) beta^(r)_{j,k} gamma^(r)_{i,k}.
; Hence every E_xy, and therefore every matrix, is a sum of p-factors of
; summands of S: the p-factors span F_2^{n x n}.

(in-package "ACL2")

(include-book "scheme")

;;; ------------------------------------------------------------------
;;; Slice selection
;;; ------------------------------------------------------------------

;; Is summand s selected by the slice (b,c) for position p?
(defun selectedp (p s b c)
  (declare (xargs :guard (and (natp p) (true-listp s) (natp b) (natp c))
                  :verify-guards nil))
  (and (equal (nth b (fac (other-lo p) s)) 1)
       (equal (nth c (fac (other-hi p) s)) 1)))

;; The p-factors of the selected summands.
(defun sel-list (p S b c)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom S) nil)
        ((selectedp p (car S) b c) (cons (fac p (car S)) (sel-list p (cdr S) b c)))
        (t (sel-list p (cdr S) b c))))

;; All p-factors of S.
(defun facs (p S)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom S) nil (cons (fac p (car S)) (facs p (cdr S)))))

(defun sel-sum (p L S b c)
  (declare (xargs :guard t :verify-guards nil))
  (bv-sum L (sel-list p S b c)))

(defthm subsetp-sel-list-facs
  (subsetp-equal (sel-list p S b c) (facs p S)))

(defthm member-facs
  (implies (member-equal s1 S) (member-equal (fac p s1) (facs p S))))

(defthm bv-listp-of-sel-list
  (implies (and (triple-listp L S) (posp3 p))
           (bv-listp L (sel-list p S b c)))
  :hints (("Goal" :in-theory (enable fac posp3 other-lo other-hi))))

(defthm bv-listp-of-facs
  (implies (and (triple-listp L S) (posp3 p))
           (bv-listp L (facs p S)))
  :hints (("Goal" :in-theory (enable fac posp3))))

;;; ------------------------------------------------------------------
;;; Tensor coordinates by position
;;; ------------------------------------------------------------------

;; Index of the tensor coordinate whose position-p coordinate is a and
;; whose lo/hi coordinates are b and c.
(defun coord-idx (p L a b c)
  (declare (xargs :guard t :verify-guards nil))
  (case p
    (0 (tidx3 L L a b c))
    (1 (tidx3 L L b a c))
    (t (tidx3 L L b c a))))

(defthm nth-coord-idx-of-rank1-0
  (implies (and (triplep L s1) (natp L)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth (coord-idx 0 L a b c) (rank1 s1))
                  (band (nth a (car s1)) (band (nth b (cadr s1)) (nth c (caddr s1))))))
  :hints (("Goal" :in-theory (e/d (rank1 coord-idx) (nth-of-outer3))
                  :use ((:instance nth-of-outer3 (A (car s1)) (B (cadr s1)) (C (caddr s1))
                                   (ia a) (ib b) (ic c))))))

(defthm nth-coord-idx-of-rank1-1
  (implies (and (triplep L s1) (natp L)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth (coord-idx 1 L a b c) (rank1 s1))
                  (band (nth a (cadr s1)) (band (nth b (car s1)) (nth c (caddr s1))))))
  :hints (("Goal" :in-theory (e/d (rank1 coord-idx) (nth-of-outer3))
                  :use ((:instance nth-of-outer3 (A (car s1)) (B (cadr s1)) (C (caddr s1))
                                   (ia b) (ib a) (ic c))))))

(defthm nth-coord-idx-of-rank1-2
  (implies (and (triplep L s1) (natp L)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth (coord-idx 2 L a b c) (rank1 s1))
                  (band (nth a (caddr s1)) (band (nth b (car s1)) (nth c (cadr s1))))))
  :hints (("Goal" :in-theory (e/d (rank1 coord-idx) (nth-of-outer3))
                  :use ((:instance nth-of-outer3 (A (car s1)) (B (cadr s1)) (C (caddr s1))
                                   (ia b) (ib c) (ic a))))))

(defthm nth-coord-idx-of-rank1
  (implies (and (posp3 p) (triplep L s1) (natp L)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth (coord-idx p L a b c) (rank1 s1))
                  (band (nth a (fac p s1))
                        (band (nth b (fac (other-lo p) s1))
                              (nth c (fac (other-hi p) s1))))))
  :hints (("Goal" :in-theory (e/d (fac posp3 other-lo other-hi) (coord-idx rank1 tidx3))
                  :cases ((equal p 0) (equal p 1) (equal p 2)))))

(defthm coord-idx-bound
  (implies (and (posp3 p) (natp L) (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (< (coord-idx p L a b c) (tlen L)))
  :hints (("Goal" :in-theory (e/d (posp3) (tidx3-bound))
                  :use ((:instance tidx3-bound (LA L) (LB L) (LC L))
                        (:instance tidx3-bound (LA L) (LB L) (LC L) (a b) (b a))
                        (:instance tidx3-bound (LA L) (LB L) (LC L) (a b) (b c) (c a)))))
  :rule-classes :linear)

(defthm natp-of-coord-idx
  (implies (and (natp L) (natp a) (natp b) (natp c))
           (natp (coord-idx p L a b c)))
  :rule-classes :type-prescription)

(in-theory (disable coord-idx))

;; Coordinate a of the slice sum is the tensor coordinate (a at p, b, c).
(defthm nth-of-sel-sum
  (implies (and (posp3 p) (natp L) (triple-listp L S)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth a (sel-sum p L S b c))
                  (nth (coord-idx p L a b c) (triple-sum L S))))
  :hints (("Goal" :induct (sel-list p S b c)
                  :in-theory (e/d (posp3 other-lo other-hi) (nth-coord-idx-of-rank1)))
          ("Subgoal *1/1" :use ((:instance coord-idx-bound)))
          ("Subgoal *1/3" :use ((:instance nth-coord-idx-of-rank1 (s1 (car S)))
                                (:instance coord-idx-bound)))
          ("Subgoal *1/2" :use ((:instance nth-coord-idx-of-rank1 (s1 (car S)))
                                (:instance coord-idx-bound)))))

;;; ------------------------------------------------------------------
;;; The span lemma
;;; ------------------------------------------------------------------

;; Coordinates (b,c) that pick out the target E_xy at position p
;; (using k = 0, i = 0, or j = 0 respectively as the free index).
(defun span-b (p n x y)
  (declare (xargs :guard (and (natp n) (natp x) (natp y))))
  (case p
    (0 (midx n y 0))
    (1 (midx n 0 x))
    (t (midx n x 0))))

(defun span-c (p n x y)
  (declare (xargs :guard (and (natp n) (natp x) (natp y))))
  (case p
    (0 (midx n x 0))
    (1 (midx n 0 y))
    (t (midx n 0 y))))

(defthm mmt-coeff-at-span-coords
  (implies (and (posp n) (posp3 p) (natp a) (< a (sq n))
                (natp x) (natp y) (< x n) (< y n))
           (equal (nth (coord-idx p (sq n) a (span-b p n x y) (span-c p n x y)) (mmt n))
                  (if (equal a (midx n x y)) 1 0)))
  :hints (("Goal" :in-theory (e/d (coord-idx posp3) (nth-of-mmt))
                  :use ((:instance nth-of-mmt (b (span-b 0 n x y)) (c (span-c 0 n x y)))
                        (:instance nth-of-mmt (a (span-b 1 n x y)) (b a) (c (span-c 1 n x y)))
                        (:instance nth-of-mmt (a (span-b 2 n x y)) (b (span-c 2 n x y)) (c a))
                        (:instance mmt-coeff-slice-A (i x) (j y) (k 0))
                        (:instance mmt-coeff-slice-B (b a) (i 0) (j x) (k y))
                        (:instance mmt-coeff-slice-C (c a) (i x) (j 0) (k y))))))

(defthm natp-of-span-b
  (implies (and (natp n) (natp x) (natp y)) (natp (span-b p n x y)))
  :rule-classes :type-prescription)
(defthm natp-of-span-c
  (implies (and (natp n) (natp x) (natp y)) (natp (span-c p n x y)))
  :rule-classes :type-prescription)
(defthm span-b-bound
  (implies (and (posp n) (natp x) (natp y) (< x n) (< y n))
           (< (span-b p n x y) (sq n)))
  :rule-classes :linear)
(defthm span-c-bound
  (implies (and (posp n) (natp x) (natp y) (< x n) (< y n))
           (< (span-c p n x y) (sq n)))
  :rule-classes :linear)

(in-theory (disable span-b span-c))

;; Per-coordinate form of the span lemma.
(defthm span-lemma-nth
  (implies (and (schemep n S) (posp3 p)
                (natp x) (natp y) (< x n) (< y n)
                (natp a) (< a (sq n)))
           (equal (nth a (sel-sum p (sq n) S (span-b p n x y) (span-c p n x y)))
                  (if (equal a (midx n x y)) 1 0)))
  :hints (("Goal" :in-theory (disable sel-sum nth-of-sel-sum mmt-coeff-at-span-coords)
                  :use ((:instance nth-of-sel-sum (L (sq n))
                                   (b (span-b p n x y)) (c (span-c p n x y)))
                        (:instance mmt-coeff-at-span-coords)))))

(defthm bvp-of-sel-sum (bvp (sel-sum p L S b c)))
(defthm len-of-sel-sum
  (implies (and (triple-listp L S) (posp3 p))
           (equal (len (sel-sum p L S b c)) (nfix L))))

(in-theory (disable sel-sum))

;; Lemma 4.2: the slice sum of the p-factors of a scheme is E_xy.
(defthm span-lemma
  (implies (and (schemep n S) (posp3 p)
                (natp x) (natp y) (< x n) (< y n))
           (equal (sel-sum p (sq n) S (span-b p n x y) (span-c p n x y))
                  (unit (sq n) (midx n x y))))
  :hints (("Goal"
           :in-theory (disable span-lemma-nth bv-diff-index-witness nth-of-unit)
           :use ((:instance bv-extensionality
                            (x (sel-sum p (sq n) S (span-b p n x y) (span-c p n x y)))
                            (y (unit (sq n) (midx n x y))))
                 (:instance bv-diff-index-witness
                            (x (sel-sum p (sq n) S (span-b p n x y) (span-c p n x y)))
                            (y (unit (sq n) (midx n x y))))
                 (:instance span-lemma-nth
                            (a (bv-diff-index (sel-sum p (sq n) S (span-b p n x y) (span-c p n x y))
                                              (unit (sq n) (midx n x y)))))
                 (:instance nth-of-unit (L (sq n)) (k (midx n x y))
                            (i (bv-diff-index (sel-sum p (sq n) S (span-b p n x y) (span-c p n x y))
                                              (unit (sq n) (midx n x y)))))))))

;;; ------------------------------------------------------------------
;;; Consequence: for n >= 2, not all p-factors are equal to any given X
;;; ------------------------------------------------------------------

(defun all-facs-equal-to (p X S)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom S) t
    (and (equal (fac p (car S)) X) (all-facs-equal-to p X (cdr S)))))

(defthm all-equal-to-sel-list-when-all-facs-equal
  (implies (all-facs-equal-to p X S)
           (all-equal-to X (sel-list p S b c))))

(defthm sel-sum-when-all-facs-equal
  (implies (and (all-facs-equal-to p X S) (triple-listp L S) (posp3 p))
           (or (equal (sel-sum p L S b c) X)
               (equal (sel-sum p L S b c) (bv-zero L))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (sel-sum)
                                  (all-equal-to-sel-list-when-all-facs-equal
                                   bv-sum-when-all-equal-to))
                  :use (all-equal-to-sel-list-when-all-facs-equal
                        (:instance bv-sum-when-all-equal-to (v X) (lst (sel-list p S b c)))))))

(defthm schemep-forward
  (implies (schemep n S)
           (and (posp n) (summand-listp (sq n) S) (triple-listp (sq n) S) (true-listp S)))
  :rule-classes :forward-chaining)

;; With n >= 2 the units E_00 and E_01 are distinct nonzero slice sums,
;; so the p-factors cannot all be equal to X.
(defthm not-all-facs-equal
  (implies (and (schemep n S) (<= 2 n) (posp3 p))
           (not (all-facs-equal-to p X S)))
  :hints (("Goal"
           :in-theory (disable span-lemma schemep)
           :use ((:instance span-lemma (x 0) (y 0))
                 (:instance span-lemma (x 0) (y 1))
                 (:instance sel-sum-when-all-facs-equal (L (sq n))
                            (b (span-b p n 0 0)) (c (span-c p n 0 0)))
                 (:instance sel-sum-when-all-facs-equal (L (sq n))
                            (b (span-b p n 0 1)) (c (span-c p n 0 1)))
                 (:instance unit-injective (L (sq n)) (k1 (midx n 0 0)) (k2 (midx n 0 1)))
                 (:instance unit-not-zero (L (sq n)) (k (midx n 0 0)))
                 (:instance unit-not-zero (L (sq n)) (k (midx n 0 1)))))))

;; The first summand of S whose p-factor differs from X.
(defun find-fac-not (p X S)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom S) nil)
        ((equal (fac p (car S)) X) (find-fac-not p X (cdr S)))
        (t (car S))))

(defthm find-fac-not-works
  (implies (not (all-facs-equal-to p X S))
           (and (member-equal (find-fac-not p X S) S)
                (not (equal (fac p (find-fac-not p X S)) X)))))

(defthm find-fac-not-member
  (implies (and (schemep n S) (<= 2 n) (posp3 p))
           (and (member-equal (find-fac-not p X S) S)
                (not (equal (fac p (find-fac-not p X S)) X))))
  :hints (("Goal" :in-theory (disable schemep find-fac-not-works)
                  :use (find-fac-not-works not-all-facs-equal))))
