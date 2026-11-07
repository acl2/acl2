; x-span.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/span.lisp
; produced by rename.py in this directory; do not edit by hand.
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

(include-book "x-scheme")

;;; ------------------------------------------------------------------
;;; Slice selection
;;; ------------------------------------------------------------------

;; Is summand s selected by the slice (b,c) for position p?
(defun x-selectedp (p s b c)
  (declare (xargs :guard (and (natp p) (true-listp s) (natp b) (natp c))
                  :verify-guards nil))
  (and (equal (nth b (x-fac (x-other-lo p) s)) 1)
       (equal (nth c (x-fac (x-other-hi p) s)) 1)))

;; The p-factors of the selected summands.
(defun x-sel-list (p S b c)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom S) nil)
        ((x-selectedp p (car S) b c) (cons (x-fac p (car S)) (x-sel-list p (cdr S) b c)))
        (t (x-sel-list p (cdr S) b c))))

;; All p-factors of S.
(defun x-facs (p S)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom S) nil (cons (x-fac p (car S)) (x-facs p (cdr S)))))

(defun x-sel-sum (p L S b c)
  (declare (xargs :guard t :verify-guards nil))
  (x-bv-sum L (x-sel-list p S b c)))

(defthm x-subsetp-sel-list-facs
  (subsetp-equal (x-sel-list p S b c) (x-facs p S)))

(defthm x-member-facs
  (implies (member-equal s1 S) (member-equal (x-fac p s1) (x-facs p S))))

(defthm x-bv-listp-of-sel-list
  (implies (and (x-triple-listp L S) (x-posp3 p))
           (x-bv-listp L (x-sel-list p S b c)))
  :hints (("Goal" :in-theory (enable x-fac x-posp3 x-other-lo x-other-hi))))

(defthm x-bv-listp-of-facs
  (implies (and (x-triple-listp L S) (x-posp3 p))
           (x-bv-listp L (x-facs p S)))
  :hints (("Goal" :in-theory (enable x-fac x-posp3))))

;;; ------------------------------------------------------------------
;;; Tensor coordinates by position
;;; ------------------------------------------------------------------

;; Index of the tensor coordinate whose position-p coordinate is a and
;; whose lo/hi coordinates are b and c.
(defun x-coord-idx (p L a b c)
  (declare (xargs :guard t :verify-guards nil))
  (case p
    (0 (x-tidx3 L L a b c))
    (1 (x-tidx3 L L b a c))
    (t (x-tidx3 L L b c a))))

(defthm x-nth-coord-idx-of-rank1-0
  (implies (and (x-triplep L s1) (natp L)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth (x-coord-idx 0 L a b c) (x-rank1 s1))
                  (x-band (nth a (car s1)) (x-band (nth b (cadr s1)) (nth c (caddr s1))))))
  :hints (("Goal" :in-theory (e/d (x-rank1 x-coord-idx) (x-nth-of-outer3))
                  :use ((:instance x-nth-of-outer3 (A (car s1)) (B (cadr s1)) (C (caddr s1))
                                   (ia a) (ib b) (ic c))))))

(defthm x-nth-coord-idx-of-rank1-1
  (implies (and (x-triplep L s1) (natp L)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth (x-coord-idx 1 L a b c) (x-rank1 s1))
                  (x-band (nth a (cadr s1)) (x-band (nth b (car s1)) (nth c (caddr s1))))))
  :hints (("Goal" :in-theory (e/d (x-rank1 x-coord-idx) (x-nth-of-outer3))
                  :use ((:instance x-nth-of-outer3 (A (car s1)) (B (cadr s1)) (C (caddr s1))
                                   (ia b) (ib a) (ic c))))))

(defthm x-nth-coord-idx-of-rank1-2
  (implies (and (x-triplep L s1) (natp L)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth (x-coord-idx 2 L a b c) (x-rank1 s1))
                  (x-band (nth a (caddr s1)) (x-band (nth b (car s1)) (nth c (cadr s1))))))
  :hints (("Goal" :in-theory (e/d (x-rank1 x-coord-idx) (x-nth-of-outer3))
                  :use ((:instance x-nth-of-outer3 (A (car s1)) (B (cadr s1)) (C (caddr s1))
                                   (ia b) (ib c) (ic a))))))

(defthm x-nth-coord-idx-of-rank1
  (implies (and (x-posp3 p) (x-triplep L s1) (natp L)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth (x-coord-idx p L a b c) (x-rank1 s1))
                  (x-band (nth a (x-fac p s1))
                        (x-band (nth b (x-fac (x-other-lo p) s1))
                              (nth c (x-fac (x-other-hi p) s1))))))
  :hints (("Goal" :in-theory (e/d (x-fac x-posp3 x-other-lo x-other-hi) (x-coord-idx x-rank1 x-tidx3))
                  :cases ((equal p 0) (equal p 1) (equal p 2)))))

(defthm x-coord-idx-bound
  (implies (and (x-posp3 p) (natp L) (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (< (x-coord-idx p L a b c) (x-tlen L)))
  :hints (("Goal" :in-theory (e/d (x-posp3) (x-tidx3-bound))
                  :use ((:instance x-tidx3-bound (LA L) (LB L) (LC L))
                        (:instance x-tidx3-bound (LA L) (LB L) (LC L) (a b) (b a))
                        (:instance x-tidx3-bound (LA L) (LB L) (LC L) (a b) (b c) (c a)))))
  :rule-classes :linear)

(defthm x-natp-of-coord-idx
  (implies (and (natp L) (natp a) (natp b) (natp c))
           (natp (x-coord-idx p L a b c)))
  :rule-classes :type-prescription)

(in-theory (disable x-coord-idx))

;; Coordinate a of the slice sum is the tensor coordinate (a at p, b, c).
(defthm x-nth-of-sel-sum
  (implies (and (x-posp3 p) (natp L) (x-triple-listp L S)
                (natp a) (natp b) (natp c) (< a L) (< b L) (< c L))
           (equal (nth a (x-sel-sum p L S b c))
                  (nth (x-coord-idx p L a b c) (x-triple-sum L S))))
  :hints (("Goal" :induct (x-sel-list p S b c)
                  :in-theory (e/d (x-posp3 x-other-lo x-other-hi) (x-nth-coord-idx-of-rank1)))
          ("Subgoal *1/1" :use ((:instance x-coord-idx-bound)))
          ("Subgoal *1/3" :use ((:instance x-nth-coord-idx-of-rank1 (s1 (car S)))
                                (:instance x-coord-idx-bound)))
          ("Subgoal *1/2" :use ((:instance x-nth-coord-idx-of-rank1 (s1 (car S)))
                                (:instance x-coord-idx-bound)))))

;;; ------------------------------------------------------------------
;;; The span lemma
;;; ------------------------------------------------------------------

;; Coordinates (b,c) that pick out the target E_xy at position p
;; (using k = 0, i = 0, or j = 0 respectively as the free index).
(defun x-span-b (p n x y)
  (declare (xargs :guard (and (natp n) (natp x) (natp y))))
  (case p
    (0 (x-midx n y 0))
    (1 (x-midx n 0 x))
    (t (x-midx n x 0))))

(defun x-span-c (p n x y)
  (declare (xargs :guard (and (natp n) (natp x) (natp y))))
  (case p
    (0 (x-midx n x 0))
    (1 (x-midx n 0 y))
    (t (x-midx n 0 y))))

(defthm x-mmt-coeff-at-span-coords
  (implies (and (posp n) (x-posp3 p) (natp a) (< a (x-sq n))
                (natp x) (natp y) (< x n) (< y n))
           (equal (nth (x-coord-idx p (x-sq n) a (x-span-b p n x y) (x-span-c p n x y)) (x-mmt n))
                  (if (equal a (x-midx n x y)) 1 0)))
  :hints (("Goal" :in-theory (e/d (x-coord-idx x-posp3) (x-nth-of-mmt))
                  :use ((:instance x-nth-of-mmt (b (x-span-b 0 n x y)) (c (x-span-c 0 n x y)))
                        (:instance x-nth-of-mmt (a (x-span-b 1 n x y)) (b a) (c (x-span-c 1 n x y)))
                        (:instance x-nth-of-mmt (a (x-span-b 2 n x y)) (b (x-span-c 2 n x y)) (c a))
                        (:instance x-mmt-coeff-slice-A (i x) (j y) (k 0))
                        (:instance x-mmt-coeff-slice-B (b a) (i 0) (j x) (k y))
                        (:instance x-mmt-coeff-slice-C (c a) (i x) (j 0) (k y))))))

(defthm x-natp-of-span-b
  (implies (and (natp n) (natp x) (natp y)) (natp (x-span-b p n x y)))
  :rule-classes :type-prescription)
(defthm x-natp-of-span-c
  (implies (and (natp n) (natp x) (natp y)) (natp (x-span-c p n x y)))
  :rule-classes :type-prescription)
(defthm x-span-b-bound
  (implies (and (posp n) (natp x) (natp y) (< x n) (< y n))
           (< (x-span-b p n x y) (x-sq n)))
  :rule-classes :linear)
(defthm x-span-c-bound
  (implies (and (posp n) (natp x) (natp y) (< x n) (< y n))
           (< (x-span-c p n x y) (x-sq n)))
  :rule-classes :linear)

(in-theory (disable x-span-b x-span-c))

;; Per-coordinate form of the span lemma.
(defthm x-span-lemma-nth
  (implies (and (x-schemep n S) (x-posp3 p)
                (natp x) (natp y) (< x n) (< y n)
                (natp a) (< a (x-sq n)))
           (equal (nth a (x-sel-sum p (x-sq n) S (x-span-b p n x y) (x-span-c p n x y)))
                  (if (equal a (x-midx n x y)) 1 0)))
  :hints (("Goal" :in-theory (disable x-sel-sum x-nth-of-sel-sum x-mmt-coeff-at-span-coords)
                  :use ((:instance x-nth-of-sel-sum (L (x-sq n))
                                   (b (x-span-b p n x y)) (c (x-span-c p n x y)))
                        (:instance x-mmt-coeff-at-span-coords)))))

(defthm x-bvp-of-sel-sum (x-bvp (x-sel-sum p L S b c)))
(defthm x-len-of-sel-sum
  (implies (and (x-triple-listp L S) (x-posp3 p))
           (equal (len (x-sel-sum p L S b c)) (nfix L))))

(in-theory (disable x-sel-sum))

;; Lemma 4.2: the slice sum of the p-factors of a scheme is E_xy.
(defthm x-span-lemma
  (implies (and (x-schemep n S) (x-posp3 p)
                (natp x) (natp y) (< x n) (< y n))
           (equal (x-sel-sum p (x-sq n) S (x-span-b p n x y) (x-span-c p n x y))
                  (x-unit (x-sq n) (x-midx n x y))))
  :hints (("Goal"
           :in-theory (disable x-span-lemma-nth x-bv-diff-index-witness x-nth-of-unit)
           :use ((:instance x-bv-extensionality
                            (x (x-sel-sum p (x-sq n) S (x-span-b p n x y) (x-span-c p n x y)))
                            (y (x-unit (x-sq n) (x-midx n x y))))
                 (:instance x-bv-diff-index-witness
                            (x (x-sel-sum p (x-sq n) S (x-span-b p n x y) (x-span-c p n x y)))
                            (y (x-unit (x-sq n) (x-midx n x y))))
                 (:instance x-span-lemma-nth
                            (a (x-bv-diff-index (x-sel-sum p (x-sq n) S (x-span-b p n x y) (x-span-c p n x y))
                                              (x-unit (x-sq n) (x-midx n x y)))))
                 (:instance x-nth-of-unit (L (x-sq n)) (k (x-midx n x y))
                            (i (x-bv-diff-index (x-sel-sum p (x-sq n) S (x-span-b p n x y) (x-span-c p n x y))
                                              (x-unit (x-sq n) (x-midx n x y)))))))))

;;; ------------------------------------------------------------------
;;; Consequence: for n >= 2, not all p-factors are equal to any given X
;;; ------------------------------------------------------------------

(defun x-all-facs-equal-to (p X S)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom S) t
    (and (equal (x-fac p (car S)) X) (x-all-facs-equal-to p X (cdr S)))))

(defthm x-all-equal-to-sel-list-when-all-facs-equal
  (implies (x-all-facs-equal-to p X S)
           (x-all-equal-to X (x-sel-list p S b c))))

(defthm x-sel-sum-when-all-facs-equal
  (implies (and (x-all-facs-equal-to p X S) (x-triple-listp L S) (x-posp3 p))
           (or (equal (x-sel-sum p L S b c) X)
               (equal (x-sel-sum p L S b c) (x-bv-zero L))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (x-sel-sum)
                                  (x-all-equal-to-sel-list-when-all-facs-equal
                                   x-bv-sum-when-all-equal-to))
                  :use (x-all-equal-to-sel-list-when-all-facs-equal
                        (:instance x-bv-sum-when-all-equal-to (v X) (lst (x-sel-list p S b c)))))))

(defthm x-schemep-forward
  (implies (x-schemep n S)
           (and (posp n) (x-summand-listp (x-sq n) S) (x-triple-listp (x-sq n) S) (true-listp S)))
  :rule-classes :forward-chaining)

;; With n >= 2 the units E_00 and E_01 are distinct nonzero slice sums,
;; so the p-factors cannot all be equal to X.
(defthm x-not-all-facs-equal
  (implies (and (x-schemep n S) (<= 2 n) (x-posp3 p))
           (not (x-all-facs-equal-to p X S)))
  :hints (("Goal"
           :in-theory (disable x-span-lemma x-schemep)
           :use ((:instance x-span-lemma (x 0) (y 0))
                 (:instance x-span-lemma (x 0) (y 1))
                 (:instance x-sel-sum-when-all-facs-equal (L (x-sq n))
                            (b (x-span-b p n 0 0)) (c (x-span-c p n 0 0)))
                 (:instance x-sel-sum-when-all-facs-equal (L (x-sq n))
                            (b (x-span-b p n 0 1)) (c (x-span-c p n 0 1)))
                 (:instance x-unit-injective (L (x-sq n)) (k1 (x-midx n 0 0)) (k2 (x-midx n 0 1)))
                 (:instance x-unit-not-zero (L (x-sq n)) (k (x-midx n 0 0)))
                 (:instance x-unit-not-zero (L (x-sq n)) (k (x-midx n 0 1)))))))

;; The first summand of S whose p-factor differs from X.
(defun x-find-fac-not (p X S)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom S) nil)
        ((equal (x-fac p (car S)) X) (x-find-fac-not p X (cdr S)))
        (t (car S))))

(defthm x-find-fac-not-works
  (implies (not (x-all-facs-equal-to p X S))
           (and (member-equal (x-find-fac-not p X S) S)
                (not (equal (x-fac p (x-find-fac-not p X S)) X)))))

(defthm x-find-fac-not-member
  (implies (and (x-schemep n S) (<= 2 n) (x-posp3 p))
           (and (member-equal (x-find-fac-not p X S) S)
                (not (equal (x-fac p (x-find-fac-not p X S)) X))))
  :hints (("Goal" :in-theory (disable x-schemep x-find-fac-not-works)
                  :use (x-find-fac-not-works x-not-all-facs-equal))))
