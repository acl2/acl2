; x-zero-subset.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/zero-subset.lisp
; produced by rename.py in this directory; do not edit by hand.
; zero-subset.lisp -- Lemma 4.5 of the paper (zero-subset).
;
; If R is a sub-multiset of a scheme S whose rank-one tensors sum to
; zero, then there is a flip/plus path from S to S \\ R.
;
; Following the paper: every summand of R is decomposed into standard
; basis tensors E_a (x) E_b (x) E_c (each factor split one unit at a time
; using Lemma 4.4 and a flip on another position); since the basis
; tensors are linearly independent and R sums to zero, every basis
; tensor then occurs an even number of times and the pairs are deleted
; with Observation 4.1.
;
; We represent S as (append R rest) up to permutation: the current
; scheme is always (append Rcur rest) where Rcur is the current
; (partially decomposed) copy of R.

(in-package "ACL2")

(include-book "x-add-arbitrary")

;;; ------------------------------------------------------------------
;;; Splitting one unit off a factor
;;; ------------------------------------------------------------------

;; For a summand u = (A B C) in the current scheme with weight(A) >= 2:
;; add two copies of E (x) B (x) C where E is the unit at the lowest set
;; bit of A (Lemma 4.4), then flip on position 1 with s = E(x)B(x)C and
;; t = A(x)B(x)C, which yields E(x)B(x)(C+C) = 0 (deleted) and
;; (A+E)(x)B(x)C.  Net effect: A(x)B(x)C is replaced by (A+E)(x)B(x)C and
;; E(x)B(x)C.  Positions 1 and 2 are handled the same way with a flip on
;; position 0.

(defun x-split-unit (L u)
  (declare (xargs :guard t :verify-guards nil))
  ;; returns (mv p E) : the first position whose factor is not a unit, and the unit
  (cond ((> (x-bv-weight (x-fac 0 u)) 1) (mv 0 (x-unit L (x-bv-first-one (x-fac 0 u)))))
        ((> (x-bv-weight (x-fac 1 u)) 1) (mv 1 (x-unit L (x-bv-first-one (x-fac 1 u)))))
        (t (mv 2 (x-unit L (x-bv-first-one (x-fac 2 u)))))))

;; The flip position used to split position p.
(defun x-split-flip-pos (p)
  (declare (xargs :guard t))
  (if (eql p 0) 1 0))

;; A summand all of whose factors are units.
(defun x-basic-summandp (u)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (x-bv-weight (x-fac 0 u)) 1)
       (equal (x-bv-weight (x-fac 1 u)) 1)
       (equal (x-bv-weight (x-fac 2 u)) 1)))

(defun x-basic-listp (R)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom R) t (and (x-basic-summandp (car R)) (x-basic-listp (cdr R)))))

;; Measure of the decomposition: total excess weight.
(defun x-excess-weight (R)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom R) 0
    (+ (- (x-bv-weight (x-fac 0 (car R))) 1)
       (- (x-bv-weight (x-fac 1 (car R))) 1)
       (- (x-bv-weight (x-fac 2 (car R))) 1)
       (x-excess-weight (cdr R)))))

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

;;; ------------------------------------------------------------------
;;; Weights, excess, and the first non-unit factor at a position
;;; ------------------------------------------------------------------

(defun x-excess-at (p R)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom R) 0
    (+ (- (x-bv-weight (x-fac p (car R))) 1) (x-excess-at p (cdr R)))))

(defun x-find-nonunit (p R)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom R) nil)
        ((> (x-bv-weight (x-fac p (car R))) 1) (car R))
        (t (x-find-nonunit p (cdr R)))))

(defthm x-find-nonunit-works
  (implies (x-find-nonunit p R)
           (and (member-equal (x-find-nonunit p R) R)
                (< 1 (x-bv-weight (x-fac p (x-find-nonunit p R)))))))

(defthm x-weight-of-fac-when-summandp
  (implies (and (posp L) (x-summandp L s) (x-posp3 p))
           (<= 1 (x-bv-weight (x-fac p s))))
  :hints (("Goal" :in-theory (disable x-bv-weight-zero-iff x-fac-nonzero-when-summandp)
                  :use (x-fac-nonzero-when-summandp
                        (:instance x-bv-weight-zero-iff (x (x-fac p s))))))
  :rule-classes :linear)

(defthm x-not-summandp-nil
  (not (x-summandp L nil))
  :hints (("Goal" :in-theory (enable x-summandp))))

(defthm x-weight-le-1-when-no-nonunit
  (implies (and (not (x-find-nonunit p R)) (member-equal u R) (x-summand-listp L R))
           (<= (x-bv-weight (x-fac p u)) 1))
  :hints (("Goal" :induct (x-summand-listp L R)))
  :rule-classes :linear)

(defthm x-excess-at-nonneg
  (implies (and (posp L) (x-summand-listp L R) (x-posp3 p))
           (<= 0 (x-excess-at p R)))
  :rule-classes :linear)

(defthm x-excess-at-zero-when-no-nonunit
  (implies (and (posp L) (x-summand-listp L R) (x-posp3 p) (not (x-find-nonunit p R)))
           (equal (x-excess-at p R) 0)))

(defthm x-excess-at-pos-when-nonunit
  (implies (and (posp L) (x-summand-listp L R) (x-posp3 p) (x-find-nonunit p R))
           (<= 1 (x-excess-at p R)))
  :hints (("Goal" :induct (x-summand-listp L R)))
  :rule-classes :linear)

(defthm x-excess-at-of-remove1
  (implies (member-equal u R)
           (equal (x-excess-at p (remove1-equal u R))
                  (- (x-excess-at p R) (- (x-bv-weight (x-fac p u)) 1))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

;;; ------------------------------------------------------------------
;;; Splitting a unit off the p-factor of a summand u in R
;;; ------------------------------------------------------------------

;; E = unit at the lowest set bit of (fac p u)
(defun x-split-E (L p u)
  (declare (xargs :guard t :verify-guards nil))
  (x-unit L (x-bv-first-one (x-fac p u))))

(defun x-split-u1 (L p u)        ; E (x) rest
  (declare (xargs :guard t :verify-guards nil))
  (x-set-fac p (x-split-E L p u) u))

(defun x-split-u2 (L p u)        ; (A+E) (x) rest
  (declare (xargs :guard t :verify-guards nil))
  (x-set-fac p (x-bv+ (x-fac p u) (x-split-E L p u)) u))

;; The position on which the flip is performed.
(defun x-split-flip-pos (p)
  (declare (xargs :guard t))
  (if (eql p 0) 1 0))

(defthm x-split-E-facts
  (implies (and (posp L) (x-summandp L u) (x-posp3 p))
           (and (x-bvp (x-split-E L p u))
                (equal (len (x-split-E L p u)) L)
                (not (equal (x-split-E L p u) (x-bv-zero L)))
                (equal (x-bv-weight (x-split-E L p u)) 1)))
  :hints (("Goal" :in-theory (disable x-bv-first-one-witness)
                  :use ((:instance x-bv-first-one-witness (x (x-fac p u)))))))

(defthm x-split-u1-summandp
  (implies (and (posp L) (x-summandp L u) (x-posp3 p))
           (x-summandp L (x-split-u1 L p u)))
  :hints (("Goal" :in-theory (disable x-split-E-facts) :use x-split-E-facts)))

(defthm x-weight-of-A-plus-E
  (implies (and (posp L) (x-summandp L u) (x-posp3 p))
           (equal (x-bv-weight (x-bv+ (x-fac p u) (x-split-E L p u)))
                  (1- (x-bv-weight (x-fac p u)))))
  :hints (("Goal" :in-theory (disable x-bv-first-one-witness x-bv-weight-of-bv+-unit)
                  :use ((:instance x-bv-first-one-witness (x (x-fac p u)))
                        (:instance x-bv-weight-of-bv+-unit (x (x-fac p u)) (k (x-bv-first-one (x-fac p u))))))))

(defthm x-split-u2-summandp
  (implies (and (posp L) (x-summandp L u) (x-posp3 p) (< 1 (x-bv-weight (x-fac p u))))
           (x-summandp L (x-split-u2 L p u)))
  :hints (("Goal" :in-theory (disable x-split-E-facts x-bv-weight-zero-iff x-weight-of-A-plus-E)
                  :use (x-split-E-facts x-weight-of-A-plus-E
                        (:instance x-bv-weight-zero-iff (x (x-bv+ (x-fac p u) (x-split-E L p u))))))))

;; rank1 (set-fac p v s) + rank1 (set-fac p w s) = rank1 (set-fac p (v+w) s)
(defthm x-rank1-of-set-fac-sum
  (implies (and (posp L) (x-summandp L s) (x-posp3 p)
                (x-bvp v) (x-bvp w) (equal (len v) L) (equal (len w) L))
           (equal (x-bv+ (x-rank1 (x-set-fac p v s)) (x-rank1 (x-set-fac p w s)))
                  (x-rank1 (x-set-fac p (x-bv+ v w) s))))
  :hints (("Goal" :in-theory (e/d (x-rank1 x-set-fac x-posp3) ())
                  :use ((:instance x-summandp-facts))
                  :cases ((equal p 0) (equal p 1) (equal p 2)))))

(defthm x-split-preserves-rank1
  (implies (and (posp L) (x-summandp L u) (x-posp3 p))
           (equal (x-bv+ (x-rank1 (x-split-u1 L p u)) (x-rank1 (x-split-u2 L p u)))
                  (x-rank1 u)))
  :hints (("Goal" :in-theory (disable x-split-E-facts x-rank1-of-set-fac-sum x-set-fac-of-fac-same)
                  :use (x-split-E-facts
                        (:instance x-summandp-facts (s u))
                        (:instance x-set-fac-of-fac-same (s u))
                        (:instance x-rank1-of-set-fac-sum (s u) (v (x-split-E L p u))
                                   (w (x-bv+ (x-fac p u) (x-split-E L p u))))))))

;;; ------------------------------------------------------------------
;;; The split step as a path: Lemma 4.4 then one flip
;;; ------------------------------------------------------------------

(defthm x-apply-flip-move-second-zero
  (implies (and (posp L) (x-posp3 p) (x-summandp L s) (x-summandp L u)
                (not (equal (x-bv+ (x-fac (x-other-hi p) s) (x-fac (x-other-hi p) u)) (x-bv-zero L)))
                (equal (x-bv+ (x-fac (x-other-lo p) u) (x-fac (x-other-lo p) s)) (x-bv-zero L)))
           (equal (x-apply-move L (x-flip-move p s u) sch)
                  (append (remove1-equal u (remove1-equal s sch))
                          (list (x-set-fac (x-other-hi p)
                                         (x-bv+ (x-fac (x-other-hi p) s) (x-fac (x-other-hi p) u))
                                         s)))))
  :hints (("Goal" :in-theory (enable x-apply-move x-flip-results x-flip-move))))

(defthm x-nz-matp-intro
  (implies (and (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n)))))
           (x-nz-matp n X))
  :hints (("Goal" :in-theory (enable x-nz-matp))))

(defthm x-list-of-facs
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (list (x-fac 0 s) (x-fac 1 s) (x-fac 2 s)) s))
  :hints (("Goal" :in-theory (enable x-fac))))

;; The current copy of R after splitting u at position p.
(defun x-split-R (L p u R)
  (declare (xargs :guard t :verify-guards nil))
  (list* (x-split-u1 L p u) (x-split-u2 L p u) (remove1-equal u R)))

;; The path: add two copies of u1 = E (x) ..., then flip u1 against u.
(defun x-split-path (n sch p u)
  (declare (xargs :guard t :verify-guards nil))
  (let ((u1 (x-split-u1 (x-sq n) p u)))
    (append (x-add-arb-path n sch (x-fac 0 u1) (x-fac 1 u1) (x-fac 2 u1))
            (list (x-flip-move (x-split-flip-pos p) u1 u)))))

(defthm x-split-u1-ne-u
  (implies (and (posp L) (x-summandp L u) (x-posp3 p) (< 1 (x-bv-weight (x-fac p u))))
           (not (equal (x-split-u1 L p u) u)))
  :hints (("Goal" :in-theory (disable x-split-E-facts)
                  :use (x-split-E-facts
                        (:instance x-not-equal-set-fac-when-fac-differs-2
                                   (v (x-split-E L p u)) (s u) (u u))))))

(defthm x-remove1-of-append-when-member-first-2
  (implies (member-equal a x)
           (equal (remove1-equal a (append x y))
                  (append (remove1-equal a x) y)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-perm-split-shape
  (perm (append (cons u1 R1) (list u2)) (list* u1 u2 R1))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal) (perm-of-append x-perm-append-list-1))
                  :use ((:instance x-perm-append-list-1 (x (cons u1 R1)) (a u2))))))

(defun x-ind-list (R) (if (atom R) nil (x-ind-list (cdr R))))

(defthm x-summandp-when-member-of-append-first
  (implies (and (member-equal u R) (x-summand-listp L (append R rest)))
           (x-summandp L u))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("Goal" :induct (x-ind-list R))))

(defthm x-summand-listp-append-parts
  (implies (x-summand-listp L (append R rest))
           (and (x-summand-listp L rest) (x-summand-listp L (true-list-fix R))))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (x-ind-list R))))

(defthm x-member-of-append-first
  (implies (member-equal u R) (member-equal u (append R rest)))
  :hints (("Goal" :induct (x-ind-list R))))

;; In this book all positions are concrete, so we normalize set-fac to
;; explicit lists.
(defthm x-set-fac-0-as-list
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (x-set-fac 0 v s) (list v (x-fac 1 s) (x-fac 2 s))))
  :hints (("Goal" :in-theory (enable x-set-fac x-fac))))
(defthm x-set-fac-1-as-list
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (x-set-fac 1 v s) (list (x-fac 0 s) v (x-fac 2 s))))
  :hints (("Goal" :in-theory (enable x-set-fac x-fac))))
(defthm x-set-fac-2-as-list
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (x-set-fac 2 v s) (list (x-fac 0 s) (x-fac 1 s) v)))
  :hints (("Goal" :in-theory (enable x-set-fac x-fac))))
(defthm x-fac-of-list
  (and (equal (x-fac 0 (list a b c)) a)
       (equal (x-fac 1 (list a b c)) b)
       (equal (x-fac 2 (list a b c)) c))
  :hints (("Goal" :in-theory (enable x-fac))))

(defthm x-perm-split-shape-2
  (perm (cons a (append x (append y (list c)))) (list* a c (append x y)))
  :hints (("Goal" :in-theory (disable perm-of-append x-perm-append-list-1)
                  :use ((:instance x-perm-append-list-1 (x (append x y)) (a c))))))

(encapsulate ()
  (local (in-theory (disable x-summandp-facts-rw perm-of-cons-arg1 perm-of-cons-arg2
                             x-perm-rotate-3 x-perm-rotate-4 x-perm-rotate-3-append
                             x-perm-rotate-4-append x-perm-step4-shape
                             x-perm-append-list-1 x-perm-append-list-2
                             x-perm-cons-remove1-when-member
                             x-set-fac-of-set-fac-other-commute
                             x-split-E-facts x-split-u1-ne-u
                             x-apply-flip-move-first-zero x-apply-flip-move-second-zero
                             x-flip-move-ok x-perm-split-shape-2 x-perm-split-shape)))

  ;; Position 0: flip on position 1; the first result E(x)B(x)(C+C) vanishes.
  (defthm x-split-step-0
    (implies (and (x-schemep n (append R rest)) (<= 2 n)
                  (member-equal u R) (< 1 (x-bv-weight (x-fac 0 u))))
             (let* ((L (x-sq n))
                    (sch (append R rest))
                    (u1 (x-split-u1 L 0 u))
                    (mid (x-apply-path L (x-add-arb-path n sch (x-fac 0 u1) (x-fac 1 u1) (x-fac 2 u1)) sch)))
               (and (x-path-ok-p L (x-add-arb-path n sch (x-fac 0 u1) (x-fac 1 u1) (x-fac 2 u1)) sch)
                    (x-move-ok-p (x-flip-move 1 u1 u) mid)
                    (perm (x-apply-move L (x-flip-move 1 u1 u) mid)
                          (append (x-split-R L 0 u R) rest)))))
    :hints (("Goal" :do-not-induct t
                    :in-theory (e/d (x-split-flip-pos) (x-split-u1-summandp x-split-u2-summandp))
                    :use ((:instance x-summandp-facts (L (x-sq n)) (s u))
                          (:instance x-split-E-facts (L (x-sq n)) (p 0))
                          (:instance x-split-u1-summandp (L (x-sq n)) (p 0))
                          (:instance x-split-u2-summandp (L (x-sq n)) (p 0))
                          (:instance x-split-u1-ne-u (L (x-sq n)) (p 0))
                          (:instance x-summandp-facts (L (x-sq n)) (s (x-split-u1 (x-sq n) 0 u)))
                          (:instance x-perm-split-shape-2 (a (x-split-u1 (x-sq n) 0 u))
                                     (x (remove1-equal u R)) (y rest) (c (x-split-u2 (x-sq n) 0 u)))
                          (:instance x-flip-move-ok (p 1) (s (x-split-u1 (x-sq n) 0 u)) (u u)
                                     (sch (list* (x-split-u1 (x-sq n) 0 u) (x-split-u1 (x-sq n) 0 u)
                                                 (append R rest))))
                          (:instance x-apply-flip-move-first-zero (L (x-sq n)) (p 1)
                                     (s (x-split-u1 (x-sq n) 0 u)) (u u)
                                     (sch (list* (x-split-u1 (x-sq n) 0 u) (x-split-u1 (x-sq n) 0 u)
                                                 (append R rest))))))))

  ;; Position 1: flip on position 0; the first result A(x)E(x)(C+C) vanishes.
  (defthm x-split-step-1
    (implies (and (x-schemep n (append R rest)) (<= 2 n)
                  (member-equal u R) (< 1 (x-bv-weight (x-fac 1 u))))
             (let* ((L (x-sq n))
                    (sch (append R rest))
                    (u1 (x-split-u1 L 1 u))
                    (mid (x-apply-path L (x-add-arb-path n sch (x-fac 0 u1) (x-fac 1 u1) (x-fac 2 u1)) sch)))
               (and (x-path-ok-p L (x-add-arb-path n sch (x-fac 0 u1) (x-fac 1 u1) (x-fac 2 u1)) sch)
                    (x-move-ok-p (x-flip-move 0 u1 u) mid)
                    (perm (x-apply-move L (x-flip-move 0 u1 u) mid)
                          (append (x-split-R L 1 u R) rest)))))
    :hints (("Goal" :do-not-induct t
                    :in-theory (e/d (x-split-flip-pos) (x-split-u1-summandp x-split-u2-summandp))
                    :use ((:instance x-summandp-facts (L (x-sq n)) (s u))
                          (:instance x-split-E-facts (L (x-sq n)) (p 1))
                          (:instance x-split-u1-summandp (L (x-sq n)) (p 1))
                          (:instance x-split-u2-summandp (L (x-sq n)) (p 1))
                          (:instance x-split-u1-ne-u (L (x-sq n)) (p 1))
                          (:instance x-summandp-facts (L (x-sq n)) (s (x-split-u1 (x-sq n) 1 u)))
                          (:instance x-perm-split-shape-2 (a (x-split-u1 (x-sq n) 1 u))
                                     (x (remove1-equal u R)) (y rest) (c (x-split-u2 (x-sq n) 1 u)))
                          (:instance x-flip-move-ok (p 0) (s (x-split-u1 (x-sq n) 1 u)) (u u)
                                     (sch (list* (x-split-u1 (x-sq n) 1 u) (x-split-u1 (x-sq n) 1 u)
                                                 (append R rest))))
                          (:instance x-apply-flip-move-first-zero (L (x-sq n)) (p 0)
                                     (s (x-split-u1 (x-sq n) 1 u)) (u u)
                                     (sch (list* (x-split-u1 (x-sq n) 1 u) (x-split-u1 (x-sq n) 1 u)
                                                 (append R rest))))))))

  ;; Position 2: flip on position 0; now the second result A(x)(B+B)(x)C vanishes
  ;; and the first result is A(x)B(x)(E+C).
  (defthm x-split-step-2
    (implies (and (x-schemep n (append R rest)) (<= 2 n)
                  (member-equal u R) (< 1 (x-bv-weight (x-fac 2 u))))
             (let* ((L (x-sq n))
                    (sch (append R rest))
                    (u1 (x-split-u1 L 2 u))
                    (mid (x-apply-path L (x-add-arb-path n sch (x-fac 0 u1) (x-fac 1 u1) (x-fac 2 u1)) sch)))
               (and (x-path-ok-p L (x-add-arb-path n sch (x-fac 0 u1) (x-fac 1 u1) (x-fac 2 u1)) sch)
                    (x-move-ok-p (x-flip-move 0 u1 u) mid)
                    (perm (x-apply-move L (x-flip-move 0 u1 u) mid)
                          (append (x-split-R L 2 u R) rest)))))
    :hints (("Goal" :do-not-induct t
                    :in-theory (e/d (x-split-flip-pos) (x-split-u1-summandp x-split-u2-summandp))
                    :use ((:instance x-summandp-facts (L (x-sq n)) (s u))
                          (:instance x-split-E-facts (L (x-sq n)) (p 2))
                          (:instance x-split-u1-summandp (L (x-sq n)) (p 2))
                          (:instance x-split-u2-summandp (L (x-sq n)) (p 2))
                          (:instance x-split-u1-ne-u (L (x-sq n)) (p 2))
                          (:instance x-summandp-facts (L (x-sq n)) (s (x-split-u1 (x-sq n) 2 u)))
                          (:instance x-perm-split-shape-2 (a (x-split-u1 (x-sq n) 2 u))
                                     (x (remove1-equal u R)) (y rest) (c (x-split-u2 (x-sq n) 2 u)))
                          (:instance x-flip-move-ok (p 0) (s (x-split-u1 (x-sq n) 2 u)) (u u)
                                     (sch (list* (x-split-u1 (x-sq n) 2 u) (x-split-u1 (x-sq n) 2 u)
                                                 (append R rest))))
                          (:instance x-apply-flip-move-second-zero (L (x-sq n)) (p 0)
                                     (s (x-split-u1 (x-sq n) 2 u)) (u u)
                                     (sch (list* (x-split-u1 (x-sq n) 2 u) (x-split-u1 (x-sq n) 2 u)
                                                 (append R rest)))))))))

;;; ------------------------------------------------------------------
;;; Phase 1: decomposing every summand of R into basis tensors
;;; ------------------------------------------------------------------

;; Effect of a split on the excess weights.
(defthm x-excess-at-of-split-R-same
  (implies (and (posp L) (x-summandp L u) (x-posp3 p) (member-equal u R) (< 1 (x-bv-weight (x-fac p u))))
           (equal (x-excess-at p (x-split-R L p u R))
                  (- (x-excess-at p R) 1)))
  :hints (("Goal" :in-theory (disable x-split-E-facts x-weight-of-A-plus-E)
                  :use (x-split-E-facts x-weight-of-A-plus-E))))

(defthm x-excess-at-of-split-R-other
  (implies (and (posp L) (x-summandp L u) (x-posp3 p) (x-posp3 q) (not (equal p q)) (member-equal u R))
           (equal (x-excess-at q (x-split-R L p u R))
                  (+ (x-excess-at q R) (- (x-bv-weight (x-fac q u)) 1)))))

(defthm x-weight-is-1-when-no-nonunit
  (implies (and (posp L) (x-summand-listp L R) (x-posp3 q) (member-equal u R) (not (x-find-nonunit q R)))
           (equal (x-bv-weight (x-fac q u)) 1))
  :hints (("Goal" :in-theory (disable x-weight-le-1-when-no-nonunit x-weight-of-fac-when-summandp)
                  :use (x-weight-le-1-when-no-nonunit
                        (:instance x-weight-of-fac-when-summandp (s u))))))

(defthm x-summand-listp-of-split-R
  (implies (and (posp L) (x-summand-listp L R) (x-posp3 p) (member-equal u R) (< 1 (x-bv-weight (x-fac p u))))
           (x-summand-listp L (x-split-R L p u R)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-split-u1-summandp x-split-u2-summandp)
                  :use (x-split-u1-summandp x-split-u2-summandp
                        (:instance x-summand-listp-member (s u) (x R))))))

(defthm x-len-of-rank1-when-summandp
  (implies (and (posp L) (x-summandp L s))
           (equal (len (x-rank1 s)) (x-tlen L)))
  :hints (("Goal" :use x-summandp-facts)))

(defthm x-bvp-of-rank1-when-summandp
  (implies (x-summandp L s) (x-bvp (x-rank1 s)))
  :hints (("Goal" :use x-summandp-facts)))

(defthm x-triple-sum-of-split-R
  (implies (and (posp L) (x-summand-listp L R) (x-posp3 p) (member-equal u R)
                (< 1 (x-bv-weight (x-fac p u))))
           (equal (x-triple-sum L (x-split-R L p u R)) (x-triple-sum L R)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (x-split-R)
                                  (x-split-preserves-rank1 x-split-u1-summandp x-split-u2-summandp
                                   x-bv+-associative))
                  :use (x-split-preserves-rank1 x-split-u1-summandp x-split-u2-summandp
                        (:instance x-summand-listp-member (s u) (x R))
                        (:instance x-triple-sum-of-remove1 (s u) (x R))
                        (:instance x-bvp-of-rank1-when-summandp (s (x-split-u1 L p u)))
                        (:instance x-bvp-of-rank1-when-summandp (s (x-split-u2 L p u)))
                        (:instance x-len-of-rank1-when-summandp (s (x-split-u1 L p u)))
                        (:instance x-len-of-rank1-when-summandp (s (x-split-u2 L p u)))
                        (:instance x-bv+-associative
                                   (x (x-rank1 (x-split-u1 L p u)))
                                   (y (x-rank1 (x-split-u2 L p u)))
                                   (z (x-bv+ (x-rank1 u) (x-triple-sum L R))))))))

(defthm x-true-listp-of-split-R
  (implies (true-listp R) (true-listp (x-split-R L p u R))))

(in-theory (disable x-split-R x-split-u1 x-split-u2 x-split-E x-split-path))

(defun x-decompose-path (n R rest)
  (declare (xargs :guard t :verify-guards nil
                  :measure (llist (x-excess-at 0 R) (x-excess-at 1 R) (x-excess-at 2 R))
                  :well-founded-relation l<
                  :hints (("Goal" :in-theory (e/d (l< d<) (x-excess-at-nonneg x-find-nonunit-works x-excess-at-pos-when-nonunit
                                                          x-excess-at-of-split-R-same
                                                          x-excess-at-of-split-R-other
                                                          x-weight-is-1-when-no-nonunit
                                                          x-summand-listp-of-split-R))
                                  :do-not-induct t
                                  :use ((:instance x-excess-at-nonneg (L (x-sq n)) (p 0))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 1))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 2))
                                        (:instance x-excess-at-pos-when-nonunit (L (x-sq n)) (p 0))
                                        (:instance x-excess-at-pos-when-nonunit (L (x-sq n)) (p 1))
                                        (:instance x-excess-at-pos-when-nonunit (L (x-sq n)) (p 2))
                                        (:instance x-find-nonunit-works (p 0))
                                        (:instance x-find-nonunit-works (p 1))
                                        (:instance x-find-nonunit-works (p 2))
                                        (:instance x-summand-listp-member (L (x-sq n)) (s (x-find-nonunit 0 R)) (x R))
                                        (:instance x-summand-listp-member (L (x-sq n)) (s (x-find-nonunit 1 R)) (x R))
                                        (:instance x-summand-listp-member (L (x-sq n)) (s (x-find-nonunit 2 R)) (x R))
                                        (:instance x-excess-at-of-split-R-same (L (x-sq n)) (p 0) (u (x-find-nonunit 0 R)))
                                        (:instance x-excess-at-of-split-R-same (L (x-sq n)) (p 1) (u (x-find-nonunit 1 R)))
                                        (:instance x-excess-at-of-split-R-same (L (x-sq n)) (p 2) (u (x-find-nonunit 2 R)))
                                        (:instance x-excess-at-of-split-R-other (L (x-sq n)) (p 1) (q 0) (u (x-find-nonunit 1 R)))
                                        (:instance x-excess-at-of-split-R-other (L (x-sq n)) (p 2) (q 0) (u (x-find-nonunit 2 R)))
                                        (:instance x-excess-at-of-split-R-other (L (x-sq n)) (p 2) (q 1) (u (x-find-nonunit 2 R)))
                                        (:instance x-weight-is-1-when-no-nonunit (L (x-sq n)) (q 0) (u (x-find-nonunit 1 R)))
                                        (:instance x-weight-is-1-when-no-nonunit (L (x-sq n)) (q 0) (u (x-find-nonunit 2 R)))
                                        (:instance x-weight-is-1-when-no-nonunit (L (x-sq n)) (q 1) (u (x-find-nonunit 2 R)))
                                        (:instance x-summand-listp-of-split-R (L (x-sq n)) (p 0) (u (x-find-nonunit 0 R)))
                                        (:instance x-summand-listp-of-split-R (L (x-sq n)) (p 1) (u (x-find-nonunit 1 R)))
                                        (:instance x-summand-listp-of-split-R (L (x-sq n)) (p 2) (u (x-find-nonunit 2 R)))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 1) (R (x-split-R (x-sq n) 0 (x-find-nonunit 0 R) R)))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 2) (R (x-split-R (x-sq n) 0 (x-find-nonunit 0 R) R)))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 2) (R (x-split-R (x-sq n) 1 (x-find-nonunit 1 R) R))))))))
  (cond ((not (and (posp n) (x-summand-listp (x-sq n) R))) nil)
        ((x-find-nonunit 0 R)
         (let ((u (x-find-nonunit 0 R)))
           (append (x-split-path n (append R rest) 0 u)
                   (x-decompose-path n (x-split-R (x-sq n) 0 u R) rest))))
        ((x-find-nonunit 1 R)
         (let ((u (x-find-nonunit 1 R)))
           (append (x-split-path n (append R rest) 1 u)
                   (x-decompose-path n (x-split-R (x-sq n) 1 u R) rest))))
        ((x-find-nonunit 2 R)
         (let ((u (x-find-nonunit 2 R)))
           (append (x-split-path n (append R rest) 2 u)
                   (x-decompose-path n (x-split-R (x-sq n) 2 u R) rest))))
        (t nil)))

(defun x-decompose-R (n R)
  (declare (xargs :guard t :verify-guards nil
                  :measure (llist (x-excess-at 0 R) (x-excess-at 1 R) (x-excess-at 2 R))
                  :well-founded-relation l<
                  :hints (("Goal" :in-theory (e/d (l< d<) (x-excess-at-nonneg x-find-nonunit-works x-excess-at-pos-when-nonunit
                                                          x-excess-at-of-split-R-same
                                                          x-excess-at-of-split-R-other
                                                          x-weight-is-1-when-no-nonunit
                                                          x-summand-listp-of-split-R))
                                  :do-not-induct t
                                  :use ((:instance x-excess-at-nonneg (L (x-sq n)) (p 0))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 1))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 2))
                                        (:instance x-excess-at-pos-when-nonunit (L (x-sq n)) (p 0))
                                        (:instance x-excess-at-pos-when-nonunit (L (x-sq n)) (p 1))
                                        (:instance x-excess-at-pos-when-nonunit (L (x-sq n)) (p 2))
                                        (:instance x-find-nonunit-works (p 0))
                                        (:instance x-find-nonunit-works (p 1))
                                        (:instance x-find-nonunit-works (p 2))
                                        (:instance x-summand-listp-member (L (x-sq n)) (s (x-find-nonunit 0 R)) (x R))
                                        (:instance x-summand-listp-member (L (x-sq n)) (s (x-find-nonunit 1 R)) (x R))
                                        (:instance x-summand-listp-member (L (x-sq n)) (s (x-find-nonunit 2 R)) (x R))
                                        (:instance x-excess-at-of-split-R-same (L (x-sq n)) (p 0) (u (x-find-nonunit 0 R)))
                                        (:instance x-excess-at-of-split-R-same (L (x-sq n)) (p 1) (u (x-find-nonunit 1 R)))
                                        (:instance x-excess-at-of-split-R-same (L (x-sq n)) (p 2) (u (x-find-nonunit 2 R)))
                                        (:instance x-excess-at-of-split-R-other (L (x-sq n)) (p 1) (q 0) (u (x-find-nonunit 1 R)))
                                        (:instance x-excess-at-of-split-R-other (L (x-sq n)) (p 2) (q 0) (u (x-find-nonunit 2 R)))
                                        (:instance x-excess-at-of-split-R-other (L (x-sq n)) (p 2) (q 1) (u (x-find-nonunit 2 R)))
                                        (:instance x-weight-is-1-when-no-nonunit (L (x-sq n)) (q 0) (u (x-find-nonunit 1 R)))
                                        (:instance x-weight-is-1-when-no-nonunit (L (x-sq n)) (q 0) (u (x-find-nonunit 2 R)))
                                        (:instance x-weight-is-1-when-no-nonunit (L (x-sq n)) (q 1) (u (x-find-nonunit 2 R)))
                                        (:instance x-summand-listp-of-split-R (L (x-sq n)) (p 0) (u (x-find-nonunit 0 R)))
                                        (:instance x-summand-listp-of-split-R (L (x-sq n)) (p 1) (u (x-find-nonunit 1 R)))
                                        (:instance x-summand-listp-of-split-R (L (x-sq n)) (p 2) (u (x-find-nonunit 2 R)))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 1) (R (x-split-R (x-sq n) 0 (x-find-nonunit 0 R) R)))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 2) (R (x-split-R (x-sq n) 0 (x-find-nonunit 0 R) R)))
                                        (:instance x-excess-at-nonneg (L (x-sq n)) (p 2) (R (x-split-R (x-sq n) 1 (x-find-nonunit 1 R) R))))))))
  (cond ((not (and (posp n) (x-summand-listp (x-sq n) R))) R)
        ((x-find-nonunit 0 R) (x-decompose-R n (x-split-R (x-sq n) 0 (x-find-nonunit 0 R) R)))
        ((x-find-nonunit 1 R) (x-decompose-R n (x-split-R (x-sq n) 1 (x-find-nonunit 1 R) R)))
        ((x-find-nonunit 2 R) (x-decompose-R n (x-split-R (x-sq n) 2 (x-find-nonunit 2 R) R)))
        (t R)))

;; A summand all of whose factors are units.
(defun x-basic-summandp (u)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (x-bv-weight (x-fac 0 u)) 1)
       (equal (x-bv-weight (x-fac 1 u)) 1)
       (equal (x-bv-weight (x-fac 2 u)) 1)))

(defun x-basic-listp (R)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom R) t (and (x-basic-summandp (car R)) (x-basic-listp (cdr R)))))

(defthm x-basic-listp-when-no-nonunits
  (implies (and (posp L) (x-summand-listp L R)
                (not (x-find-nonunit 0 R)) (not (x-find-nonunit 1 R)) (not (x-find-nonunit 2 R)))
           (x-basic-listp R))
  :hints (("Goal" :induct (x-summand-listp L R))))

(defthm x-decompose-R-facts
  (implies (and (posp n) (x-summand-listp (x-sq n) R))
           (and (x-summand-listp (x-sq n) (x-decompose-R n R))
                (equal (x-triple-sum (x-sq n) (x-decompose-R n R)) (x-triple-sum (x-sq n) R))
                (x-basic-listp (x-decompose-R n R))))
  :hints (("Goal" :induct (x-decompose-R n R))))

(defthm x-schemep-of-append-when-sum-preserved
  (implies (and (x-schemep n (append R rest)) (x-summand-listp (x-sq n) R)
                (x-summand-listp (x-sq n) R2)
                (equal (x-triple-sum (x-sq n) R2) (x-triple-sum (x-sq n) R)))
           (x-schemep n (append R2 rest)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-triple-sum-of-append)
                  :use ((:instance x-summand-listp-append-parts (L (x-sq n)))
                        (:instance x-summand-listp-of-append (L (x-sq n)) (x R2) (y rest))
                        (:instance x-triple-sum-of-append (L (x-sq n)) (x R) (y rest))
                        (:instance x-triple-sum-of-append (L (x-sq n)) (x R2) (y rest))))))

;; Correctness of phase 1.
(defthm x-decompose-path-correct
  (implies (and (x-schemep n (append R rest)) (x-summand-listp (x-sq n) R) (<= 2 n))
           (and (x-path-ok-p (x-sq n) (x-decompose-path n R rest) (append R rest))
                (perm (x-apply-path (x-sq n) (x-decompose-path n R rest) (append R rest))
                      (append (x-decompose-R n R) rest))))
  :hints (("Goal" :induct (x-decompose-path n R rest)
                  :in-theory (e/d (x-split-path) (x-summandp-facts-rw
                                                perm-of-cons-arg1 perm-of-cons-arg2
                                                x-perm-rotate-3 x-perm-rotate-4 x-perm-rotate-3-append
                                                x-perm-rotate-4-append x-perm-step4-shape
                                                x-perm-append-list-1 x-perm-append-list-2
                                                x-perm-cons-remove1-when-member
                                                x-perm-split-shape x-perm-split-shape-2
                                                x-set-fac-of-set-fac-other-commute)))))

;;; ------------------------------------------------------------------
;;; Phase 2: a zero-sum multiset of basis tensors consists of pairs
;;; ------------------------------------------------------------------

;; Tensor index of a basic summand.
(defun x-bidx (L u)
  (declare (xargs :guard t :verify-guards nil))
  (x-tidx3 L L (x-bv-first-one (x-fac 0 u)) (x-bv-first-one (x-fac 1 u)) (x-bv-first-one (x-fac 2 u))))

;; A basic summand is determined by its three unit positions.
(defthm x-basic-summand-is-units
  (implies (and (posp L) (x-summandp L u) (x-basic-summandp u))
           (equal (list (x-unit L (x-bv-first-one (x-fac 0 u)))
                        (x-unit L (x-bv-first-one (x-fac 1 u)))
                        (x-unit L (x-bv-first-one (x-fac 2 u))))
                  u))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-bv-weight-one-is-unit x-list-of-facs)
                  :use ((:instance x-summandp-facts (s u))
                        (:instance x-list-of-facs (s u))
                        (:instance x-bv-weight-one-is-unit (x (x-fac 0 u)))
                        (:instance x-bv-weight-one-is-unit (x (x-fac 1 u)))
                        (:instance x-bv-weight-one-is-unit (x (x-fac 2 u)))))))

(defthm x-first-one-bound-when-summandp
  (implies (and (posp L) (x-summandp L u) (x-posp3 p))
           (< (x-bv-first-one (x-fac p u)) L))
  :hints (("Goal" :in-theory (disable x-bv-first-one-witness x-fac-nonzero-when-summandp)
                  :use ((:instance x-fac-nonzero-when-summandp (s u))
                        (:instance x-bv-first-one-witness (x (x-fac p u))))))
  :rule-classes :linear)

;; Coordinate (bidx u) of the rank-one tensor of a basic summand v is 1
;; iff v = u.
(defthm x-nth-bidx-of-rank1-basic
  (implies (and (posp L) (x-summandp L u) (x-basic-summandp u)
                (x-summandp L v) (x-basic-summandp v))
           (equal (nth (x-bidx L u) (x-rank1 v))
                  (if (equal v u) 1 0)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (x-rank1 x-fac) (x-nth-of-outer3 x-basic-summand-is-units
                                                x-first-one-bound-when-summandp
                                                x-bv-weight-one-is-unit x-nth-of-unit))
                  :use ((:instance x-summandp-facts (s u))
                        (:instance x-summandp-facts (s v))
                        (:instance x-basic-summand-is-units)
                        (:instance x-basic-summand-is-units (u v))
                        (:instance x-bv-weight-one-is-unit (x (x-fac 0 v)))
                        (:instance x-bv-weight-one-is-unit (x (x-fac 1 v)))
                        (:instance x-bv-weight-one-is-unit (x (x-fac 2 v)))
                        (:instance x-nth-of-unit (L L) (i (x-bv-first-one (x-fac 0 u))) (k (x-bv-first-one (x-fac 0 v))))
                        (:instance x-nth-of-unit (L L) (i (x-bv-first-one (x-fac 1 u))) (k (x-bv-first-one (x-fac 1 v))))
                        (:instance x-nth-of-unit (L L) (i (x-bv-first-one (x-fac 2 u))) (k (x-bv-first-one (x-fac 2 v))))
                        (:instance x-first-one-bound-when-summandp (p 0))
                        (:instance x-first-one-bound-when-summandp (p 1))
                        (:instance x-first-one-bound-when-summandp (p 2))
                        (:instance x-first-one-bound-when-summandp (u v) (p 0))
                        (:instance x-first-one-bound-when-summandp (u v) (p 1))
                        (:instance x-first-one-bound-when-summandp (u v) (p 2))
                        (:instance x-nth-of-outer3 (A (car v)) (B (cadr v)) (C (caddr v))
                                   (ia (x-bv-first-one (x-fac 0 u)))
                                   (ib (x-bv-first-one (x-fac 1 u)))
                                   (ic (x-bv-first-one (x-fac 2 u))))))))

(defun x-odd-count (u R)
  (declare (xargs :guard t))
  (cond ((atom R) nil)
        ((equal (car R) u) (not (x-odd-count u (cdr R))))
        (t (x-odd-count u (cdr R)))))

(defthm x-odd-count-implies-member
  (implies (x-odd-count u R) (member-equal u R)))

(defthm x-bidx-bound
  (implies (and (posp L) (x-summandp L u))
           (< (x-bidx L u) (x-tlen L)))
  :hints (("Goal" :in-theory (disable x-tidx3-bound x-first-one-bound-when-summandp)
                  :use ((:instance x-tidx3-bound (LA L) (LB L) (LC L)
                                   (a (x-bv-first-one (x-fac 0 u)))
                                   (b (x-bv-first-one (x-fac 1 u)))
                                   (c (x-bv-first-one (x-fac 2 u))))
                        (:instance x-first-one-bound-when-summandp (p 0))
                        (:instance x-first-one-bound-when-summandp (p 1))
                        (:instance x-first-one-bound-when-summandp (p 2)))))
  :rule-classes :linear)

(defthm x-natp-of-bidx
  (implies (natp L) (natp (x-bidx L u)))
  :hints (("Goal" :in-theory (enable x-tidx3)))
  :rule-classes :type-prescription)

(in-theory (disable x-bidx))

(defthm x-nth-bidx-of-triple-sum-basic
  (implies (and (posp L) (x-summandp L u) (x-basic-summandp u)
                (x-summand-listp L R) (x-basic-listp R))
           (equal (nth (x-bidx L u) (x-triple-sum L R))
                  (if (x-odd-count u R) 1 0)))
  :hints (("Goal" :induct (x-odd-count u R)
                  :in-theory (disable x-nth-bidx-of-rank1-basic x-bidx-bound))
          ("Subgoal *1/3" :use ((:instance x-nth-bidx-of-rank1-basic (v (car R)))
                                (:instance x-bidx-bound)
                                (:instance x-len-of-rank1-when-summandp (s (car R)))
                                (:instance x-nth-of-bv+ (i (x-bidx L u)) (x (x-rank1 (car R)))
                                           (y (x-triple-sum L (cdr R))))))
          ("Subgoal *1/2" :use ((:instance x-nth-bidx-of-rank1-basic (v (car R)))
                                (:instance x-bidx-bound)
                                (:instance x-len-of-rank1-when-summandp (s (car R)))
                                (:instance x-nth-of-bv+ (i (x-bidx L u)) (x (x-rank1 (car R)))
                                           (y (x-triple-sum L (cdr R))))))
          ("Subgoal *1/1" :use ((:instance x-bidx-bound)))))

;; The first summand of a zero-sum basic list occurs again later.
(defthm x-car-member-cdr-when-zero-sum-basic
  (implies (and (posp L) (x-summand-listp L R) (x-basic-listp R) (consp R)
                (equal (x-triple-sum L R) (x-bv-zero (x-tlen L))))
           (member-equal (car R) (cdr R)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-nth-bidx-of-triple-sum-basic x-odd-count-implies-member)
                  :use ((:instance x-nth-bidx-of-triple-sum-basic (u (car R)))
                        (:instance x-odd-count-implies-member (u (car R)) (R (cdr R)))))))

(defthm x-basic-listp-of-remove1
  (implies (x-basic-listp R) (x-basic-listp (remove1-equal u R)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defun x-delete-pairs-path (R)
  (declare (xargs :guard t :verify-guards nil :measure (len R)))
  (if (atom R)
      nil
    (cons (x-delete-pair-move (car R))
          (x-delete-pairs-path (remove1-equal (car R) (cdr R))))))

(defthm x-triple-sum-of-remove1-car
  (implies (and (posp L) (x-summand-listp L R) (consp R) (member-equal (car R) (cdr R)))
           (equal (x-triple-sum L (remove1-equal (car R) (cdr R)))
                  (x-triple-sum L R)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-triple-sum-of-remove1)
                  :use ((:instance x-triple-sum-of-remove1 (s (car R)) (x (cdr R)))
                        (:instance x-summandp-facts (s (car R)))))))

(defthm x-triplep-when-summandp
  (implies (x-summandp L s) (x-triplep L s))
  :hints (("Goal" :in-theory (enable x-summandp))))

(defthm x-delete-pairs-correct
  (implies (and (posp L) (x-summand-listp L R) (x-basic-listp R) (true-listp rest)
                (equal (x-triple-sum L R) (x-bv-zero (x-tlen L))))
           (and (x-path-ok-p L (x-delete-pairs-path R) (append R rest))
                (perm (x-apply-path L (x-delete-pairs-path R) (append R rest)) rest)))
  :hints (("Goal" :induct (x-delete-pairs-path R)
                  :in-theory (disable x-car-member-cdr-when-zero-sum-basic
                                      x-apply-delete-pair-move x-delete-pair-move-ok
                                      x-triple-sum-of-remove1-car
                                      perm-of-cons-arg1 perm-of-cons-arg2))
          ("Subgoal *1/2" :use (x-car-member-cdr-when-zero-sum-basic
                                x-triple-sum-of-remove1-car
                                (:instance x-apply-delete-pair-move (s1 (car R)) (S (append R rest)))
                                (:instance x-delete-pair-move-ok (s1 (car R)) (S (append R rest)))))))

;;; ------------------------------------------------------------------
;;; Lemma 4.5
;;; ------------------------------------------------------------------

(defun x-zero-subset-path (n R rest)
  (declare (xargs :guard t :verify-guards nil))
  (append (x-decompose-path n R rest)
          (x-delete-pairs-path (x-decompose-R n R))))

(defthm x-zero-subset-lemma
  (implies (and (x-schemep n (append R rest)) (x-summand-listp (x-sq n) R) (<= 2 n)
                (equal (x-triple-sum (x-sq n) R) (x-bv-zero (x-tlen (x-sq n)))))
           (and (x-path-ok-p (x-sq n) (x-zero-subset-path n R rest) (append R rest))
                (perm (x-apply-path (x-sq n) (x-zero-subset-path n R rest) (append R rest))
                      rest)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable perm-of-cons-arg1 perm-of-cons-arg2 perm-of-append
                                      perm-of-append-of-cons perm-of-append-of-cdr-and-cons-of-car)
                  :use ((:instance x-summand-listp-append-parts (L (x-sq n)))))))
