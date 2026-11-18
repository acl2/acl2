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

(include-book "add-arbitrary")

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

(defun split-unit (L u)
  (declare (xargs :guard t :verify-guards nil))
  ;; returns (mv p E) : the first position whose factor is not a unit, and the unit
  (cond ((> (bv-weight (fac 0 u)) 1) (mv 0 (unit L (bv-first-one (fac 0 u)))))
        ((> (bv-weight (fac 1 u)) 1) (mv 1 (unit L (bv-first-one (fac 1 u)))))
        (t (mv 2 (unit L (bv-first-one (fac 2 u)))))))

;; The flip position used to split position p.
(defun split-flip-pos (p)
  (declare (xargs :guard t))
  (if (eql p 0) 1 0))

;; A summand all of whose factors are units.
(defun basic-summandp (u)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (bv-weight (fac 0 u)) 1)
       (equal (bv-weight (fac 1 u)) 1)
       (equal (bv-weight (fac 2 u)) 1)))

(defun basic-listp (R)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom R) t (and (basic-summandp (car R)) (basic-listp (cdr R)))))

;; Measure of the decomposition: total excess weight.
(defun excess-weight (R)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom R) 0
    (+ (- (bv-weight (fac 0 (car R))) 1)
       (- (bv-weight (fac 1 (car R))) 1)
       (- (bv-weight (fac 2 (car R))) 1)
       (excess-weight (cdr R)))))

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

;;; ------------------------------------------------------------------
;;; Weights, excess, and the first non-unit factor at a position
;;; ------------------------------------------------------------------

(defun excess-at (p R)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom R) 0
    (+ (- (bv-weight (fac p (car R))) 1) (excess-at p (cdr R)))))

(defun find-nonunit (p R)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom R) nil)
        ((> (bv-weight (fac p (car R))) 1) (car R))
        (t (find-nonunit p (cdr R)))))

(defthm find-nonunit-works
  (implies (find-nonunit p R)
           (and (member-equal (find-nonunit p R) R)
                (< 1 (bv-weight (fac p (find-nonunit p R)))))))

(defthm weight-of-fac-when-summandp
  (implies (and (posp L) (summandp L s) (posp3 p))
           (<= 1 (bv-weight (fac p s))))
  :hints (("Goal" :in-theory (disable bv-weight-zero-iff fac-nonzero-when-summandp)
                  :use (fac-nonzero-when-summandp
                        (:instance bv-weight-zero-iff (x (fac p s))))))
  :rule-classes :linear)

(defthm not-summandp-nil
  (not (summandp L nil))
  :hints (("Goal" :in-theory (enable summandp))))

(defthm weight-le-1-when-no-nonunit
  (implies (and (not (find-nonunit p R)) (member-equal u R) (summand-listp L R))
           (<= (bv-weight (fac p u)) 1))
  :hints (("Goal" :induct (summand-listp L R)))
  :rule-classes :linear)

(defthm excess-at-nonneg
  (implies (and (posp L) (summand-listp L R) (posp3 p))
           (<= 0 (excess-at p R)))
  :rule-classes :linear)

(defthm excess-at-zero-when-no-nonunit
  (implies (and (posp L) (summand-listp L R) (posp3 p) (not (find-nonunit p R)))
           (equal (excess-at p R) 0)))

(defthm excess-at-pos-when-nonunit
  (implies (and (posp L) (summand-listp L R) (posp3 p) (find-nonunit p R))
           (<= 1 (excess-at p R)))
  :hints (("Goal" :induct (summand-listp L R)))
  :rule-classes :linear)

(defthm excess-at-of-remove1
  (implies (member-equal u R)
           (equal (excess-at p (remove1-equal u R))
                  (- (excess-at p R) (- (bv-weight (fac p u)) 1))))
  :hints (("Goal" :in-theory (enable remove1-equal))))

;;; ------------------------------------------------------------------
;;; Splitting a unit off the p-factor of a summand u in R
;;; ------------------------------------------------------------------

;; E = unit at the lowest set bit of (fac p u)
(defun split-E (L p u)
  (declare (xargs :guard t :verify-guards nil))
  (unit L (bv-first-one (fac p u))))

(defun split-u1 (L p u)        ; E (x) rest
  (declare (xargs :guard t :verify-guards nil))
  (set-fac p (split-E L p u) u))

(defun split-u2 (L p u)        ; (A+E) (x) rest
  (declare (xargs :guard t :verify-guards nil))
  (set-fac p (bv+ (fac p u) (split-E L p u)) u))

;; The position on which the flip is performed.
(defun split-flip-pos (p)
  (declare (xargs :guard t))
  (if (eql p 0) 1 0))

(defthm split-E-facts
  (implies (and (posp L) (summandp L u) (posp3 p))
           (and (bvp (split-E L p u))
                (equal (len (split-E L p u)) L)
                (not (equal (split-E L p u) (bv-zero L)))
                (equal (bv-weight (split-E L p u)) 1)))
  :hints (("Goal" :in-theory (disable bv-first-one-witness)
                  :use ((:instance bv-first-one-witness (x (fac p u)))))))

(defthm split-u1-summandp
  (implies (and (posp L) (summandp L u) (posp3 p))
           (summandp L (split-u1 L p u)))
  :hints (("Goal" :in-theory (disable split-E-facts) :use split-E-facts)))

(defthm weight-of-A-plus-E
  (implies (and (posp L) (summandp L u) (posp3 p))
           (equal (bv-weight (bv+ (fac p u) (split-E L p u)))
                  (1- (bv-weight (fac p u)))))
  :hints (("Goal" :in-theory (disable bv-first-one-witness bv-weight-of-bv+-unit)
                  :use ((:instance bv-first-one-witness (x (fac p u)))
                        (:instance bv-weight-of-bv+-unit (x (fac p u)) (k (bv-first-one (fac p u))))))))

(defthm split-u2-summandp
  (implies (and (posp L) (summandp L u) (posp3 p) (< 1 (bv-weight (fac p u))))
           (summandp L (split-u2 L p u)))
  :hints (("Goal" :in-theory (disable split-E-facts bv-weight-zero-iff weight-of-A-plus-E)
                  :use (split-E-facts weight-of-A-plus-E
                        (:instance bv-weight-zero-iff (x (bv+ (fac p u) (split-E L p u))))))))

;; rank1 (set-fac p v s) + rank1 (set-fac p w s) = rank1 (set-fac p (v+w) s)
(defthm rank1-of-set-fac-sum
  (implies (and (posp L) (summandp L s) (posp3 p)
                (bvp v) (bvp w) (equal (len v) L) (equal (len w) L))
           (equal (bv+ (rank1 (set-fac p v s)) (rank1 (set-fac p w s)))
                  (rank1 (set-fac p (bv+ v w) s))))
  :hints (("Goal" :in-theory (e/d (rank1 set-fac posp3) ())
                  :use ((:instance summandp-facts))
                  :cases ((equal p 0) (equal p 1) (equal p 2)))))

(defthm split-preserves-rank1
  (implies (and (posp L) (summandp L u) (posp3 p))
           (equal (bv+ (rank1 (split-u1 L p u)) (rank1 (split-u2 L p u)))
                  (rank1 u)))
  :hints (("Goal" :in-theory (disable split-E-facts rank1-of-set-fac-sum set-fac-of-fac-same)
                  :use (split-E-facts
                        (:instance summandp-facts (s u))
                        (:instance set-fac-of-fac-same (s u))
                        (:instance rank1-of-set-fac-sum (s u) (v (split-E L p u))
                                   (w (bv+ (fac p u) (split-E L p u))))))))

;;; ------------------------------------------------------------------
;;; The split step as a path: Lemma 4.4 then one flip
;;; ------------------------------------------------------------------

(defthm apply-flip-move-second-zero
  (implies (and (posp L) (posp3 p) (summandp L s) (summandp L u)
                (not (equal (bv+ (fac (other-hi p) s) (fac (other-hi p) u)) (bv-zero L)))
                (equal (bv+ (fac (other-lo p) u) (fac (other-lo p) s)) (bv-zero L)))
           (equal (apply-move L (flip-move p s u) sch)
                  (append (remove1-equal u (remove1-equal s sch))
                          (list (set-fac (other-hi p)
                                         (bv+ (fac (other-hi p) s) (fac (other-hi p) u))
                                         s)))))
  :hints (("Goal" :in-theory (enable apply-move flip-results flip-move))))

(defthm nz-matp-intro
  (implies (and (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n)))))
           (nz-matp n X))
  :hints (("Goal" :in-theory (enable nz-matp))))

(defthm list-of-facs
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (list (fac 0 s) (fac 1 s) (fac 2 s)) s))
  :hints (("Goal" :in-theory (enable fac))))

;; The current copy of R after splitting u at position p.
(defun split-R (L p u R)
  (declare (xargs :guard t :verify-guards nil))
  (list* (split-u1 L p u) (split-u2 L p u) (remove1-equal u R)))

;; The path: add two copies of u1 = E (x) ..., then flip u1 against u.
(defun split-path (n sch p u)
  (declare (xargs :guard t :verify-guards nil))
  (let ((u1 (split-u1 (sq n) p u)))
    (append (add-arb-path n sch (fac 0 u1) (fac 1 u1) (fac 2 u1))
            (list (flip-move (split-flip-pos p) u1 u)))))

(defthm split-u1-ne-u
  (implies (and (posp L) (summandp L u) (posp3 p) (< 1 (bv-weight (fac p u))))
           (not (equal (split-u1 L p u) u)))
  :hints (("Goal" :in-theory (disable split-E-facts)
                  :use (split-E-facts
                        (:instance not-equal-set-fac-when-fac-differs-2
                                   (v (split-E L p u)) (s u) (u u))))))

(defthm remove1-of-append-when-member-first-2
  (implies (member-equal a x)
           (equal (remove1-equal a (append x y))
                  (append (remove1-equal a x) y)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm perm-split-shape
  (perm (append (cons u1 R1) (list u2)) (list* u1 u2 R1))
  :hints (("Goal" :in-theory (e/d (perm remove1-equal) (perm-of-append perm-append-list-1))
                  :use ((:instance perm-append-list-1 (x (cons u1 R1)) (a u2))))))

(defun ind-list (R) (if (atom R) nil (ind-list (cdr R))))

(defthm summandp-when-member-of-append-first
  (implies (and (member-equal u R) (summand-listp L (append R rest)))
           (summandp L u))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("Goal" :induct (ind-list R))))

(defthm summand-listp-append-parts
  (implies (summand-listp L (append R rest))
           (and (summand-listp L rest) (summand-listp L (true-list-fix R))))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (ind-list R))))

(defthm member-of-append-first
  (implies (member-equal u R) (member-equal u (append R rest)))
  :hints (("Goal" :induct (ind-list R))))

;; In this book all positions are concrete, so we normalize set-fac to
;; explicit lists.
(defthm set-fac-0-as-list
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (set-fac 0 v s) (list v (fac 1 s) (fac 2 s))))
  :hints (("Goal" :in-theory (enable set-fac fac))))
(defthm set-fac-1-as-list
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (set-fac 1 v s) (list (fac 0 s) v (fac 2 s))))
  :hints (("Goal" :in-theory (enable set-fac fac))))
(defthm set-fac-2-as-list
  (implies (and (true-listp s) (equal (len s) 3))
           (equal (set-fac 2 v s) (list (fac 0 s) (fac 1 s) v)))
  :hints (("Goal" :in-theory (enable set-fac fac))))
(defthm fac-of-list
  (and (equal (fac 0 (list a b c)) a)
       (equal (fac 1 (list a b c)) b)
       (equal (fac 2 (list a b c)) c))
  :hints (("Goal" :in-theory (enable fac))))

(defthm perm-split-shape-2
  (perm (cons a (append x (append y (list c)))) (list* a c (append x y)))
  :hints (("Goal" :in-theory (disable perm-of-append perm-append-list-1)
                  :use ((:instance perm-append-list-1 (x (append x y)) (a c))))))

(encapsulate ()
  (local (in-theory (disable summandp-facts-rw perm-of-cons-arg1 perm-of-cons-arg2
                             perm-rotate-3 perm-rotate-4 perm-rotate-3-append
                             perm-rotate-4-append perm-step4-shape
                             perm-append-list-1 perm-append-list-2
                             perm-cons-remove1-when-member
                             set-fac-of-set-fac-other-commute
                             split-E-facts split-u1-ne-u
                             apply-flip-move-first-zero apply-flip-move-second-zero
                             flip-move-ok perm-split-shape-2 perm-split-shape)))

  ;; Position 0: flip on position 1; the first result E(x)B(x)(C+C) vanishes.
  (defthm split-step-0
    (implies (and (schemep n (append R rest)) (<= 2 n)
                  (member-equal u R) (< 1 (bv-weight (fac 0 u))))
             (let* ((L (sq n))
                    (sch (append R rest))
                    (u1 (split-u1 L 0 u))
                    (mid (apply-path L (add-arb-path n sch (fac 0 u1) (fac 1 u1) (fac 2 u1)) sch)))
               (and (path-ok-p L (add-arb-path n sch (fac 0 u1) (fac 1 u1) (fac 2 u1)) sch)
                    (move-ok-p (flip-move 1 u1 u) mid)
                    (perm (apply-move L (flip-move 1 u1 u) mid)
                          (append (split-R L 0 u R) rest)))))
    :hints (("Goal" :do-not-induct t
                    :in-theory (e/d (split-flip-pos) (split-u1-summandp split-u2-summandp))
                    :use ((:instance summandp-facts (L (sq n)) (s u))
                          (:instance split-E-facts (L (sq n)) (p 0))
                          (:instance split-u1-summandp (L (sq n)) (p 0))
                          (:instance split-u2-summandp (L (sq n)) (p 0))
                          (:instance split-u1-ne-u (L (sq n)) (p 0))
                          (:instance summandp-facts (L (sq n)) (s (split-u1 (sq n) 0 u)))
                          (:instance perm-split-shape-2 (a (split-u1 (sq n) 0 u))
                                     (x (remove1-equal u R)) (y rest) (c (split-u2 (sq n) 0 u)))
                          (:instance flip-move-ok (p 1) (s (split-u1 (sq n) 0 u)) (u u)
                                     (sch (list* (split-u1 (sq n) 0 u) (split-u1 (sq n) 0 u)
                                                 (append R rest))))
                          (:instance apply-flip-move-first-zero (L (sq n)) (p 1)
                                     (s (split-u1 (sq n) 0 u)) (u u)
                                     (sch (list* (split-u1 (sq n) 0 u) (split-u1 (sq n) 0 u)
                                                 (append R rest))))))))

  ;; Position 1: flip on position 0; the first result A(x)E(x)(C+C) vanishes.
  (defthm split-step-1
    (implies (and (schemep n (append R rest)) (<= 2 n)
                  (member-equal u R) (< 1 (bv-weight (fac 1 u))))
             (let* ((L (sq n))
                    (sch (append R rest))
                    (u1 (split-u1 L 1 u))
                    (mid (apply-path L (add-arb-path n sch (fac 0 u1) (fac 1 u1) (fac 2 u1)) sch)))
               (and (path-ok-p L (add-arb-path n sch (fac 0 u1) (fac 1 u1) (fac 2 u1)) sch)
                    (move-ok-p (flip-move 0 u1 u) mid)
                    (perm (apply-move L (flip-move 0 u1 u) mid)
                          (append (split-R L 1 u R) rest)))))
    :hints (("Goal" :do-not-induct t
                    :in-theory (e/d (split-flip-pos) (split-u1-summandp split-u2-summandp))
                    :use ((:instance summandp-facts (L (sq n)) (s u))
                          (:instance split-E-facts (L (sq n)) (p 1))
                          (:instance split-u1-summandp (L (sq n)) (p 1))
                          (:instance split-u2-summandp (L (sq n)) (p 1))
                          (:instance split-u1-ne-u (L (sq n)) (p 1))
                          (:instance summandp-facts (L (sq n)) (s (split-u1 (sq n) 1 u)))
                          (:instance perm-split-shape-2 (a (split-u1 (sq n) 1 u))
                                     (x (remove1-equal u R)) (y rest) (c (split-u2 (sq n) 1 u)))
                          (:instance flip-move-ok (p 0) (s (split-u1 (sq n) 1 u)) (u u)
                                     (sch (list* (split-u1 (sq n) 1 u) (split-u1 (sq n) 1 u)
                                                 (append R rest))))
                          (:instance apply-flip-move-first-zero (L (sq n)) (p 0)
                                     (s (split-u1 (sq n) 1 u)) (u u)
                                     (sch (list* (split-u1 (sq n) 1 u) (split-u1 (sq n) 1 u)
                                                 (append R rest))))))))

  ;; Position 2: flip on position 0; now the second result A(x)(B+B)(x)C vanishes
  ;; and the first result is A(x)B(x)(E+C).
  (defthm split-step-2
    (implies (and (schemep n (append R rest)) (<= 2 n)
                  (member-equal u R) (< 1 (bv-weight (fac 2 u))))
             (let* ((L (sq n))
                    (sch (append R rest))
                    (u1 (split-u1 L 2 u))
                    (mid (apply-path L (add-arb-path n sch (fac 0 u1) (fac 1 u1) (fac 2 u1)) sch)))
               (and (path-ok-p L (add-arb-path n sch (fac 0 u1) (fac 1 u1) (fac 2 u1)) sch)
                    (move-ok-p (flip-move 0 u1 u) mid)
                    (perm (apply-move L (flip-move 0 u1 u) mid)
                          (append (split-R L 2 u R) rest)))))
    :hints (("Goal" :do-not-induct t
                    :in-theory (e/d (split-flip-pos) (split-u1-summandp split-u2-summandp))
                    :use ((:instance summandp-facts (L (sq n)) (s u))
                          (:instance split-E-facts (L (sq n)) (p 2))
                          (:instance split-u1-summandp (L (sq n)) (p 2))
                          (:instance split-u2-summandp (L (sq n)) (p 2))
                          (:instance split-u1-ne-u (L (sq n)) (p 2))
                          (:instance summandp-facts (L (sq n)) (s (split-u1 (sq n) 2 u)))
                          (:instance perm-split-shape-2 (a (split-u1 (sq n) 2 u))
                                     (x (remove1-equal u R)) (y rest) (c (split-u2 (sq n) 2 u)))
                          (:instance flip-move-ok (p 0) (s (split-u1 (sq n) 2 u)) (u u)
                                     (sch (list* (split-u1 (sq n) 2 u) (split-u1 (sq n) 2 u)
                                                 (append R rest))))
                          (:instance apply-flip-move-second-zero (L (sq n)) (p 0)
                                     (s (split-u1 (sq n) 2 u)) (u u)
                                     (sch (list* (split-u1 (sq n) 2 u) (split-u1 (sq n) 2 u)
                                                 (append R rest)))))))))

;;; ------------------------------------------------------------------
;;; Phase 1: decomposing every summand of R into basis tensors
;;; ------------------------------------------------------------------

;; Effect of a split on the excess weights.
(defthm excess-at-of-split-R-same
  (implies (and (posp L) (summandp L u) (posp3 p) (member-equal u R) (< 1 (bv-weight (fac p u))))
           (equal (excess-at p (split-R L p u R))
                  (- (excess-at p R) 1)))
  :hints (("Goal" :in-theory (disable split-E-facts weight-of-A-plus-E)
                  :use (split-E-facts weight-of-A-plus-E))))

(defthm excess-at-of-split-R-other
  (implies (and (posp L) (summandp L u) (posp3 p) (posp3 q) (not (equal p q)) (member-equal u R))
           (equal (excess-at q (split-R L p u R))
                  (+ (excess-at q R) (- (bv-weight (fac q u)) 1)))))

(defthm weight-is-1-when-no-nonunit
  (implies (and (posp L) (summand-listp L R) (posp3 q) (member-equal u R) (not (find-nonunit q R)))
           (equal (bv-weight (fac q u)) 1))
  :hints (("Goal" :in-theory (disable weight-le-1-when-no-nonunit weight-of-fac-when-summandp)
                  :use (weight-le-1-when-no-nonunit
                        (:instance weight-of-fac-when-summandp (s u))))))

(defthm summand-listp-of-split-R
  (implies (and (posp L) (summand-listp L R) (posp3 p) (member-equal u R) (< 1 (bv-weight (fac p u))))
           (summand-listp L (split-R L p u R)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable split-u1-summandp split-u2-summandp)
                  :use (split-u1-summandp split-u2-summandp
                        (:instance summand-listp-member (s u) (x R))))))

(defthm len-of-rank1-when-summandp
  (implies (and (posp L) (summandp L s))
           (equal (len (rank1 s)) (tlen L)))
  :hints (("Goal" :use summandp-facts)))

(defthm bvp-of-rank1-when-summandp
  (implies (summandp L s) (bvp (rank1 s)))
  :hints (("Goal" :use summandp-facts)))

(defthm triple-sum-of-split-R
  (implies (and (posp L) (summand-listp L R) (posp3 p) (member-equal u R)
                (< 1 (bv-weight (fac p u))))
           (equal (triple-sum L (split-R L p u R)) (triple-sum L R)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (split-R)
                                  (split-preserves-rank1 split-u1-summandp split-u2-summandp
                                   bv+-associative))
                  :use (split-preserves-rank1 split-u1-summandp split-u2-summandp
                        (:instance summand-listp-member (s u) (x R))
                        (:instance triple-sum-of-remove1 (s u) (x R))
                        (:instance bvp-of-rank1-when-summandp (s (split-u1 L p u)))
                        (:instance bvp-of-rank1-when-summandp (s (split-u2 L p u)))
                        (:instance len-of-rank1-when-summandp (s (split-u1 L p u)))
                        (:instance len-of-rank1-when-summandp (s (split-u2 L p u)))
                        (:instance bv+-associative
                                   (x (rank1 (split-u1 L p u)))
                                   (y (rank1 (split-u2 L p u)))
                                   (z (bv+ (rank1 u) (triple-sum L R))))))))

(defthm true-listp-of-split-R
  (implies (true-listp R) (true-listp (split-R L p u R))))

(in-theory (disable split-R split-u1 split-u2 split-E split-path))

(defun decompose-path (n R rest)
  (declare (xargs :guard t :verify-guards nil
                  :measure (llist (excess-at 0 R) (excess-at 1 R) (excess-at 2 R))
                  :well-founded-relation l<
                  :hints (("Goal" :in-theory (e/d (l< d<) (excess-at-nonneg find-nonunit-works excess-at-pos-when-nonunit
                                                          excess-at-of-split-R-same
                                                          excess-at-of-split-R-other
                                                          weight-is-1-when-no-nonunit
                                                          summand-listp-of-split-R))
                                  :do-not-induct t
                                  :use ((:instance excess-at-nonneg (L (sq n)) (p 0))
                                        (:instance excess-at-nonneg (L (sq n)) (p 1))
                                        (:instance excess-at-nonneg (L (sq n)) (p 2))
                                        (:instance excess-at-pos-when-nonunit (L (sq n)) (p 0))
                                        (:instance excess-at-pos-when-nonunit (L (sq n)) (p 1))
                                        (:instance excess-at-pos-when-nonunit (L (sq n)) (p 2))
                                        (:instance find-nonunit-works (p 0))
                                        (:instance find-nonunit-works (p 1))
                                        (:instance find-nonunit-works (p 2))
                                        (:instance summand-listp-member (L (sq n)) (s (find-nonunit 0 R)) (x R))
                                        (:instance summand-listp-member (L (sq n)) (s (find-nonunit 1 R)) (x R))
                                        (:instance summand-listp-member (L (sq n)) (s (find-nonunit 2 R)) (x R))
                                        (:instance excess-at-of-split-R-same (L (sq n)) (p 0) (u (find-nonunit 0 R)))
                                        (:instance excess-at-of-split-R-same (L (sq n)) (p 1) (u (find-nonunit 1 R)))
                                        (:instance excess-at-of-split-R-same (L (sq n)) (p 2) (u (find-nonunit 2 R)))
                                        (:instance excess-at-of-split-R-other (L (sq n)) (p 1) (q 0) (u (find-nonunit 1 R)))
                                        (:instance excess-at-of-split-R-other (L (sq n)) (p 2) (q 0) (u (find-nonunit 2 R)))
                                        (:instance excess-at-of-split-R-other (L (sq n)) (p 2) (q 1) (u (find-nonunit 2 R)))
                                        (:instance weight-is-1-when-no-nonunit (L (sq n)) (q 0) (u (find-nonunit 1 R)))
                                        (:instance weight-is-1-when-no-nonunit (L (sq n)) (q 0) (u (find-nonunit 2 R)))
                                        (:instance weight-is-1-when-no-nonunit (L (sq n)) (q 1) (u (find-nonunit 2 R)))
                                        (:instance summand-listp-of-split-R (L (sq n)) (p 0) (u (find-nonunit 0 R)))
                                        (:instance summand-listp-of-split-R (L (sq n)) (p 1) (u (find-nonunit 1 R)))
                                        (:instance summand-listp-of-split-R (L (sq n)) (p 2) (u (find-nonunit 2 R)))
                                        (:instance excess-at-nonneg (L (sq n)) (p 1) (R (split-R (sq n) 0 (find-nonunit 0 R) R)))
                                        (:instance excess-at-nonneg (L (sq n)) (p 2) (R (split-R (sq n) 0 (find-nonunit 0 R) R)))
                                        (:instance excess-at-nonneg (L (sq n)) (p 2) (R (split-R (sq n) 1 (find-nonunit 1 R) R))))))))
  (cond ((not (and (posp n) (summand-listp (sq n) R))) nil)
        ((find-nonunit 0 R)
         (let ((u (find-nonunit 0 R)))
           (append (split-path n (append R rest) 0 u)
                   (decompose-path n (split-R (sq n) 0 u R) rest))))
        ((find-nonunit 1 R)
         (let ((u (find-nonunit 1 R)))
           (append (split-path n (append R rest) 1 u)
                   (decompose-path n (split-R (sq n) 1 u R) rest))))
        ((find-nonunit 2 R)
         (let ((u (find-nonunit 2 R)))
           (append (split-path n (append R rest) 2 u)
                   (decompose-path n (split-R (sq n) 2 u R) rest))))
        (t nil)))

(defun decompose-R (n R)
  (declare (xargs :guard t :verify-guards nil
                  :measure (llist (excess-at 0 R) (excess-at 1 R) (excess-at 2 R))
                  :well-founded-relation l<
                  :hints (("Goal" :in-theory (e/d (l< d<) (excess-at-nonneg find-nonunit-works excess-at-pos-when-nonunit
                                                          excess-at-of-split-R-same
                                                          excess-at-of-split-R-other
                                                          weight-is-1-when-no-nonunit
                                                          summand-listp-of-split-R))
                                  :do-not-induct t
                                  :use ((:instance excess-at-nonneg (L (sq n)) (p 0))
                                        (:instance excess-at-nonneg (L (sq n)) (p 1))
                                        (:instance excess-at-nonneg (L (sq n)) (p 2))
                                        (:instance excess-at-pos-when-nonunit (L (sq n)) (p 0))
                                        (:instance excess-at-pos-when-nonunit (L (sq n)) (p 1))
                                        (:instance excess-at-pos-when-nonunit (L (sq n)) (p 2))
                                        (:instance find-nonunit-works (p 0))
                                        (:instance find-nonunit-works (p 1))
                                        (:instance find-nonunit-works (p 2))
                                        (:instance summand-listp-member (L (sq n)) (s (find-nonunit 0 R)) (x R))
                                        (:instance summand-listp-member (L (sq n)) (s (find-nonunit 1 R)) (x R))
                                        (:instance summand-listp-member (L (sq n)) (s (find-nonunit 2 R)) (x R))
                                        (:instance excess-at-of-split-R-same (L (sq n)) (p 0) (u (find-nonunit 0 R)))
                                        (:instance excess-at-of-split-R-same (L (sq n)) (p 1) (u (find-nonunit 1 R)))
                                        (:instance excess-at-of-split-R-same (L (sq n)) (p 2) (u (find-nonunit 2 R)))
                                        (:instance excess-at-of-split-R-other (L (sq n)) (p 1) (q 0) (u (find-nonunit 1 R)))
                                        (:instance excess-at-of-split-R-other (L (sq n)) (p 2) (q 0) (u (find-nonunit 2 R)))
                                        (:instance excess-at-of-split-R-other (L (sq n)) (p 2) (q 1) (u (find-nonunit 2 R)))
                                        (:instance weight-is-1-when-no-nonunit (L (sq n)) (q 0) (u (find-nonunit 1 R)))
                                        (:instance weight-is-1-when-no-nonunit (L (sq n)) (q 0) (u (find-nonunit 2 R)))
                                        (:instance weight-is-1-when-no-nonunit (L (sq n)) (q 1) (u (find-nonunit 2 R)))
                                        (:instance summand-listp-of-split-R (L (sq n)) (p 0) (u (find-nonunit 0 R)))
                                        (:instance summand-listp-of-split-R (L (sq n)) (p 1) (u (find-nonunit 1 R)))
                                        (:instance summand-listp-of-split-R (L (sq n)) (p 2) (u (find-nonunit 2 R)))
                                        (:instance excess-at-nonneg (L (sq n)) (p 1) (R (split-R (sq n) 0 (find-nonunit 0 R) R)))
                                        (:instance excess-at-nonneg (L (sq n)) (p 2) (R (split-R (sq n) 0 (find-nonunit 0 R) R)))
                                        (:instance excess-at-nonneg (L (sq n)) (p 2) (R (split-R (sq n) 1 (find-nonunit 1 R) R))))))))
  (cond ((not (and (posp n) (summand-listp (sq n) R))) R)
        ((find-nonunit 0 R) (decompose-R n (split-R (sq n) 0 (find-nonunit 0 R) R)))
        ((find-nonunit 1 R) (decompose-R n (split-R (sq n) 1 (find-nonunit 1 R) R)))
        ((find-nonunit 2 R) (decompose-R n (split-R (sq n) 2 (find-nonunit 2 R) R)))
        (t R)))

;; A summand all of whose factors are units.
(defun basic-summandp (u)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (bv-weight (fac 0 u)) 1)
       (equal (bv-weight (fac 1 u)) 1)
       (equal (bv-weight (fac 2 u)) 1)))

(defun basic-listp (R)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom R) t (and (basic-summandp (car R)) (basic-listp (cdr R)))))

(defthm basic-listp-when-no-nonunits
  (implies (and (posp L) (summand-listp L R)
                (not (find-nonunit 0 R)) (not (find-nonunit 1 R)) (not (find-nonunit 2 R)))
           (basic-listp R))
  :hints (("Goal" :induct (summand-listp L R))))

(defthm decompose-R-facts
  (implies (and (posp n) (summand-listp (sq n) R))
           (and (summand-listp (sq n) (decompose-R n R))
                (equal (triple-sum (sq n) (decompose-R n R)) (triple-sum (sq n) R))
                (basic-listp (decompose-R n R))))
  :hints (("Goal" :induct (decompose-R n R))))

(defthm schemep-of-append-when-sum-preserved
  (implies (and (schemep n (append R rest)) (summand-listp (sq n) R)
                (summand-listp (sq n) R2)
                (equal (triple-sum (sq n) R2) (triple-sum (sq n) R)))
           (schemep n (append R2 rest)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable triple-sum-of-append)
                  :use ((:instance summand-listp-append-parts (L (sq n)))
                        (:instance summand-listp-of-append (L (sq n)) (x R2) (y rest))
                        (:instance triple-sum-of-append (L (sq n)) (x R) (y rest))
                        (:instance triple-sum-of-append (L (sq n)) (x R2) (y rest))))))

;; Correctness of phase 1.
(defthm decompose-path-correct
  (implies (and (schemep n (append R rest)) (summand-listp (sq n) R) (<= 2 n))
           (and (path-ok-p (sq n) (decompose-path n R rest) (append R rest))
                (perm (apply-path (sq n) (decompose-path n R rest) (append R rest))
                      (append (decompose-R n R) rest))))
  :hints (("Goal" :induct (decompose-path n R rest)
                  :in-theory (e/d (split-path) (summandp-facts-rw
                                                perm-of-cons-arg1 perm-of-cons-arg2
                                                perm-rotate-3 perm-rotate-4 perm-rotate-3-append
                                                perm-rotate-4-append perm-step4-shape
                                                perm-append-list-1 perm-append-list-2
                                                perm-cons-remove1-when-member
                                                perm-split-shape perm-split-shape-2
                                                set-fac-of-set-fac-other-commute)))))

;;; ------------------------------------------------------------------
;;; Phase 2: a zero-sum multiset of basis tensors consists of pairs
;;; ------------------------------------------------------------------

;; Tensor index of a basic summand.
(defun bidx (L u)
  (declare (xargs :guard t :verify-guards nil))
  (tidx3 L L (bv-first-one (fac 0 u)) (bv-first-one (fac 1 u)) (bv-first-one (fac 2 u))))

;; A basic summand is determined by its three unit positions.
(defthm basic-summand-is-units
  (implies (and (posp L) (summandp L u) (basic-summandp u))
           (equal (list (unit L (bv-first-one (fac 0 u)))
                        (unit L (bv-first-one (fac 1 u)))
                        (unit L (bv-first-one (fac 2 u))))
                  u))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable bv-weight-one-is-unit list-of-facs)
                  :use ((:instance summandp-facts (s u))
                        (:instance list-of-facs (s u))
                        (:instance bv-weight-one-is-unit (x (fac 0 u)))
                        (:instance bv-weight-one-is-unit (x (fac 1 u)))
                        (:instance bv-weight-one-is-unit (x (fac 2 u)))))))

(defthm first-one-bound-when-summandp
  (implies (and (posp L) (summandp L u) (posp3 p))
           (< (bv-first-one (fac p u)) L))
  :hints (("Goal" :in-theory (disable bv-first-one-witness fac-nonzero-when-summandp)
                  :use ((:instance fac-nonzero-when-summandp (s u))
                        (:instance bv-first-one-witness (x (fac p u))))))
  :rule-classes :linear)

;; Coordinate (bidx u) of the rank-one tensor of a basic summand v is 1
;; iff v = u.
(defthm nth-bidx-of-rank1-basic
  (implies (and (posp L) (summandp L u) (basic-summandp u)
                (summandp L v) (basic-summandp v))
           (equal (nth (bidx L u) (rank1 v))
                  (if (equal v u) 1 0)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (rank1 fac) (nth-of-outer3 basic-summand-is-units
                                                first-one-bound-when-summandp
                                                bv-weight-one-is-unit nth-of-unit))
                  :use ((:instance summandp-facts (s u))
                        (:instance summandp-facts (s v))
                        (:instance basic-summand-is-units)
                        (:instance basic-summand-is-units (u v))
                        (:instance bv-weight-one-is-unit (x (fac 0 v)))
                        (:instance bv-weight-one-is-unit (x (fac 1 v)))
                        (:instance bv-weight-one-is-unit (x (fac 2 v)))
                        (:instance nth-of-unit (L L) (i (bv-first-one (fac 0 u))) (k (bv-first-one (fac 0 v))))
                        (:instance nth-of-unit (L L) (i (bv-first-one (fac 1 u))) (k (bv-first-one (fac 1 v))))
                        (:instance nth-of-unit (L L) (i (bv-first-one (fac 2 u))) (k (bv-first-one (fac 2 v))))
                        (:instance first-one-bound-when-summandp (p 0))
                        (:instance first-one-bound-when-summandp (p 1))
                        (:instance first-one-bound-when-summandp (p 2))
                        (:instance first-one-bound-when-summandp (u v) (p 0))
                        (:instance first-one-bound-when-summandp (u v) (p 1))
                        (:instance first-one-bound-when-summandp (u v) (p 2))
                        (:instance nth-of-outer3 (A (car v)) (B (cadr v)) (C (caddr v))
                                   (ia (bv-first-one (fac 0 u)))
                                   (ib (bv-first-one (fac 1 u)))
                                   (ic (bv-first-one (fac 2 u))))))))

(defun odd-count (u R)
  (declare (xargs :guard t))
  (cond ((atom R) nil)
        ((equal (car R) u) (not (odd-count u (cdr R))))
        (t (odd-count u (cdr R)))))

(defthm odd-count-implies-member
  (implies (odd-count u R) (member-equal u R)))

(defthm bidx-bound
  (implies (and (posp L) (summandp L u))
           (< (bidx L u) (tlen L)))
  :hints (("Goal" :in-theory (disable tidx3-bound first-one-bound-when-summandp)
                  :use ((:instance tidx3-bound (LA L) (LB L) (LC L)
                                   (a (bv-first-one (fac 0 u)))
                                   (b (bv-first-one (fac 1 u)))
                                   (c (bv-first-one (fac 2 u))))
                        (:instance first-one-bound-when-summandp (p 0))
                        (:instance first-one-bound-when-summandp (p 1))
                        (:instance first-one-bound-when-summandp (p 2)))))
  :rule-classes :linear)

(defthm natp-of-bidx
  (implies (natp L) (natp (bidx L u)))
  :hints (("Goal" :in-theory (enable tidx3)))
  :rule-classes :type-prescription)

(in-theory (disable bidx))

(defthm nth-bidx-of-triple-sum-basic
  (implies (and (posp L) (summandp L u) (basic-summandp u)
                (summand-listp L R) (basic-listp R))
           (equal (nth (bidx L u) (triple-sum L R))
                  (if (odd-count u R) 1 0)))
  :hints (("Goal" :induct (odd-count u R)
                  :in-theory (disable nth-bidx-of-rank1-basic bidx-bound))
          ("Subgoal *1/3" :use ((:instance nth-bidx-of-rank1-basic (v (car R)))
                                (:instance bidx-bound)
                                (:instance len-of-rank1-when-summandp (s (car R)))
                                (:instance nth-of-bv+ (i (bidx L u)) (x (rank1 (car R)))
                                           (y (triple-sum L (cdr R))))))
          ("Subgoal *1/2" :use ((:instance nth-bidx-of-rank1-basic (v (car R)))
                                (:instance bidx-bound)
                                (:instance len-of-rank1-when-summandp (s (car R)))
                                (:instance nth-of-bv+ (i (bidx L u)) (x (rank1 (car R)))
                                           (y (triple-sum L (cdr R))))))
          ("Subgoal *1/1" :use ((:instance bidx-bound)))))

;; The first summand of a zero-sum basic list occurs again later.
(defthm car-member-cdr-when-zero-sum-basic
  (implies (and (posp L) (summand-listp L R) (basic-listp R) (consp R)
                (equal (triple-sum L R) (bv-zero (tlen L))))
           (member-equal (car R) (cdr R)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable nth-bidx-of-triple-sum-basic odd-count-implies-member)
                  :use ((:instance nth-bidx-of-triple-sum-basic (u (car R)))
                        (:instance odd-count-implies-member (u (car R)) (R (cdr R)))))))

(defthm basic-listp-of-remove1
  (implies (basic-listp R) (basic-listp (remove1-equal u R)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defun delete-pairs-path (R)
  (declare (xargs :guard t :verify-guards nil :measure (len R)))
  (if (atom R)
      nil
    (cons (delete-pair-move (car R))
          (delete-pairs-path (remove1-equal (car R) (cdr R))))))

(defthm triple-sum-of-remove1-car
  (implies (and (posp L) (summand-listp L R) (consp R) (member-equal (car R) (cdr R)))
           (equal (triple-sum L (remove1-equal (car R) (cdr R)))
                  (triple-sum L R)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable triple-sum-of-remove1)
                  :use ((:instance triple-sum-of-remove1 (s (car R)) (x (cdr R)))
                        (:instance summandp-facts (s (car R)))))))

(defthm triplep-when-summandp
  (implies (summandp L s) (triplep L s))
  :hints (("Goal" :in-theory (enable summandp))))

(defthm delete-pairs-correct
  (implies (and (posp L) (summand-listp L R) (basic-listp R) (true-listp rest)
                (equal (triple-sum L R) (bv-zero (tlen L))))
           (and (path-ok-p L (delete-pairs-path R) (append R rest))
                (perm (apply-path L (delete-pairs-path R) (append R rest)) rest)))
  :hints (("Goal" :induct (delete-pairs-path R)
                  :in-theory (disable car-member-cdr-when-zero-sum-basic
                                      apply-delete-pair-move delete-pair-move-ok
                                      triple-sum-of-remove1-car
                                      perm-of-cons-arg1 perm-of-cons-arg2))
          ("Subgoal *1/2" :use (car-member-cdr-when-zero-sum-basic
                                triple-sum-of-remove1-car
                                (:instance apply-delete-pair-move (s1 (car R)) (S (append R rest)))
                                (:instance delete-pair-move-ok (s1 (car R)) (S (append R rest)))))))

;;; ------------------------------------------------------------------
;;; Lemma 4.5
;;; ------------------------------------------------------------------

(defun zero-subset-path (n R rest)
  (declare (xargs :guard t :verify-guards nil))
  (append (decompose-path n R rest)
          (delete-pairs-path (decompose-R n R))))

(defthm zero-subset-lemma
  (implies (and (schemep n (append R rest)) (summand-listp (sq n) R) (<= 2 n)
                (equal (triple-sum (sq n) R) (bv-zero (tlen (sq n)))))
           (and (path-ok-p (sq n) (zero-subset-path n R rest) (append R rest))
                (perm (apply-path (sq n) (zero-subset-path n R rest) (append R rest))
                      rest)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable perm-of-cons-arg1 perm-of-cons-arg2 perm-of-append
                                      perm-of-append-of-cons perm-of-append-of-cdr-and-cons-of-car)
                  :use ((:instance summand-listp-append-parts (L (sq n)))))))
