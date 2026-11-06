; x-add-arbitrary.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/add-arbitrary.lisp
; produced by rename.py in this directory; do not edit by hand.
; add-arbitrary.lisp -- Lemma 4.4 of the paper (add-arbitrary).
;
; For a scheme S (n >= 2) and nonzero matrices X, Y, Z there is a path
; from S to S (+) { X(x)Y(x)Z, X(x)Y(x)Z }.
;
; Following the paper we first change the p-factor of a summand step by
; step, each step using Lemma 4.3 and then deleting the previous pair
; (Observation 4.1).  The paper chooses the steps from a basis
; expansion; here we make the choice constructive: starting from a
; summand s0 with p-factor A0 /= X we take the multiset of p-factors
; whose sum is A0 + X (obtained from the span lemma, Lemma 4.2), cancel
; duplicate pairs to get a set Us, and then greedily walk through Us,
; always picking an element U different from the current partial sum cur
; (so that cur + U is nonzero).  Such a U exists because otherwise Us is
; {cur} and X = cur + cur = 0.

(in-package "ACL2")

(include-book "x-add-dup")

;;; ------------------------------------------------------------------
;;; Picking the next step of the walk
;;; ------------------------------------------------------------------

;; The first element of Us different from cur (nil if none).
(defun x-pick-U (cur Us)
  (declare (xargs :guard t))
  (cond ((atom Us) nil)
        ((equal (car Us) cur) (x-pick-U cur (cdr Us)))
        (t (car Us))))

(defthm x-pick-U-member
  (implies (x-pick-U cur Us)
           (and (member-equal (x-pick-U cur Us) Us)
                (not (equal (x-pick-U cur Us) cur)))))

(defthm x-all-equal-to-when-no-pick
  (implies (and (not (x-pick-U cur Us)) (x-bv-listp L Us) (posp L))
           (x-all-equal-to cur Us))
  :hints (("Goal" :induct (x-bv-listp L Us))))

(defthm x-member-when-all-equal-to
  (implies (and (x-all-equal-to cur x) (consp x))
           (member-equal cur x)))

(defthm x-cdr-atom-when-all-equal-no-dups
  (implies (and (x-all-equal-to cur Us) (no-duplicatesp-equal Us) (consp Us))
           (not (consp (cdr Us))))
  :hints (("Goal" :in-theory (disable x-member-when-all-equal-to)
                  :use ((:instance x-member-when-all-equal-to (x (cdr Us)))))))

(defthm x-all-equal-no-dups-singleton
  (implies (and (x-all-equal-to cur Us) (no-duplicatesp-equal Us) (consp Us)
                (x-bv-listp L Us) (posp L))
           (equal (x-bv-sum L Us) cur))
  :hints (("Goal" :in-theory (disable x-bv-sum-when-all-equal-to x-member-when-all-equal-to
                                      x-cdr-atom-when-all-equal-no-dups)
                  :use (x-cdr-atom-when-all-equal-no-dups)
                  :expand ((x-bv-sum L Us) (x-bv-sum L (cdr Us)) (x-all-equal-to cur Us)))))

(defthm x-pick-U-exists
  (implies (and (consp Us) (no-duplicatesp-equal Us) (x-bv-listp L Us)
                (posp L) (x-bvp cur) (equal (len cur) L)
                (not (equal (x-bv+ cur (x-bv-sum L Us)) (x-bv-zero L))))
           (x-pick-U cur Us))
  :hints (("Goal" :in-theory (disable x-all-equal-no-dups-singleton x-all-equal-to-when-no-pick
                                      x-bv-sum-when-all-equal-to x-member-when-all-equal-to
                                      x-cdr-atom-when-all-equal-no-dups)
                  :use (x-all-equal-no-dups-singleton x-all-equal-to-when-no-pick))))

(in-theory (disable x-all-equal-no-dups-singleton x-all-equal-to-when-no-pick
                    x-bv-sum-when-all-equal-to x-member-when-all-equal-to
                    x-cdr-atom-when-all-equal-no-dups))

;; A summand of S whose p-factor is U.
(defun x-find-fac (p U S)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom S) nil)
        ((equal (x-fac p (car S)) U) (car S))
        (t (x-find-fac p U (cdr S)))))

(defthm x-find-fac-works
  (implies (member-equal U (x-facs p S))
           (and (member-equal (x-find-fac p U S) S)
                (equal (x-fac p (x-find-fac p U S)) U))))

(defthm x-facs-are-summand-factors
  (implies (and (member-equal U (x-facs p S)) (x-summand-listp L S) (x-posp3 p) (posp L))
           (and (x-bvp U) (equal (len U) L) (not (equal U (x-bv-zero L)))))
  :hints (("Goal" :induct (x-facs p S))
          ("Subgoal *1/2" :use ((:instance x-summandp-facts (s (car S)))
                                (:instance x-fac-nonzero-when-summandp (s (car S)))))))

(defthm x-member-subsetp-facs
  (implies (and (member-equal U Us) (subsetp-equal Us (x-facs p S)))
           (member-equal U (x-facs p S))))

;;; ------------------------------------------------------------------
;;; The walk
;;; ------------------------------------------------------------------

;; Current scheme: (list* sP sP S) with sP = (set-fac p cur s0).
;; Each round: Lemma 4.3 with s = sP and a summand u of S whose p-factor
;; is U, then delete the old pair.
(defun x-walk-path (p s0 cur Us S)
  (declare (xargs :guard t :verify-guards nil :measure (len Us)))
  (let ((U (x-pick-U cur Us)))
    (if (not U)
        nil
      (let* ((usum (x-find-fac p U S))
             (sP (x-set-fac p cur s0))
             (P2 (x-bv+ cur U)))
        (append (x-add-dup-path p sP usum)
                (cons (x-delete-pair-move sP)
                      (x-walk-path p s0 P2 (remove1-equal U Us) S)))))))

(defthm x-no-duplicatesp-of-remove1
  (implies (no-duplicatesp-equal x) (no-duplicatesp-equal (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-subsetp-of-remove1-equal-arg1
  (implies (subsetp-equal x y) (subsetp-equal (remove1-equal a x) y))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-summand-listp-of-list*-pair
  (equal (x-summand-listp L (list* a a S))
         (and (x-summandp L a) (x-summand-listp L S))))

(defthm x-walk-path-correct
  (implies (and (posp L) (x-summand-listp L S) (x-posp3 p)
                (x-summandp L s0)
                (x-bvp cur) (equal (len cur) L) (not (equal cur (x-bv-zero L)))
                (x-bv-listp L Us) (no-duplicatesp-equal Us)
                (subsetp-equal Us (x-facs p S))
                (x-bvp X) (equal (len X) L) (not (equal X (x-bv-zero L)))
                (equal (x-bv+ cur (x-bv-sum L Us)) X))
           (and (x-path-ok-p L (x-walk-path p s0 cur Us S)
                           (list* (x-set-fac p cur s0) (x-set-fac p cur s0) S))
                (perm (x-apply-path L (x-walk-path p s0 cur Us S)
                                  (list* (x-set-fac p cur s0) (x-set-fac p cur s0) S))
                      (list* (x-set-fac p X s0) (x-set-fac p X s0) S))))
  :hints (("Goal" :induct (x-walk-path p s0 cur Us S)
                  :in-theory (disable x-pick-U-exists x-find-fac-works
                                      x-facs-are-summand-factors x-summandp-facts-rw
                                      perm-of-cons-arg1 perm-of-cons-arg2
                                      x-perm-rotate-3 x-perm-rotate-4 x-perm-rotate-3-append
                                      x-perm-rotate-4-append x-perm-step4-shape
                                      x-perm-append-list-1 x-perm-append-list-2
                                      x-perm-cons-remove1-when-member
                                      x-set-fac-of-set-fac-other-commute))
          ("Subgoal *1/2" :use (x-pick-U-exists
                                (:instance x-find-fac-works (U (x-pick-U cur Us)))
                                (:instance x-facs-are-summand-factors (U (x-pick-U cur Us)))
                                (:instance x-summandp-of-set-fac (s s0) (v cur))
                                (:instance x-summandp-of-set-fac (s s0) (v (x-bv+ cur (x-pick-U cur Us))))
                                (:instance x-bv-sum-of-remove1 (a (x-pick-U cur Us)) (x Us))
                                (:instance x-bv+-equal-zero (x cur) (y (x-pick-U cur Us)))))
          ("Subgoal *1/1" :use (x-pick-U-exists))))

;;; ------------------------------------------------------------------
;;; The multiset of p-factors summing to X (from the span lemma)
;;; ------------------------------------------------------------------

;; X with the coordinates below k cleared.
(defun x-bv-mask-from (X k)
  (declare (xargs :guard (and (x-bvp X) (integerp k))))
  (if (atom X) nil (cons (if (<= (ifix k) 0) (car X) 0) (x-bv-mask-from (cdr X) (1- (ifix k))))))

(defthm x-bvp-of-bv-mask-from (implies (x-bvp X) (x-bvp (x-bv-mask-from X k))))
(defthm x-len-of-bv-mask-from (equal (len (x-bv-mask-from X k)) (len X)))
(defthm x-bv-mask-from-nonpos
  (implies (and (x-bvp X) (integerp k) (<= k 0)) (equal (x-bv-mask-from X k) X)))
(defthm x-bv-mask-from-0 (implies (x-bvp X) (equal (x-bv-mask-from X 0) X)))
(defthm x-bv-mask-from-end
  (implies (and (x-bvp X) (integerp k) (<= (len X) k))
           (equal (x-bv-mask-from X k) (x-bv-zero (len X)))))
(defun x-ind-xik (X i k)
  (if (atom X) (list X i k) (x-ind-xik (cdr X) (1- i) (1- k))))

(defthm x-nth-of-bv-mask-from
  (implies (and (x-bvp X) (natp i) (< i (len X)) (integerp k))
           (equal (nth i (x-bv-mask-from X k)) (if (< i k) 0 (nth i X))))
  :hints (("Goal" :induct (x-ind-xik X i k))))

(defthm x-bv-mask-from-step
  (implies (and (x-bvp X) (natp k) (< k (len X)))
           (equal (x-bv+ (if (equal (nth k X) 1) (x-unit (len X) k) (x-bv-zero (len X)))
                       (x-bv-mask-from X (1+ k)))
                  (x-bv-mask-from X k)))
  :hints (("Goal" :use ((:instance x-bv-extensionality
                                   (x (x-bv+ (if (equal (nth k X) 1) (x-unit (len X) k) (x-bv-zero (len X)))
                                           (x-bv-mask-from X (1+ k))))
                                   (y (x-bv-mask-from X k)))
                        (:instance x-bv-diff-index-witness
                                   (x (x-bv+ (if (equal (nth k X) 1) (x-unit (len X) k) (x-bv-zero (len X)))
                                           (x-bv-mask-from X (1+ k))))
                                   (y (x-bv-mask-from X k))))
                  :in-theory (disable x-bv-diff-index-witness))))

;; The p-factors selected by the span lemma for every unit in the support
;; of X (coordinates k, k+1, ..., n^2 - 1).
(defun x-unit-facs (p n S X k)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix (- (x-sq n) k))))
  (if (or (not (natp n)) (not (natp k)) (>= k (x-sq n)))
      nil
    (append (if (equal (nth k X) 1)
                (x-sel-list p S (x-span-b p n (floor k n) (mod k n))
                          (x-span-c p n (floor k n) (mod k n)))
              nil)
            (x-unit-facs p n S X (1+ k)))))

(defthm x-true-listp-of-sel-list (true-listp (x-sel-list p S b c)))

(defthm x-bv-listp-of-unit-facs
  (implies (and (x-triple-listp (x-sq n) S) (x-posp3 p))
           (x-bv-listp (x-sq n) (x-unit-facs p n S X k))))

(defthm x-subsetp-of-unit-facs
  (subsetp-equal (x-unit-facs p n S X k) (x-facs p S)))

(defthm x-midx-of-floor-mod
  (implies (and (natp k) (posp n))
           (equal (x-midx n (floor k n) (mod k n)) k))
  :hints (("Goal" :in-theory (enable x-midx) :use x-floor-mod-decompose)))

(defthm x-unit-facs-step
  (implies (and (x-schemep n S) (x-posp3 p) (x-bvp X) (equal (len X) (x-sq n))
                (natp k) (< k (x-sq n)))
           (equal (x-bv-sum (x-sq n) (x-unit-facs p n S X k))
                  (x-bv+ (if (equal (nth k X) 1) (x-unit (x-sq n) k) (x-bv-zero (x-sq n)))
                       (x-bv-sum (x-sq n) (x-unit-facs p n S X (1+ k))))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (x-sel-sum) (x-span-lemma x-bv-listp-of-unit-facs x-bv-listp-of-sel-list))
                  :expand ((x-unit-facs p n S X k))
                  :use ((:instance x-span-lemma (x (floor k n)) (y (mod k n)))
                        (:instance x-floor-bound (a k))
                        (:instance x-mod-bound (a k))
                        (:instance x-bv-listp-of-unit-facs (k (1+ k)))
                        (:instance x-bv-listp-of-sel-list (L (x-sq n))
                                   (b (x-span-b p n (floor k n) (mod k n)))
                                   (c (x-span-c p n (floor k n) (mod k n))))
                        (:instance x-bv-sum-of-append (L (x-sq n))
                                   (x (x-sel-list p S (x-span-b p n (floor k n) (mod k n))
                                                (x-span-c p n (floor k n) (mod k n))))
                                   (y (x-unit-facs p n S X (1+ k))))))))

(defthm x-bv-sum-of-unit-facs
  (implies (and (x-schemep n S) (x-posp3 p) (x-bvp X) (equal (len X) (x-sq n)) (natp k))
           (equal (x-bv-sum (x-sq n) (x-unit-facs p n S X k))
                  (x-bv-mask-from X k)))
  :hints (("Goal" :induct (x-unit-facs p n S X k)
                  :in-theory (disable x-unit-facs-step x-bv-mask-from-step (:definition x-unit-facs)))
          ("Subgoal *1/2" :use (x-unit-facs-step
                                (:instance x-bv-mask-from-step)))
          ("Subgoal *1/1" :expand ((x-unit-facs p n S X k)))))

;; The set of factors to walk through: sum = A0 + X, no duplicates.
(defun x-arb-Us (p n S s0 X)
  (declare (xargs :guard t :verify-guards nil))
  (x-cancel-dups (cons (x-fac p s0) (x-unit-facs p n S X 0))))

(defthm x-subsetp-trans-helper
  (implies (and (subsetp-equal x y) (subsetp-equal y z))
           (subsetp-equal x z)))

(defthm x-arb-Us-bv-listp
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S))
           (x-bv-listp (x-sq n) (x-arb-Us p n S s0 X)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (enable x-arb-Us)
                  :use ((:instance x-summandp-facts (L (x-sq n)) (s s0))))))

(defthm x-arb-Us-no-dups
  (no-duplicatesp-equal (x-arb-Us p n S s0 X))
  :hints (("Goal" :in-theory (enable x-arb-Us))))

(defthm x-arb-Us-subsetp
  (implies (member-equal s0 S)
           (subsetp-equal (x-arb-Us p n S s0 X) (x-facs p S)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (x-arb-Us) (x-subsetp-trans-helper x-subsetp-of-cancel-dups))
                  :use ((:instance x-subsetp-of-cancel-dups
                                   (lst (cons (x-fac p s0) (x-unit-facs p n S X 0))))
                        (:instance x-subsetp-trans-helper
                                   (x (x-arb-Us p n S s0 X))
                                   (y (cons (x-fac p s0) (x-unit-facs p n S X 0)))
                                   (z (x-facs p S)))))))

(defthm x-arb-Us-sum
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n)))
           (equal (x-bv-sum (x-sq n) (x-arb-Us p n S s0 X))
                  (x-bv+ (x-fac p s0) X)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (x-arb-Us) (x-bv-sum-of-cancel-dups x-bv-sum-of-unit-facs))
                  :use ((:instance x-bv-sum-of-cancel-dups (L (x-sq n))
                                   (lst (cons (x-fac p s0) (x-unit-facs p n S X 0))))
                        (:instance x-bv-sum-of-unit-facs (k 0))
                        (:instance x-summandp-facts (L (x-sq n)) (s s0))))))

(defthm x-arb-Us-facts
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n)))
           (and (x-bv-listp (x-sq n) (x-arb-Us p n S s0 X))
                (no-duplicatesp-equal (x-arb-Us p n S s0 X))
                (subsetp-equal (x-arb-Us p n S s0 X) (x-facs p S))
                (equal (x-bv-sum (x-sq n) (x-arb-Us p n S s0 X))
                       (x-bv+ (x-fac p s0) X))))
  :rule-classes nil
  :hints (("Goal" :in-theory nil
                  :use (x-arb-Us-bv-listp x-arb-Us-no-dups x-arb-Us-subsetp x-arb-Us-sum))))

(in-theory (disable x-arb-Us))

;;; ------------------------------------------------------------------
;;; Changing one factor of a summand to an arbitrary nonzero X
;;; ------------------------------------------------------------------

(defun x-add-arb-p-path (p n S s0 X)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((A0 (x-fac p s0))
         (Us (x-arb-Us p n S s0 X))
         (U0 (x-pick-U A0 Us))
         (usum0 (x-find-fac p U0 S)))
    (append (x-add-dup-path p s0 usum0)
            (x-walk-path p s0 (x-bv+ A0 U0) (remove1-equal U0 Us) S))))

(defthm x-bv-sum-nil (equal (x-bv-sum L nil) (x-bv-zero L)))

(defthm x-not-equal-when-fac-differs
  (implies (not (equal (x-fac p u) (x-fac p s)))
           (not (equal u s)))
  :rule-classes nil)

(defthm x-arb-Us-consp
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n))
                (not (equal (x-fac p s0) X)))
           (consp (x-arb-Us p n S s0 X)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-arb-Us-sum x-arb-Us-bv-listp)
                  :use (x-arb-Us-sum x-arb-Us-bv-listp
                        (:instance x-summandp-facts (L (x-sq n)) (s s0))
                        (:instance x-bv+-equal-zero (x (x-fac p s0)) (y X))))))

;; Facts about the first step U0 = (pick-U A0 Us).
(defthm x-arb-pick-facts
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n))))
                (not (equal (x-fac p s0) X)))
           (let ((U0 (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X))))
             (and U0
                  (member-equal U0 (x-arb-Us p n S s0 X))
                  (not (equal U0 (x-fac p s0)))
                  (member-equal U0 (x-facs p S)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-pick-U-exists x-arb-Us-sum x-arb-Us-bv-listp x-arb-Us-no-dups
                                      x-arb-Us-subsetp x-arb-Us-consp x-pick-U-member)
                  :use (x-arb-Us-sum x-arb-Us-bv-listp x-arb-Us-no-dups x-arb-Us-subsetp x-arb-Us-consp
                        (:instance x-summandp-facts (L (x-sq n)) (s s0))
                        (:instance x-pick-U-exists (L (x-sq n)) (cur (x-fac p s0)) (Us (x-arb-Us p n S s0 X)))
                        (:instance x-pick-U-member (cur (x-fac p s0)) (Us (x-arb-Us p n S s0 X)))
                        (:instance x-bv+-self-in-middle (x (x-fac p s0)) (y X))))))

(defthm x-arb-U0-facts
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n))))
                (not (equal (x-fac p s0) X)))
           (let ((U0 (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X))))
             (and (x-bvp U0) (equal (len U0) (x-sq n)) (not (equal U0 (x-bv-zero (x-sq n))))
                  (not (equal (x-bv+ (x-fac p s0) U0) (x-bv-zero (x-sq n)))))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-arb-pick-facts x-facs-are-summand-factors)
                  :use (x-arb-pick-facts
                        (:instance x-summandp-facts (L (x-sq n)) (s s0))
                        (:instance x-facs-are-summand-factors (L (x-sq n))
                                   (U (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X))))
                        (:instance x-bv+-equal-zero (x (x-fac p s0))
                                   (y (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X))))))))

(defthm x-arb-usum0-summand-facts
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n))))
                (not (equal (x-fac p s0) X)))
           (let* ((U0 (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X)))
                  (usum0 (x-find-fac p U0 S)))
             (and (member-equal usum0 S)
                  (equal (x-fac p usum0) U0)
                  (member-equal usum0 (remove1-equal s0 S)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-arb-pick-facts x-find-fac-works)
                  :use (x-arb-pick-facts
                        (:instance x-find-fac-works (U (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X))))
                        (:instance x-not-equal-when-fac-differs
                                   (u (x-find-fac p (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X)) S))
                                   (s s0))
                        (:instance x-member-remove1-when-different
                                   (u (x-find-fac p (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X)) S))
                                   (s1 s0) (S S))))))

;; The first step: Lemma 4.3 on s0 and usum0.
(defthm x-arb-first-step
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n))))
                (not (equal (x-fac p s0) X)))
           (let* ((U0 (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X)))
                  (usum0 (x-find-fac p U0 S))
                  (s1 (x-set-fac p (x-bv+ (x-fac p s0) U0) s0)))
             (and (x-path-ok-p (x-sq n) (x-add-dup-path p s0 usum0) S)
                  (perm (x-apply-path (x-sq n) (x-add-dup-path p s0 usum0) S)
                        (list* s1 s1 S)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-arb-pick-facts x-arb-U0-facts x-arb-usum0-summand-facts x-add-dup-lemma)
                  :use (x-arb-U0-facts x-arb-usum0-summand-facts
                        (:instance x-add-dup-lemma (L (x-sq n)) (sch S) (s s0)
                                   (u (x-find-fac p (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X)) S)))))))

;; The walk: from (list* s1 s1 S) to (list* sX sX S).
(defthm x-arb-walk-step
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n))))
                (not (equal (x-fac p s0) X)))
           (let* ((U0 (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X)))
                  (cur (x-bv+ (x-fac p s0) U0))
                  (Us1 (remove1-equal U0 (x-arb-Us p n S s0 X)))
                  (s1 (x-set-fac p cur s0)))
             (and (x-path-ok-p (x-sq n) (x-walk-path p s0 cur Us1 S) (list* s1 s1 S))
                  (perm (x-apply-path (x-sq n) (x-walk-path p s0 cur Us1 S) (list* s1 s1 S))
                        (list* (x-set-fac p X s0) (x-set-fac p X s0) S)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-arb-pick-facts x-arb-U0-facts x-walk-path-correct
                                      x-arb-Us-sum x-arb-Us-bv-listp x-arb-Us-no-dups x-arb-Us-subsetp
                                      x-summandp-facts-rw)
                  :use (x-arb-pick-facts x-arb-U0-facts
                        x-arb-Us-sum x-arb-Us-bv-listp x-arb-Us-no-dups x-arb-Us-subsetp
                        (:instance x-summandp-facts (L (x-sq n)) (s s0))
                        (:instance x-bv-sum-of-remove1 (L (x-sq n))
                                   (a (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X)))
                                   (x (x-arb-Us p n S s0 X)))
                        (:instance x-walk-path-correct (L (x-sq n))
                                   (cur (x-bv+ (x-fac p s0) (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X))))
                                   (Us (remove1-equal (x-pick-U (x-fac p s0) (x-arb-Us p n S s0 X))
                                                      (x-arb-Us p n S s0 X))))))))

(defthm x-add-arb-p-lemma
  (implies (and (x-schemep n S) (x-posp3 p) (member-equal s0 S)
                (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n))))
                (not (equal (x-fac p s0) X)))
           (and (x-path-ok-p (x-sq n) (x-add-arb-p-path p n S s0 X) S)
                (perm (x-apply-path (x-sq n) (x-add-arb-p-path p n S s0 X) S)
                      (list* (x-set-fac p X s0) (x-set-fac p X s0) S))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable x-arb-first-step x-arb-walk-step
                                      perm-of-cons-arg1 perm-of-cons-arg2
                                      x-perm-rotate-3 x-perm-rotate-4 x-perm-rotate-3-append
                                      x-perm-rotate-4-append x-perm-step4-shape
                                      x-perm-append-list-1 x-perm-append-list-2
                                      x-perm-cons-remove1-when-member
                                      x-set-fac-of-set-fac-other-commute)
                  :use (x-arb-first-step x-arb-walk-step))))

(in-theory (disable x-add-arb-p-path))

;;; ------------------------------------------------------------------
;;; Lemma 4.4: adding two copies of X (x) Y (x) Z
;;; ------------------------------------------------------------------

(defun x-nz-matp (n X)
  (declare (xargs :guard (natp n)))
  (and (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n))))))

(defthm x-nz-matp-facts
  (implies (x-nz-matp n X)
           (and (x-bvp X) (equal (len X) (x-sq n)) (not (equal X (x-bv-zero (x-sq n))))))
  :rule-classes nil)

(defthm x-summandp-list-is-nz-matp
  (implies (posp n)
           (equal (x-summandp (x-sq n) (list X Y Z))
                  (and (x-nz-matp n X) (x-nz-matp n Y) (x-nz-matp n Z))))
  :hints (("Goal" :in-theory (enable x-summandp))))

(defthm x-summandp-of-set-fac-nz
  (implies (and (posp n) (x-summandp (x-sq n) s) (x-posp3 p) (x-nz-matp n v))
           (x-summandp (x-sq n) (x-set-fac p v s)))
  :hints (("Goal" :in-theory (disable x-summandp-of-set-fac)
                  :use ((:instance x-summandp-of-set-fac (L (x-sq n)))))))

(defthm x-nz-matp-bvp (implies (x-nz-matp n X) (x-bvp X)))
(defthm x-nz-matp-len (implies (x-nz-matp n X) (equal (len X) (x-sq n))))
(defthm x-nz-matp-nonzero (implies (x-nz-matp n X) (not (equal X (x-bv-zero (x-sq n))))))

(in-theory (disable x-nz-matp))

(defthm x-schemep-of-list*-pair
  (implies (and (x-schemep n S) (x-summandp (x-sq n) a))
           (x-schemep n (list* a a S)))
  :hints (("Goal" :in-theory (enable x-rank1)
                  :use ((:instance x-summandp-facts (L (x-sq n)) (s a))))))

;; Position 0, then position 1, then position 2, deleting the previous
;; pair after each of the last two stages.
(defun x-add-arb-path (n S X Y Z)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s0 (x-find-fac-not 0 X S))
         (pA (x-add-arb-p-path 0 n S s0 X))
         (s1 (x-set-fac 0 X s0))
         (sch1 (list* s1 s1 S))
         (pB (if (equal (x-fac 1 s1) Y)
                 nil
               (append (x-add-arb-p-path 1 n sch1 s1 Y) (list (x-delete-pair-move s1)))))
         (s2 (x-set-fac 1 Y s1))
         (sch2 (list* s2 s2 S))
         (pC (if (equal (x-fac 2 s2) Z)
                 nil
               (append (x-add-arb-p-path 2 n sch2 s2 Z) (list (x-delete-pair-move s2))))))
    (append pA (append pB pC))))

(defthm x-set-fac-chain-is-list
  (implies (and (true-listp s0) (equal (len s0) 3))
           (equal (x-set-fac 2 Z (x-set-fac 1 Y (x-set-fac 0 X s0))) (list X Y Z)))
  :hints (("Goal" :in-theory (enable x-set-fac))))

(defthm x-set-fac-chain-is-list-skip-1
  (implies (and (true-listp s0) (equal (len s0) 3))
           (equal (x-set-fac 2 Z (x-set-fac 0 X s0)) (list X (x-fac 1 s0) Z)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable x-set-fac x-fac))))

(defthm x-set-fac-chain-is-list-skip-2
  (implies (and (true-listp s0) (equal (len s0) 3))
           (equal (x-set-fac 1 Y (x-set-fac 0 X s0)) (list X Y (x-fac 2 s0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable x-set-fac x-fac))))

(encapsulate ()
  (local (in-theory (disable x-add-arb-p-lemma x-summandp-facts-rw x-find-fac-not-member
                             perm-of-cons-arg1 perm-of-cons-arg2
                             x-perm-rotate-3 x-perm-rotate-4 x-perm-rotate-3-append
                             x-perm-rotate-4-append x-perm-step4-shape
                             x-perm-append-list-1 x-perm-append-list-2
                             x-perm-cons-remove1-when-member
                             x-set-fac-of-set-fac-other-commute
                             x-apply-delete-pair-move x-delete-pair-move-ok
                             x-schemep-of-list*-pair)))

  ;; Stage A: S --> S (+) {s1, s1}, s1 = X (x) B0 (x) C0.
  (defthm x-add-arb-stage-A
    (implies (and (x-schemep n S) (<= 2 n) (x-nz-matp n X))
             (let* ((s0 (x-find-fac-not 0 X S))
                    (s1 (x-set-fac 0 X s0)))
               (and (x-path-ok-p (x-sq n) (x-add-arb-p-path 0 n S s0 X) S)
                    (perm (x-apply-path (x-sq n) (x-add-arb-p-path 0 n S s0 X) S)
                          (list* s1 s1 S)))))
    :hints (("Goal" :do-not-induct t
                    :use ((:instance x-nz-matp-facts)
                          (:instance x-find-fac-not-member (p 0))
                          (:instance x-add-arb-p-lemma (p 0) (s0 (x-find-fac-not 0 X S)))))))

  ;; Generic stage: from (list* sm sm S) with (fac p sm) /= V to (list* sm' sm' S)
  ;; where sm' = (set-fac p V sm), via add-arb-p-path and a pair deletion.
  ;; Stated in the form the final proof sees after splitting the path.
  (defthm x-add-arb-stage-generic
    (implies (and (x-schemep n S) (x-posp3 p) (x-summandp (x-sq n) sm)
                  (x-nz-matp n V)
                  (not (equal (x-fac p sm) V)))
             (let* ((sch1 (list* sm sm S))
                    (mid (x-apply-path (x-sq n) (x-add-arb-p-path p n sch1 sm V) sch1)))
               (and (x-path-ok-p (x-sq n) (x-add-arb-p-path p n sch1 sm V) sch1)
                    (x-move-ok-p (x-delete-pair-move sm) mid)
                    (perm (x-apply-move (x-sq n) (x-delete-pair-move sm) mid)
                          (list* (x-set-fac p V sm) (x-set-fac p V sm) S)))))
    :hints (("Goal" :do-not-induct t
                    :in-theory (enable x-add-arb-p-lemma x-summandp-facts-rw)
                    :use ((:instance x-schemep-of-list*-pair (a sm))
                          (:instance x-summandp-facts (L (x-sq n)) (s sm))
                          (:instance x-summandp-of-set-fac (L (x-sq n)) (s sm) (v V))
                          (:instance x-apply-delete-pair-move (L (x-sq n)) (s1 sm)
                                     (S (list* (x-set-fac p V sm) (x-set-fac p V sm) sm sm S)))
                          (:instance x-delete-pair-move-ok (s1 sm)
                                     (S (list* (x-set-fac p V sm) (x-set-fac p V sm) sm sm S))))))))

(defthm x-add-arb-lemma
  (implies (and (x-schemep n S) (<= 2 n)
                (x-summandp (x-sq n) (list X Y Z)))
           (and (x-path-ok-p (x-sq n) (x-add-arb-path n S X Y Z) S)
                (perm (x-apply-path (x-sq n) (x-add-arb-path n S X Y Z) S)
                      (list* (list X Y Z) (list X Y Z) S))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable perm-of-cons-arg1 perm-of-cons-arg2
                                      x-perm-rotate-3 x-perm-rotate-4 x-perm-rotate-3-append
                                      x-perm-rotate-4-append x-perm-step4-shape
                                      x-perm-append-list-1 x-perm-append-list-2
                                      x-perm-cons-remove1-when-member
                                      x-set-fac-of-set-fac-other-commute
                                      x-apply-delete-pair-move x-delete-pair-move-ok
                                      x-schemep-of-list*-pair x-add-arb-p-lemma
                                      x-summandp-of-set-fac)
                  :use ((:instance x-find-fac-not-member (p 0))
                        (:instance x-set-fac-chain-is-list-skip-1 (s0 (x-find-fac-not 0 X S)))
                        (:instance x-set-fac-chain-is-list-skip-2 (s0 (x-find-fac-not 0 X S)))))))

(in-theory (disable x-add-arb-path))
