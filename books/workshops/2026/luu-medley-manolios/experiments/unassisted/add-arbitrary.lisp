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

(include-book "add-dup")

;;; ------------------------------------------------------------------
;;; Picking the next step of the walk
;;; ------------------------------------------------------------------

;; The first element of Us different from cur (nil if none).
(defun pick-U (cur Us)
  (declare (xargs :guard t))
  (cond ((atom Us) nil)
        ((equal (car Us) cur) (pick-U cur (cdr Us)))
        (t (car Us))))

(defthm pick-U-member
  (implies (pick-U cur Us)
           (and (member-equal (pick-U cur Us) Us)
                (not (equal (pick-U cur Us) cur)))))

(defthm all-equal-to-when-no-pick
  (implies (and (not (pick-U cur Us)) (bv-listp L Us) (posp L))
           (all-equal-to cur Us))
  :hints (("Goal" :induct (bv-listp L Us))))

(defthm member-when-all-equal-to
  (implies (and (all-equal-to cur x) (consp x))
           (member-equal cur x)))

(defthm cdr-atom-when-all-equal-no-dups
  (implies (and (all-equal-to cur Us) (no-duplicatesp-equal Us) (consp Us))
           (not (consp (cdr Us))))
  :hints (("Goal" :in-theory (disable member-when-all-equal-to)
                  :use ((:instance member-when-all-equal-to (x (cdr Us)))))))

(defthm all-equal-no-dups-singleton
  (implies (and (all-equal-to cur Us) (no-duplicatesp-equal Us) (consp Us)
                (bv-listp L Us) (posp L))
           (equal (bv-sum L Us) cur))
  :hints (("Goal" :in-theory (disable bv-sum-when-all-equal-to member-when-all-equal-to
                                      cdr-atom-when-all-equal-no-dups)
                  :use (cdr-atom-when-all-equal-no-dups)
                  :expand ((bv-sum L Us) (bv-sum L (cdr Us)) (all-equal-to cur Us)))))

(defthm pick-U-exists
  (implies (and (consp Us) (no-duplicatesp-equal Us) (bv-listp L Us)
                (posp L) (bvp cur) (equal (len cur) L)
                (not (equal (bv+ cur (bv-sum L Us)) (bv-zero L))))
           (pick-U cur Us))
  :hints (("Goal" :in-theory (disable all-equal-no-dups-singleton all-equal-to-when-no-pick
                                      bv-sum-when-all-equal-to member-when-all-equal-to
                                      cdr-atom-when-all-equal-no-dups)
                  :use (all-equal-no-dups-singleton all-equal-to-when-no-pick))))

(in-theory (disable all-equal-no-dups-singleton all-equal-to-when-no-pick
                    bv-sum-when-all-equal-to member-when-all-equal-to
                    cdr-atom-when-all-equal-no-dups))

;; A summand of S whose p-factor is U.
(defun find-fac (p U S)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom S) nil)
        ((equal (fac p (car S)) U) (car S))
        (t (find-fac p U (cdr S)))))

(defthm find-fac-works
  (implies (member-equal U (facs p S))
           (and (member-equal (find-fac p U S) S)
                (equal (fac p (find-fac p U S)) U))))

(defthm facs-are-summand-factors
  (implies (and (member-equal U (facs p S)) (summand-listp L S) (posp3 p) (posp L))
           (and (bvp U) (equal (len U) L) (not (equal U (bv-zero L)))))
  :hints (("Goal" :induct (facs p S))
          ("Subgoal *1/2" :use ((:instance summandp-facts (s (car S)))
                                (:instance fac-nonzero-when-summandp (s (car S)))))))

(defthm member-subsetp-facs
  (implies (and (member-equal U Us) (subsetp-equal Us (facs p S)))
           (member-equal U (facs p S))))

;;; ------------------------------------------------------------------
;;; The walk
;;; ------------------------------------------------------------------

;; Current scheme: (list* sP sP S) with sP = (set-fac p cur s0).
;; Each round: Lemma 4.3 with s = sP and a summand u of S whose p-factor
;; is U, then delete the old pair.
(defun walk-path (p s0 cur Us S)
  (declare (xargs :guard t :verify-guards nil :measure (len Us)))
  (let ((U (pick-U cur Us)))
    (if (not U)
        nil
      (let* ((usum (find-fac p U S))
             (sP (set-fac p cur s0))
             (P2 (bv+ cur U)))
        (append (add-dup-path p sP usum)
                (cons (delete-pair-move sP)
                      (walk-path p s0 P2 (remove1-equal U Us) S)))))))

(defthm no-duplicatesp-of-remove1
  (implies (no-duplicatesp-equal x) (no-duplicatesp-equal (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm subsetp-of-remove1-equal-arg1
  (implies (subsetp-equal x y) (subsetp-equal (remove1-equal a x) y))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm summand-listp-of-list*-pair
  (equal (summand-listp L (list* a a S))
         (and (summandp L a) (summand-listp L S))))

(defthm walk-path-correct
  (implies (and (posp L) (summand-listp L S) (posp3 p)
                (summandp L s0)
                (bvp cur) (equal (len cur) L) (not (equal cur (bv-zero L)))
                (bv-listp L Us) (no-duplicatesp-equal Us)
                (subsetp-equal Us (facs p S))
                (bvp X) (equal (len X) L) (not (equal X (bv-zero L)))
                (equal (bv+ cur (bv-sum L Us)) X))
           (and (path-ok-p L (walk-path p s0 cur Us S)
                           (list* (set-fac p cur s0) (set-fac p cur s0) S))
                (perm (apply-path L (walk-path p s0 cur Us S)
                                  (list* (set-fac p cur s0) (set-fac p cur s0) S))
                      (list* (set-fac p X s0) (set-fac p X s0) S))))
  :hints (("Goal" :induct (walk-path p s0 cur Us S)
                  :in-theory (disable pick-U-exists find-fac-works
                                      facs-are-summand-factors summandp-facts-rw
                                      perm-of-cons-arg1 perm-of-cons-arg2
                                      perm-rotate-3 perm-rotate-4 perm-rotate-3-append
                                      perm-rotate-4-append perm-step4-shape
                                      perm-append-list-1 perm-append-list-2
                                      perm-cons-remove1-when-member
                                      set-fac-of-set-fac-other-commute))
          ("Subgoal *1/2" :use (pick-U-exists
                                (:instance find-fac-works (U (pick-U cur Us)))
                                (:instance facs-are-summand-factors (U (pick-U cur Us)))
                                (:instance summandp-of-set-fac (s s0) (v cur))
                                (:instance summandp-of-set-fac (s s0) (v (bv+ cur (pick-U cur Us))))
                                (:instance bv-sum-of-remove1 (a (pick-U cur Us)) (x Us))
                                (:instance bv+-equal-zero (x cur) (y (pick-U cur Us)))))
          ("Subgoal *1/1" :use (pick-U-exists))))

;;; ------------------------------------------------------------------
;;; The multiset of p-factors summing to X (from the span lemma)
;;; ------------------------------------------------------------------

;; X with the coordinates below k cleared.
(defun bv-mask-from (X k)
  (declare (xargs :guard (and (bvp X) (integerp k))))
  (if (atom X) nil (cons (if (<= (ifix k) 0) (car X) 0) (bv-mask-from (cdr X) (1- (ifix k))))))

(defthm bvp-of-bv-mask-from (implies (bvp X) (bvp (bv-mask-from X k))))
(defthm len-of-bv-mask-from (equal (len (bv-mask-from X k)) (len X)))
(defthm bv-mask-from-nonpos
  (implies (and (bvp X) (integerp k) (<= k 0)) (equal (bv-mask-from X k) X)))
(defthm bv-mask-from-0 (implies (bvp X) (equal (bv-mask-from X 0) X)))
(defthm bv-mask-from-end
  (implies (and (bvp X) (integerp k) (<= (len X) k))
           (equal (bv-mask-from X k) (bv-zero (len X)))))
(defun ind-xik (X i k)
  (if (atom X) (list X i k) (ind-xik (cdr X) (1- i) (1- k))))

(defthm nth-of-bv-mask-from
  (implies (and (bvp X) (natp i) (< i (len X)) (integerp k))
           (equal (nth i (bv-mask-from X k)) (if (< i k) 0 (nth i X))))
  :hints (("Goal" :induct (ind-xik X i k))))

(defthm bv-mask-from-step
  (implies (and (bvp X) (natp k) (< k (len X)))
           (equal (bv+ (if (equal (nth k X) 1) (unit (len X) k) (bv-zero (len X)))
                       (bv-mask-from X (1+ k)))
                  (bv-mask-from X k)))
  :hints (("Goal" :use ((:instance bv-extensionality
                                   (x (bv+ (if (equal (nth k X) 1) (unit (len X) k) (bv-zero (len X)))
                                           (bv-mask-from X (1+ k))))
                                   (y (bv-mask-from X k)))
                        (:instance bv-diff-index-witness
                                   (x (bv+ (if (equal (nth k X) 1) (unit (len X) k) (bv-zero (len X)))
                                           (bv-mask-from X (1+ k))))
                                   (y (bv-mask-from X k))))
                  :in-theory (disable bv-diff-index-witness))))

;; The p-factors selected by the span lemma for every unit in the support
;; of X (coordinates k, k+1, ..., n^2 - 1).
(defun unit-facs (p n S X k)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix (- (sq n) k))))
  (if (or (not (natp n)) (not (natp k)) (>= k (sq n)))
      nil
    (append (if (equal (nth k X) 1)
                (sel-list p S (span-b p n (floor k n) (mod k n))
                          (span-c p n (floor k n) (mod k n)))
              nil)
            (unit-facs p n S X (1+ k)))))

(defthm true-listp-of-sel-list (true-listp (sel-list p S b c)))

(defthm bv-listp-of-unit-facs
  (implies (and (triple-listp (sq n) S) (posp3 p))
           (bv-listp (sq n) (unit-facs p n S X k))))

(defthm subsetp-of-unit-facs
  (subsetp-equal (unit-facs p n S X k) (facs p S)))

(defthm midx-of-floor-mod
  (implies (and (natp k) (posp n))
           (equal (midx n (floor k n) (mod k n)) k))
  :hints (("Goal" :in-theory (enable midx) :use floor-mod-decompose)))

(defthm unit-facs-step
  (implies (and (schemep n S) (posp3 p) (bvp X) (equal (len X) (sq n))
                (natp k) (< k (sq n)))
           (equal (bv-sum (sq n) (unit-facs p n S X k))
                  (bv+ (if (equal (nth k X) 1) (unit (sq n) k) (bv-zero (sq n)))
                       (bv-sum (sq n) (unit-facs p n S X (1+ k))))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (sel-sum) (span-lemma bv-listp-of-unit-facs bv-listp-of-sel-list))
                  :expand ((unit-facs p n S X k))
                  :use ((:instance span-lemma (x (floor k n)) (y (mod k n)))
                        (:instance floor-bound (a k))
                        (:instance mod-bound (a k))
                        (:instance bv-listp-of-unit-facs (k (1+ k)))
                        (:instance bv-listp-of-sel-list (L (sq n))
                                   (b (span-b p n (floor k n) (mod k n)))
                                   (c (span-c p n (floor k n) (mod k n))))
                        (:instance bv-sum-of-append (L (sq n))
                                   (x (sel-list p S (span-b p n (floor k n) (mod k n))
                                                (span-c p n (floor k n) (mod k n))))
                                   (y (unit-facs p n S X (1+ k))))))))

(defthm bv-sum-of-unit-facs
  (implies (and (schemep n S) (posp3 p) (bvp X) (equal (len X) (sq n)) (natp k))
           (equal (bv-sum (sq n) (unit-facs p n S X k))
                  (bv-mask-from X k)))
  :hints (("Goal" :induct (unit-facs p n S X k)
                  :in-theory (disable unit-facs-step bv-mask-from-step (:definition unit-facs)))
          ("Subgoal *1/2" :use (unit-facs-step
                                (:instance bv-mask-from-step)))
          ("Subgoal *1/1" :expand ((unit-facs p n S X k)))))

;; The set of factors to walk through: sum = A0 + X, no duplicates.
(defun arb-Us (p n S s0 X)
  (declare (xargs :guard t :verify-guards nil))
  (cancel-dups (cons (fac p s0) (unit-facs p n S X 0))))

(defthm subsetp-trans-helper
  (implies (and (subsetp-equal x y) (subsetp-equal y z))
           (subsetp-equal x z)))

(defthm arb-Us-bv-listp
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S))
           (bv-listp (sq n) (arb-Us p n S s0 X)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (enable arb-Us)
                  :use ((:instance summandp-facts (L (sq n)) (s s0))))))

(defthm arb-Us-no-dups
  (no-duplicatesp-equal (arb-Us p n S s0 X))
  :hints (("Goal" :in-theory (enable arb-Us))))

(defthm arb-Us-subsetp
  (implies (member-equal s0 S)
           (subsetp-equal (arb-Us p n S s0 X) (facs p S)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (arb-Us) (subsetp-trans-helper subsetp-of-cancel-dups))
                  :use ((:instance subsetp-of-cancel-dups
                                   (lst (cons (fac p s0) (unit-facs p n S X 0))))
                        (:instance subsetp-trans-helper
                                   (x (arb-Us p n S s0 X))
                                   (y (cons (fac p s0) (unit-facs p n S X 0)))
                                   (z (facs p S)))))))

(defthm arb-Us-sum
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n)))
           (equal (bv-sum (sq n) (arb-Us p n S s0 X))
                  (bv+ (fac p s0) X)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (arb-Us) (bv-sum-of-cancel-dups bv-sum-of-unit-facs))
                  :use ((:instance bv-sum-of-cancel-dups (L (sq n))
                                   (lst (cons (fac p s0) (unit-facs p n S X 0))))
                        (:instance bv-sum-of-unit-facs (k 0))
                        (:instance summandp-facts (L (sq n)) (s s0))))))

(defthm arb-Us-facts
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n)))
           (and (bv-listp (sq n) (arb-Us p n S s0 X))
                (no-duplicatesp-equal (arb-Us p n S s0 X))
                (subsetp-equal (arb-Us p n S s0 X) (facs p S))
                (equal (bv-sum (sq n) (arb-Us p n S s0 X))
                       (bv+ (fac p s0) X))))
  :rule-classes nil
  :hints (("Goal" :in-theory nil
                  :use (arb-Us-bv-listp arb-Us-no-dups arb-Us-subsetp arb-Us-sum))))

(in-theory (disable arb-Us))

;;; ------------------------------------------------------------------
;;; Changing one factor of a summand to an arbitrary nonzero X
;;; ------------------------------------------------------------------

(defun add-arb-p-path (p n S s0 X)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((A0 (fac p s0))
         (Us (arb-Us p n S s0 X))
         (U0 (pick-U A0 Us))
         (usum0 (find-fac p U0 S)))
    (append (add-dup-path p s0 usum0)
            (walk-path p s0 (bv+ A0 U0) (remove1-equal U0 Us) S))))

(defthm bv-sum-nil (equal (bv-sum L nil) (bv-zero L)))

(defthm not-equal-when-fac-differs
  (implies (not (equal (fac p u) (fac p s)))
           (not (equal u s)))
  :rule-classes nil)

(defthm arb-Us-consp
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n))
                (not (equal (fac p s0) X)))
           (consp (arb-Us p n S s0 X)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable arb-Us-sum arb-Us-bv-listp)
                  :use (arb-Us-sum arb-Us-bv-listp
                        (:instance summandp-facts (L (sq n)) (s s0))
                        (:instance bv+-equal-zero (x (fac p s0)) (y X))))))

;; Facts about the first step U0 = (pick-U A0 Us).
(defthm arb-pick-facts
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n))))
                (not (equal (fac p s0) X)))
           (let ((U0 (pick-U (fac p s0) (arb-Us p n S s0 X))))
             (and U0
                  (member-equal U0 (arb-Us p n S s0 X))
                  (not (equal U0 (fac p s0)))
                  (member-equal U0 (facs p S)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable pick-U-exists arb-Us-sum arb-Us-bv-listp arb-Us-no-dups
                                      arb-Us-subsetp arb-Us-consp pick-U-member)
                  :use (arb-Us-sum arb-Us-bv-listp arb-Us-no-dups arb-Us-subsetp arb-Us-consp
                        (:instance summandp-facts (L (sq n)) (s s0))
                        (:instance pick-U-exists (L (sq n)) (cur (fac p s0)) (Us (arb-Us p n S s0 X)))
                        (:instance pick-U-member (cur (fac p s0)) (Us (arb-Us p n S s0 X)))
                        (:instance bv+-self-in-middle (x (fac p s0)) (y X))))))

(defthm arb-U0-facts
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n))))
                (not (equal (fac p s0) X)))
           (let ((U0 (pick-U (fac p s0) (arb-Us p n S s0 X))))
             (and (bvp U0) (equal (len U0) (sq n)) (not (equal U0 (bv-zero (sq n))))
                  (not (equal (bv+ (fac p s0) U0) (bv-zero (sq n)))))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable arb-pick-facts facs-are-summand-factors)
                  :use (arb-pick-facts
                        (:instance summandp-facts (L (sq n)) (s s0))
                        (:instance facs-are-summand-factors (L (sq n))
                                   (U (pick-U (fac p s0) (arb-Us p n S s0 X))))
                        (:instance bv+-equal-zero (x (fac p s0))
                                   (y (pick-U (fac p s0) (arb-Us p n S s0 X))))))))

(defthm arb-usum0-summand-facts
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n))))
                (not (equal (fac p s0) X)))
           (let* ((U0 (pick-U (fac p s0) (arb-Us p n S s0 X)))
                  (usum0 (find-fac p U0 S)))
             (and (member-equal usum0 S)
                  (equal (fac p usum0) U0)
                  (member-equal usum0 (remove1-equal s0 S)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable arb-pick-facts find-fac-works)
                  :use (arb-pick-facts
                        (:instance find-fac-works (U (pick-U (fac p s0) (arb-Us p n S s0 X))))
                        (:instance not-equal-when-fac-differs
                                   (u (find-fac p (pick-U (fac p s0) (arb-Us p n S s0 X)) S))
                                   (s s0))
                        (:instance member-remove1-when-different
                                   (u (find-fac p (pick-U (fac p s0) (arb-Us p n S s0 X)) S))
                                   (s1 s0) (S S))))))

;; The first step: Lemma 4.3 on s0 and usum0.
(defthm arb-first-step
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n))))
                (not (equal (fac p s0) X)))
           (let* ((U0 (pick-U (fac p s0) (arb-Us p n S s0 X)))
                  (usum0 (find-fac p U0 S))
                  (s1 (set-fac p (bv+ (fac p s0) U0) s0)))
             (and (path-ok-p (sq n) (add-dup-path p s0 usum0) S)
                  (perm (apply-path (sq n) (add-dup-path p s0 usum0) S)
                        (list* s1 s1 S)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable arb-pick-facts arb-U0-facts arb-usum0-summand-facts add-dup-lemma)
                  :use (arb-U0-facts arb-usum0-summand-facts
                        (:instance add-dup-lemma (L (sq n)) (sch S) (s s0)
                                   (u (find-fac p (pick-U (fac p s0) (arb-Us p n S s0 X)) S)))))))

;; The walk: from (list* s1 s1 S) to (list* sX sX S).
(defthm arb-walk-step
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n))))
                (not (equal (fac p s0) X)))
           (let* ((U0 (pick-U (fac p s0) (arb-Us p n S s0 X)))
                  (cur (bv+ (fac p s0) U0))
                  (Us1 (remove1-equal U0 (arb-Us p n S s0 X)))
                  (s1 (set-fac p cur s0)))
             (and (path-ok-p (sq n) (walk-path p s0 cur Us1 S) (list* s1 s1 S))
                  (perm (apply-path (sq n) (walk-path p s0 cur Us1 S) (list* s1 s1 S))
                        (list* (set-fac p X s0) (set-fac p X s0) S)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable arb-pick-facts arb-U0-facts walk-path-correct
                                      arb-Us-sum arb-Us-bv-listp arb-Us-no-dups arb-Us-subsetp
                                      summandp-facts-rw)
                  :use (arb-pick-facts arb-U0-facts
                        arb-Us-sum arb-Us-bv-listp arb-Us-no-dups arb-Us-subsetp
                        (:instance summandp-facts (L (sq n)) (s s0))
                        (:instance bv-sum-of-remove1 (L (sq n))
                                   (a (pick-U (fac p s0) (arb-Us p n S s0 X)))
                                   (x (arb-Us p n S s0 X)))
                        (:instance walk-path-correct (L (sq n))
                                   (cur (bv+ (fac p s0) (pick-U (fac p s0) (arb-Us p n S s0 X))))
                                   (Us (remove1-equal (pick-U (fac p s0) (arb-Us p n S s0 X))
                                                      (arb-Us p n S s0 X))))))))

(defthm add-arb-p-lemma
  (implies (and (schemep n S) (posp3 p) (member-equal s0 S)
                (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n))))
                (not (equal (fac p s0) X)))
           (and (path-ok-p (sq n) (add-arb-p-path p n S s0 X) S)
                (perm (apply-path (sq n) (add-arb-p-path p n S s0 X) S)
                      (list* (set-fac p X s0) (set-fac p X s0) S))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable arb-first-step arb-walk-step
                                      perm-of-cons-arg1 perm-of-cons-arg2
                                      perm-rotate-3 perm-rotate-4 perm-rotate-3-append
                                      perm-rotate-4-append perm-step4-shape
                                      perm-append-list-1 perm-append-list-2
                                      perm-cons-remove1-when-member
                                      set-fac-of-set-fac-other-commute)
                  :use (arb-first-step arb-walk-step))))

(in-theory (disable add-arb-p-path))

;;; ------------------------------------------------------------------
;;; Lemma 4.4: adding two copies of X (x) Y (x) Z
;;; ------------------------------------------------------------------

(defun nz-matp (n X)
  (declare (xargs :guard (natp n)))
  (and (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n))))))

(defthm nz-matp-facts
  (implies (nz-matp n X)
           (and (bvp X) (equal (len X) (sq n)) (not (equal X (bv-zero (sq n))))))
  :rule-classes nil)

(defthm summandp-list-is-nz-matp
  (implies (posp n)
           (equal (summandp (sq n) (list X Y Z))
                  (and (nz-matp n X) (nz-matp n Y) (nz-matp n Z))))
  :hints (("Goal" :in-theory (enable summandp))))

(defthm summandp-of-set-fac-nz
  (implies (and (posp n) (summandp (sq n) s) (posp3 p) (nz-matp n v))
           (summandp (sq n) (set-fac p v s)))
  :hints (("Goal" :in-theory (disable summandp-of-set-fac)
                  :use ((:instance summandp-of-set-fac (L (sq n)))))))

(defthm nz-matp-bvp (implies (nz-matp n X) (bvp X)))
(defthm nz-matp-len (implies (nz-matp n X) (equal (len X) (sq n))))
(defthm nz-matp-nonzero (implies (nz-matp n X) (not (equal X (bv-zero (sq n))))))

(in-theory (disable nz-matp))

(defthm schemep-of-list*-pair
  (implies (and (schemep n S) (summandp (sq n) a))
           (schemep n (list* a a S)))
  :hints (("Goal" :in-theory (enable rank1)
                  :use ((:instance summandp-facts (L (sq n)) (s a))))))

;; Position 0, then position 1, then position 2, deleting the previous
;; pair after each of the last two stages.
(defun add-arb-path (n S X Y Z)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s0 (find-fac-not 0 X S))
         (pA (add-arb-p-path 0 n S s0 X))
         (s1 (set-fac 0 X s0))
         (sch1 (list* s1 s1 S))
         (pB (if (equal (fac 1 s1) Y)
                 nil
               (append (add-arb-p-path 1 n sch1 s1 Y) (list (delete-pair-move s1)))))
         (s2 (set-fac 1 Y s1))
         (sch2 (list* s2 s2 S))
         (pC (if (equal (fac 2 s2) Z)
                 nil
               (append (add-arb-p-path 2 n sch2 s2 Z) (list (delete-pair-move s2))))))
    (append pA (append pB pC))))

(defthm set-fac-chain-is-list
  (implies (and (true-listp s0) (equal (len s0) 3))
           (equal (set-fac 2 Z (set-fac 1 Y (set-fac 0 X s0))) (list X Y Z)))
  :hints (("Goal" :in-theory (enable set-fac))))

(defthm set-fac-chain-is-list-skip-1
  (implies (and (true-listp s0) (equal (len s0) 3))
           (equal (set-fac 2 Z (set-fac 0 X s0)) (list X (fac 1 s0) Z)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable set-fac fac))))

(defthm set-fac-chain-is-list-skip-2
  (implies (and (true-listp s0) (equal (len s0) 3))
           (equal (set-fac 1 Y (set-fac 0 X s0)) (list X Y (fac 2 s0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable set-fac fac))))

(encapsulate ()
  (local (in-theory (disable add-arb-p-lemma summandp-facts-rw find-fac-not-member
                             perm-of-cons-arg1 perm-of-cons-arg2
                             perm-rotate-3 perm-rotate-4 perm-rotate-3-append
                             perm-rotate-4-append perm-step4-shape
                             perm-append-list-1 perm-append-list-2
                             perm-cons-remove1-when-member
                             set-fac-of-set-fac-other-commute
                             apply-delete-pair-move delete-pair-move-ok
                             schemep-of-list*-pair)))

  ;; Stage A: S --> S (+) {s1, s1}, s1 = X (x) B0 (x) C0.
  (defthm add-arb-stage-A
    (implies (and (schemep n S) (<= 2 n) (nz-matp n X))
             (let* ((s0 (find-fac-not 0 X S))
                    (s1 (set-fac 0 X s0)))
               (and (path-ok-p (sq n) (add-arb-p-path 0 n S s0 X) S)
                    (perm (apply-path (sq n) (add-arb-p-path 0 n S s0 X) S)
                          (list* s1 s1 S)))))
    :hints (("Goal" :do-not-induct t
                    :use ((:instance nz-matp-facts)
                          (:instance find-fac-not-member (p 0))
                          (:instance add-arb-p-lemma (p 0) (s0 (find-fac-not 0 X S)))))))

  ;; Generic stage: from (list* sm sm S) with (fac p sm) /= V to (list* sm' sm' S)
  ;; where sm' = (set-fac p V sm), via add-arb-p-path and a pair deletion.
  ;; Stated in the form the final proof sees after splitting the path.
  (defthm add-arb-stage-generic
    (implies (and (schemep n S) (posp3 p) (summandp (sq n) sm)
                  (nz-matp n V)
                  (not (equal (fac p sm) V)))
             (let* ((sch1 (list* sm sm S))
                    (mid (apply-path (sq n) (add-arb-p-path p n sch1 sm V) sch1)))
               (and (path-ok-p (sq n) (add-arb-p-path p n sch1 sm V) sch1)
                    (move-ok-p (delete-pair-move sm) mid)
                    (perm (apply-move (sq n) (delete-pair-move sm) mid)
                          (list* (set-fac p V sm) (set-fac p V sm) S)))))
    :hints (("Goal" :do-not-induct t
                    :in-theory (enable add-arb-p-lemma summandp-facts-rw)
                    :use ((:instance schemep-of-list*-pair (a sm))
                          (:instance summandp-facts (L (sq n)) (s sm))
                          (:instance summandp-of-set-fac (L (sq n)) (s sm) (v V))
                          (:instance apply-delete-pair-move (L (sq n)) (s1 sm)
                                     (S (list* (set-fac p V sm) (set-fac p V sm) sm sm S)))
                          (:instance delete-pair-move-ok (s1 sm)
                                     (S (list* (set-fac p V sm) (set-fac p V sm) sm sm S))))))))

(defthm add-arb-lemma
  (implies (and (schemep n S) (<= 2 n)
                (summandp (sq n) (list X Y Z)))
           (and (path-ok-p (sq n) (add-arb-path n S X Y Z) S)
                (perm (apply-path (sq n) (add-arb-path n S X Y Z) S)
                      (list* (list X Y Z) (list X Y Z) S))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable perm-of-cons-arg1 perm-of-cons-arg2
                                      perm-rotate-3 perm-rotate-4 perm-rotate-3-append
                                      perm-rotate-4-append perm-step4-shape
                                      perm-append-list-1 perm-append-list-2
                                      perm-cons-remove1-when-member
                                      set-fac-of-set-fac-other-commute
                                      apply-delete-pair-move delete-pair-move-ok
                                      schemep-of-list*-pair add-arb-p-lemma
                                      summandp-of-set-fac)
                  :use ((:instance find-fac-not-member (p 0))
                        (:instance set-fac-chain-is-list-skip-1 (s0 (find-fac-not 0 X S)))
                        (:instance set-fac-chain-is-list-skip-2 (s0 (find-fac-not 0 X S)))))))

(in-theory (disable add-arb-path))
