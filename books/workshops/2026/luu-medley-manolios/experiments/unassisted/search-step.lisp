; search-step.lisp -- Appendix C of the paper: one step of a walk of the
; GPU search, and the warp-level matching primitive of Section 5.1.
;
; We do not model registers, lanes, slots, or random number generation;
; we model what a step does to the scheme a warp holds and prove that
; every step keeps the scheme a scheme (a decomposition of M^(n) into
; nonzero rank-one tensors), which is the invariant the search relies
; on, and that a Reduce step strictly lowers the rank.
;
; __match_any_sync(mask, value): for a calling lane t, bit i of the
; result is 1 iff lane i participates and holds the same value as lane t.

(in-package "ACL2")

(include-book "genflip")

;;; ------------------------------------------------------------------
;;; __match_any_sync
;;; ------------------------------------------------------------------

;; vals: the value held by each lane (a list indexed by lane);
;; active: a bit list (the participation mask); t-lane: the caller.
;; Result: a bit list (the returned bitmask), lane by lane.
(defun match-any-sync (active vals t-val)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom vals) nil)
        (t (cons (if (and (eql (car active) 1) (equal (car vals) t-val)) 1 0)
                 (match-any-sync (cdr active) (cdr vals) t-val)))))

;; Specification (the displayed equivalence of Section 5.1):
;;   (match_any_sync(x_t))_i = 1  <->  participating lane i has x_i = x_t.
(defun ind-xka (x k a) (if (atom x) (list x k a) (ind-xka (cdr x) (1- k) (cdr a))))

(defthm match-any-sync-spec-general
  (implies (and (natp i) (< i (len vals)))
           (iff (equal (nth i (match-any-sync active vals tv)) 1)
                (and (equal (nth i active) 1)
                     (equal (nth i vals) tv))))
  :hints (("Goal" :induct (ind-xka vals i active))))

(defthm match-any-sync-spec
  (implies (and (natp i) (< i (len vals)))
           (iff (equal (nth i (match-any-sync active vals (nth t-lane vals))) 1)
                (and (equal (nth i active) 1)
                     (equal (nth i vals) (nth t-lane vals)))))
  :hints (("Goal" :use ((:instance match-any-sync-spec-general (tv (nth t-lane vals)))))))

;; The caller's own bit is set whenever it participates.
(defthm match-any-sync-self
  (implies (and (natp t-lane) (< t-lane (len vals)) (equal (nth t-lane active) 1))
           (equal (nth t-lane (match-any-sync active vals (nth t-lane vals))) 1))
  :hints (("Goal" :use ((:instance match-any-sync-spec (i t-lane))))))

;; Ones in the mask are exactly flip opportunities: two lanes whose
;; summands agree at position p (Definition 2.3's precondition).
(defun facs-at (p S)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom S) nil (cons (fac p (car S)) (facs-at p (cdr S)))))

(defthm nth-of-facs-at
  (implies (and (natp i) (< i (len S)))
           (equal (nth i (facs-at p S)) (fac p (nth i S))))
  :hints (("Goal" :induct (ind-xk S i))))

(defthm len-of-facs-at (equal (len (facs-at p S)) (len S)))

(defthm match-any-sync-gives-flip-precondition
  (implies (and (natp i) (natp j) (< i (len S)) (< j (len S))
                (equal (nth i (match-any-sync active (facs-at p S) (nth j (facs-at p S)))) 1))
           (equal (fac p (nth i S)) (fac p (nth j S))))
  :hints (("Goal" :use ((:instance match-any-sync-spec (vals (facs-at p S)) (t-lane j))))))

;;; ------------------------------------------------------------------
;;; One step of a walk (Algorithm 1)
;;; ------------------------------------------------------------------

;; A candidate is one of
;;   (:flip p s u)      -- s and u share the factor at position p
;;   (:plus p piv tgt)  -- attempted only when no flip candidate exists
;;   (:reduce flags G rest) -- a group G (sharing the A factor) whose
;;                             flagged B factors xor to zero; the scheme
;;                             is (append G rest)
;;   nil                -- no transition (a plus was skipped)
;; The random choices of the kernel are abstracted into the candidate.

(defun step-kind (c) (declare (xargs :guard t)) (if (consp c) (car c) nil))

(defun apply-step (n S c)
  (declare (xargs :guard t :verify-guards nil))
  (case (step-kind c)
    (:flip (apply-move (sq n) (flip-move (second c) (third c) (fourth c)) S))
    (:plus (apply-move (sq n) (plus-move (second c) (third c) (fourth c)) S))
    (:reduce (append (gen-flip (sq n) (second c) (third c)) (fourth c)))
    (t S)))

;; When is a candidate valid for the current scheme S?
(defun step-ok-p (n S c)
  (declare (xargs :guard t :verify-guards nil))
  (case (step-kind c)
    (:flip (move-ok-p (flip-move (second c) (third c) (fourth c)) S))
    (:plus (move-ok-p (plus-move (second c) (third c) (fourth c)) S))
    (:reduce (let ((flags (second c)) (G (third c)) (rest (fourth c)))
               (and (equal S (append G rest))
                    (summand-listp (sq n) G)
                    (consp G)
                    (shared-A-p (fac 0 (car G)) G)
                    (some-flag flags G)
                    (equal (flagged-B-sum (sq n) flags G) (bv-zero (sq n))))))
    (t t)))

;; Invariant: a step maps schemes to schemes.
(defthm apply-step-preserves-schemep
  (implies (and (schemep n S) (step-ok-p n S c))
           (schemep n (apply-step n S c)))
  :hints (("Goal" :in-theory (disable gen-flip-in-scheme apply-move-preserves-schemep)
                  :use ((:instance apply-move-preserves-schemep
                                   (m (flip-move (second c) (third c) (fourth c))))
                        (:instance apply-move-preserves-schemep
                                   (m (plus-move (second c) (third c) (fourth c))))
                        (:instance gen-flip-in-scheme
                                   (G (third c)) (rest (fourth c)) (flags (second c))
                                   (A (fac 0 (car (third c)))))
                        (:instance summandp-facts (L (sq n)) (s (car (third c))))))))

;; A Reduce step strictly lowers the rank (the number of summands).
(defthm reduce-step-lowers-rank
  (implies (and (schemep n S) (step-ok-p n S c) (equal (step-kind c) :reduce))
           (< (len (apply-step n S c)) (len S)))
  :hints (("Goal" :in-theory (disable gen-flip-in-scheme)
                  :use ((:instance gen-flip-in-scheme
                                   (G (third c)) (rest (fourth c)) (flags (second c))
                                   (A (fac 0 (car (third c)))))
                        (:instance summandp-facts (L (sq n)) (s (car (third c))))))))

;; A whole walk: a sequence of candidates, each valid for the scheme at
;; that point, keeps the invariant; a snapshot taken on improvement is
;; therefore always a scheme.
(defun apply-steps (n S cs)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count cs)))
  (if (atom cs) S (apply-steps n (apply-step n S (car cs)) (cdr cs))))

(defun steps-ok-p (n S cs)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count cs)))
  (if (atom cs) t
    (and (step-ok-p n S (car cs))
         (steps-ok-p n (apply-step n S (car cs)) (cdr cs)))))

(defthm apply-steps-preserves-schemep
  (implies (and (schemep n S) (steps-ok-p n S cs))
           (schemep n (apply-steps n S cs)))
  :hints (("Goal" :induct (apply-steps n S cs)
                  :in-theory (disable apply-step step-ok-p schemep))))

;; Every scheme reached by the search is reachable from the start by
;; ordinary flips and pluses alone (Section 5.2, via Theorem 4.1).
(defthm search-result-reachable-by-flips-and-pluses
  (implies (and (<= 2 n) (schemep n S) (steps-ok-p n S cs))
           (let ((S2 (apply-steps n S cs)))
             (and (path-ok-p (sq n) (connect-path n S S2) S)
                  (perm (apply-path (sq n) (connect-path n S S2) S) S2))))
  :hints (("Goal" :in-theory (disable apply-steps steps-ok-p schemep
                                      flip-graph-strongly-connected apply-steps-preserves-schemep)
                  :use (apply-steps-preserves-schemep
                        (:instance flip-graph-strongly-connected (S2 (apply-steps n S cs)))))))
