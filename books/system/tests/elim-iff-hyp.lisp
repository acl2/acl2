; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

(in-package "ACL2")

; SOUNDNESS BUG: a non-EQUAL (:equiv = IFF) destructor-elimination (:ELIM) rule
; is accepted, and when applied, apply-instantiated-elim-rule (other-processes.lisp)
; substitutes the crucial variable (equal-substitution, subst-var-lst) into the
; rule's HYPOTHESES.  The soundness guard every-occurrence-equiv-hittablep-in-clausep
; (simplify.lisp, called from select-instantiated-elim-rule) only vets occurrences
; of the crucial variable in the GOAL clause -- it never checks the elim rule's
; hypotheses.  So a hyp containing the crucial variable in a non-IFF-hittable
; (e.g. EQUAL) position gets an unsound iff-substitution, letting a false goal be
; "proved".

(defun h (x) x)
(defun tobool (x) (if x t x))
(in-theory (disable h (:definition h)))

; Helper so the "pathological" elim subgoal (h x)=3 => x=3 can close while h is
; disabled.  (Sound: h is the identity.)
(defthm h-inv
  (implies (equal (h x) 3) (equal x 3))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable h))))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

; A genuine theorem: (iff (tobool (h x)) x) holds for all x, so the implication
; below is a theorem regardless of the hypothesis.  But as an :ELIM rule with
; :equiv = IFF and a hypothesis (equal x 3) that mentions the crucial variable x
; in an EQUAL position, it is exploitable.
(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm h-elim
  (implies (equal x 3) (iff (tobool (h x)) x))
  :rule-classes :elim)
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
; FALSE: (not (equal (h x) 3)) is false at x=3, yet ACL2 proves it via the bogus
; :ELIM rule (the hyp (equal x 3) becomes (equal (tobool d) 3), always false, so
; the "normal" elim clause collapses to T; the pathological clause closes via h-inv).
(defthm bad
  (not (equal (h x) 3))
  :rule-classes nil)
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved
  nil
  :hints (("Goal" :use ((:instance bad (x 3)))))
  :rule-classes nil)
)
