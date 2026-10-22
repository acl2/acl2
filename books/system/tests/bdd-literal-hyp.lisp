; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; ISSUE B10 (bdd.lisp bdd-clause1: a :bdd hint with :literal naming a
; hypothesis reports the whole goal proved when the *hypothesis* reduces to T)
; Example B10-a.  bdd-clause1 builds TERM = (if hyp t nil) for the hypothesis
; literal (not hyp), runs the BDD algorithm on it, and in the case (cst-tp cst)
; returns (mv 'hit nil ...) -- "no subgoals remain" -- exactly as for :conc and
; :all.  But a hypothesis that is identically true does not prove the clause;
; the literal should simply be dropped.  So any goal whose hypotheses contain a
; propositional tautology in Boolean variables is "proved".
; EXPECT-AFTER-FIX: BAD32 fails (the :bdd hint should just delete the
; hypothesis (if p t t)).

; Added by Matt K. to make this a book:
(in-package "ACL2")

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; Wrapper of must-fail added by Matt K.
(defthm bad32 (implies (and (booleanp p) (if p t t)) r)
; Matt K. note: p works above too, in place of (if p t t).
  :rule-classes nil
  :hints (("Goal'" :bdd (:vars nil :literal 1))))
)
; Matt K. mod -- No longer relevant since bad32 fails above:
#|
(defthm contradiction32 nil
  :rule-classes nil
  :hints (("Goal" :use ((:instance bad32 (p t) (r nil))))))
|#
