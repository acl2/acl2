; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Finding 31: the proof-builder's :S primitive, in its "Contradiction in the
; hypotheses" branch, decides whether the goal may be dropped from an INNER
; derivation but records the tag tree of the OUTER one, so a FORCED hypothesis
; used to reach the contradiction never becomes a forced subgoal.
;
; proof-builder-b.lisp:3585-3618.  The outer call
;   (hyps-type-alist-and-pot-lst assumptions ...)   ; hyps + IF-governors
; supplies TTREE; the inner call
;   (mv-let (flg hyps-type-alist ttree) (hyps-type-alist hyps pc-ens w state)
;     (declare (ignore hyps-type-alist ttree)) flg)  ; hyps ALONE
; can be what licenses dropping the goal -- and its TTREE is explicitly ignored,
; while :LOCAL-TAG-TREE and (TAGGED-OBJECTS 'ASSUMPTION ttree) both use the
; OUTER ttree.  PC-SINGLE-STEP-PRIMITIVE's
; RESUME-SUSPENDED-ASSUMPTION-REWRITING / PC-PROCESS-ASSUMPTIONS
; (proof-builder-a.lisp:828-1005) therefore never see the forced assumption.
;
; This is note-8-7's proof-builder forcing bug in a spot the note-8-7 fix does
; not reach (the note-8-7 example itself still fails correctly).  The stale
; comment on HYPS-TYPE-ALIST (other-events.lisp:27994-27996) -- "the force-flg
; arg to type-alist-clause is nil here, so we shouldn't wind up with any
; assumptions in the returned tag-tree" -- is false, since the call at
; :27999-28004 passes (OK-TO-FORCE-ENS ENS), and is the likely origin.
;
; Trigger: dive so the IF-governors give a force-FREE contradiction with the
; hyps (clean outer ttree) while the hyps alone are contradictory only via a
; forced, false hypothesis.  Without the (:DIVE 2) the outer ttree is the
; deciding one (line 3593, CURRENT-ADDR null) and the forced goal IS created.
; FIX: hoist the inner call so its ttree is available at lines 3608/3617 and use
; it.  The linear branch needs the same treatment, since
; HYPS-TYPE-ALIST-AND-POT-LST (proof-builder-b.lisp:3462) also forces via
; SETUP-SIMPLIFY-CLAUSE-POT-LST.
; [Added by Matt K.: The sentence immediately above looks wrong.]
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
; Matt K. mod: Moved the must-fail wrapper from here, which is around the outer
; encapsulate, to the events that actually fail.
(encapsulate ()
  (encapsulate
    (((sfgg *) => *) ((sfbar *) => *) ((sfpp *) => *))
    (local (defun sfgg (x) x))
    (local (defun sfbar (x) x))
    (local (defun sfpp (x) (declare (ignore x)) nil))
    (defthm sf-fc-rule
      (implies (and (sfgg x) (force (sfpp x)))
               (sfbar x))
      :rule-classes ((:forward-chaining :trigger-terms ((sfgg x))))))
  (must-fail ; This must-fail wrapper was added by Matt Kaufmann:
; False: sfgg := (lambda (x) t), sfbar := sfpp := (lambda (x) nil).
  (defthm sf-bogus
    (implies (and (sfgg x) (not (sfbar x)))
             (if (sfbar x) (sfgg x) nil))
    :rule-classes nil
    :instructions (:promote (:dive 2) :s))
  )
  (must-fail ; This must-fail wrapper was added by Matt Kaufmann:
  (defthm sf-nil nil
    :rule-classes nil
    :hints (("Goal" :use ((:functional-instance
                           sf-bogus
                           (sfgg (lambda (x) t))
                           (sfbar (lambda (x) nil))
                           (sfpp (lambda (x) nil)))))))
  )
  )
