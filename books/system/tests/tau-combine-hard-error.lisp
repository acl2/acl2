; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-199 (symptom: in a goal, the unchecked bound next to a :pos-evg makes combine-tau signal a hard error, aborting a valid thm).
; Not self-checking. Expected while the issue is present: HARD ACL2 ERROR in COMBINE-TAU; SBCL and CCL.
;
; G168: further evidence for S-199 (other symptom: hard error on a valid goal).
; add-to-tau1's bound branch does not test a bound against an existing
; :pos-evg (S-199).  In a goal, the hypotheses x = :k and (big x), where a
; :tau-system rule says (big x) -> 1 <= x, give x the unsatisfiable tau
; "x = :K, BIG, 1 <= x over ACL2-NUMBERP", which is not recognized as a
; contradiction.  The IF in the conclusion then makes combine-tau
; (tau.lisp ~10457) disjoin that tau with the tau of 3; its consistency check
; finds the interval domain ACL2-NUMBERP missing from :pos-pairs and signals
; "HARD ACL2 ERROR in COMBINE-TAU", aborting the proof of a valid formula.
; (Under *hard-error-returns-nilp* the result would be NIL, the empty tau, so
; this is not a soundness problem by itself.)  The suggested S-199 fix
; (decide the bound on the :pos-evg) removes it.
; Control: with the IF replaced by x the proof just fails (no hard error);
; tau also misses the contradiction there, which is S-199's weakness in goals.
(in-package "ACL2")
(encapsulate (((big *) => *))
  (local (defun big (x) (and (rationalp x) (<= 1 x))))
  (defthm big-bool (booleanp (big x)) :rule-classes :tau-system)
  (defthm big-bound (implies (big x) (<= 1 x)) :rule-classes :tau-system))
(thm (implies (and (equal x :k) (big x)) (equal (if (consp y) x 3) 5)))
; control (fails without a hard error):
; (thm (implies (and (equal x :k) (big x)) (equal x 5)))
