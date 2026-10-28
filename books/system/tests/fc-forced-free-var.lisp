; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  See also fc-unbound-free-capture.lisp.

(in-package "ACL2") ; Added by Matt K. to make a certifiable book

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

; B8: forward chaining, forced hypothesis with a free variable
; (simplify.lisp, advance-fc-activation1).  When a FORCEd/CASE-SPLIT hyp has
; free variables and no match is found, the hyp is forced with the free vars
; replaced by UNBOUND-FREE-<var>, but the rule's conclusion (and remaining
; hyps) are instantiated with the ORIGINAL unify-subst, so the conclusion
; keeps the rule's own variable Y.  If the conjecture happens to have variables
; named Y and UNBOUND-FREE-Y, the forced obligation and the derived fact
; disagree.  Rewrite rules and type-prescription rules use the fully bound
; substitution consistently; forward chaining does not.
; EXPECT-AFTER-FIX: bad22 fails (forcing round should be (H A Y), unprovable),
; so CONTRADICTION22 is not admitted.
(defun q (x) (declare (ignore x)) t)
(defun h (x y) (declare (ignore x)) (equal y 0))
(defun p (x y) (h x y))
(defun r (z) (equal z 0))
(defthm fc-rule (implies (and (q x) (force (h x y))) (p x y))
  :rule-classes ((:forward-chaining :trigger-terms ((q x)))))
(defthm r-h (implies (r z) (h x z)))
(in-theory (disable q h p r (:t q) (:t h) (:t p) (:t r) (:e q) (:e h) (:e p) (:e r)))
; The hint just stops the forcing round from re-triggering the same rule.
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad22 (implies (and (q a) (r unbound-free-y)) (p a y)) :rule-classes nil
  :hints (("[1]Goal" :in-theory (disable fc-rule))))
)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction22 nil :rule-classes nil
  :hints (("Goal" :use ((:instance bad22 (a 1) (unbound-free-y 0) (y 1)))
                  :in-theory (enable q h p r))))
)
