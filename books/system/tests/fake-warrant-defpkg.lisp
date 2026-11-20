; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-202 (lead F8-354, stage-2 batch G61): the same with a user package that imports a warranted function's
; name but not its warrant's.  Proves nil, no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.
;
(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)
(defun g (x) x)
(defwarrant g)
(encapsulate (((q::apply$-warrant-g) => *))
  (local (defun q::apply$-warrant-g () nil))
  (defthm wnil (not (q::apply$-warrant-g)) :rule-classes nil))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defattach q::apply$-warrant-g true-apply$-warrant)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defevaluator my-ev my-ev-lst ((if a b c)))
(defun cp (cl) (if (q::apply$-warrant-g) nil (list cl)))
(defthm cp-correct
  (implies (and (pseudo-term-listp cl) (alistp a) (my-ev (conjoin-clauses (cp cl)) a))
           (my-ev (disjoin cl) a))
  :hints (("Goal" :use wnil))
  :rule-classes :clause-processor)
(defthm nil-proved nil :hints (("Goal" :clause-processor (cp clause))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
