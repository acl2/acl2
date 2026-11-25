; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-158 (leads F1-534, F1-536, stage-2 batch G18), CCL only: CCL 1.13 gets
; (member ...) types with complex elements wrong ((typep #c(1 1) '(member
; #c(1 2))) is T).  ACL2's guard for the type-spec is exact, so for
; (and (member #c(1 1)) (not (member #c(1 2)))) CCL computes the empty type and
; folds (equal x #c(1 1)) to NIL in a guard-verified function.
; Proves nil and certifies on CCL at 21aaad6, 227bafe2d1, eda4d85572 and
; 9a589490e6; fails on SBCL, as expected.
(in-package "ACL2")
(defun f (x)
  (declare (type (and (member #c(1 1)) (not (member #c(1 2)))) x))
  (if (equal x #c(1 1)) 'yes 'no))
(defun f2 (x)
  (declare (type (and (member #c(1 1)) (not (member #c(1 2)))) x))
  (if (eql x #c(1 1)) 'yes 'no))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm f-exec (equal (f #c(1 1)) 'no) :rule-classes nil)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defthm f-logic (equal (f #c(1 1)) 'yes)
  :hints (("Goal" :in-theory (disable (:e f)))) :rule-classes nil)
(defthm bad nil :hints (("Goal" :use (f-exec f-logic))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
