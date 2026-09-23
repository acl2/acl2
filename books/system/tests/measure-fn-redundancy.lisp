; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Variant: redundancy of DEFUN ignores the default measure function
; (SET-MEASURE-FUNCTION) when neither definition has an explicit :measure.
(in-package "ACL2")

(defun zero-m (x)
  (declare (ignore x))
  0)

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  ()
  (local (defun f (x)
           (if (consp x) (f (cdr x)) x)))
  (set-measure-function zero-m)
; The must-fail wrapper below was added by Matt Kaufmann, as the following
; definition of f is no longer redundant as of mid-September, 2026.
  (must-fail
  (defun f (x)
    (if (consp x) (f (cdr x)) x))
  ))

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm bad
  (not (consp x))
  :rule-classes nil
  :hints (("Goal" :use (:termination-theorem f))))
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (:instance bad (x '(1))))))
)
