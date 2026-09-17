; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  See also measure-fn-redundancy.lisp.

; NEW variant: the ENCAPSULATE-level redundancy check (redundant-encapsulate-tuplep,
; other-events.lisp ~7783) compares the ambient acl2-defaults-table only for
; defun-mode, ruler-extenders and verify-guards-eagerness -- NOT for the default
; MEASURE FUNCTION (nor the well-founded relation).  So two syntactically identical
; encapsulates processed under different (set-measure-function ...) defaults are
; deemed redundant, and the second one's termination is never proved under the new
; default.  This is the encapsulate-level analogue of the (now-fixed) defun-level
; bug in non-identical-defp.
(in-package "ACL2")

(defun zero-m (x)
  (declare (ignore x))
  0)

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  ()
  (local (encapsulate
           ()
           (defun f (x)
             (if (consp x) (f (cdr x)) x))))
  (set-measure-function zero-m)
; The must-fail wrapper below was added by Matt Kaufmann, as the following
; definition of f is no longer redundant as of mid-September, 2026.
  (must-fail
  (encapsulate
    ()
    (defun f (x)
      (if (consp x) (f (cdr x)) x))
    )))

; Commented out by Matt Kaufmann:
#|
(defthm bad
  (not (consp x))
  :rule-classes nil
  :hints (("Goal" :use (:termination-theorem f))))

(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (:instance bad (x '(1))))))
|#
