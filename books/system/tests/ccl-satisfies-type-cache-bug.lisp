; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  See CCL Issue 754
; (https://github.com/Clozure/ccl/issues/754).

(in-package "ACL2")

(encapsulate ()
  (local (defun p (x) (declare (xargs :guard t)) (integerp x)))
  (local (defun f1 (x)
           (declare (type (and (or null (integer 0 1)) (satisfies p)) x))
           x)))
(defun p (x) (declare (xargs :guard t)) (or (null x) (integerp x)))
(defstobj st
  (ar :type (array (and (or null (integer 0 1)) (satisfies p)) (4)) :initially 1))
(defun g () (declare (xargs :guard t))
  (with-local-stobj st (mv-let (v st) (mv (equal (ari 0 st) 1) st) v)))
(defthm g-is-t   (equal (g) t)   :hints (("Goal" :in-theory (disable (:e g)))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm g-is-nil (equal (g) nil) :hints (("Goal" :in-theory '((:e g)))))
)

; The following was commented out by Matt K. since the event just above now
; fails.
#|
(defthm contradiction nil :rule-classes nil
  :hints (("Goal" :use (g-is-t g-is-nil) :in-theory nil)))
|#
