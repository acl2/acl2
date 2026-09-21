; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Single-book variant: use PASS 2 OF ENCAPSULATE instead of include-book to get
; skip-proofs-due-to-system, and a LOCAL event to make the macro alias differ
; between the two passes.
(in-package "ACL2")
(defun victim (x) (declare (xargs :guard t)) (cons x x))
(defun g (x) (declare (xargs :guard t)) (if (equal x 3) 99 (victim x)))
(defun good (x) (declare (xargs :guard t)) (if (equal x 3) 99 (victim x)))
(defthm good-is-g (equal (good x) (g x)) :rule-classes nil)
(defmacro m (x) (list 'good x))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(encapsulate ()
  (local (defun marker (x) x))
  (table macro-aliases-table 'm
         (if (function-symbolp 'marker world) 'good 'victim))
  (memoize 'm :invoke 'g))
)

; The rest, commented out by Matt K., is no longer relevant after the bug fix.
#|
(local (defthm victim-3-by-execution (equal (victim 3) 99) :rule-classes nil))
(local (defthm victim-3-by-definition (equal (victim 3) '(3 . 3)) :rule-classes nil
         :hints (("Goal" :in-theory (disable (:e victim))))))
(defthm nil-proved nil :rule-classes nil
  :hints (("Goal" :use (victim-3-by-execution victim-3-by-definition))))
|#
