; This book, modified only as noted below and by deleting some initial
; comments, was produced by Claude and passed along by Eric Smith.

(in-package "ACL2")

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(encapsulate
  (((rec *) => *))
  (local (defun rec (x) (consp x)))   ; Boolean only in pass 1
  (defthm rec-cr
    (implies (rec x) (consp x))
    :rule-classes :compound-recognizer))
)

; The rest, commented out by Matt K., is no longer admissible after the bug fix.
#|
(defthm rec-t
  (implies (rec x) (equal (rec x) t))
  :rule-classes nil)

(defthm nil-proved
  nil
  :hints (("Goal" :use ((:instance (:functional-instance rec-t
                                     (rec (lambda (x) (if (consp x) 5 nil))))
                                   (x (cons 1 2))))))
  :rule-classes nil)
|#
