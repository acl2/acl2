; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

(in-package "ACL2")

(defun f (x y) (if (equal x y) t 17))

; (f x x) = T, so this is a genuine theorem.
(defthm f-tp
  (booleanp (f x x))
  :rule-classes ((:type-prescription :typed-term (f x x))))

(in-theory (disable f (:e f)))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm bad
  (booleanp (f x y))
  :rule-classes nil
  :hints (("Goal" :bdd (:vars nil))))
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved nil
  :rule-classes nil
  :hints (("Goal" :use ((:instance bad (x t) (y nil)))
                  :in-theory (enable f))))
)
