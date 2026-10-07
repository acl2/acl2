; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

(in-package "ACL2")

; myrec is a Boolean recognizer that IS satisfiable: (myrec 3) = T.
(defun myrec (x) (if (integerp x) t nil))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
; A trivially true theorem.  Its conclusion (EQUAL Y Y) does not mention
; the recognizer's argument variable, which is deliberately named EMPTY.
(defthm myrec-cr
  (implies (myrec empty) (equal y y))
  :rule-classes :compound-recognizer)
)

; The rest, commented out by Matt K., is no longer relevant after the bug fix.
#|
(defthm bad
  (not (myrec x))
  :rule-classes nil)

(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use ((:instance bad (x 3)))
                  :in-theory (disable myrec-cr))))
|#
