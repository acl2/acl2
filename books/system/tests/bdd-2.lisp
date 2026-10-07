; Copyright (C) 2026, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book was inspired by bdd-1.lisp, which was produced by Claude and passed
; along by Eric Smith.  Like that book, it exploits bugs in ACL2 source
; functions first-boolean-type-prescription and bool-mask, illustrating a
; soundness bug fixed before ACL2 Version 8.8.

(in-package "ACL2")

(defun f (x y) (if (equal x y) x t))

(defthm f-tp
  (or (booleanp (f a b))
      (equal (f a b) a))
  :rule-classes ((:type-prescription :typed-term (f a b))))

(in-theory (disable f (:e f)))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; passed in ACL2 Version 8.7
(defthm bad
  (booleanp (f a b))
  :rule-classes nil
  :hints (("Goal" :bdd (:vars nil))))
)

(must-fail
(defthm nil-proved nil
  :rule-classes nil
  :hints (("Goal" :use ((:instance bad (a 7) (b 7)))
                  :in-theory (enable f))))
)
