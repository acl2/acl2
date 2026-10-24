; Tests and examples for clean-up-conjunction.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in clean-up-conjunction.lisp.
;; This book is not included by top.lisp.

(include-book "clean-up-conjunction")

;; Clean-up-nots preserves the truth of a term (clean-up-nots-correct), but not
;; always its value: (NOT (NOT X)) is T or NIL, and X need not be.
(defthm clean-up-nots-does-not-preserve-value
  (let ((p '(not (not x)))
        (a '((x . 3))))
    (and (equal (clean-up-nots p) 'x)
         (equal (cleanup-eval p a) t)
         (equal (cleanup-eval (clean-up-nots p) a) 3)))
  :rule-classes nil)
