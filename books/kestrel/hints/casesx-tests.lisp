; Tests for casesx.lisp
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "casesx")

;; Constrain foo to be true for all combinations of 0 and 1:
(encapsulate ((foo (x y z) t))
  (local (defun foo (x y z) (declare (ignore x y z)) t))
  (defthm foo000 (foo 0 0 0))
  (defthm foo001 (foo 0 0 1))
  (defthm foo010 (foo 0 1 0))
  (defthm foo011 (foo 0 1 1))
  (defthm foo100 (foo 1 0 0))
  (defthm foo101 (foo 1 0 1))
  (defthm foo110 (foo 1 1 0))
  (defthm foo111 (foo 1 1 1)))

;; Fails without the :casesx hint
(must-fail
  (thm
    (implies (and (<= 0 a)
                  (<= a 1)
                  (<= 0 b)
                  (<= b 1)
                  (<= 0 c)
                  (<= c 1)
                  (integerp a)
                  (integerp b)
                  (integerp c))
             (foo a b c))))

;; Fails with a simple :cases hint (which doesn't even make sense here, since it
;; doesn't make all combinations of cases).
(must-fail
  (thm
    (implies (and (<= 0 a)
                  (<= a 1)
                  (<= 0 b)
                  (<= b 1)
                  (<= 0 c)
                  (<= c 1)
                  (integerp a)
                  (integerp b)
                  (integerp c))
             (foo a b c))
    :hints (("Goal" :cases ((equal 0 a) (equal 0 b) (equal 0 c))))))

; Added by Matt K. 2/2/2024 to avoid ACL2(p) error about producing an error
; triple.
(set-waterfall-parallelism nil)

;; Works with the :casesx hint, which creates 8 cases
(defthm test1
  (implies (and (<= 0 a)
                (<= a 1)
                (<= 0 b)
                (<= b 1)
                (<= 0 c)
                (<= c 1)
                (integerp a)
                (integerp b)
                (integerp c))
           (foo a b c))
  :hints (("Goal" :casesx ((equal 0 a) (equal 0 b) (equal 0 c)))))
