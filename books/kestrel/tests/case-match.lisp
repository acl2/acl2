; Some tests of case-match
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/assert-equal" :dir :system)

(defun foo (x)
  (case-match x
    (3 'x-is-three)
    (('cons y z) (declare (ignore y z)) 'x-is-a-call-of-cons)
    (& 'x-is-something-else)))

(assert-equal (foo '3) 'x-is-three)
(assert-equal (foo '(cons x y)) 'x-is-a-call-of-cons)
(assert-equal (foo '(blah x y)) 'x-is-something-else)

(defun foo2 (x)
  (case-match x
    ;; test that multiple ampersands don't have to match the same thing:
    (('cons & &) 'x-is-a-call-of-cons)
    (& 'x-is-something-else)))

(assert-equal (foo2 '(cons x y)) 'x-is-a-call-of-cons)
(assert-equal (foo2 '(blah x y)) 'x-is-something-else)

;; A test with multiple declares.  Previously, :doc case-match disallowed this,
;; though it worked fine.
(defun foo3 (x)
  (case-match x
    (('cons y z) (declare (ignore y)) (declare (ignore z)) 'x-is-a-call-of-cons)
    (& 'x-is-something-else)))

(assert-equal (foo3 '(cons x y)) 'x-is-a-call-of-cons)
(assert-equal (foo3 '(blah x y)) 'x-is-something-else)
