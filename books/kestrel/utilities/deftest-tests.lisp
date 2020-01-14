; Tests of deftest itself
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "deftest")

;; A simple test:
(deftest (defun foo (x) x))

;; This foo is different from the foo in the deftest just above:
(deftest (defun foo (x) (+ 1 x)))

(deftest (assert-event (equal (+ 1 1) 2)))

;; Test with more then one event inside deftest.
(deftest
  (defun foo (x) x)
  (defun bar (x) x))

(deftest
  (defun foo (x) x)
  (must-be-redundant (defun foo (x) x)))
