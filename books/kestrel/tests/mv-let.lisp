; Some tests of mv-let
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defun mv3 (x y z) (mv (+ 1 x) (+ 2 y) (+ 3 z)))

  ;; Ok
  (defun foo (x y z)
    (mv-let (a b c)
      (mv3 x y z)
      (+ a b c)))

  ;; Illegal: missing ignore declare for b
  (must-fail
   (defun foo2 (x y z)
     (mv-let (a b c)
       (mv3 x y z)
       (+ a a c))))

  ;; Ok
  (defun foo2b (x y z)
    (mv-let (a b c)
      (mv3 x y z)
      (declare (ignore b))
      (+ a a c)))

  ;; Ok
  (defun foo2c (x y z)
    (mv-let (a b c)
      (mv3 x y z)
      (declare (ignorable b))
      (+ a a c)))

  ;; Ok (multiple ignores for same var in a declare)
  (defun foo2d (x y z)
    (mv-let (a b c)
      (mv3 x y z)
      (declare (ignore b) (ignore b))
      (+ a a c)))

  ;; Ok multiple declare ignores for same var
  (defun foo2e (x y z)
    (mv-let (a b c)
      (mv3 x y z)
      (declare (ignore b)) (declare (ignore b))
      (+ a a c)))

  ;; Ok (ignore and ignorable for same var in a declare)
  (defun foo2f (x y z)
    (mv-let (a b c)
      (mv3 x y z)
      (declare (ignore b) (ignorable b))
      (+ a a c)))

  ;; Ok (ignore and ignorable for same var in different declares)
  (defun foo2g (x y z)
    (mv-let (a b c)
      (mv3 x y z)
      (declare (ignore b)) (declare (ignorable b))
      (+ a a c)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest
  (defun mv3i (x y z) (declare (xargs :guard (and (integerp x) (integerp y) (integerp z)))) (mv (+ 1 x) (+ 2 y) (+ 3 z)))

  (defun bar (x y z)
    (declare (xargs :guard (and (integerp x) (integerp y) (integerp z))))
    (mv-let (a b c)
      (mv3i x y z)
      (declare (type integer a))
      (+ a b c))))
