; Tests for rename-calls
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rename-calls")
(include-book "std/testing/must-be-redundant" :dir :system)

(defund foo (x) (* (+ 1 1) x))
;; We defun foo2 and foo-becomes-foo2 manually, but they are the kind of thing a transformation would produce:
(defund foo2 (x) (* 2 x))
(defthm foo-becomes-foo2
  (equal (foo x)
         (foo2 x))
  :hints (("Goal" :in-theory (enable foo foo2))))
;; Register the renaming:
(table renaming-rule-table 'foo 'foo-becomes-foo2)

(defun bar (x) (+ 0 x))
(defun bar2 (x) (fix x))
;; We defun bar2 and bar-becomes-bar2 manually, but they are the kind of thing a transformation would produce:
(defthm bar-becomes-bar2
  (equal (bar x)
         (bar2 x))
  :hints (("Goal" :in-theory (enable bar bar2))))
;; Register the renaming:
(table renaming-rule-table 'bar 'bar-becomes-bar2)

;; Function to transform.  We'll rename the calls of FOO and BAR.
(defun baz (x y)
  (+ (foo x) (bar y)))

(rename-calls baz
              ;; the renaming to apply:
              ;; TODO: Consider auto-generating this, from the world, or a table?
              ((foo foo2)
               (bar bar2))
              :new-name baz.new)

;; Expected results:
(must-be-redundant
 (DEFUN BAZ.NEW (X Y)
   (DECLARE (XARGS :VERIFY-GUARDS NIL))
   (+ (FOO2 X) (BAR2 Y)))
 (DEFTHM BAZ-BECOMES-BAZ.NEW (EQUAL (BAZ X Y) (BAZ.NEW X Y))))
