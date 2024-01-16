; Theorems that justify the operation of the Axe Rewriter(s)
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/booleans/boolif" :dir :system)

(thm
  (implies test
           (equal (boolif test x y)
                  ;; this then gets further simplified:
                  (boolif t x y))))

(thm
  (implies test
           (equal (boolif t x y)
                  (bool-fix$inline x))))

(thm
  (implies test
           (equal (boolif nil x y)
                  (bool-fix$inline y))))

;; combines 2 of the rules above (test becomes t and then the then-branch is selected):
(thm
  (implies test
           (equal (boolif test x y)
                  (bool-fix$inline x))))

(thm
  (implies x
           (equal (boolif test x y)
                  (boolif test t y))))

(thm
  (implies y
           (equal (boolif test x y)
                  (boolif test x t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(thm
  (implies arg
           (equal (not arg)
                  (not t))))

(thm
  (implies arg
           (equal (not arg)
                  nil)))
