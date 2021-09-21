; Tests for rename-vars-in-term
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/assert-equal" :dir :system)

(include-book "rename-vars-in-term")

;; Swapping the names (no new names need to be created)
(assert-equal (rename-vars-in-term '((x . y) (y . x))
                                   '((lambda (x y) (+ x y))
                                     (foo x)
                                     (foo y))
                                   '((x . y) (y . x)))
              '((lambda (y x) (+ y x))
                (foo y)
                (foo x)))

;; TODO: Add more tests
