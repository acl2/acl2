; Tests of renaming functions in untranslated terms
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rename-functions")
(include-book "std/testing/assert-equal" :dir :system)

(defstub foo (x y) t)

(assert-equal (rename-functions-in-untranslated-term  '(foo (foo x 3) nil) '((foo . bar)) nil state)
              '(bar (bar x 3) nil))

;; Test with a cond
(assert-equal (rename-functions-in-untranslated-term  '(cond ((equal x 3) (natp 3))
                                                             ((equal x 4) (natp 4)))
                                                      '((natp . posp)) nil state)
              '(COND ((EQUAL X 3) (POSP 3))
                     ((EQUAL X 4) (POSP 4))))

;; Test with a cond with a clause of length 1
(assert-equal (rename-functions-in-untranslated-term  '(cond ((equal x 3))
                                                             ((equal x 4) (natp 4)))
                                                      '((natp . posp)) nil state)
              '(COND ((EQUAL X 3))
                     ((EQUAL X 4) (POSP 4))))
