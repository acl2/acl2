; Tests of renaming functions in untranslated terms
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add more tests

(include-book "rename-functions")
(include-book "std/testing/assert-equal" :dir :system)

(defstub foo (x y) t)

(assert-equal (rename-functions-in-untranslated-term
               '(foo (foo x 3) nil) '((foo . bar)) state)
              '(bar (bar x 3) nil))

;; Test with a cond:
(assert-equal (rename-functions-in-untranslated-term
               '(cond ((equal x 3) (natp 3))
                      ((equal x 4) (natp 4)))
               '((natp . posp)) state)
              '(COND ((EQUAL X 3) (POSP 3))
                     ((EQUAL X 4) (POSP 4))))

;; Test with a cond with a clause of length 1:
(assert-equal (rename-functions-in-untranslated-term
               '(cond ((equal x 3))
                      ((equal x 4) (natp 4)))
               '((natp . posp)) state)
              '(COND ((EQUAL X 3))
                     ((EQUAL X 4) (POSP 4))))

;; Test with a case:
(assert-equal (rename-functions-in-untranslated-term
               '(case x
                  (a (foo x 3))
                  ((b c) (foo x 4))
                  (foo (+ x 1))
                  (otherwise (foo x 2)))
               '((foo . bar))
               state)
              '(case x
                 (a (bar x 3))
                 ((b c) (bar x 4))
                 (foo (+ x 1))
                 (otherwise (bar x 2))))

;; Test of b*:
(assert-equal
 (rename-functions-in-untranslated-term
  '(b* ((x (car y))
        ((when (consp x))
         (+ (car x) (cdr x)))
        (- (cw "Hello"))
        ((mv a b c) (mv (< a a) b c)))
     (list x a b c))
  '((< . new<) (car . newcar) (consp . newconsp)) state)
 '(B* ((X (NEWCAR Y))
       ((WHEN (newCONSP X))
        (+ (newcar x) (cdr x)))
       (- (CW "Hello"))
       ((MV A B C) (MV (new< A A) B C)))
    (LIST X A B C)))

;; Test with a let:
(assert-equal
 (rename-functions-in-untranslated-term
 '(LET ((Y (foo x 4)) (z (foo y 5))) (/ (foo x 6)))
 '((foo . bar))
 state)
 '(LET ((Y (bar x 4)) (z (bar y 5))) (/ (bar x 6))))

;; Example with an ignored let var.  Gave an error before we changed the tool to set ignore-ok.
(assert-equal
 (rename-functions-in-untranslated-term
 '(LET ((Y 4)) x)
 '((foo . bar))
 state)
 '(LET ((Y 4)) x))

;; TODO: Add tests of case-match, etc.
