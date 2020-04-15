; Lists of Integers in Ranges -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "integer-range-lists")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (integer-range-listp -5 68 nil))

(assert! (integer-range-listp -5 68 '(4 7 55 -5 67)))

(assert! (not (integer-range-listp -5 68 "10")))

(assert! (not (integer-range-listp -5 68 '(a 1 2))))

(assert! (not (integer-range-listp -5 68 '(-6 0))))

(assert! (not (integer-range-listp -5 68 '(68 0))))

(assert! (not (integer-range-listp -5 68 '(7 10/3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (integer-range-list-fix 20 10 nil) nil)

(assert-equal (integer-range-list-fix 10 20 nil) nil)

(defthm test1
  (equal (integer-range-list-fix 20 10 '("a" 5 '(1 2 3)))
         '(0 0 0)))

(defthm test2
  (equal (integer-range-list-fix 10 20 '(5 100 15 "zzz"))
         '(10 19 15 10)))
