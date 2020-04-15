; Fixing Function for Integer Ranges -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "integer-range-fixing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm test1
  (equal (integer-range-fix 20 10 "abc") 0))

(defthm test2
  (equal (integer-range-fix 20 10 5) 0))

(defthm test3
  (equal (integer-range-fix 20 10 100) 0))

(defthm test4
  (equal (integer-range-fix 20 10 15) 0))

(defthm test5
  (equal (integer-range-fix 10 20 5) 10))

(defthm test6
 (equal (integer-range-fix 10 20 100) 19))

(defthm test7
  (equal (integer-range-fix 10 20 '(15)) 10))
