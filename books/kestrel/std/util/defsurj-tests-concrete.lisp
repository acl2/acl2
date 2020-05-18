; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defsurj-tests-utils")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Concrete (i.e. non-template-based) tests.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Identity surjection over all values.")

(must-succeed (defsurj all-id any-p any-p identity identity))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Identity surjection over natural numbers.")

(must-succeed (defsurj nat-id natp natp identity identity))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Isomorphic surjections between naturals and integers.")

(must-succeed*

 (defun nat-to-int (n)
   (declare (xargs :guard (natp n)))
   (if (evenp n)
       (/ n 2)
     (- (/ (1+ n) 2))))

 (defun int-to-nat (i)
   (declare (xargs :guard (integerp i)))
   (if (>= i 0)
       (* 2 i)
     (1- (- (* 2 i)))))

 (local (include-book "arithmetic-5/top" :dir :system))

 (defsurj nat-int natp integerp nat-to-int int-to-nat)

 (defsurj int-nat integerp natp int-to-nat nat-to-int))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Surjection from all values to naturals.")

(must-succeed (defsurj nfix (lambda (x) t) natp nfix identity))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Surjection from all values to integers.")

(must-succeed (defsurj ifix (lambda (x) t) integerp ifix identity))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Isomorphic surjection between {0, ..., 9} and {9, ..., 0}.")

(must-succeed*

 (defun swap-range (x)
   (declare (xargs :guard (integer-range-p 0 10 x)))
   (- 9 x))

 (defsurj zeronine
   (lambda (x) (integer-range-p 0 10 x))
   (lambda (x) (integer-range-p 0 10 x))
   swap-range
   swap-range))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Isomorphic surjection between (MV X Y) and (MV Y X).")

(must-succeed*

 (defun swap-pair (x y)
   (declare (xargs :guard t))
   (mv y x))

 (defsurj swap-pair
   (lambda (x y) t)
   (lambda (x y) t)
   swap-pair
   swap-pair))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Isomorphic surjections between (MV X Y Z) and (MV (CONS X Y) Z).")

(must-succeed*

 (defun groupedp (xy z)
   (declare (xargs :guard t))
   (declare (ignore z))
   (consp xy))

 (defun group (x y z)
   (declare (xargs :guard t))
   (mv (cons x y) z))

 (defun ungroup (xy z)
   (declare (xargs :guard (consp xy)))
   (mv (car xy) (cdr xy) z))

 (defsurj grouping
   (lambda (x y z) t)
   groupedp
   group
   ungroup)

 (defsurj ungrouping
   groupedp
   (lambda (x y z) t)
   ungroup
   group))
