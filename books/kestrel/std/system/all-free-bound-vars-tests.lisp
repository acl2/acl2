; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-free-bound-vars")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro same-member-eq (x y)
  `(let ((x ,x) (y ,y))
     (and (subsetp-eq x y)
          (subsetp-eq y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (same-member-eq (all-free/bound-vars 'x) '(x)))

(assert! (same-member-eq (all-free/bound-vars '(quote 3)) nil))

(assert! (same-member-eq (all-free/bound-vars '(quote (1 2 3))) nil))

(assert! (same-member-eq (all-free/bound-vars '(f y zz)) '(y zz)))

(assert! (same-member-eq (all-free/bound-vars '((lambda (x) (cons x x))
                                                (quote 3)))
                         '(x)))

(assert! (same-member-eq (all-free/bound-vars '((lambda (x) (cons x x))
                                                (g x)))
                         '(x)))

(assert! (same-member-eq (all-free/bound-vars '((lambda (x) (cons x x))
                                                (h y y)))
                         '(x y)))
