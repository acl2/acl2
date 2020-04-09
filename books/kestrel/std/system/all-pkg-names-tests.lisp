; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-pkg-names")

(include-book "std/testing/assert-equal" :dir :system) ; includes ASSERT!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro same-member-equal (x y)
  `(let ((x ,x) (y ,y))
     (and (subsetp-equal x y)
          (subsetp-equal y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-pkg-names '(quote 4))
              nil)

(assert-equal (all-pkg-names 'x)
              '("ACL2"))

(assert-equal (all-pkg-names '(binary-+ '5 'x))
              '("ACL2"))

(assert! (same-member-equal (all-pkg-names '(car (binary-/ 'x)))
                            (list "ACL2" *main-lisp-package-name*)))

(assert! (same-member-equal (all-pkg-names '(f std::abcde))
                            (list "ACL2" "STD")))

(assert-equal (all-pkg-names '(std::deflist '8))
              '("STD"))
