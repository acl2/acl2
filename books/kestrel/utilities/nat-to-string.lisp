; Converting a nat to a string
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "coerce"))
(local (include-book "explode-nonnegative-integer"))

;Convert the natural N into a base-10 string representation.
(defund nat-to-string (n)
  (declare (xargs :guard (natp n)
                  :split-types t)
           (type (integer 0 *) n))
  (coerce (explode-nonnegative-integer n 10 nil) 'string))

;; NAT-TO-STRING is essentially injective
(defthm equal-of-nat-to-string-and-nat-to-string
  (equal (equal (nat-to-string n1)
                (nat-to-string n2))
         (equal (nfix n1) (nfix n2)))
  :hints (("Goal" :in-theory (enable nat-to-string))))
