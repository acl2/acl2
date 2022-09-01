; Converting a nat to a string
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "coerce"))
(local (include-book "explode-nonnegative-integer"))

;Convert the natural N into a base-10 string representation.
;; todo: remove the check since we have a guard
(defund nat-to-string (n)
  (declare (type (integer 0 *) n))
  (if (not (mbt (natp n))) ;drop this?:
      (prog2$ (hard-error 'nat-to-string "Argument must be a natural, but we got ~x0." (acons #\0 n nil))
              "ERROR IN NAT-TO-STRING")
    (coerce (explode-nonnegative-integer n 10 nil) 'string)))

;; NAT-TO-STRING is essentially injective
(defthm equal-of-nat-to-string-and-nat-to-string
  (implies (and (natp n1)
                (natp n2))
           (equal (equal (nat-to-string n1)
                         (nat-to-string n2))
                  (equal n1 n2)))
  :hints (("Goal" :in-theory (enable nat-to-string))))

(defthm stringp-of-nat-to-string
  (stringp (nat-to-string x))
  :hints (("Goal" :in-theory (enable nat-to-string))))
