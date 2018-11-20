; Typed List Utilities -- Theorems about NAT-LIST-FIX
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/baselists" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nat-list-fix-theorems
  :parents (typed-list-utilities nat-list-fix)
  :short "Some theorems about the library function @(tsee nat-list-fix)."

  (defrule cdr-of-nat-list-fix
    (equal (cdr (nat-list-fix x))
           (nat-list-fix (cdr x))))

  (defrule car-of-nat-list-fix-when-consp
    (implies (consp x)
             (equal (car (nat-list-fix x))
                    (nfix (car x)))))

  (defrule car-of-nat-list-fix-iff-consp
    (iff (car (nat-list-fix x))
         (consp x)))

  (defrule rev-of-nat-list-fix
    (equal (rev (nat-list-fix x))
           (nat-list-fix (rev x)))
    :enable nat-list-fix)

  (defrule nat-list-fix-of-true-list-fix
    (equal (nat-list-fix (true-list-fix x))
           (nat-list-fix x))
    :enable nat-list-fix))
