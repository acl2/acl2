; Theorems about Typed Lists
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides some theorems about typed lists.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/baselists" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-nat-lists

  :parents (theorems-about-non-kestrel-books)

  :short "Some theorems about lists of natural numbers."

  (defrule cdr-of-nat-list-fix
    (equal (cdr (nat-list-fix x))
           (nat-list-fix (cdr x))))

  (defrule car-of-nat-list-fix-when-consp
    (implies (consp x)
             (equal (car (nat-list-fix x))
                    (nfix (car x)))))

  (defrule car-of-nat-list-fix-iff-consp
    (iff (car (nat-list-fix x))
         (consp x))))
