; List Utilities -- Theorems about UNION-EQUAL
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection union-equal-theorems
  :parents (list-utilities union$)
  :short "Some theorems about the built-in function @(tsee union$)."

  (defrule true-listp-of-union-equal
    (equal (true-listp (union-equal x y))
           (true-listp y)))

  (defrule true-listp-of-union-equal-type
    (implies (true-listp y)
             (true-listp (union-equal x y)))
    :rule-classes :type-prescription))
