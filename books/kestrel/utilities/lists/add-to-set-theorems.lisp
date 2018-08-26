; List Utilities -- Theorems about ADD-TO-SET-EQUAL
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

(defsection add-to-set-equal-theorems
  :parents (list-utilities add-to-set)
  :short "Some theorems about the built-in function @(tsee add-to-set)."

  (defrule true-listp-of-add-to-set-equal
    (equal (true-listp (add-to-set-equal a x))
           (true-listp x)))

  (defrule true-listp-of-add-to-set-equal-type
    (implies (true-listp x)
             (true-listp (add-to-set-equal a x)))
    :rule-classes :type-prescription))
