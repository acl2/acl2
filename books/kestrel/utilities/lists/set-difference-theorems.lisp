; List Utilities -- Theorems about SET-DIFFERENCE-EQUAL
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

(defsection set-difference-equal-theorems
  :parents (list-utilities set-difference$)
  :short "Some theorems about the built-in function @(tsee set-difference$)."

  (defrule true-listp-of-set-difference-equal
    (true-listp (set-difference-equal x y))
    :rule-classes (:rewrite :type-prescription)))
