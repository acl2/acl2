; List Utilities -- Theorems about INTERSECTION-EQUAL
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

(defsection intersection-equal-theorems
  :parents (list-utilities intersection$)
  :short "Some theorems about the built-in function @(tsee intersection$)."

  (defrule true-listp-of-intersection-equal
    (true-listp (intersection-equal x y))
    :rule-classes (:rewrite :type-prescription)))
