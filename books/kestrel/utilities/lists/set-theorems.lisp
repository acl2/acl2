; Theorems about Sets Represented as Lists
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-sets-represented-as-lists

  :parents (theorems-about-non-kestrel-books)

  :short "Theorems about sets represented as lists."

  (defrule true-listp-of-add-to-set-equal
    :parents (add-to-set)
    (equal (true-listp (add-to-set-equal a x))
           (true-listp x)))

  (defrule true-listp-of-add-to-set-equal-type
    :parents (add-to-set)
    (implies (true-listp x)
             (true-listp (add-to-set-equal a x)))
    :rule-classes :type-prescription)

  (defrule true-listp-of-union-equal
    :parents (union$)
    (equal (true-listp (union-equal x y))
           (true-listp y)))

  (defrule true-listp-of-union-equal-type
    :parents (union$)
    (implies (true-listp y)
             (true-listp (union-equal x y)))
    :rule-classes :type-prescription)

  (defrule true-listp-of-intersection-equal
    :parents (intersection$)
    (true-listp (intersection-equal x y))
    :rule-classes (:rewrite :type-prescription))

  (defrule true-listp-of-set-difference-equal
    :parents (set-difference$)
    (true-listp (set-difference-equal x y))
    :rule-classes (:rewrite :type-prescription)))
