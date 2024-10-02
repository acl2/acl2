; Standard Lists Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/lists/add-to-set
  :parents (std/lists add-to-set)
  :short "Theorems about the built-in function @(tsee add-to-set)."

  (defthm true-listp-of-add-to-set-equal
    (equal (true-listp (add-to-set-equal a x))
           (true-listp x)))

  (defthm true-listp-of-add-to-set-equal-type
    (implies (true-listp x)
             (true-listp (add-to-set-equal a x)))
    :rule-classes :type-prescription))
