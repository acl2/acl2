; Typed List Utilities -- Theorems about STRING-LISTP
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/lists/list-fix" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection string-listp-theorems
  :parents (typed-list-utilities string-listp)
  :short "Some theorems about the built-in function @(tsee string-listp)."

  (defrule string-listp-of-remove-duplicates-equal
    (equal (string-listp (remove-duplicates-equal x))
           (string-listp (list-fix x)))))
