; System Utilities -- Theorems about ARGLISTP
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

(defsection theorems-about-arglistp
  :parents (theorems-about-non-kestrel-books system-utilities-non-built-in)
  :short "Theorems about @(tsee arglistp)."

  (defrule true-listp-when-arglistp
    (implies (arglistp x)
             (true-listp x))
    :rule-classes :compound-recognizer))
