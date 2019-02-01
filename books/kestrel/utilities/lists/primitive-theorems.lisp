; List Utilities -- Theorems about Primitives
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection list-primitive-theorems
  :parents (list-utilities)
  :short "Some theorems about the list primitive functions
          (i.e. @(tsee car), @(tsee cdr), @(tsee cons), and @(tsee consp))."

  (defrule list-of-car-when-one
    (implies (and (consp list)
                  (not (consp (cdr list))))
             (equal (list (car list)) (true-list-fix list)))))
