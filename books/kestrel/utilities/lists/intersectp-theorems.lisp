; List Utilities -- Theorems about INTERSECTP-EQUAL
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/intersectp" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection intersectp-equal-theorems
  :parents (list-utilities intersectp)
  :short "Some theorems about the built-in function @(tsee intersectp)."

  (defrule intersectp-append-left
    (equal (intersectp-equal (append x y) z)
           (or (intersectp-equal x z)
               (intersectp-equal y z)))
    :enable append)

  (defrule intersectp-append-right
    (equal (intersectp-equal x (append y z))
           (or (intersectp-equal x y)
               (intersectp-equal x z)))
    :enable append))
