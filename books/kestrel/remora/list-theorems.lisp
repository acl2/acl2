; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "kestrel/typed-lists-light/nat-list-listp" :dir :system)

(include-book "std/lists/repeat" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection list-theorems
  :parents (library-extensions)
  :short "Theorems about lists."

  (defruled car-of-repeat
    (equal (car (repeat n x))
           (if (zp n) nil x))
    :induct t
    :enable repeat)

  (defrule nat-list-listp-of-repeat
    (equal (nat-list-listp (repeat n x))
           (or (zp n) (nat-listp x)))
    :induct t
    :enable repeat))
