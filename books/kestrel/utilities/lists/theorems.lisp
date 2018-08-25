; Theorems about Lists
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

(defsection theorems-about-lists

  :parents (list-utilities)

  :short "Some theorems about lists."

  (defrule last-of-cdr
    (equal (last (cdr x))
           (if (consp (cdr x))
               (last x)
             (cdr x))))

  (defrule list-of-car-when-one
    (implies (and (consp list)
                  (not (consp (cdr list))))
             (equal (list (car list)) (list-fix list)))))
