; Error Checking Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ensure-value-is-true-list")

(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-value-is-true-list nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-value-is-true-list '(1 2 3) "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-value-is-true-list '(#\c 2/3 (3 3 3))
                                         "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-value-is-true-list #\Space "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-value-is-true-list '(a 1 b . 4) "This" t nil 'test state)
 :with-output-off nil)
