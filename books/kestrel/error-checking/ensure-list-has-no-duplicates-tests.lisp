; Error Checking Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ensure-list-has-no-duplicates")

(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-list-has-no-duplicates nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-list-has-no-duplicates '(1 2 3) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-list-has-no-duplicates '(1 2 2) "This" t nil 'test state)
 :with-output-off nil)
