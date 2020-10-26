; Error Checking Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ensure-value-is-function-name")

(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-value-is-function-name 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-value-is-function-name 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun g (x) x)
 (must-eval-to-t
  (b* (((er x) (ensure-value-is-function-name 'g "This" t nil 'test state)))
    (value (equal x nil)))))

(must-fail
 (ensure-value-is-function-name #\w "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-value-is-function-name 'lenn "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-value-is-function-name 'car-cdr-elim "This" t nil 'test state)
 :with-output-off nil)
