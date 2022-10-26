; Error Checking Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ensure-value-is-constant-name")

(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-value-is-constant-name '*primitive-formals-and-guards*
                                             "This"
                                             t
                                             nil
                                             'test
                                             state)))
   (value (equal x nil))))

(must-succeed*
 (defconst *g* 1)
 (must-eval-to-t
  (b* (((er x) (ensure-value-is-constant-name '*g* "This" t nil 'test state)))
    (value (equal x nil)))))

(must-fail
 (ensure-value-is-constant-name #\w "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-value-is-constant-name '*not-a-const* "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-value-is-constant-name 'car-cdr-elim "This" t nil 'test state)
 :with-output-off nil)
