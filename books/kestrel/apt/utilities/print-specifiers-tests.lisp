; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "print-specifiers")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (print-specifier-p nil))

(assert! (print-specifier-p :error))

(assert! (print-specifier-p :result))

(assert! (print-specifier-p :info))

(assert! (print-specifier-p :all))

(assert! (not (print-specifier-p #\c)))

(assert! (not (print-specifier-p 55/3)))

(assert! (not (print-specifier-p '(1 2 3))))

(assert! (not (print-specifier-p '(:info))))

(assert! (not (print-specifier-p 'result)))

(assert! (not (print-specifier-p "all")))

(assert! (not (print-specifier-p t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (ensure-is-print-specifier 6/7 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-is-print-specifier ":info" "This" t nil 'test state)
 :with-output-off nil)

(acl2::must-succeed
 (ensure-is-print-specifier nil "This" t nil 'test state)
 :with-output-off nil)

(acl2::must-succeed
 (ensure-is-print-specifier :error "This" t nil 'test state)
 :with-output-off nil)

(acl2::must-succeed
 (ensure-is-print-specifier :result "This" t nil 'test state)
 :with-output-off nil)

(acl2::must-succeed
 (ensure-is-print-specifier :info "This" t nil 'test state)
 :with-output-off nil)

(acl2::must-succeed
 (ensure-is-print-specifier :all "This" t nil 'test state)
 :with-output-off nil)
