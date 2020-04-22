; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "try-event")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (make-event
  (try-event
   '(defthm try-event-test (acl2-numberp (+ x y)))
   'top t nil "This is not printed."))
 (assert! (not (eq t (getpropc 'try-event-test 'theorem t (w state))))))

(must-fail
 (make-event
  (try-event
   '(defthm try-event-test (acl2-numberp x))
   'top t nil "This is printed."))
 :with-output-off nil)
