; User Interface -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "user-interface")
(include-book "testing")
(include-book "er-soft-plus") ; to test FAIL-EVENT
(include-book "orelse") ; to test TRY-EVENT

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (local
   (defmacro m () (suppress-output '(make-event '(defun f (x) x)))))
  (local (m)))

(encapsulate
  ()
  (local
   (defmacro m() '(make-event '(defun f (x) x))))
  (local (m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (local
   (defmacro m () (maybe-suppress-output t '(make-event '(defun f (x) x)))))
  (local (m)))

(encapsulate
  ()
  (local
   (defmacro m () (maybe-suppress-output nil '(make-event '(defun f (x) x)))))
  (local (m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (local
   (defmacro m () (control-screen-output nil '(make-event '(defun f (x) x)))))
  (local (m)))

(encapsulate
  ()
  (local
   (defmacro m () (control-screen-output t '(make-event '(defun f (x) x)))))
  (local (m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (local
   (defmacro m () (manage-screen-output nil '(make-event '(defun f (x) x)))))
  (local (m)))

(encapsulate
  ()
  (local
   (defmacro m () (manage-screen-output t '(make-event '(defun f (x) x)))))
  (local (m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(progn
  (cw-event "Message."))

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
