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

(make-event-terse
 '(defun a (x) x))

(make-event-terse
 '(defun a1 (x) x)
 :suppress-errors nil)

(make-event-terse
 '(defun a2 (x) x)
 :suppress-errors t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event-terse
 `(progn
    (defun b (x) x)
    ,(restore-output '(defun c (x) x))))

(assert! (equal (restore-output '(form))
                '(with-output :stack :pop (form))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event-terse
 `(progn
    (defun d (x) x)
    ,(restore-output? t '(defun e (x) x))))

(make-event-terse
 `(progn
    (defun f (x) x)
    ,(restore-output? nil '(defun g (x) x))))

(assert! (equal (restore-output? t '(form))
                '(with-output :stack :pop (form))))

(assert! (equal (restore-output? nil '(form))
                '(form)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (fail-event top t nil "This is a test error message.")
 :with-output-off nil)

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
