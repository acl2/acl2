; Event Forms -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "event-forms")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-event-formp '(defun f (x) x)))

(assert! (pseudo-event-formp '(encapsulate () (defun f (x) x))))

(assert! (not (pseudo-event-formp 33)))

(assert! (not (pseudo-event-formp '("a" 1))))

(assert! (not (pseudo-event-formp nil)))

(assert! (not (pseudo-event-formp '((f x) y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-event-form-listp nil))

(assert! (pseudo-event-form-listp '((defun f (x) x)
                                    (encapsulate () (defun f (x) x)))))

(assert! (not (pseudo-event-form-listp 2)))

(assert! (not (pseudo-event-form-listp '(defun f (x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (maybe-pseudo-event-formp nil))

(assert! (maybe-pseudo-event-formp '(defun f (x) x)))

(assert! (maybe-pseudo-event-formp '(encapsulate () (defun f (x) x))))

(assert! (not (maybe-pseudo-event-formp 33)))

(assert! (not (maybe-pseudo-event-formp '("a" 1))))

(assert! (not (maybe-pseudo-event-formp '((f x) y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (function-intro-macro t nil) 'defun)

(assert-equal (function-intro-macro nil nil) 'defund)

(assert-equal (function-intro-macro t t) 'defun-nx)

(assert-equal (function-intro-macro nil t) 'defund-nx)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (theorem-intro-macro t) 'defthm)

(assert-equal (theorem-intro-macro nil) 'defthmd)
