; Event Forms -- Tests
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the recognizers in event-forms.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "event-forms")
(include-book "kestrel/general/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (pseudo-event-formp '(defun f (x) x)))

(assert-event (pseudo-event-formp '(encapsulate () (defun f (x) x))))

(assert-event (not (pseudo-event-formp 33)))

(assert-event (not (pseudo-event-formp '("a" 1))))

(assert-event (not (pseudo-event-formp nil)))

(assert-event (not (pseudo-event-formp '((f x) y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (pseudo-event-form-listp nil))

(assert-event (pseudo-event-form-listp '((defun f (x) x)
                                         (encapsulate () (defun f (x) x)))))

(assert-event (not (pseudo-event-form-listp 2)))

(assert-event (not (pseudo-event-form-listp '(defun f (x) x))))
