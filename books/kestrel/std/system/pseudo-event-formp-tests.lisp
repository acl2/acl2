; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-event-formp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-event-formp '(defun f (x) x)))

(assert! (pseudo-event-formp '(encapsulate () (defun f (x) x))))

(assert! (not (pseudo-event-formp 33)))

(assert! (not (pseudo-event-formp '("a" 1))))

(assert! (not (pseudo-event-formp nil)))

(assert! (not (pseudo-event-formp '((f x) y))))
