; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "maybe-pseudo-event-formp")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (maybe-pseudo-event-formp nil))

(assert! (maybe-pseudo-event-formp '(defun f (x) x)))

(assert! (maybe-pseudo-event-formp '(encapsulate () (defun f (x) x))))

(assert! (not (maybe-pseudo-event-formp 33)))

(assert! (not (maybe-pseudo-event-formp '("a" 1))))

(assert! (not (maybe-pseudo-event-formp '((f x) y))))
