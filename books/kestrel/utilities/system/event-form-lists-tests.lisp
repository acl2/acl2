; System Utilities -- Event Form Lists -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "event-form-lists")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-event-form-listp nil))

(assert! (pseudo-event-form-listp '((defun f (x) x)
                                    (encapsulate () (defun f (x) x)))))

(assert! (not (pseudo-event-form-listp 2)))

(assert! (not (pseudo-event-form-listp '(defun f (x) x))))
