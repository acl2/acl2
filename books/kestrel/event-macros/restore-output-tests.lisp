; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "restore-output")

(include-book "make-event-terse")

(include-book "std/testing/assert-bang" :dir :system)

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
