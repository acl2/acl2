; Standard Testing Library
;
; Copyright (C) 2018 Regents of the University of Texas
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "must-be-redundant")
(include-book "must-eval-to")
(include-book "must-eval-to-t")
(include-book "must-fail")
(include-book "must-fail-local")
(include-book "must-fail-with-error")
(include-book "must-fail-with-hard-error")
(include-book "must-fail-with-soft-error")
(include-book "must-not-prove")
(include-book "must-prove")
(include-book "must-succeed")
(include-book "must-succeed-star")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Event-Level Evaluation

; Here we define macros that employ make-event to check evaluations of forms.
; See community book make-event/eval-tests.lisp (and many other .lisp files in
; that directory) for how these macros may be employed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; deprecated:

(defsection ensure-error
  :parents (must-fail-with-error)
  :short "Deprecated synonym of @(tsee must-fail-with-error)"
  (defmacro ensure-error (&rest args)
    `(must-fail-with-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; deprecated:

(defsection ensure-soft-error
  :parents (must-fail-with-soft-error)
  :short "Deprecated synonym of @(tsee must-fail-with-soft-error)"
  (defmacro ensure-soft-error (&rest args)
    `(must-fail-with-soft-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; deprecated:

(defsection ensure-hard-error
  :parents (must-fail-with-hard-error)
  :short "Deprecated synonym of @(tsee must-fail-with-hard-error)"
  (defmacro ensure-hard-error (&rest args)
    `(must-fail-with-hard-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; deprecated:

(defsection thm?
  :parents (must-prove)
  :short "Deprecated synonym of @(tsee must-prove)."
  (defmacro thm? (&rest args)
    `(must-prove ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; deprecated:

(defsection not-thm?
  :parents (must-not-prove)
  :short "Deprecated synonym of @(tsee must-not-prove)."
  (defmacro not-thm? (&rest args)
    `(must-not-prove ,@args)))
