; User Interface -- Tests
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the user interface utilities
; in user-interface.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "user-interface")

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

(progn
  (cw-event "Message."))
