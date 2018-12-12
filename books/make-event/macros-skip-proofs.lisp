; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This is just a little variation macros.lisp that uses skip-proofs.  We check
; the expansions in macros-skip-proofs-include.lisp, much as we check
; expansions from macros.lisp in macros-include.lisp.

(in-package "ACL2")

; The following book reads the .cert file of the present book.  So recertify
; the present book if the following book changes, in case that's because the
; format of .cert files has changed.

; (depends-on "macros-skip-proofs-include.lisp")

(defmacro my-mac (x) x)

(encapsulate
 ((local-fn (x) t))
 (local (defun local-fn (x) x))
 (local
  (make-event '(defun foo1 (x) x)))
 (my-mac
  (skip-proofs
   (make-event '(defun foo2 (x) x)
               :check-expansion t)))
 (skip-proofs
  (my-mac
   (make-event '(defun foo3 (x) x)
               :check-expansion t)))
 (make-event '(defun foo4 (x) x)))

; Identical to form above, hence should be redundant.
(encapsulate
 ((local-fn (x) t))
 (local (defun local-fn (x) x))
 (local
  (make-event '(defun foo1 (x) x)))
 (my-mac
  (skip-proofs
   (make-event '(defun foo2 (x) x)
               :check-expansion t)))
 (skip-proofs
  (my-mac
   (make-event '(defun foo3 (x) x)
               :check-expansion t)))
 (make-event '(defun foo4 (x) x)))

