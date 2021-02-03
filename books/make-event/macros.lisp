; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here are some tests involving macros.  See macros-include.lisp for expected
; expansion results.  Each form below is labeled with its position [p] in the
; resulting expansion-alist.

(in-package "ACL2")

; The following book reads the .cert file of the present book.  So recertify
; the present book if the following book changes, in case that's because the
; format of .cert files has changed.

; (depends-on "macros-include.lisp")

; [1]
(defmacro my-mac (x) x)

; [2]
(my-mac (make-event '(defun foo (x) x)))
; [3]
(my-mac (make-event '(defun foo (x) x)
                    :check-expansion t))

; The following fails during the include-book pass of certification because no
; expansion occurs (and my-mac is local):
; (my-mac (make-event '(defun foo (x) x) :check-expansion (defun foo (x) x)))

; Note that the final event stored has a filled-in :check-expansion field but
; stores the original event in the first argument of record-expansion.
; [4]
(encapsulate
 ((local-fn (x) t))
 (local (defun local-fn (x) x))
 (my-mac (make-event '(defun foo2 (x) x)
                     :check-expansion t)))

; The following encapsulate's expansion eliminates make-event from its
; sub-event, because the :check-expansion field is (by default) nil.
; [5]
(encapsulate
 ()
 (my-mac (make-event '(defun foo3 (x) x))))

; [6]
(set-enforce-redundancy t)

; Redundant with (identical to) command 3, and thus has identical expansion.
; [7]
(encapsulate
 ((local-fn (x) t))
 (local (defun local-fn (x) x))
 (my-mac (make-event '(defun foo2 (x) x)
                     :check-expansion t)))

; As above, just for emphasis:
; Redundant with (identical to) command 3, and thus has identical expansion.
; [8]
(encapsulate
 ((local-fn (x) t))
 (local (defun local-fn (x) x))
 (my-mac (make-event '(defun foo2 (x) x)
                     :check-expansion t)))

; Needed for definition of must-fail, used below:
; [9]
(include-book "std/testing/must-fail" :dir :system)

; Not redundant with command 3 (my-mac call is missing).
; [10]
(must-fail
 (encapsulate
  ((local-fn (x) t))
  (local (defun local-fn (x) x))
  (make-event '(defun foo2 (x) x)
              :check-expansion t)))

; Not redundant with command 3 (different :check-expansion).
; [11]
(must-fail
 (encapsulate
  ((local-fn (x) t))
  (local (defun local-fn (x) x))
  (my-mac (make-event '(defun foo2 (x) x)
                      :check-expansion
                      (defun foo2 (x) x)))))
