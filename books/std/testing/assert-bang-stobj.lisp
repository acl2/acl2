; Standard Testing Library
;
; Copyright (C) 2017 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following is an extension of assert! that works with stobjs, in
; this case for assertions that return (mv val st) where val is an ordinary
; value and st is a stobj.  Our intention is to illustrate how to write other
; versions of assert!.  If you understand this extension, you can then write
; your own extensions that can similarly handle other signatures for the
; assertion.

(defxdoc assert!-stobj
  :parents (std/testing assert$ errors)
  :short "Form of @(tsee assert$) involving @(see stobj)s that is an event"
  :long "<p>This variant of @(see assert!) allows forms that modify @(see
 stobj)s.</p>

 <p>General Form:</p>

 @({
 (assert!-stobj assertion stobj)
 })

 <p>Example Forms:</p>

 @({
 (assert!-stobj (mv-let (erp val state)
                  (set-inhibit-output-lst nil)
                  (declare (ignore val))
                  (mv (null erp) state))
                state)

 (defstobj st fld)
 (assert!-stobj (let ((st (update-fld 3 st)))
                  (mv (eql (fld st) 3)
                      st))
                st)
 })

 <p>The first argument (the assertion) should evaluate to multiple values
 @('(mv val st)'), where @('val') is an ordinary value and @('st') is a @(see
 stobj) (either user-defined or @(tsee state)).  The second argument should be
 the name of the stobj that is being returned.</p>")

(defun assert!-stobj-body (assertion st form)

; Assertion should evaluate to (mv val st), where val is an ordinary value and
; st is a stobj.  See also assert!-body.

  (declare (xargs :guard t))
  (let ((extra (if (eq st 'state) nil (list st))))
    `(mv-let (result ,st)
       ,assertion
       (mv nil
           (if result
               ',(if form
                     `(with-output :stack :pop ,form)
                   '(value-triple :success))
             '(value-triple nil
                            :check (msg "~x0" ',assertion)
                            :ctx 'assert!-stobj))
           state
           ,@extra))))

(defmacro assert!-stobj (&whole whole-form
                                assertion st &optional form)

; Assertion should evaluate to (mv val st), where val is an ordinary value and
; st is a stobj.  See also assert!.

  `(with-output
     :stack :push
     :off summary
     (make-event ,(assert!-stobj-body assertion st form)
                 :on-behalf-of ,whole-form)))
