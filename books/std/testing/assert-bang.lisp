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

; Thanks to David Rager for a request leading to the definition of assert!.

(defxdoc assert!
  :parents (std/testing assert$ errors)
  :short "Form of @(tsee assert$) that is an event"
  :long "<p>The @('assert!') macro is similar to @('assert$'), but its calls
  may appear as top-level @(see events) in @(see books) and @(see encapsulate)
  forms.  In that sense @('assert!') is similar to @('assert-event'); see @(see
  assert-event) for a comparison of features offered by @('assert!') and
  @('assert-event').</p>

 <p>General forms:</p>

 @({
 (assert! assertion)
 (assert! assertion event)
 })

 <p>where @('assertion') is an expression that evaluates to a single non-@(see
 stobj) value.  If @('assertion') evaluates to @('nil'), then an error occurs.
 Otherwise the form @('(value-triple :success)') is evaluated unless @('event')
 is supplied, in which case @('event') is evaluated.</p>

 <p>Example forms:</p>

 @({
 (assert! (equal 3 3))
 (assert! (equal 3 3)
          (defun f (x) (cons x x)))
 })

 <p>Also see @(see assert!-stobj), which is an analogous utility for assertions
 that return @('stobj')s.  Also see @(see must-fail) and @(see must-succeed)
 for other tests that certain commands fail or succeed.</p>")

(defun assert!-body (assertion form)

; Note that assertion should evaluate to a single non-stobj value.  See also
; assert!-stobj-body.

  (declare (xargs :guard t))
  `(let ((assertion ,assertion))
     (value (if assertion
                ',(if form
                      `(with-output :stack :pop ,form)
                    '(value-triple :success))
              '(value-triple nil
                             :check (msg "~x0" ',assertion)
                             :ctx 'assert!)))))

(defmacro assert! (&whole whole-form
                          assertion &optional form)

; Note that assertion should evaluate to a single non-stobj value.  See also
; assert!-stobj.

  `(with-output
     :stack :push
     :off summary
     (make-event ,(assert!-body assertion form)
                 :on-behalf-of ,whole-form)))
