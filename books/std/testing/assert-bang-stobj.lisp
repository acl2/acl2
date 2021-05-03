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

; The following was developed as an extension of assert! that works with
; stobjs, to illustrate how to write other versions of assert!.  Starting late
; April 2021, when assert-event became more full-featured and ceased using
; safe-mode by default, assert!-stobj became a trivial wrapper for certain
; calls of assert-event.

(defxdoc assert!-stobj
  :parents (std/testing assert-event errors)
  :short "Variant of @(tsee assert!) and @(tsee assert-event) allowing @(see stobj)s"
  :long "<p>The @('assert!-stobj') macro is a variant of @(tsee assert!) that
 expects its first argument to evaluate to multiple values, specifically, two
 values where the first is not a @(see stobj) and the second is a specified
 stobj.  @('Assert!-stobj') is an @(see event) macro: its calls may appear as
 top-level @(see events) in @(see books) as well as @(tsee encapsulate) and
 @(tsee progn) forms.  As with @('assert!'), calls of @('assert!-stobj')
 directly abbreviate corresponding calls of the built-in @(see event) macro,
 @(tsee assert-event).  You may find it more convenient to use @(tsee
 assert-event), which has more options.  In particular, with @('assert-event')
 the assertion may evaluate to a single value or to any number of multiple
 values, with no limit on the number of stobjs retured, and a keyword option
 @(':STOBJS-OUT :auto') that makes it unnessary to to specify the shape of the
 return.</p>

 <p>See @(see assert$) and @(see assert*) for assertion-checking utilities to
 use in programs.</p>

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

 <p>General Forms:</p>

 @({
 (assert!-stobj assertion st)
 (assert!-stobj assertion st event)
 })

 <p>where: @('assertion') evaluates to multiple values @('(mv val st)'), where
 @('val') is an ordinary value and @('st') &mdash; which is the second argument
 above &mdash; is a @(see stobj) (either user-defined or @(tsee state)); and
 @('event'), if supplied and non-@('nil'), is an @(see event) to be evaluated
 if the first return value is not @('nil').  It is an error if the first return
 value is @('nil').  As noted above, a call of @('assert!-stobj') is an @(see
 event): it can go into a book or an @(tsee encapsulate) or @(tsee progn)
 event.</p>

 <p>Calls of @('assert!-stobj') skip evaluation of the given assertion when
 proofs are being skipped: during @(tsee include-book), during the second pass
 of an @(tsee encapsulate) event, and after evaluating @('(set-ld-skip-proofsp
 t state)').</p>

 <p>The two General Forms above may be expressed, respectively, in terms of the
 more flexible built-in @(see event) macro, @(tsee assert-event), as follows.
 See @(see assert-event) for more detailed documentation.</p>

 @({
 (assert-event assertion
               :stobjs-out '(nil st)
               :ctx ''assert!-stobj)
 (assert-event assertion
               :stobjs-out '(nil st)
               :event event
               :ctx ''assert!-stobj)
 })")

(defmacro assert!-stobj (assertion st &optional event)
  `(assert-event ,assertion
                 :stobjs-out '(nil ,st)
                 ,@(and event `(:event ,event))
                 :ctx ''assert!-stobj))
