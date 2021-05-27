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
; Starting late April 2021, when assert-event became more full-featured and
; ceased using safe-mode by default, assert! became a trivial wrapper for
; certain calls of assert-event.

(defxdoc assert!
  :parents (std/testing assert-event errors)
  :short "@(see Event) variant of @(tsee assert$) that abbreviates @(tsee assert-event)"
  :long "<p>The @('assert!') macro is similar to @(tsee assert$), in that both
 check that a given form evaluates to a non-@('nil') value.  However, calls of
 @('assert!')  may appear as top-level @(see events) in @(see books) and @(see
 encapsulate) forms.  Indeed, calls of @('assert!') directly abbreviate
 corresponding calls of the built-in @(see event) macro, @(tsee assert-event).
 You may find it more convenient to use @(tsee assert-event), which has more
 options.  In particular, with @('assert-event') the assertion need not return
 a single, non-@(see stobj) value.</p>

 <p>See @(see assert$) and @(see assert*) for assertion-checking utilities to
 use in programs.</p>

 <p>Example Forms:</p>

 @({
 (assert! (equal 3 3))
 (assert! (null (@ ld-skip-proofsp)))
 (assert! (equal 3 3)
          (defun f (x) (cons x x)))
 })

 <p>General Forms:</p>

 @({
 (assert! assertion)
 (assert! assertion event)
 })

 <p>where @('assertion') evaluates to a single non-@('stobj') value and
 @('event'), if supplied and non-@('nil'), is an @(see event) to be evaluated
 if the value of @('assertion') is not @('nil').  It is an error if that value
 is @('nil').  As noted above, a call of @('assert!') is an @(see event): it
 can go into a book or an @(tsee encapsulate) or @(tsee progn) event.</p>

 <p>Calls of @('assert!') skip evaluation of the given assertion when proofs
 are being skipped: during @(tsee include-book), during the second pass of an
 @(tsee encapsulate) event, and after evaluating @('(set-ld-skip-proofsp t
 state)').</p>

 <p>The two General Forms above may be expressed, respectively, in terms of the
 more flexible built-in @(see event) macro, @(tsee assert-event), as follows.
 See @(see assert-event) for more detailed documentation.</p>

 @({
 (assert-event assertion
               :ctx ''assert!)
 (assert-event assertion
               :event event
               :ctx ''assert!)
 })")

(defmacro assert! (assertion &optional event)
  `(assert-event ,assertion
                 ,@(and event `(:event ,event))
                 :ctx ''assert!))
