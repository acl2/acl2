; User Interface
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2017 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/pseudo-event-formp" :dir :system)
(include-book "maybe-unquote")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection user-interface
  :parents (kestrel-utilities system-utilities-non-built-in)
  :short "Utilities for the user interface of event-generating macros
          (e.g. program transformations).")

(define suppress-output ((form pseudo-event-formp))
  :returns (form-with-output-suppressed pseudo-event-formp)
  :parents (user-interface)
  :short "Wrap an event form with a construct to suppress its output."
  `(with-output
     :gag-mode nil
     :off :all
     :on error
     ,form))

(define maybe-suppress-output (suppress (form pseudo-event-formp))
  :returns (form-with-output-maybe-suppressed pseudo-event-formp :hyp :guard)
  :parents (user-interface)
  :short "Conditionally wrap an event form
          with a construct to suppress its output."
  :long
  "<p>
   If @('suppress') is non-@('nil'),
   wrap the event-form @('form') with a construct to suppress its output.
   Otherwise, just return @('form').
   </p>"
  (if suppress
      (suppress-output form)
    form))

; The following function should probably be completely replaced by
; manage-screen-output, below.  The key difference is that
; control-screen-output will show error output even if it is suppressed
; globally, while manage-screen output respects the case of global suppression
; by avoiding the production of error output.
(define control-screen-output (verbose (form pseudo-event-formp))
  :returns (form-with-output-controlled pseudo-event-formp :hyp :guard)
  :parents (user-interface)
  :short "Control the screen output generated from an event form."
  :long
  "<p>
   If @('verbose') is not @('nil') or @(''nil'), keep all screen output.
   If @('verbose') is @('nil') or @(''nil'), suppress all non-error screen
   output.
   </p>
   <p>
   This function can be used in a macro of the following form:
   @({
     (defmacro mac (... &key verbose ...)
       (control-screen-output verbose `(make-event ...)))
   })
   Invoking @('mac') at the ACL2 top-level will submit the event,
   with the screen output controlled by @('verbose').
   </p>"
  (cond ((maybe-unquote verbose) form)
        (t `(with-output
              :gag-mode nil
              :off :all
              :on error
              ,form))))

(define manage-screen-output-aux (verbose (form pseudo-event-formp) bangp)
  :returns (form-with-output-managed pseudo-event-formp :hyp :guard)
  (cond ((maybe-unquote verbose) form)
        (t (let ((output-names (remove1 'error *valid-output-names*)))
             `(,(if bangp 'with-output! 'with-output)
               :off ,output-names
               :gag-mode nil
               ,form)))))

(define manage-screen-output (verbose (form pseudo-event-formp))
  :returns (form-with-output-managed pseudo-event-formp :hyp :guard)
  :parents (user-interface)
  :short "Manage the screen output generated from an event form."
  :long
  "<p>
   If @('verbose') is not @('nil') or @(''nil'), keep all screen output.
   If @('verbose') is @('nil') or @(''nil'), suppress all non-error screen
   output.
   </p>
   <p>
   This function can be used in a macro of the following form:
   @({
     (defmacro mac (... &key verbose ...)
       (manage-screen-output verbose `(make-event ...)))
   })
   Invoking @('mac') at the ACL2 top-level will submit the event,
   with the screen output managed by @('verbose').
   </p>
   <p>
   Note that if @('form') is an event (see @(see embedded-event-form)), then
   @('(manage-screen-output verbose form)') evaluates to an event.
   </p>"
  (manage-screen-output-aux verbose form nil))
