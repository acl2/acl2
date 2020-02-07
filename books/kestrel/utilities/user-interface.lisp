; User Interface
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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

(defsection cw-event
  :parents (user-interface)
  :short "Event form of @(tsee cw)."
  :long
  "<p>
   When this macro is processed as an event,
   its arguments are passed to @(tsee cw).
   Exception: No printing is done while including
   a book or during the second pass of an
   @(tsee encapsulate) event.
   </p>
   @(def cw-event)"
  (defmacro cw-event (str &rest args)
    `(value-triple (cw ,str ,@args)
                   :on-skip-proofs :interactive)))

(defsection make-event-terse
  :parents (user-interface make-event)
  :short "A variant of @(tsee make-event) with terser screen output."
  :long
  "<p>
   We wrap a normal @(tsee make-event)
   in a @(tsee with-output) that removes all the screen output
   except possibly errors.
   We also suppress the concluding error message of @(tsee make-event)
   (when an error occurs),
   via @(':on-behalf-of :quiet!').
   </p>
   <p>
   The @(':suppress-output') argument
   determines whether errors should be also suppressed or not.
   If this argument is @('nil') (the default),
   errors are not suppressed,
   but they are not enabled either;
   that is, they retain the suppression status they had before.
   If this argument is non-@('nil'), errors are suppressed;
   @('make-event-terse') will fail silently in case of an error,
   so errors should not be suppressed in normal circumstances.
   </p>
   <p>
   We save, via @(':stack :push'), the current status of the outputs,
   so that, inside the form passed to @('make-event-terse'),
   that output status can be selectively restored for some sub-forms.
   That output status can be restored via @('(with-output :stack :pop ...)'),
   or by using the @(tsee restore-output) or @(tsee restore-output?) utilities.
   </p>
   <p>
   Currently @('make-event-terse') does not support
   @(tsee make-event)'s @(':check-expansion') and @(':expansion?'),
   but it could be extended to support them and pass them to @(tsee make-event).
   </p>
   <p>
   @('make-event-terse') may be useful in event-generating macros.
   </p>
   @(def make-event-terse)"
  (defmacro make-event-terse (form &key (suppress-errors 'nil))
    `(with-output
       :gag-mode nil
       :off ,(if suppress-errors
                 :all
               (remove-eq 'error *valid-output-names*))
       :stack :push
       (make-event ,form :on-behalf-of :quiet!))))

(define restore-output ((form pseudo-event-formp))
  :returns (form-with-output-restored pseudo-event-formp)
  :parents (user-interface)
  :short "Wrap a form to have it produce screen output
          according to previously saved screen output settings."
  :long
  "<p>
   This wraps the form in a @('(with-output :stack :pop ...)').
   It can be used on a sub-form
   of the form passed to a @(tsee make-event-terse).
   </p>"
  `(with-output :stack :pop ,form))

(define restore-output? ((yes/no booleanp) (form pseudo-event-formp))
  :returns (form-maybe-with-output-restored pseudo-event-formp
                                            :hyp (pseudo-event-formp form))
  :parents (user-interface)
  :short "Conditionally wrap a form to have it produce screen output
          according to previously saved screen output settings."
  :long
  "<p>
   This leaves the form unchanged if the boolean is @('nil'),
   otherwise it calls @(tsee restore-output) on it.
   </p>"
  (if yes/no
      (restore-output form)
    form))

(defsection fail-event
  :parents (user-interface)
  :short "An event that always fails
          with a specified error context, flag, value, and message."
  :long
  "<p>
   This is realized by always generating a soft error (via @(tsee er-soft+))
   during the expansion phase of @(tsee make-event).
   The error context, flag, value, and message passed to this macro
   are not evaluated.
   </p>
   <p>
   The use of @(tsee make-event-terse) instead of @(tsee make-event)
   avoids any screen output other than the specified error message.
   </p>
   <p>
   This macro is used by @(tsee try-event).
   </p>
   @(def fail-event)"
  (defmacro fail-event (ctx erp val msg)
    (declare (xargs :guard (msgp msg)))
    `(make-event-terse (er-soft+ ',ctx ',erp ',val "~@0" ',msg))))

(define try-event (form ctx erp val (msg msgp))
  :returns (event pseudo-event-formp)
  :parents (user-interface)
  :short "Try to submit an event,
          generating a customized error if the submission fails."
  :long
  "<p>
   This is useful to &ldquo;replace&rdquo; the error generated by an event
   (e.g. a @(tsee defun) or a @(tsee defthm))
   with a customized soft error.
   The event is submitted with all output off (including error output),
   so there is no output if the submission succeeds.
   If the submission fails,
   @(tsee orelse) is used to submit a @(tsee fail-event) to cause an error
   with the specified context, flag, value, and message.
   </p>"
  `(orelse
    (with-output :gag-mode nil :off :all ,form)
    (fail-event ,ctx ,erp ,val ,msg)))
