; User Interface
;
; Copyright (C) 2015-2016
;   Kestrel Institute (http://www.kestrel.edu)
;   Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides utilities for the user interface of macro libraries
; (e.g. transformations).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/system/event-forms" :dir :system)

(local (set-default-parents user-interface))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection user-interface
  :parents (kestrel-system-utilities system-utilities)
  :short
  "Utilities for the user interface of macro libraries (e.g. transformations).")

(define suppress-output ((form pseudo-event-formp))
  :returns (form-with-output-suppressed pseudo-event-formp)
  :short
  "Wrap the event form @('form') with a construct to suppress its output."
  `(with-output
     :gag-mode nil
     :off :all
     :on error
     ,form))

(define maybe-suppress-output (suppress (form pseudo-event-formp))
  :returns (form-with-output-maybe-suppressed pseudo-event-formp :hyp :guard)
  :short
  "If @('suppress') is non-@('nil'),
  wrap the event-form @('form') with a construct to suppress its output.
  Otherwise, just return @('form')."
  (if suppress
      (suppress-output form)
    form))

(define control-screen-output (verbose (form pseudo-event-formp))
  :returns (form-with-output-controlled pseudo-event-formp :hyp :guard)
  :short
  "Use the @('verbose') argument
  to control the screen output generated from the event form @('form')."
  :long
  "<p>
  If @('verbose') is not @('nil'), keep all screen output.
  If @('verbose') is @('nil'), suppress all non-error screen output.
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
  (cond (verbose form)
        (t `(with-output
              :gag-mode nil
              :off :all
              :on error
              ,form))))

(defsection cw-event
  :short "Event form of @(tsee cw)."
  :long
  "<p>
  When this macro is processed as an event,
  its arguments are passed to @(tsee cw).
  </p>
  @(def cw-event)"
  (defmacro cw-event (str &rest args)
    `(value-triple (cw ,str ,@args))))
