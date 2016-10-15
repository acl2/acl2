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

; This file provides utilities for
; the user interface of event-generating macros.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/event-forms" :dir :system)

(local (set-default-parents user-interface))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection user-interface
  :parents (kestrel-utilities system-utilities)
  :short "Utilities for the user interface of event-generating macros
          (e.g. program transformations).")

(define suppress-output ((form pseudo-event-formp))
  :returns (form-with-output-suppressed pseudo-event-formp)
  :short "Wrap the event form @('form')
          with a construct to suppress its output."
  `(with-output
     :gag-mode nil
     :off :all
     :on error
     ,form))

(define maybe-suppress-output (suppress (form pseudo-event-formp))
  :returns (form-with-output-maybe-suppressed pseudo-event-formp :hyp :guard)
  :short "If @('suppress') is non-@('nil'),
          wrap the event-form @('form') with a construct to suppress its output.
          Otherwise, just return @('form')."
  (if suppress
      (suppress-output form)
    form))

(defun maybe-unquote (x)
  (declare (xargs :guard t))
  (case-match x
    (('quote y) y)
    (& x)))

(define control-screen-output (verbose (form pseudo-event-formp))
  :returns (form-with-output-controlled pseudo-event-formp :hyp :guard)
  :short "Use the @('verbose') argument
          to control the screen output generated from the event form @('form')."
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

(define control-screen-output-and-maybe-replay
  ((verbose "@('T') (or @(''t')) or @('nil') (or @(''nil')), else indicates
             replay on failure.")
   (event-p "Make an event when true.")
   (form (pseudo-event-formp form)))
  :returns (new-form pseudo-event-formp :hyp (pseudo-event-formp form))
  :short "Variant of @(tsee control-screen-output)
          that can replay a failure verbosely."
  :long
  "<p>Usage:</p>

   @({
   (control-screen-output-and-maybe-replay verbose event-p form)
   })

   <p>where @('verbose') is not evaluated.</p>

   <p>If @('verbose') is @('t'), @(''t'), @('nil'), or @(''nil'), this is just
   @(tsee control-screen-output), and @(':event-p') is ignored.  So suppose
   otherwise for the rest of this documentation.</p>

   <p>In that case, @('(control-screen-output nil form)') is evaluated, and
   then if evaluation fails, @('(control-screen-output t form)') is
   subsequently evaluated so that the failure can be seen with more output.
   Moreover, the value of @(':event-p') is relevant, with the following two
   cases.</p>

   <ul>

   <li>For @(':event-p t'), the call of
   @('control-screen-output-and-maybe-replay') can go into a book, but @('form')
   must be a legal event form (see @(see embedded-event-form)).</li>

   <li>For @(':event-p nil'), the call of
   @('control-screen-output-and-maybe-replay') cannot go into a book, but
   @('form') need not be a legal event form.</li>

   </ul>"

  (let ((verbose (maybe-unquote verbose)))
    (cond ((booleanp verbose)
           (control-screen-output verbose form))
          (t
           (let ((form-nil (control-screen-output nil form))
                 (form-t (control-screen-output t form)))
             (cond
              (event-p
               `(make-event
                 '(:or ,form-nil
                       (with-output
                         :off :all
                         :on error
                         :stack :push
                         (progn
                           (value-triple (cw "~%===== VERBOSE REPLAY: =====~|"))
                           (with-output :stack :pop ,form-t))))))
              (t `(mv-let (erp val state)
                    ,form-nil
                    (cond (erp (prog2$ (cw "~%===== VERBOSE REPLAY: =====~|")
                                       ,form-t))
                          (t (value val)))))))))))

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
