; Event Macros Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection make-event-terse
  :parents (event-macros make-event)
  :short "A variant of @(tsee make-event) with terser screen output."
  :long
  (xdoc::topstring
   (xdoc::p
    "We wrap a normal @(tsee make-event)
     in a @(tsee with-output) that removes all the screen output
     except possibly errors and except comments.
     We also suppress the concluding error message of @(tsee make-event)
     (when an error occurs),
     via @(':on-behalf-of :quiet!').")
   (xdoc::p
    "The @(':suppress-errors') argument
     determines whether errors should be also suppressed or not.
     If this argument is @('nil') (the default),
     errors are not suppressed,
     but they are not enabled either;
     that is, they retain the ``status'' they had before.
     If this argument is non-@('nil') instead, errors are suppressed;
     @('make-event-terse') will fail silently in case of an error,
     so errors should not be suppressed in normal circumstances.")
   (xdoc::p
    "The reason why comments
     (i.e. the kinds of outputs represented by @('comment') in "
    (xdoc::seetopic "set-inhibit-output-lst" "this list")
    ") are not suppressed is that
     the event macros that use @('make-event-terse')
     normally support the "
    (xdoc::seetopic "evmac-input-print-p" "the @(':print') input")
    ", which uses comment output for @(':result') and @(':info').
     Thus, these event macro outputs are controlled by @(':print'),
     and should not be suppressed by @('make-event-terse').")
   (xdoc::p
    "We save, via @(':stack :push'), the current status of the outputs,
     so that, inside the form passed to @('make-event-terse'),
     the saved output status can be selectively restored for some sub-forms.
     The saved output status can be restored
     via @('(with-output :stack :pop ...)'),
     or by using the @(tsee restore-output)
     or @(tsee restore-output?) utilities.")
   (xdoc::p
    "Currently @('make-event-terse') does not support
     @(tsee make-event)'s @(':check-expansion') and @(':expansion?'),
     but it could be extended to support them
     and pass them to @(tsee make-event).")
   (xdoc::@def "make-event-terse"))

  (defmacro make-event-terse (form &key (suppress-errors 'nil))
    `(with-output
       :gag-mode nil
       :off ,(if suppress-errors
                 (remove-eq 'comment *valid-output-names*)
               (set-difference-eq *valid-output-names* '(error comment)))
       :stack :push
       (make-event ,form :on-behalf-of :quiet!))))
