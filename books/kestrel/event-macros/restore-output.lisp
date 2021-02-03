; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "system/pseudo-event-formp" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restore-output ((event pseudo-event-formp))
  :returns (new-event pseudo-event-formp)
  :parents (event-macros)
  :short "Wrap an event form to have it produce screen output
          according to previously saved screen output settings."
  :long
  (xdoc::topstring-p
   "This wraps the form in a @('(with-output :stack :pop ...)').
    Among other possible uses, this can be used on a sub-form
    of the form passed to a @(tsee make-event-terse).")
  `(with-output :stack :pop ,event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restore-output? ((yes/no booleanp) (event pseudo-event-formp))
  :returns (new-event pseudo-event-formp
                      :hyp (pseudo-event-formp event)
                      :hints (("Goal" :in-theory (disable pseudo-event-formp))))
  :parents (event-macros)
  :short "Conditionally wrap an event form to have it produce screen output
          according to previously saved screen output settings."
  :long
  (xdoc::topstring-p
   "This leaves the form unchanged if the boolean is @('nil'),
    otherwise it calls @(tsee restore-output) on it.")
  (if yes/no
      (restore-output event)
    event))
