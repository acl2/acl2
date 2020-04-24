; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-event-terse")

(include-book "kestrel/utilities/er-soft-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fail-event
  :parents (event-macros)
  :short "An event that always fails
          with a specified error context, flag, value, and message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is realized by always generating a soft error (via @(tsee er-soft+))
     during the expansion phase of @(tsee make-event).
     The error context, flag, value, and message passed to this macro
     are not evaluated.")
   (xdoc::p
    "The use of @(tsee make-event-terse) instead of @(tsee make-event)
     avoids any screen output other than the specified error message.")
   (xdoc::p
    "This macro is used by @(tsee try-event).")
   (xdoc::@def "fail-event"))

  (defmacro fail-event (ctx erp val msg)
    (declare (xargs :guard (msgp msg)))
    `(make-event-terse (er-soft+ ',ctx ',erp ',val "~@0" ',msg))))
