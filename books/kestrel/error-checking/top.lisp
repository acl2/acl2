; Error Checking Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "def-error-checker")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc error-checking
  :parents (kestrel-books errors)
  :short "A library of utilities for error checking."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each error checking function in this library
     causes a "
    (xdoc::seetopic "er" "soft error")
    ", with an informative message,
     and optionally informative error flag and value,
     when certain conditions are not satisified.
     These error checking functions are useful, for instance,
     to programmatically validate inputs of "
    (xdoc::seetopic "event-macros" "event macros")
    ", providing the informative error messages to the user.
     The informative error flags and values are useful
     when event macros are invoked programmatically,
     to enable the caller to take appropriate actions
     based on the nature of the error,
     as with an exception mechanism.")
   (xdoc::p
    "Inside @(tsee b*), the "
    (xdoc::seetopic "patbind-er" "@('er') binder")
    " can be used with calls to these error checking functions.")
   (xdoc::p
    "These error checking functions include @(tsee msgp) parameters
     to describe the values being checked in error message.
     When these functions are called,
     the strings in the description parameters
     should be capitalized based on where they occur in the error messages.")
   (xdoc::p
    "These error checking functions are being moved
     from @('[books]/kestrel/utilities/error-checking/')
     to @('[books]/kestrel/error-checking'),
     and are being refactored and improved in the process.")))
