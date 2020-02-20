; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ubody")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unwrapped-nonexec-body ((fn symbolp) (wrld plist-worldp))
  :returns (unwrapped-body "A @(tsee pseudo-termp).")
  :verify-guards nil
  :parents (std/system/function-queries)
  :short "Body of a non-executable defined named function,
          without the ``non-executable wrapper''."
  :long
  (xdoc::topstring
   (xdoc::p
    "@(tsee defun-nx) generates
     a logic-mode function whose body is wrapped as follows:")
   (xdoc::codeblock
    "(return-last 'progn"
    "             (throw-nonexec-error 'fn"
    "                                  (cons arg1 ... (cons argN 'nil)...))"
    "             body)")
   (xdoc::p
    "If @(tsee defun) is used for a logic-mode function with "
    (xdoc::seetopic "non-executable" "@(':non-executable')")
    " set to @('t'),
     the submitted body (once translated) must be wrapped as above.")
   (xdoc::p
    "It is also possible to use @(tsee defun) to introduce
     program-mode functions with @(':non-executable') set to @(':program'),
     in which case the body must be wrapped as above.
     (These @(tsee defun)s are introduced via @(tsee defproxy).)")
   (xdoc::p
    "This utility returns
     the unwrapped body of a logic-mode or program-mode
     defined non-executable function @('fn'),
     by removing the wrapper shown above.
     Here, `defined' means that the function has
     an @('unnormalized-body') property,
     which is retrieved and unwrapped.")
   (xdoc::p
    "See @(tsee unwrapped-nonexec-body+) for
     an enhanced variant of this utility."))
  (fourth (ubody fn wrld)))
