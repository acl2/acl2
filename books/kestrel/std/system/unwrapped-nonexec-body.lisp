; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
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
  :short "Body of a named logic-mode defined non-executable function,
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
    "This utility returns
     the unwrapped body of a logic-mode non-executable function @('fn'),
     by removing the wrapper shown above.")
   (xdoc::p
    "See @(tsee unwrapped-nonexec-body+) for
     a logic-friendly variant of this utility."))
  (fourth (ubody fn wrld)))
