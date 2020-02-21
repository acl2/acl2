; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irecursivep ((fn symbolp) (wrld plist-worldp))
  :returns (clique "A @(tsee symbol-listp).")
  :parents (std/system/function-queries)
  :short "List of mutually recursive functions of which
          the specified named function is a member,
          based on the @(tsee defun) form that introduced this function,
          or @('nil') if the specified function is not recursive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(tsee recursivep)
     with @('nil') as the second argument:
     the @('i') that starts the name of @('irecursivep') conveys that
     the result is based on the @(tsee defun) form that
     <i>introduced</i> @('fn').")
   (xdoc::p
    "See @(tsee irecursivep+) for an enhanced variant of this utility."))
  (recursivep fn nil wrld))
