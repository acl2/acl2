; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definedp ((fn symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries)
  :short "Check if a named logic-mode function is defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the function symbol has an @('unnormalized-body') property.")
   (xdoc::p
    "The built-in program-mode functions are defined
     but do not have an @('unnormalized-body') property.
     This is why this utility should only be used on logic-mode functions.")
   (xdoc::p
    "See @(tsee definedp+) for an enhanced variant of this utility."))
  (if (getpropc fn 'unnormalized-body nil wrld) t nil))
