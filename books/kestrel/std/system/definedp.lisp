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

(define definedp ((fn symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries)
  :short "Check if a named logic-mode function is defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the function symbol has an @('unnormalized-body') property.")
   (xdoc::p
    "Some program-mode functions may be defined
     but not have an @('unnormalized-body') property.")
   (xdoc::p
    "See @(tsee definedp+) for an enhanced variant of this utility."))
  (if (getpropc fn 'unnormalized-body nil wrld) t nil))
