; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "definedp")
(include-book "logic-function-namep")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definedp+ ((fn (logic-function-namep fn wrld)) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee definedp).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee definedp),
     but it has a stronger guard.")
   (xdoc::p
    "Some program-mode functions may be defined
     but not have an @('unnormalized-body') property."))
  (definedp fn wrld))
