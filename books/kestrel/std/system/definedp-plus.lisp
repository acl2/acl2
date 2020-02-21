; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "definedp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definedp+ ((fn symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee definedp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee definedp),
     but it causes an error if called on a symbol
     that does not name a logic-mode function.
     The reason for ensuring logic mode is that this utility
     checks whether the function has an @('unnormalized body') property,
     but some program-mode functions may be defined
     without having an @('unnormalized-body') property."))
  (cond ((not (function-symbolp fn wrld))
         (raise "The symbol ~x0 does not name a function." fn))
        ((not (logicp fn wrld))
         (raise "The function ~x0 is not in logic mode." fn))
        (t (definedp fn wrld)))
  ///

  (defthmd function-symbolp-when-definedp+
    (implies (definedp+ fn wrld)
             (function-symbolp fn wrld)))

  (defthmd logicp-when-definedp+
    (implies (definedp+ fn wrld)
             (logicp fn wrld))))
