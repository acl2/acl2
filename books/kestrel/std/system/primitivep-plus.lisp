; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "primitivep")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitivep+ ((fn symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee primitivep)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee primitivep),
     but it causes an error if called on a symbol
     that does not name a function.
     This check requires an extra @(see world) argument
     (compared to @(tsee primitivep)),
     which is usually available when doing system programming."))
  (if (not (function-symbolp fn wrld))
      (raise "The symbol ~x0 does not name a function." fn)
    (primitivep fn)))
