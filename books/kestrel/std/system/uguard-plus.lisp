; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "function-namep")
(include-book "uguard")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uguard+ ((fn (or (function-namep fn wrld)
                         (pseudo-lambdap fn)))
                 (wrld plist-worldp))
  :returns (guard pseudo-termp)
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee uguard).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee uguard),
     but it has a stronger guard
     and includes a run-time check (which should always succeed) on the result
     that allows us to prove the return type theorem
     without strengthening the guard on @('wrld')."))
  (b* ((result (uguard fn wrld)))
    (if (pseudo-termp result)
        result
      (raise "Internal error: ~
              the guard ~x0 of ~x1 is not a pseudo-term."
             result fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp))))
