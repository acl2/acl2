; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "uguard")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uguard+ ((fn pseudo-termfnp) (wrld plist-worldp))
  :returns (guard pseudo-termp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee uguard)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee uguard),
    but it includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    Furthermore, this utility causes an error if called on
    a symbol that does not name a function.")
  (if (and (symbolp fn)
           (not (function-symbolp fn wrld)))
      (raise "The symbol ~x0 does not name a function." fn)
    (b* ((result (uguard fn wrld)))
      (if (pseudo-termp result)
          result
        (raise "Internal error: ~
                the guard ~x0 of ~x1 is not a pseudo-term."
               result fn)))))
