; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "thm-formula")
(include-book "theorem-symbolp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define thm-formula+ ((thm symbolp) (wrld plist-worldp))
  :returns (formula pseudo-termp)
  :parents (std/system/theorem-queries)
  :short "Enhanced variant of @(tsee thm-formula)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee thm-formula),
    but it includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    Furthermore, this utility causes an error if called on
    a symbol that does not name a theorem.")
  (if (not (theorem-symbolp thm wrld))
      (raise "The symbol ~x0 does not name a theorem." thm)
    (b* ((result (thm-formula thm wrld)))
      (if (pseudo-termp result)
          result
        (raise "Internal error: ~
                the FORMULA property ~x0 of ~x1 is not a pseudo-term."
               result thm)))))
