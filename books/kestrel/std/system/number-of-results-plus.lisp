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
(include-book "number-of-results")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define number-of-results+ ((fn (function-namep fn wrld))
                            (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (n posp)
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee number-of-results).")
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee number-of-results),
    but it has a stronger guard
    and includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').")
  (b* ((result (number-of-results fn wrld)))
    (if (posp result)
        result
      (prog2$
       (raise "Internal error: ~
              the STOBJS-OUT property of ~x0 is empty."
              fn)
       1))))
