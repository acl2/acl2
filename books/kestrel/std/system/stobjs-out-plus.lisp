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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stobjs-out+ ((fn (function-namep fn wrld))
                     (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (result symbol-listp)
  :parents (world-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee stobjs-out).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee stobjs-out),
     but it has a stronger guard
     and includes a run-time check (which should always succeed) on the result
     that allows us to prove the return type theorem
     without strengthening the guard on @('wrld').")
   (xdoc::p
    "The function must not be in @('*stobjs-out-invalid*'),
     because in that case its output stobjs depend on how it is called."))
  (b* ((result (stobjs-out fn wrld)))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the STOBJS-OUT property ~x0 of ~x1 is not a true list of symbols."
             result fn))))
