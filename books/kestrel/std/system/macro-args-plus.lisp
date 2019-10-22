; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "macro-namep")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-args+ ((mac (macro-namep mac wrld))
                     (wrld plist-worldp))
  :returns (result true-listp)
  :parents (std/system/macro-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee macro-args).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee macro-args),
     but it has a stronger guard
     and includes a run-time check (which should always succeed) on the result
     that allows us to prove the return type theorem
     without strengthening the guard on @('wrld')."))
  (b* ((result (macro-args mac wrld)))
    (if (true-listp result)
        result
      (raise "Internal error: ~
              the MACRO-ARGS property ~x0 of ~x1 is not a true list."
             result mac))))
