; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logic-function-namep")
(include-book "measure")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define measure+ ((fn (and (logic-function-namep fn wrld)
                           (recursivep fn nil wrld)))
                  (wrld plist-worldp))
  :returns (measure pseudo-termp)
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee measure).")
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee measure),
    but it has a stronger guard,
    is guard-verified,
    and includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    This utility also includes a run-time check (which should always succeed)
    on the form of the @('justification') property of the function
    that allows us to verify the guards
    without strengthening the guard of @('wrld').")
  (b* ((justification (getpropc fn 'justification nil wrld))
       ((unless (weak-justification-p justification))
        (raise "Internal error: ~
                the JUSTIFICATION property ~x0 of ~x1 is not well-formed."
               justification fn))
       (measure (access justification justification :measure))
       ((unless (pseudo-termp measure))
        (raise "Internal error: ~
                the measure ~x0 of ~x1 is not a pseudo-term."
               measure fn)))
    measure))
