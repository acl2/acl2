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
(include-book "formals-plus")
(include-book "logic-function-namep")
(include-book "non-executablep")
(include-book "ubody-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unwrapped-nonexec-body+ ((fn (and (logic-function-namep fn wrld)
                                          (definedp fn wrld)
                                          (non-executablep fn wrld)))
                                 (wrld plist-worldp-with-formals))
  :returns (unwrapped-body pseudo-termp)
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee unwrapped-nonexec-body).")
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee unwrapped-nonexec-body),
    but it has a stronger guard,
    is guard-verified,
    and includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    This utility also includes a run-time check (which should always succeed)
    that the wrapper around the body has the expected form,
    via the built-in function @('throw-nonexec-error-p');
    this allows us to verify the guards
    without strengthening the guard of @('wrld').")
  (b* ((body (ubody+ fn wrld))
       ((unless (and (throw-nonexec-error-p body fn (formals+ fn wrld))
                     (consp (cdddr body))))
        (raise "Internal error: ~
                the body ~x0 of the non-executable function ~x1 ~
                does not have the expected wrapper."
               body fn))
       (unwrapped-body (fourth body))
       ((unless (pseudo-termp unwrapped-body))
        (raise "Internal error: ~
                the unwrapped body ~x0 of the non-executable function ~x1 ~
                is not a pseudo-term."
               unwrapped-body fn)))
    unwrapped-body))
