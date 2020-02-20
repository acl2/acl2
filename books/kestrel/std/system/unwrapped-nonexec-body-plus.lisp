; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "formals-plus")
(include-book "non-executablep-plus")
(include-book "ubody-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unwrapped-nonexec-body+ ((fn symbolp) (wrld plist-worldp))
  :returns (unwrapped-body pseudo-termp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee unwrapped-nonexec-body)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee unwrapped-nonexec-body),
    but it is guard-verified
    and includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    This utility also includes a run-time check (which should always succeed)
    that the wrapper around the body has the expected form,
    via the built-in function @('throw-nonexec-error-p');
    this allows us to verify the guards
    without strengthening the guard of @('wrld').
    Furthermore, this utility causes an error
    if called on a symbol that does not name a function
    (the error is caused via the call to @(tsee non-executablep+)),
    or if the function is executable (i.e. @(':non-executable') is @('nil'),
    or if the function does not have an @('unnormalized-body')
    (which is retrieved and unwrapped).")
  (b* (((unless (non-executablep fn wrld))
        (raise "The function ~x0 is executable." fn))
       (body (ubody+ fn wrld))
       ((unless body)
        (raise "The function ~x0 does not have an unnormalized body." fn))
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
