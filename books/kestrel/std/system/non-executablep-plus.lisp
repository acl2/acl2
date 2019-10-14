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
(include-book "non-executablep")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define non-executablep+ ((fn (function-namep fn wrld))
                          (wrld plist-worldp))
  :returns (nonexec (or (booleanp nonexec) (eq nonexec :program)))
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee non-executablep).")
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee non-executablep),
    but it has a stronger guard
    and includes run-time checks (which should always succeed) on the result
    that allow us to prove the return type theorems
    without strengthening the guard on @('wrld').")
  (b* ((result (non-executablep fn wrld))
       ((unless (or (booleanp result)
                    (eq result :program)))
        (raise "Internal error: ~
                the non-executable status ~x0 of ~x1 is not ~
                T, NIL, or :PROGRAM."
               result fn))
       ((when (and (logicp fn wrld)
                   (eq result :program)))
        (raise "Internal error: ~
                the non-executable status of the logic-mode function ~x0 ~
                is :PROGRAM instead of T or NIL."
               fn)))
    result)
  ///

  (more-returns
   (nonexec booleanp
            :hyp (logicp fn wrld)
            :name booleanp-of-non-executablep+-when-logicp)))
