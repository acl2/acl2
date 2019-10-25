; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "definedp-plus")
(include-book "logic-function-namep")
(include-book "ubody")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubody+ ((fn (or (and (logic-function-namep fn wrld)
                             (definedp fn wrld))
                        (pseudo-lambdap fn)))
                (wrld plist-worldp))
  :returns (body pseudo-termp
                 :hyp (or (symbolp fn) (pseudo-lambdap fn))
                 :hints (("Goal" :in-theory (enable pseudo-lambdap))))
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee ubody).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee ubody),
     but it has a stronger guard
     and includes a run-time check (which should always succeed) on the result
     that allows us to prove the return type theorem
     without strengthening the guard on @('wrld').")
   (xdoc::p
    "Some program-mode functions may be defined
     but not have an @('unnormalized-body') property."))
  (b* ((result (ubody fn wrld)))
    (if (pseudo-termp result)
        result
      (raise "Internal error: ~
              the unnormalized body ~x0 of ~x1 is not a pseudo-term."
             result fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp))))
