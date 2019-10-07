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
(include-book "pseudo-lambdap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define formals+ ((fn (or (function-namep fn wrld)
                          (pseudo-lambdap fn)))
                  (wrld plist-worldp-with-formals))
  :returns (formals symbol-listp)
  :parents (std/system)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee formals).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee formals) on named functions,
     but it has a stronger guard for named functions
     and includes a run-time check (which should always succeed) on the result
     that allows us to prove the return type theorem
     without strengthening the guard on @('wrld').")
   (xdoc::p
    "This utility also operates on lambda expressions,
     unlike @(tsee formals)."))
  (b* ((result (cond ((symbolp fn) (formals fn wrld))
                     (t (lambda-formals fn)))))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the formals ~x0 of ~x1 are not a true list of symbols."
             result fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))
