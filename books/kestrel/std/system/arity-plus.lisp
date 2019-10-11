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

(define arity+ ((fn (or (function-namep fn wrld)
                        (pseudo-lambdap fn)))
                (wrld plist-worldp-with-formals))
  :returns (result natp
                   :hyp (or (function-namep fn wrld) (pseudo-lambdap fn))
                   :hints (("Goal" :in-theory (enable arity pseudo-lambdap))))
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee arity).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee arity),
     but it has a stronger guard."))
  (arity fn wrld)
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))
