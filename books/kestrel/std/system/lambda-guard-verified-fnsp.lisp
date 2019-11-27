; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "guard-verified-fnsp")
(include-book "pseudo-lambdap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-guard-verified-fnsp ((lambd pseudo-lambdap) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/term-queries)
  :short "Check if all the functions in a lambda expression
          are guard-verified."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of this function is consistent with
     the name of @(tsee guard-verified-fnsp).")
   (xdoc::p
    "Note that if @('lambd') includes @(tsee mbe),
     @('nil') is returned
     if any function inside the @(':logic') component of @(tsee mbe)
     is not guard-verified,
     even when @('lambd') could otherwise be fully guard-verified.
     See @(tsee lambda-guard-verified-exec-fnsp) for a similar utility
     that ignores the @(':logic') components of @(tsee mbe)s.")
  (guard-verified-fnsp (lambda-body lambd) wrld)
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))
