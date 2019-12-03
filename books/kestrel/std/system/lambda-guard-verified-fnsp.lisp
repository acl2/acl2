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
    "Note that if any function
     inside the @(':logic') component of an @(tsee mbe)
     or called via @(tsee ec-call)
     is not guard-verified,
     we return @('nil'),
     even when @('lambd') could otherwise be fully guard-verified.
     See @(tsee lambda-guard-verified-exec-fnsp) for a similar utility
     that ignores the guard verification status of functions
     in the @(':logic') components of @(tsee mbe)s
     or called via @(tsee ec-call)."))
  (guard-verified-fnsp (lambda-body lambd) wrld)
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))
