; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-termfnp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubody ((fn pseudo-termfnp) (wrld plist-worldp))
  :returns (body "A @(tsee pseudo-termp).")
  :parents (std/system)
  :short "Unnormalized body of a named function,
          or body of a lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of the built-in @(tsee body)
     with @('nil') as the second argument.
     Since @(tsee body) is not guard-verified only because of
     the code that handles the case
     in which the second argument is non-@('nil'),
     we avoid calling @(tsee body) and instead replicate
     the (simple) code that handles the case
     in which the second argument is @('nil');
     thus, this utility is guard-verified.")
   (xdoc::p
    "The unnormalized body of a named function
     is its @('unnormalized-body') property.
     If a function is not defined, this property is @('nil').
     Note that some program-mode functions may be defined
     but not have an @('unnormalized-body') property.")
   (xdoc::p
    "See @(tsee ubody+) for a logic-friendly variant of this utility."))
  (cond ((symbolp fn) (getpropc fn 'unnormalized-body nil wrld))
        (t (lambda-body fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp pseudo-lambdap))))
