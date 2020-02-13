; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-termfnp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uguard ((fn pseudo-termfnp) (wrld plist-worldp))
  :returns (guard "A @(tsee pseudo-termp).")
  :parents (std/system/function-queries)
  :short "Unoptimized guard of a named function or of a lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of "
    (xdoc::seetopic "system-utilities" "@('guard')")
    " with @('nil') as the second argument.
     Since @(tsee guard) is in program mode only because of
     the code that handles the case in which
     the second argument is non-@('nil'),
     we avoid calling @(tsee guard) and instead replicate
     the code that handles the case in which the second argument is @('nil');
     thus, this utility is in logic mode and guard-verified.")
   (xdoc::p
    "See @(tsee uguard+) for an enhanced variant of this utility."))
  (cond ((symbolp fn) (getpropc fn 'guard *t* wrld))
        (t *t*)))
