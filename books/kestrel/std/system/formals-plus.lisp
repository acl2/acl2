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

(define formals+ ((fn pseudo-termfnp) (wrld plist-worldp))
  :returns (formals symbol-listp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee formals)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee formals) on named functions,
     but it includes a run-time check (which should always succeed)
     on the result
     that allows us to prove the return type theorem
     without strengthening the guard on @('wrld').")
   (xdoc::p
    "Similarly to @(tsee formals),
     this utility causes an error if called on a symbol
     that does not name a function.
     But the error message is slightly different
     from the one of @(tsee formals).")
   (xdoc::p
    "This utility also operates on lambda expressions,
     unlike @(tsee formals)."))
  (b* ((result (if (symbolp fn)
                   (b* ((formals (getpropc fn 'formals t wrld)))
                     (if (eq formals t)
                         (raise "The symbol ~x0 does not name a function." fn)
                       formals))
                 (lambda-formals fn))))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the formals ~x0 of ~x1 are not a true list of symbols."
             result fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp pseudo-lambdap))))
