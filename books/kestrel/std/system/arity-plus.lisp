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
                (wrld plist-worldp))
  :returns (result natp)
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee arity).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee arity)
     on named functions and lambda expressions,
     but it has a guard that is stronger on @('fn') but weaker on @('wrld').
     The reason for weakening the guard on @('wrld'),
     from @('plist-worldp-with-formals') to @(tsee plist-worldp)
     is a practical one:
     when doing system programming,
     currently @(tsee plist-worldp) is normally used for the ACL2 @(see world),
     so using @('plist-worldp-with-formals') in some system utilities
     (like @('arity+') here)
     would essentially force its use in many or all the other utilities.")
   (xdoc::p
    "Since @(tsee arity) has a stronger guard on the world,
     in order for @('arity+') to be guard-verified,
     it cannot call @(tsee arity).
     Thus, here we replicate the (simple) code of @(tsee arity),
     with the only slight difference that we return 0
     if @('fn') does not satisfy the guard."))
  (cond ((flambdap fn) (len (lambda-formals fn)))
        (t (len (getpropc fn 'formals t wrld))))
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))
