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

(define arity+ ((fn (pseudo-termfnp fn)) (wrld plist-worldp))
  :returns (arity natp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee arity)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee arity)
     on named functions and lambda expressions,
     but it causes an error on symbols that do not name functions
     (while @(tsee arity) returns @('nil') in this case).")
   (xdoc::p
    "Compared to @(tsee arity),
     @('arity+') has a slightly stronger guard on @('fn')
     but a weaker guard on @('wrld').
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
     with the only slight difference that, logically,
     we return 0 if @('fn') does not name a function
     (but in this case an error actually occurs),
     so that the return type theorem is simpler."))
  (cond ((flambdap fn) (len (lambda-formals fn)))
        (t (len (b* ((formals (getpropc fn 'formals t wrld)))
                  (if (eq formals t)
                      (raise "The symbol ~x0 does not name a function." fn)
                    formals)))))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp pseudo-lambdap))))
