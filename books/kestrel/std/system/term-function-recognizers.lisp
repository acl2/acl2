; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-lambdap")
(include-book "pseudo-lambda-listp")
(include-book "pseudo-termfnp")
(include-book "pseudo-termfn-listp")
(include-book "lambdap")
(include-book "lambda-listp")
(include-book "termfnp")
(include-book "termfn-listp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/term-function-recognizers
  :parents (std/system)
  :short "Recognizers of functions in terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "In translated @(see term)s,
     the `functions' that are applied to argument terms are
     function symbols and lambda expressions.")
   (xdoc::p
    "The built-in predicates @(tsee pseudo-termp) and @(tsee termp)
     recognize pseudo-terms and valid translated terms.
     The following predicates recognize
     lambda expressions in pseudo-terms and in valid translated terms,
     as well as functions (in the sense above)
     in pseudo-terms and in valid translated terms.")
   (xdoc::p
    "Note that the built-in predicate @(tsee symbolp) recognizes
     functions in pseudo-terms that are not lambda expressions,
     and that the predicate @(tsee function-symbolp) recognizes
     functions in valid translated terms that are not lambda expressions
     (the latter has guard @(tsee symbolp),
     so it must be actually preceded by a call of @(tsee symbolp)
     in guard-verified code).
     These predicates, with the ones below,
     provide ways to recognize all kinds of functions in terms.")))
