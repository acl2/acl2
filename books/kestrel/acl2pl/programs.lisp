; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "packages")
(include-book "functions")

(include-book "kestrel/std/system/known-packages-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ programs
  :parents (acl2-programming-language)
  :short "A formalization of ACL2 programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we formalize an ACL2 program as consisting of
     a list of packages and a set of functions.
     This should suffice for our initial purposes,
     but we will extend this notion of ACL2 program as needed.")
   (xdoc::p
    "This notion of program captures
     part of the ACL2 environment in which ACL2 code executes.
     The list of packages captures the package definitions,
     in the order in which they appear in the ACL2 @(see world).
     The set of functions captures the function definitions,
     without considering their order in the ACL2 @(see world);
     note that, due to mutually recursive functions,
     we do not quite have a total ordering on functions in the @(see world),
     but rather a total ordering of mutually recursive function cliques."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod program
  :short "Fixtype of programs."
  ((packages package-list)
   (functions function-set))
  :layout :list
  :pred programp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-program ((fns symbol-listp) state)
  :returns (program programp)
  :short "Lift a program from the current ACL2 environment to the meta level."
  :long
  (xdoc::topstring
   (xdoc::p
    "We lift all the known packages,
     along with the functions specified by symbol.
     In general there are too many functions in the ACL2 environment,
     so we only lift the specified functions.
     Care must be exercised so that the list of functions is closed
     with respect to calls."))
  (b* ((packages (lift-package-list (known-packages+ state)))
       (functions (lift-function-list fns (w state))))
    (make-program :packages packages :functions functions)))
