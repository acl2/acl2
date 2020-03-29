; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "irecursivep")
(include-book "ruler-extenders")
(include-book "ubody")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define recursive-calls ((fn symbolp) (wrld plist-worldp))
  :returns (calls-with-tests "A @(tsee pseudo-tests-and-call-listp).")
  :mode :program
  :parents (std/system/function-queries)
  :short "Recursive calls of a named non-mutually-recursive function,
          along with the controlling tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "For singly recursive logic-mode functions,
     this is similar to the result of @(tsee induction-machine),
     but each record has one recursive call (instead of zero or more),
     and there is exactly one record for each recursive call.")
   (xdoc::p
    "This utility works on both logic-mode and program-mode functions
     (if the program-mode functions have an @('unnormalized-body') property).
     This utility should not be called on a function that is
     mutually recursive with other functions;
     it must be called only on singly recursive functions,
     or on non-recursive functions (the result is @('nil') in this case).")
   (xdoc::p
    "This utility may be extended to handle also mutually recursive functions.")
   (xdoc::p
    "If the function is in logic mode and recursive,
     we obtain its ruler extenders and pass them to
     the built-in function @('termination-machine').
     Otherwise, we pass the default ruler extenders."))
  (b* ((ruler-extenders (if (and (logicp fn wrld)
                                 (irecursivep fn wrld))
                            (ruler-extenders fn wrld)
                          (default-ruler-extenders wrld))))
    (termination-machine
     nil nil ; loop$-recursion-checkep = nil --> arglists irrel
     (list fn) nil (ubody fn wrld) nil nil ruler-extenders)))
