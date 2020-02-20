; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "induction-machine")
(include-book "irecursivep-plus")

(include-book "system/pseudo-tests-and-calls-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define induction-machine+ ((fn symbolp) (wrld plist-worldp))
  :returns (result pseudo-tests-and-calls-listp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee induction-machine)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee induction-machine),
    but it includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    Furthermore, this utility causes an error if called on a symbol
    that does not name a singly recursive logic-mode function;
    the reason for ensuring logic-mode is that
    recursive program-mode functions do not have a measure;
    the reason for ensuring single recursion is that
    only singly-recursive functions have an induction machine.")
  (if (not (= (len (irecursivep+ fn wrld)) 1))
      (raise "The function ~x0 is not singly recursive." fn)
    (b* ((result (induction-machine fn wrld)))
      (if (pseudo-tests-and-calls-listp result)
          result
        (raise "Internal error: ~
                the INDUCTION-MACHINE property ~x0 of ~x1 ~
                does not have the expected form."
               result fn)))))
