; Standard System Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "irecursivep-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-ruler-extenders+ ((fn symbolp) (wrld plist-worldp))
  :returns (ruler-extenders (or (symbol-listp ruler-extenders)
                                (equal ruler-extenders :all)))
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee get-ruler-extenders)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee get-ruler-extenders),
    but it is guard-verified
    and includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    This utility also includes a run-time check (which should always succeed)
    on the form of the @('justification') property of the function
    that allows us to verify the guards
    without strengthening the guard of @('wrld').
    Furthermore, this utility causes an error if called on a symbol
    that does not name a recursive logic-mode function;
    the reason for ensuring logic-mode is that
    recursive program-mode functions do not have ruler extenders.")
  (if (not (irecursivep+ fn wrld))
      (raise "The function ~x0 is not recursive." fn)
    (b* ((justification (getpropc fn 'justification nil wrld))
         ((unless (weak-justification-p justification))
          (raise "Internal error: ~
                  the 'JUSTIFICATION property ~x0 of ~x1 is not well-formed."
                 justification fn))
         (ruler-extenders (access justification justification :ruler-extenders))
         ((unless (or (symbol-listp ruler-extenders)
                      (eq ruler-extenders :all)))
          (raise "Internal error: ~
                  the well-founded relation ~x0 of ~x1 ~
                  is neither a true list of symbols nor :ALL."
                 ruler-extenders fn)))
      ruler-extenders)))
