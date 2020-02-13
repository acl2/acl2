; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "irecursivep-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define measured-subset+ ((fn symbolp) (wrld plist-worldp))
  :returns (measured-subset symbol-listp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee measured-subset)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee measured-subset),
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
    recursive program-mode functions do not have a measured subset.")
  (if (not (irecursivep+ fn wrld))
      (raise "The function ~x0 is not recursive." fn)
    (b* ((justification (getpropc fn 'justification nil wrld))
         ((unless (weak-justification-p justification))
          (raise "Internal error: ~
                  the JUSTIFICATION property ~x0 of ~x1 is not well-formed."
                 justification fn))
         (measured-subset (access justification justification :subset))
         ((unless (symbol-listp measured-subset))
          (raise "Internal error: ~
                  the measured subset ~x0 of ~x1 is not a true list of symbols."
                 measured-subset fn)))
      measured-subset)))
