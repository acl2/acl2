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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irecursivep+ ((fn symbolp) (wrld plist-worldp))
  :returns (clique symbol-listp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee irecursivep)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee irecursivep),
    but it includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    Furthermore, this utility causes an error if called on a symbol
    that does not name a logic-mode function;
    the reason for ensuring logic mode is that this utility
    looks at the @('recursivep') property,
    which is always @('nil') for program-mode functions
    (i.e. it is set only for logic-mode functions).")
  (cond ((not (function-symbolp fn wrld))
         (raise "The symbol ~x0 does not name a function." fn))
        ((not (logicp fn wrld))
         (raise "The function ~x0 is not in logic mode." fn))
        (t (b* ((result (irecursivep fn wrld)))
             (if (symbol-listp result)
                 result
               (raise "Internal error: ~
                       the RECURSIVEP property ~x0 of ~x1 ~
                       is not a true list of symbols."
                      result fn))))))
