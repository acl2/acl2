; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "macro-symbolp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-args+ ((mac symbolp) (wrld plist-worldp))
  :returns (result true-listp)
  :parents (std/system/macro-queries)
  :short "Enhanced variant of @(tsee macro-args)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee macro-args),
     but it has a run-time check (which should always succeed) on the result
     that allows us to prove the return type theorem
     without strengthening the guard on @('wrld').
     Furthermore, this utility causes an error
     if called on a symbol that does not name a macro."))
  (if (not (macro-symbolp mac wrld))
      (raise "The symbol ~x0 does not name a macro." mac)
    (b* ((result (macro-args mac wrld)))
      (if (true-listp result)
          result
        (raise "Internal error: ~
                the MACRO-ARGS property ~x0 of ~x1 is not a true list."
               result mac)))))
