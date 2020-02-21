; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "number-of-results")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define number-of-results+ ((fn symbolp) (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (n posp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee number-of-results)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee number-of-results),
     but it includes a run-time check (which should always succeed)
     on the result
     that allows us to prove a tighter return type theorem
     than @(tsee number-of-results)
     without strengthening the guard on @('wrld').
     Furthermore, this utility causes an error if called on a symbol
     that does not name a function.")
   (xdoc::p
    "The function must not be in @('*stobjs-out-invalid*'),
     because in that case its output stobjs,
     and therefore the number of its results,
     depend on how it is called.
     This condition is part of the guard of this utility."))
  (cond ((not (function-symbolp fn wrld))
         (prog2$ (raise "The symbol ~x0 does not name a function." fn)
                 1))
        (t (b* ((result (number-of-results fn wrld)))
             (if (posp result)
                 result
               (prog2$ (raise "Internal error: ~
                               the STOBJS-OUT property of ~x0 is empty."
                              fn)
                       1))))))
