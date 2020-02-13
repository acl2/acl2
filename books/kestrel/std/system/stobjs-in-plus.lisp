; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stobjs-in+ ((fn symbolp) (wrld plist-worldp))
  :returns (result symbol-listp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee stobjs-in)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee stobjs-in),
    but it includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    Furthermore, this utility causes an error if called on a symbol
    that does not name a function.")
  (if (not (function-symbolp fn wrld))
      (raise "The symbol ~x0 does not name a function." fn)
    (b* ((result (stobjs-in fn wrld)))
      (if (symbol-listp result)
          result
        (raise "Internal error: ~
                the STOBJS-IN property ~x0 of ~x1 ~
                is not a true list of symbols."
               result fn)))))
