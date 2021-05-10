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

(define table-alist+ ((name symbolp) (wrld plist-worldp))
  :returns (alist alistp)
  :parents (std/system)
  :short "Enhanced variant of @(tsee table-alist)."
  :long
  (xdoc::topstring-p
   "This returns the same result as the built-in @(tsee table-alist) function
    (see the ACL2 system sources),
    but it includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').")
  (b* ((result (table-alist name wrld)))
    (if (alistp result)
        result
      (raise "Internal error: ~
              the TABLE-ALIST property ~x0 of ~x1 is not an alist."
             result name))))
