; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "known-packages")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define known-packages+ (state)
  :returns (pkg-names string-listp)
  :parents (std/system)
  :short "Enhanced variant of @(tsee known-packages)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee known-packages),
    but it includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('state').")
  (b* ((result (known-packages state)))
    (if (string-listp result)
        result
      (raise "Internal error: ~
              the list of keys ~x0 of the alist of known packages ~
              is not a true list of strings."
             result))))
