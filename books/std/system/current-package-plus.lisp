; Standard System Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define current-package+ (state)
  :returns (package stringp)
  :parents (std/system)
  :short "Logic-friendly wrapper of the built-in @(tsee current-package)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee current-package),
     but it has a run-time check (which should always succeed) on the result
     that allows us to prove the return type theorems
     without strengthening the guard on @('state')."))
  (b* ((package (current-package state))
       ((unless (and (stringp package)
                     (not (equal package ""))))
        (raise "Internal error: ~
                current package ~x0 is not a non-empty string."
               package)
        "irrelevant string"))
    package)

  ///

  (defret current-package+-not-empty
    (not (equal package ""))))
