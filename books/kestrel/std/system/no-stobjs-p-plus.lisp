; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "stobjs-in-plus")
(include-book "stobjs-out-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define no-stobjs-p+ ((fn symbolp) (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries)
  :short "Enhanced variant of @(tsee no-stobjs-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee no-stobjs-p),
     but it is guard-verified
     and it causes an error (via @(tsee stobjs-in+)
     if called on a symbol that does not name a function.")
   (xdoc::p
    "The function must not be in @('*stobjs-out-invalid*'),
     because in that case its output stobjs depend on how it is called.
     This condition is part of the guard of this utility."))
  (and (all-nils (stobjs-in+ fn wrld))
       (all-nils (stobjs-out+ fn wrld))))
