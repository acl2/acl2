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

(define no-stobjs-p ((fn symbolp) (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (yes/no booleanp)
  :verify-guards nil
  :parents (std/system/function-queries)
  :short "Check if a named function has no input or output @(see stobj)s."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function must not be in @('*stobjs-out-invalid*'),
     because in that case its (output) stobjs depend on how it is called.")
   (xdoc::p
    "See @(tsee no-stobjs-p+) for an enhanced variant of this utility."))
  (and (all-nils (stobjs-in fn wrld))
       (all-nils (stobjs-out fn wrld))))
