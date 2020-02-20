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

(define number-of-results ((fn symbolp) (wrld plist-worldp))
  :guard (not (member-eq fn *stobjs-out-invalid*))
  :returns (n natp "Actually always a @(tsee posp).")
  :parents (std/system/function-queries)
  :short "Number of values returned by a named function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is 1, unless the function uses @(tsee mv)
     (directly, or indirectly by calling another function that does)
     to return multiple values.")
   (xdoc::p
    "The number of results of the function
     is the length of its @(tsee stobjs-out) list.")
   (xdoc::p
    "The function must not be in @('*stobjs-out-invalid*'),
     because in that case the number of its results
     depends on how it is called.")
   (xdoc::p
    "See @(tsee number-of-results+) for
     an enhanced variant of this utility."))
  (len (stobjs-out fn wrld)))
