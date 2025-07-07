; Standard System Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-measure ((fn symbolp) (wrld plist-worldp))
  :returns (measure "A @(tsee pseudo-termp).")
  :verify-guards nil
  :parents (std/system/function-queries)
  :short "Measure expression of a named logic-mode recursive function."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see xargs) for a discussion of the @(':measure') keyword.")
   (xdoc::p
    "See @(tsee get-measure+) for an enhanced variant of this utility.")
   (xdoc::p
    "This is called @('get-measure')
     instead of just @('measure')
     to avoid a topic conflict with the XDOC manual."))
  (b* ((justification (getpropc fn 'justification nil wrld)))
    (access justification justification :measure)))
