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

(define measured-subset ((fn symbolp) (wrld plist-worldp))
  :returns (measured-subset "A @(tsee symbol-listp).")
  :verify-guards nil
  :parents (std/system/function-queries)
  :short "Subset of the formal arguments
          of a named logic-mode recursive function
          that occur in its @(see measure) expression."
  :long
  (xdoc::topstring-p
   "See @(tsee measured-subset+) for an enhanced variant of this utility.")
  (b* ((justification (getpropc fn 'justification nil wrld)))
    (access justification justification :subset)))
