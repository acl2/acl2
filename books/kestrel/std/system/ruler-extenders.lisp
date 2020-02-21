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

(define ruler-extenders ((fn symbolp) (wrld plist-worldp))
  :returns (ruler-extenders "A @(tsee symbol-listp) of @(':all').")
  :verify-guards nil
  :parents (std/system/function-queries)
  :short "Ruler-extenders of a named logic-mode recursive function."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rulers) for background.")
   (xdoc::p
    "See @(tsee ruler-extenders+) for
     an enhanced variant of this utility."))
  (b* ((justification (getpropc fn 'justification nil wrld)))
    (access justification justification :ruler-extenders)))
