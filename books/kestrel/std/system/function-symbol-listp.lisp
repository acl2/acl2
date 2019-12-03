; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist function-symbol-listp (x wrld)
  :parents (std/system/event-name-queries)
  :short "Lift @(tsee function-symbolp) to lists."
  :long
  (xdoc::topstring-p
   "We would need stronger world assumptions for @(':elementp-of-nil nil'),
    so with the current weaker world assumptions we leave the default,
    i.e. @(':elementp-of-nil :unknown').")
  :guard (and (symbol-listp x)
              (plist-worldp wrld))
  (function-symbolp x wrld)
  :true-listp t)
