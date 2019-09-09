; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitivep ((fn symbolp))
  :returns (yes/no booleanp)
  :parents (std/system)
  :short "Check if a named function is @(see primitive)."
  :long
  (xdoc::topstring-p
   "See @(tsee primitivep+) for a logic-friendly variant of this utility.")
  (and (member-eq fn (strip-cars *primitive-formals-and-guards*)) t)
  ///

  (defthm primitivep-forward-to-symbolp
    (implies (primitivep fn)
             (symbolp fn))
    :rule-classes :forward-chaining))
