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

(define non-executablep ((fn symbolp) (wrld plist-worldp))
  :returns (status "@('t'), @('nil'), or @(':program').")
  :parents (std/system/function-queries)
  :short "@(see Non-executable) status of a named function."
  :long
  (xdoc::topstring-p
   "See @(tsee non-executablep+) for an enhanced variant of this utility.")
  (getpropc fn 'non-executablep nil wrld))
