; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "function-namep")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define logic-function-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/event-name-queries)
  :short "Recognize symbols that name logic-mode functions."
  :long
  (xdoc::topstring-p
   "This function is enabled because it is meant as an abbreviation.
    Theorems triggered by this function should be generally avoided.")
  (and (function-namep x wrld)
       (logicp x wrld))
  :enabled t)
