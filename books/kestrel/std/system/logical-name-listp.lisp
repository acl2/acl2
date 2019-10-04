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

(define logical-name-listp (names (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :parents (std/system/event-name-queries)
  :short "Recognize true lists of logical names."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @('logical-namep') in the ACL2 source code.")
   (xdoc::p
    "While @('logical-namep') is not boolean-valued,
     this function always returns a boolean.")
   (xdoc::p
    "We cannot use @(tsee std::deflist) to define this function
     because that macro attempts to prove that
     @('logical-namep') is boolean-valued."))
  (cond ((atom names) (null names))
        (t (and (logical-namep (car names) wrld)
                (logical-name-listp (cdr names) wrld)))))
