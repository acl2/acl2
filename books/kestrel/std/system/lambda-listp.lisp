; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lambdap")

(include-book "std/util/deflist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist lambda-listp (x wrld)
  :parents (std/system/term-function-recognizers lambdap)
  :short (xdoc::topstring
          "Recognize true lists of "
          (xdoc::seetopic "lambdap" "translated lambda expressions")
          ".")
  :guard (plist-worldp-with-formals wrld)
  (lambdap x wrld)
  :true-listp t
  :elementp-of-nil nil)
