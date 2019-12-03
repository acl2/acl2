; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "termfnp")

(include-book "std/util/deflist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist termfn-listp (x wrld)
  :parents (std/system/term-function-recognizers termfnp)
  :short (xdoc::topstring
          "Recognize true lists of "
          (xdoc::seetopic "termfnp" "translated term functions")
          ".")
  :long
  (xdoc::topstring-p
   "We would need stronger world assumptions for @(':elementp-of-nil nil'),
    so with the current weaker world assumptions we leave the default,
    i.e. @(':elementp-of-nil :unknown').")
  :guard (plist-worldp-with-formals wrld)
  (termfnp x wrld)
  :true-listp t)
