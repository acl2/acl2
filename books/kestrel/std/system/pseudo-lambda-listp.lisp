; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-lambdap")

(include-book "std/util/deflist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist pseudo-lambda-listp (x)
  :parents (std/system/term-function-recognizers pseudo-lambdap)
  :short (xdoc::topstring
          "Recognize true lists of "
          (xdoc::seetopic "pseudo-lambdap" "pseudo-lambda-expressions")
          ".")
  (pseudo-lambdap x)
  :true-listp t
  :elementp-of-nil nil)
