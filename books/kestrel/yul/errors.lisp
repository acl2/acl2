; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ errors
  :parents (yul)
  :short "Errors used in the formalization of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we formalize static and dynamic semantics of Yul,
     our ACL2 functions return error values in certain circumstances.
     An example is when a variable is referenced that is not accessible.")
   (xdoc::p
    "We use @(tsee fty::defresult) and companion utilities
     to handle errors in our Yul formalization.")))
