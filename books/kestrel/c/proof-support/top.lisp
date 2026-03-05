; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../portcullis")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proof-support
  :parents (c)
  :short "Proof support for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide theorems to reason about C code
     as formalized in our "
    (xdoc::seetopic "language" "model")
    ". These rules can be used for
     synthesis, verification, and transformation of C code.")
   (xdoc::p
    "This is just an initial placeholder,
     but we plan to move all the "
    (xdoc::seetopic "atc-symbolic-execution-rules"
                    "ATC symbolic execution rules")
    " here, along with possibly others."))
  :order-subtopics t
  :default-parent t)
