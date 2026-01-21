; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ printer
  :parents (syntax-for-tools)
  :short "Printing for our C syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide an executable (pretty-)printer from the "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " to the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    ".")
   (xdoc::p
    "Currently the printer is neither verified nor proof-generating,
     but we plan to work towards these goals."))
  :order-subtopics (printer))
