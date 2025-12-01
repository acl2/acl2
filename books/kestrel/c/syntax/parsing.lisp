; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parsing
  :parents (syntax-for-tools)
  :short "Parsing for our C syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide an executable parser from the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    " to the "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    ". The parser is fairly efficient by way of using a stobj.")
   (xdoc::p
    "Currently the parser is neither verified nor proof-generating,
     but we plan to work towards these goals."))
  :order-subtopics (parser))
