; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "validation-information")
(include-book "validator")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation
  :parents (syntax-for-tools)
  :short "Validation for our C syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides syntactic validity,
     C code must satisfy a number of additional constraints
     in order to be compiled.
     These constraints form the static semantics of C.
     C compilers check that the code satisfies these constraints
     prior to translating it.")
   (xdoc::p
    "We provide an executable validator,
     which performs a (currently conservative) validation of C code,
     and also annotates the ASTs with information (e.g. calculated types)."))
  :order-subtopics (validation-information))
