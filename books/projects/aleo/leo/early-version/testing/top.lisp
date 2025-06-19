; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "xdoc/defxdoc-plus" :dir :system)

;; Testing infrastructure, not test data.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ testing
  :parents (early-version)
  :short "Formal model of test cases for Formal Model of Leo and code to run tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "The eventual goal is for every step of the Leo compilation toolchain to be
     backed by correctness proofs.  However, in order to detect specification
     or formatting issues early, and to support change in the Leo language,
     it is good to have some specific regression tests.")
   (xdoc::p
    "For testing a specific function in a specific program, we have a
     @('test-case').  The test case includes the function's
     input and output types.")
   (xdoc::p
    "A test case has zero or more @('test-io-pair') objects that contain
     specific input and output values.  The values are abstract syntax
     objects of type valuep.")
   (xdoc::p
    "For running test cases, we currently support running dynamic execution
     in the formal model.")
   (xdoc::p
    "This is work in progress.  Additional structure and support for more kinds
     of tests will be added."))
  :order-subtopics t)
