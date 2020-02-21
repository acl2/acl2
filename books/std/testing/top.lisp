; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "assert")
(include-book "eval")
(include-book "must-be-table-key")
(include-book "must-not-be-table-key")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/testing
  :parents (std testing-utilities)
  :short "A library of testing utilities."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are utilities for creating tests.
     This library does not contain actual tests
     (other than perhaps tests for the testing utilities themselves),
     which are normally next to the code that they test.
     Note that @('[books]/system/tests/') contains actual tests,
     for the ACL2 system code.")))
