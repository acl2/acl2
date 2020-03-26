; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "assert-bang")
(include-book "assert-bang-stobj")
(include-book "assert-equal")
(include-book "assert-qmark")
(include-book "eval") ; for some deprecated synonyms of MUST-... macros
(include-book "must-be-redundant")
(include-book "must-be-table-key")
(include-book "must-eval-to")
(include-book "must-eval-to-t")
(include-book "must-fail")
(include-book "must-fail-local")
(include-book "must-fail-with-error")
(include-book "must-fail-with-hard-error")
(include-book "must-fail-with-soft-error")
(include-book "must-not-be-table-key")
(include-book "must-not-prove")
(include-book "must-prove")
(include-book "must-succeed")
(include-book "must-succeed-star")

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
