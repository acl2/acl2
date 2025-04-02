; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "static-safety-checking")
(include-book "static-safety-checking-evm")
(include-book "static-shadowing-checking")
(include-book "static-identifier-checking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (language)
  :short "Static semantics of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the static semantics of Yul
     via ACL2 functions that check that the abstract syntax of Yul
     satisfies a number of constraints, described in [Yul].
     We formalize different kinds of constraints separately."))
  :order-subtopics (static-safety-checking
                    static-safety-checking-evm
                    static-shadowing-checking
                    static-identifier-checking))
