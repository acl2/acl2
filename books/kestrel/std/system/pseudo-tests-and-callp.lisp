; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pseudo-tests-and-callp (x)
  :returns (yes/no booleanp)
  :parents (std/system)
  :short "Recognize well-formed @('tests-and-call') records."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('tests-and-call') record is defined as")
   (xdoc::codeblock
    "(defrec tests-and-call (tests call) nil)")
   (xdoc::p
    "(see the ACL2 source code).")
   (xdoc::p
    "In a well-formed @('tests-and-call') record,
     @('tests') must be a list of terms and
     @('call') must be a term.")
   (xdoc::p
    "This recognizer is analogous to @(tsee pseudo-tests-and-callsp)."))
  (case-match x
    (('tests-and-call tests call)
     (and (pseudo-term-listp tests)
          (pseudo-termp call)))
    (& nil))
  ///

  (defthm weak-tests-and-call-p-when-pseudo-tests-and-callp
    (implies (pseudo-tests-and-callp x)
             (weak-tests-and-call-p x))))
