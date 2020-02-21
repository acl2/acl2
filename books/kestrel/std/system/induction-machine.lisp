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

(define induction-machine ((fn symbolp) (wrld plist-worldp))
  :returns (result "A @(tsee pseudo-tests-and-calls-listp).")
  :parents (std/system/function-queries)
  :short "Induction machine of a named logic-mode (singly) recursive function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a list of @('tests-and-calls') records
     (see the ACL2 source code for information on these records),
     each of which contains zero or more recursive calls
     along with the tests that lead to them.
     The induction machine is a value of type @('pseudo-tests-and-calls-listp'),
     which is defined in
     @('[books]/system/pseudo-tests-and-calls-listp.lisp').")
   (xdoc::p
    "Note that
     induction is not directly supported for mutually recursive functions.")
   (xdoc::p
    "See @(tsee induction-machine+) for
     an enhanced variant of this utility."))
  (getpropc fn 'induction-machine nil wrld))
