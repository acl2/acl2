; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rawp ((fn symbolp) state)
  :returns (yes/no booleanp)
  :verify-guards nil
  :parents (std/system/function-queries)
  :short "Check if a named function has raw Lisp code."
  :long
  (xdoc::topstring
   (xdoc::p
    "The global variables
     @('logic-fns-with-raw-code') and @('program-fns-with-raw-code')
     list the logic-mode and program-mode functions with raw Lisp code.
     Their initial values are
     @('*initial-logic-fns-with-raw-code*') and
     @('*initial-program-fns-with-raw-code*'),
     but they may change if functions with raw Lisp code are introduced.")
   (xdoc::p
    "This function checks whether a function has raw Lisp code
     by checking whether it is listed in one of those global variables."))
  (and (or (member-eq fn (@ logic-fns-with-raw-code))
           (member-eq fn (@ program-fns-with-raw-code)))
       t))
