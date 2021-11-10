; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The current abstract syntax for expressions has separate cases for
; unary operators, binary operators, and named functions.
; This leads to a certain verbosity and repetition in the static semantics
; (and presumably in other places too).
; Furthermore, the static semantics has a notion of built-in functions,
; which the abstract syntax does not explicitly have.

; So we could introduce the following fixtype for functions,
; which includes unary and binary operators,
; and built-in and defined named functions.
; And then we can simplify the definition of expressions
; by removing the separate cases for unary and binary expressions,
; and instead having just the call case.
; After all, operators are functions in ACL2.

(fty::deftagsum function-name
  :short "Fixtype of Syntheto functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are functions in the mathematical sense (as in ACL2).
     They include unary and binary operators,
     built-in functions (i.e. without Syntheto definitions),
     and defined functions (i.e. the ones defined in Syntheto)."))
  (:unary-op ((get unary-op)))
  (:binary-op ((get binary-op)))
  (:builtin ((get identifier)))
  (:defined ((get identifier)))
  :pred function-namep)

#|

; Then we can change
    (:call ((function identifier)
            (types type-list)
            (arguments expression-list)))
; to this
    (:call ((function functionp)
            (types type-list)
            (arguments expression-list)))

|#
