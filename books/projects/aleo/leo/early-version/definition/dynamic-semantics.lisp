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

(include-book "errors")
(include-book "program-execution")
(include-book "output-execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-semantics
  :parents (definition)
  :short "Dynamic semantics of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "The dynamic semantics of Leo defines
     how the execution of
     the expressions, statements, etc. defined in the "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " manipulate values and computation states.")
   (xdoc::p
    "The definition consists of
     mathematical structures that characterize
     the form of values and computation states,
     and functions saying how values and computation states are
     created and transformed by the execution of the Leo constructs.
     These execution functions do not assume that the constructs
     satisfy the static semantic requirements in the"
    (xdoc::seetopic "static-semantics" "static semantics")
    ": the execution functions are defensive,
     i.e. they perform the dynamic equivalent
     of some of the static checks prescribed by the static semantics,
     such as the fact that an operator is applied
     to operands of the right types;
     if the checks fail, special error results are produced,
     distinct from values and computation states.
     An important property of Leo is that
     if the static semantic requirements in are satisfied,
     then these dynamic semantic checks never fail;
     we plan to formally prove this property."))
  :order-subtopics t
  :default-parent t)
