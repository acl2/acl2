; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc event-macro-applicability-conditions
  :parents (event-macros)
  :short "Applicability conditions of event macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "In general, the inputs of an event macro
     must satisfy certain (event-macro-specific) conditions
     in order for the call of the event macro to succeed.
     Some of these conditions are computable,
     so the implementation of the event macro can reliably check them.
     But other conditions amount to theorems to be proved,
     so the implementation of the event macro
     must generally resort to the ACL2 theorem proving engine
     to check whether these conditions hold or not.
     We call the latter `applicability conditions':
     they are (proof) conditions that must be satisfied
     in order for the event macro to be applied successfully to its inputs.
     Even though the non-proof conditions are also necessary
     for the event macro to be applied successfully to its inputs,
     we reserve that terminology for the proof conditions,
     since they are the ones that require more special handling.")
   (xdoc::p
    "Often an event macro generates theorems
     that can be systematically proved
     from the event macro's applicability conditions.
     Prime examples are APT transformations like @(tsee apt::tailrec),
     which generates correctness and guard proofs
     from its applicability conditions.")))
