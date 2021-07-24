; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "semantics-deep")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proof-support
  :parents (prime-field-constraint-systems)
  :short "Proof support for PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "PFCS representing specific gadgets can be reasoned about
     (to prove properties of them, such as compliance to specifications)
     using either the shallowly or deeply embedded semantics.
     Both work fine for the case of fixed, completely defined PFCS.
     However, to reason about parameterized families of PFCS,
     such as a gadget to decompose a number into a varying number of bits
     (where the number of bits is a parameter),
     or even more simply a gadget parameterized over
     the choice of names of its variables,
     needs the deeply embedded semantics.
     The reason is that we can define an ACL2 function
     that takes the parameters as inputs
     and returns the corresponding gadget in PFCS abstract syntax,
     whose properties we can then prove,
     universally quantified over the parameters
     (perhaps with some restrictions on the parameters).
     This is only possible in the deeply embedded semantics,
     which treats the PFCS abstract syntax explicitly.
     In contrast, the shallowly embedded semantics
     turns fixed instances of PFCS abstract syntax into ACL2 predicates,
     without an easy way to parameterize them.
     It may be possible to extend the shallowly embedded semantics
     to recognize and take into account certain forms of parameterized PFCS,
     or even extend PFCS with forms of parameterization.
     But for now,
     with PFCS and their shallowly embedded semantics being what they are,
     the deeply embedded semantics must be used
     to reason about parameterized PFCS.")
   (xdoc::p
    "However, the (deeply embedded) semantics of PFCS is somewhat complicated,
     defined in terms of existentially quantifier proof trees and their execution.
     The reason for that complication is discussed
     in @(see semantics-deeply-embedded).
     The complication extends to attempts to reason about PFCS
     (whether parameterized or not)
     directly in terms of the defined semantics.")
   (xdoc::p
    "Fortunately, it is possible to prove theorems
     that facilitate reasoning with the deeply embedded semantics.
     The rules let us avoid dealing explcitly with proof trees.
     These rules are work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add proof rules
