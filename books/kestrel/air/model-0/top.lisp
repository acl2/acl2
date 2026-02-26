; AIR Library
; Model 0: A Minimal zkVM with AIR Constraints
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

;; Language Component (ISA, no field dependencies)
(include-book "language/abstract-syntax")
(include-book "language/static-semantics")
(include-book "language/dynamic-semantics")
(include-book "language/input-output-semantics")

;; AIR Component (field embedding and constraints)
(include-book "air/field")
(include-book "air/traces")
(include-book "air/field-encoding")
(include-book "air/pfcs-constraints")
(include-book "air/pfcs-lifting")
(include-book "air/correctness")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ model-0
  :parents (projects)
  :short "A minimal zkVM formalized in ACL2 with AIR constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "Model 0 (M0 for short) is the first in a series of pedagogical models
     for understanding Algebraic Intermediate Representation (AIR),
     the constraint system used by zero-knowledge virtual machines (zkVMs)
     such as "
    (xdoc::ahref "https://github.com/ProjectZKM/Ziren" "Ziren")
    ".")
   (xdoc::p
    "The Model 0 VM has an extremely simple architecture:")
   (xdoc::ul
    (xdoc::li "An 8-bit accumulator register with wrap-around arithmetic")
    (xdoc::li "A program counter")
    (xdoc::li "Three opcodes: @('INCR'), @('DECR'), and @('HALT')"))
   (xdoc::p
    "Despite its simplicity, Model 0 demonstrates the key concepts of AIR:")
   (xdoc::ul
    (xdoc::li "Execution traces as tables of field elements")
    (xdoc::li "Transition constraints as polynomial equations")
    (xdoc::li "Boundary constraints for public inputs/outputs")
    (xdoc::li "The Ziren-style wrap constraint @('t * (256 - t) = 0')
               for handling overflow"))
   (xdoc::h3 "Organization")
   (xdoc::p
    "The formalization is organized into two components:")
   (xdoc::ul
    (xdoc::li
     (xdoc::b "Language component")
     " — defines the ISA:"
     (xdoc::ul
      (xdoc::li "@(see abstract-syntax) — opcodes and programs")
      (xdoc::li "@(see static-semantics) — program well-formedness")
      (xdoc::li "@(see dynamic-semantics) — interpreter")))
    (xdoc::li
     (xdoc::b "AIR component")
     " — represents execution as polynomial constraints over a finite field:"
     (xdoc::ul
      (xdoc::li "@(see field) — Koala Bear field arithmetic")
      (xdoc::li "@(see traces) — execution traces as tables of field elements")
      (xdoc::li "@(see constraints) — polynomial constraints characterizing valid executions")
      (xdoc::li "@(see equivalence) — proofs that constraints match the operational semantics"))))
   (xdoc::h3 "Field")
   (xdoc::p
    "Model 0 uses the Koala Bear prime field,
     matching Ziren's Plonky3-based implementation:")
   (xdoc::codeblock "p = 2^31 - 2^24 + 1 = 2,130,706,433")
   (xdoc::p
    "Since @('256 < p'), all 8-bit values embed uniquely into the field.
     See @(see primes::koala-bear) for the certified primality proof."))
  :order-subtopics (abstract-syntax
                    static-semantics
                    dynamic-semantics
                    input-output-semantics
                    field
                    traces
                    field-encoding
                    pfcs-constraints
                    pfcs-lifting
                    correctness))
