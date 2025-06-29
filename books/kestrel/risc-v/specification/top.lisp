; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "features")
(include-book "instructions")
(include-book "encoding")
(include-book "decoding")
(include-book "states")
(include-book "reads-over-writes")
(include-book "semantics")
(include-book "semantics-equivalences")
(include-book "execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ specification
  :parents (riscv)
  :short "Specification of the RISC-V ISA."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the RISC-V ISA, based on [ISA] and [ISAP].")
   (xdoc::p
    "Since RISC-V is a family of ISAs,
     depending on base and extensions,
     we define a notion of @(see features)
     that determine the exact family member.
     We define a data type (like an abstract syntax) for @(see instructions),
     and the @(see encoding) of these instructions;
     we define instruction @(see decoding) declaratively,
     as the inverse of encoding.
     We formalize the possible @(see states) of execution,
     the @(see semantics) of the instructions,
     and how @(see execution) proceeds in steps.")
   (xdoc::p
    "This specification is high-level, aimed at maximizing clarity.
     It is not aimed at being efficiently executable;
     in fact, since decoding is specified as inverse of encoding,
     this specification is not fully executable.
     See @(see executable) for an executable refinement."))
  :order-subtopics (features
                    instructions
                    encoding
                    decoding
                    states
                    reads-over-writes
                    semantics
                    semantics-equivalences
                    execution))
