; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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
(include-book "semantics")
(include-book "execution")
(include-book "rv32im")
(include-book "rv64im")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ riscv
  :parents (acl2::projects)
  :short "A library for RISC-V."
  :long
  (xdoc::topstring
   (xdoc::p
    (xdoc::ahref "https://riscv.org" "RISC-V")
    " is an open instruction set architecture (ISA)
     based on reduced-instruction-set-computer (RISC) principles.
     RISC-V is modular, with base instruction sets and optional extensions.")
   (xdoc::p
    "This ACL2 library includes
     a preliminary formalization of part of the the RISC-V ISA:
     unprivileged RV32IM and RV64IM
     (except for
     the @('FENCE'), @('HINT'), @('ECALL') and @('EBREAK') instructions),
     little endian memory access,
     fully readable and writable address space,
     no alignment checks.
     We plan to extend and improve this library.")
   (xdoc::p
    "We have a generic model of RISC-V,
     parameterized over a growing set of features,
     and we have two specialized models tailored to RV32IM and RV64IM.
     We plan to have the general model cover more features,
     and we plan to re-obtain the specialized models via
     transformation and specialization of the general model.")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     "The "
     (xdoc::ahref "https://riscv.org/technical/specifications/"
                  "The RISC-V Insruction Set Manual Volume 1,
                   Unprivileged Architecture v. 20240411")
     ", referenced as `[ISA]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[ISA:2.2]' references Section 2.2 of [ISA].")
    (xdoc::li
     "The "
     (xdoc::ahref "https://riscv.org/technical/specifications/"
                  "The RISC-V Insruction Set Manual Volume 2,
                   Privileged Architecture v. 20240411")
     ", referenced as `[ISAP]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[ISAP:3.3]' references Section 3.3 of [ISAP]."))
   (xdoc::p
    "These square-bracketed references may be used
     as nouns or parenthentically."))
  :order-subtopics (features
                    instructions
                    states
                    encoding
                    decoding
                    semantics
                    execution
                    rv32im
                    rv64im))
