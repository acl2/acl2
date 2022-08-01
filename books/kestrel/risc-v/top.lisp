; RISC-V Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (acoglio on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "instructions")
(include-book "state")
(include-book "semantics")
(include-book "decoding")
(include-book "execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ riscv
  :parents (projects)
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
     a preliminary formalization of part of the the RISC-V ISA.
     It is expected that this library will be extended with more
     RISC-V formalizations and tools.")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     "The "
     (xdoc::a :href "https://riscv.org/specifications/isa-spec-pdf/"
       "RISC-V Unprivileged ISA Manual")
     ", referenced as `[ISA]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[ISA:2.2]' references Section 2.2 of [ISA].")
    (xdoc::li
     "The "
     (xdoc::a :href "https://riscv.org/specifications/privileged-isa/"
       "RISC-V Privileged ISA Manual")
     ", referenced as `[ISAP]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[ISAP:3.3]' references Section 3.3 of [ISAP]."))
   (xdoc::p
    "These square-bracketed references may be used
     as nouns or parenthentically."))
  :order-subtopics t
  :default-parent t)
