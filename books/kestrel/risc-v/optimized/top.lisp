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

(include-book "state-stobj")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ optimized
  :parents (riscv)
  :short "Optimized refinements of the RISC-V @(see specification)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(see specification) is aimed at clarity,
     and not at efficient execution, or even execution.
     In @(see executable), the specification is refined to be executable.
     Here, we perform further refinements
     to make the specification efficiently executable."))
  :order-subtopics (state-stobj))
