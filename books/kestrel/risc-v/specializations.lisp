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

(include-book "rv32im")
(include-book "rv64im")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ specializations
  :parents (riscv)
  :short "Specializations of the RISC-V ISA."
  :long
  (xdoc::topstring
   (xdoc::p
    "RISC-V is a family of ISAs, parameterized over the @(see features).
     We provide some specializations of the ISA,
     currently one for RV32IM and one for RV64IM.
     Those are currently both hand-written,
     but we plan to re-obtain them, and possibly others, via "
    (xdoc::seetopic "apt::apt" "APT")
    " transformation applied to the general model."))
  :order-subtopics (rv32im
                    rv64im))
