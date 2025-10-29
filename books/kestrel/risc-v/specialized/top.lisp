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
(include-book "states")
(include-book "rv32im-le/top")
(include-book "rv64im")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ specialized
  :parents (riscv)
  :short "Specialized versions of the RISC-V ISA."
  :long
  (xdoc::topstring
   (xdoc::p
    "RISC-V is a family of ISAs, parameterized over the @(see features).
     We provide some specializations of the ISA.")
   (xdoc::p
    "This is work in progresss.
     Currently most of these specializations are handwritten,
     but we have started to use "
    (xdoc::seetopic "apt::apt" "APT")
    " transformation, applied to the general model,
     to automate the generation of these specializations."))
  :order-subtopics (specialized-features
                    specialized-states
                    rv32im
                    rv64im))
