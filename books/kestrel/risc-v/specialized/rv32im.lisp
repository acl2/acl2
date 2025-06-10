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

(include-book "states32")
(include-book "semantics32")
(include-book "execution32")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rv32im
  :parents (specialized)
  :short "Specialized model for RV32IM."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of a model of states and instruction execution for RV32IM.
     This was developed before the more general model with @(see features).
     We plan to re-obtain this specialized model via
     transformation and specialization of the general one at some point,
     but until then we keep it around."))
  :order-subtopics (states32
                    semantics32
                    execution32))
