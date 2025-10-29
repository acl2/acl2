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

(include-book "states64")
(include-book "semantics64")
(include-book "execution64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rv64im
  :parents (specialized)
  :short "Specialized model for RV64IM."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of a model of states and instruction execution for RV64IM.
     This was developed before the more general model with @(see features).
     We plan to re-obtain this specialized model via
     transformation and specialization of the general one at some point,
     but until then we keep it around."))
  :order-subtopics (states64
                    semantics64
                    execution64))
