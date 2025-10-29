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
(include-book "states32i")
(include-book "states32")
(include-book "semantics32")
(include-book "execution32")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ specialized-rv32im-le
  :parents (specialized)
  :short "Specialization of the model to RV32IM little endian."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of a model of states and instruction execution for RV32IM.
     This was developed before the more general model with @(see features).
     We plan to re-obtain this specialized model via
     transformation and specialization of the general one at some point,
     but until then we keep it around."))
  :order-subtopics (rv32im-le-features
                    states32i
                    states32
                    semantics32
                    execution32))
