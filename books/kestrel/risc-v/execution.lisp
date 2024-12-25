; RISC-V Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "execution32")
(include-book "execution64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ execution
  :parents (riscv)
  :short "Model of execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we have two similar but slightly different models,
     one for RV32I and one for RV64I.
     We plan to consolidate them into one model for both."))
  :order-subtopics (execution32
                    execution64))
