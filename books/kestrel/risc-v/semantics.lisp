; RISC-V Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "semantics32")
(include-book "semantics64")

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics
  :parents (riscv)
  :short "Semantics of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we have two similar but slightly different semantics,
     one for RV32I and one for RV64I.
     We plan to consolidate them into one semantics for both."))
  :order-subtopics (semantics32
                    semantics64))
