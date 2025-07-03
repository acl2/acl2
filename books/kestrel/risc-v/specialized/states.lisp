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

(include-book "states32i")
(include-book "states64i")
(include-book "states32e")
(include-book "states64e")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ specialized-states
  :parents (specialized)
  :short "Specialized states."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the RISC-V variants covered by our model of @(see features)
     have states of four possible kinds, one for each base.
     For each of the bases, we define a recognizer of those states
     obtained by conjoining @(tsee statp) with @(tsee stat-validp),
     where the latter is passed any of the features for the base."))
  :order-subtopics (states32i
                    states64i
                    states32e
                    states64e)
  :default-parent t)
