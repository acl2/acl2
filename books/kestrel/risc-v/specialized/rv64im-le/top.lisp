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
(include-book "semantics")
(include-book "execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ specialized-rv64im-le
  :parents (specialized)
  :short "Specialization of the model to RV64IM little endian."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is characterized by
     the choice of the RV64I base,
     the presence of the M extension,
     and little endian data access to memory.")
   (xdoc::p
    "In our current general model of RISC-V,
     this completely pins down the @(see features).
     We introduce a nullary function corresponding to those features,
     along with specialized types and operations
     that do not depend on features."))
  :order-subtopics (rv64im-le-features
                    rv64im-le-states
                    rv64im-le-semantics
                    rv64im-le-execution))
