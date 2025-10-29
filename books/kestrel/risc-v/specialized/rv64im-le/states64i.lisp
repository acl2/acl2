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

(include-book "../../specification/states")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states64i
  :parents (specialized-rv64im-le)
  :short "Specialized states for features with the RV64I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a recognizer for the valid states for the RV64I base."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv64i-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of states with base RV64I."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv64im-le))))
