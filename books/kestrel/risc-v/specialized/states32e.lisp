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

(include-book "../specification/states")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states32e
  :parents (specialized-states)
  :short "Specialized states for features with the RV32E base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a recognizer for the valid states for the RV32E base."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv32e-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of states with base RV32E."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv32e-le)))

  ///

  (defruled stat-rv32e-p-alt-def-be
    (equal (stat-rv32e-p x)
           (and (statp x)
                (stat-validp x (feat-rv32e-be))))
    :enable (stat-validp
             (:e feat-rv32e-le)
             (:e feat-rv32e-be)))

  (defruled stat-rv32e-p-alt-def-m-le
    (equal (stat-rv32e-p x)
           (and (statp x)
                (stat-validp x (feat-rv32em-le))))
    :enable (stat-validp
             (:e feat-rv32e-le)
             (:e feat-rv32em-le)))

  (defruled stat-rv32e-p-alt-def-m-be
    (equal (stat-rv32e-p x)
           (and (statp x)
                (stat-validp x (feat-rv32em-be))))
    :enable (stat-validp
             (:e feat-rv32e-le)
             (:e feat-rv32em-be))))
