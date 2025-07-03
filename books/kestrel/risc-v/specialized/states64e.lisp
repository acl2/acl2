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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states64e
  :parents (specialized-states)
  :short "Specialized states for features with the RV64E base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a recognizer for the valid states for the RV64E base."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv64e-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of states with base RV64E."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv64e-le)))

  ///

  (defruled stat-rv64e-p-alt-def-be
    (equal (stat-rv64e-p x)
           (and (statp x)
                (stat-validp x (feat-rv64e-be))))
    :enable stat-validp)

  (defruled stat-rv64e-p-alt-def-m-le
    (equal (stat-rv64e-p x)
           (and (statp x)
                (stat-validp x (feat-rv64em-le))))
    :enable stat-validp)

  (defruled stat-rv64e-p-alt-def-m-be
    (equal (stat-rv64e-p x)
           (and (statp x)
                (stat-validp x (feat-rv64em-be))))
    :enable stat-validp))
