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

(defxdoc+ states64i
  :parents (specialized-states)
  :short "Specialized states for features with the RV64I base."
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
       (stat-validp x (feat-rv64i-le)))

  ///

  (defruled stat-rv64i-p-alt-def-be
    (equal (stat-rv64i-p x)
           (and (statp x)
                (stat-validp x (feat-rv64i-be))))
    :enable stat-validp)

  (defruled stat-rv64i-p-alt-def-m-le
    (equal (stat-rv64i-p x)
           (and (statp x)
                (stat-validp x (feat-rv64im-le))))
    :enable stat-validp)

  (defruled stat-rv64i-p-alt-def-m-be
    (equal (stat-rv64i-p x)
           (and (statp x)
                (stat-validp x (feat-rv64im-be))))
    :enable stat-validp))
