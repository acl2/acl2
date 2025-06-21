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

(defxdoc+ specialized-states
  :parents (specialized)
  :short "Specialized states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define recognizers for states corresponding to
     the specialized features defined in @(see specialized-features)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv32i-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of RV32I(M) states."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv32i-le)))

  ///

  (defruled stat-rv32i-p-alt-def-be
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32i-be))))
    :enable stat-validp)

  (defruled stat-rv32i-p-alt-def-m-le
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32im-le))))
    :enable stat-validp)

  (defruled stat-rv32i-p-alt-def-m-be
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32im-be))))
    :enable stat-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv64i-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of RV64I(M) states."
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv32e-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of RV32E states."
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
    :enable stat-validp)

  (defruled stat-rv32e-p-alt-def-m-le
    (equal (stat-rv32e-p x)
           (and (statp x)
                (stat-validp x (feat-rv32em-le))))
    :enable stat-validp)

  (defruled stat-rv32e-p-alt-def-m-be
    (equal (stat-rv32e-p x)
           (and (statp x)
                (stat-validp x (feat-rv32em-be))))
    :enable stat-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv64e-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of RV64E states."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv64e-be)))

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
