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

(include-book "../specification/features")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ specialized-features
  :parents (specialized)
  :short "Specialized features."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define constants for various combinations of @(see features)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32i-le ()
  :returns (feat featp)
  :short "Features for RV32I, with little endian memory."
  (make-feat :base (feat-base-rv32i)
             :endian (feat-endian-little)
             :m nil))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv32i-be ()
  :returns (feat featp)
  :short "Features for RV32I, with big endian memory."
  (make-feat :base (feat-base-rv32i)
             :endian (feat-endian-big)
             :m nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv64i-le ()
  :returns (feat featp)
  :short "Features for RV64I, with little endian memory."
  (make-feat :base (feat-base-rv64i)
             :endian (feat-endian-little)
             :m nil))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv64i-be ()
  :returns (feat featp)
  :short "Features for RV64I, with big endian memory."
  (make-feat :base (feat-base-rv64i)
             :endian (feat-endian-big)
             :m nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32e-le ()
  :returns (feat featp)
  :short "Features for RV32E, with little endian memory."
  (make-feat :base (feat-base-rv32e)
             :endian (feat-endian-little)
             :m nil))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv32e-be ()
  :returns (feat featp)
  :short "Features for RV32E, with big endian memory."
  (make-feat :base (feat-base-rv32e)
             :endian (feat-endian-big)
             :m nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv64e-le ()
  :returns (feat featp)
  :short "Features for RV64E, with little endian memory."
  (make-feat :base (feat-base-rv64e)
             :endian (feat-endian-little)
             :m nil))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv64e-be ()
  :returns (feat featp)
  :short "Features for RV64E, with big endian memory."
  (make-feat :base (feat-base-rv64e)
             :endian (feat-endian-big)
             :m nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32im-le ()
  :returns (feat featp)
  :short "Features for RV32IM, with little endian memory."
  (make-feat :base (feat-base-rv32i)
             :endian (feat-endian-little)
             :m t))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv32im-be ()
  :returns (feat featp)
  :short "Features for RV32IM, with big endian memory."
  (make-feat :base (feat-base-rv32i)
             :endian (feat-endian-big)
             :m t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv64im-le ()
  :returns (feat featp)
  :short "Features for RV64IM, with little endian memory."
  (make-feat :base (feat-base-rv64i)
             :endian (feat-endian-little)
             :m t))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv64im-be ()
  :returns (feat featp)
  :short "Features for RV64IM, with big endian memory."
  (make-feat :base (feat-base-rv64i)
             :endian (feat-endian-big)
             :m t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32em-le ()
  :returns (feat featp)
  :short "Features for RV32EM, with little endian memory."
  (make-feat :base (feat-base-rv32e)
             :endian (feat-endian-little)
             :m t))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv32em-be ()
  :returns (feat featp)
  :short "Features for RV32EM, with big endian memory."
  (make-feat :base (feat-base-rv32e)
             :endian (feat-endian-big)
             :m t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv64em-le ()
  :returns (feat featp)
  :short "Features for RV64EM, with little endian memory."
  (make-feat :base (feat-base-rv64e)
             :endian (feat-endian-little)
             :m t))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv64em-be ()
  :returns (feat featp)
  :short "Features for RV64EM, with big endian memory."
  (make-feat :base (feat-base-rv64e)
             :endian (feat-endian-big)
             :m t))
