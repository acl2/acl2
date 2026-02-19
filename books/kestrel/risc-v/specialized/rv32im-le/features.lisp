; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV32IM-LE")

(include-book "../../specification/features")

(include-book "portcullis")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rv32im-le-features
  :parents (specialized-rv32im-le)
  :short (xdoc::topstring
          "Specialization of "
          (xdoc::seetopic "riscv::features" "features")
          " to RV32IM little endian.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32im-le ()
  :returns (feat riscv::featp)
  :short "Features for RV32IM little endian."
  (riscv::make-feat :base (riscv::feat-base-rv32i)
                    :endian (riscv::feat-endian-little)
                    :m t)
  ///
  (in-theory (disable (:e feat-rv32im-le))))
