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
(include-book "semantics")

(include-book "../../executable/decoding-executable")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rv32im-le-execution
  :parents (specialized-rv32im-le)
  :short "Model of execution for RV32IM."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put together instruction decoding and instruction semantics,
     and define single and multi step functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step32 ((stat stat32p))
  :returns (new-stat stat32p)
  :short "Single-step execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We make no change if the error flag is set.
     Otherwise, we read the program counter,
     we read the 32-bit encoding of the instruction from there
     (which is always little endian [ISA:1.5]),
     we decode it, and, if we obtain an instruction,
     we run the semantic function of the instruction;
     if decoding fails, we set the error flag instead."))
  (b* (((when (error32p stat)) (stat32-fix stat))
       (pc (read32-pc stat))
       (enc (read32-mem-ubyte32-lendian pc stat))
       (instr? (decodex enc (feat-rv32im-le)))
       ((unless instr?) (error32 stat)))
    (exec32-instr instr? pc stat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step32n ((n natp) (stat stat32p))
  :returns (new-stat stat32p)
  :short "Multi-step execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform @('n') steps,
     or fewer if the error flag is or gets set.
     If @('n') is 0, we return the state unchanged."))
  (cond ((zp n) (stat32-fix stat))
        ((error32p stat) (stat32-fix stat))
        (t (step32n (1- n) (step32 stat))))

  ///

  (fty::deffixequiv step32n
    :hints (("Goal" :induct t :in-theory (enable nfix)))))
