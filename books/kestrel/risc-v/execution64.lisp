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

(include-book "decoding")
(include-book "semantics64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ execution64
  :parents (execution)
  :short "Model of execution for RV64IM."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put together instruction decoding and instruction semantics,
     and define single and multi step functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step64 ((stat state64p))
  :returns (new-stat state64p)
  :short "Single-step execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We make no change if the error flag is set.
     Otherwise, we read the program counter,
     we read the 32-bit encoding of the instruction from there
     (which is always little endian [ISA:1.5.1]),
     we decode it, and, if we obtain an instruction,
     we run the semantic function of the instruction;
     if decoding fails, we set the error flag instead."))
  (b* (((when (error64p stat)) (state64-fix stat))
       (pc (read64-pc stat))
       (enc (read64-mem-ubyte32-lendian pc stat))
       (instr? (decodex enc (feat-rv64im-le)))
       ((unless instr?) (error64 stat)))
    (exec64-instr instr? pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step64n ((n natp) (stat state64p))
  :returns (new-stat state64p)
  :short "Multi-step execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform @('n') steps,
     or fewer if the error flag is or gets set.
     If @('n') is 0, we return the state unchanged."))
  (cond ((zp n) (state64-fix stat))
        ((error64p stat) (state64-fix stat))
        (t (step64n (1- n) (step64 stat))))
  :hooks (:fix))
