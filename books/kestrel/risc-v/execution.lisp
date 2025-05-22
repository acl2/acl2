; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "decoding")
(include-book "semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ execution
  :parents (riscv)
  :short "Model of execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we have two similar but slightly different models,
     one for RV32I and one for RV64I.
     We plan to consolidate them into one model for both."))
  :default-parent t
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step ((stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Single-step execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We make no change if the error flag is set.
     Otherwise, we read the program counter,
     we read the 32-bit encoding of the instruction from there,
     we decode it, and, if we obtain an instruction,
     we run the semantic function of the instruction;
     if decoding fails, we set the error flag instead."))
  (b* (((when (errorp stat feat)) (stat-fix stat))
       (pc (read-pc stat feat))
       (enc (read-instruction pc stat feat))
       (instr? (decode enc feat))
       ((unless instr?) (error stat feat)))
    (exec-instr instr? pc stat feat))
  :guard-hints (("Goal" :in-theory (enable feat-32p feat-64p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-step
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stepn ((n natp) (stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Multi-step execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform @('n') steps,
     or fewer if the error flag is or gets set.
     If @('n') is 0, we return the state unchanged."))
  (cond ((zp n) (stat-fix stat))
        ((errorp stat feat) (stat-fix stat))
        (t (stepn (1- n) (step stat feat) feat)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-stepn
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))
