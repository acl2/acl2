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

(include-book "kestrel/fty/ubyte4" :dir :system)
(include-book "kestrel/fty/ubyte5" :dir :system)
(include-book "kestrel/fty/ubyte6" :dir :system)
(include-book "kestrel/fty/ubyte12" :dir :system)
(include-book "kestrel/fty/ubyte20" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ instructions
  :parents (specification)
  :short "Model of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce fixtypes that define essentially
     an abstract syntax of RISC-V instructions.
     This only exists in the model, not in the processor,
     which represents instructions in binary.
     These high-level instructions are the result of decoding the binary format;
     they are close in spirit to assembly instructions.")
   (xdoc::p
    "We start with the unprivileged instructions
     in RV32I [ISA:2] and RV64I [ISA:4],
     which are the same for RV32E and RV64E [ISA:3],
     except for @('FENCE'), @('ECALL'), @('EBREAK'), and @('HINT').
     We also cover the instructions for the M extension [ISA:13].
     We plan to add privileged instructions,
     as well as instructions for more extensions.")
   (xdoc::p
    "Not all the instructions defined here are valid
     in every instantiation of the RISC-V ISA.
     For example, @('ADDIW') is only valid when the base is RV64I or RV64E,
     and @('MUL') is only valid with the M extension.
     We define a predicate saying which instructions are valid
     with respect to given @(see features)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-imm-funct
  :short "Fixtype of
          names of non-shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These instructions are encoded in the I-type format [ISA:2.4].
     They are designated by the @('funct3') field,
     which motivates the name of this fixtype.")
   (xdoc::p
    "The @('OP-IMM') opcode also includes shift instructions,
     but those are in a slightly different format,
     and thus their names are in a separate fixtype, @(tsee op-imms-funct),
     to facilitate the definition of the fixtype of instructions."))
  (:addi ())
  (:slti ())
  (:sltiu ())
  (:andi ())
  (:ori ())
  (:xori ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-imms-funct
  :short "Fixtype of names of shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee op-imm-funct), but for the shift instructions,
     which use a specialization of the I-type format;
     see discussion in @(tsee op-imm-funct).
     The instruction is designated not only by the @('funct3') field,
     but also by the @('imm[11:5]') field,
     which here acts like the @('funct7') field in other instructions.")
   (xdoc::p
    "The @('s') in the @('imms') of this fixtype name indicates `shift'."))
  (:slli ())
  (:srli ())
  (:srai ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-imm-32-funct
  :short "Fixtype of
          names of non-shift instructions with the @('OP-IMM-32') opcode
          [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee op-imm-funct),
     but for the @('OP-IMM-32') opcode."))
  (:addiw ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-imms-32-funct
  :short "Fixtype of
          names of shift instructions with the @('OP-IMM-32') opcode
          [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee op-imms-funct),
     but for the @('OP-IMM-32') opcode.
     See the documentation of @(tsee op-imms-funct)."))
  (:slliw ())
  (:srliw ())
  (:sraiw ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-funct
  :short "Fixtype of names of instructions with the @('OP') opcode
          [ISA:2.4.2] [ISA:13.1] [ISA:13.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These instructions are encoded in the R-type format [ISA:2.4].
     They are designated by the @('funct3') and @('funct7') fields,
     which motivates the name of this fixtype."))
  (:add ())
  (:sub ())
  (:slt ())
  (:sltu ())
  (:and ())
  (:or ())
  (:xor ())
  (:sll ())
  (:srl ())
  (:sra ())
  (:mul ())
  (:mulh ())
  (:mulhu ())
  (:mulhsu ())
  (:div ())
  (:divu ())
  (:rem ())
  (:remu ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-32-funct
  :short "Fixtype of names of instructions with the @('OP-32') opcode
          [ISA:4.2.2] [ISA:13.1] [ISA:13.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee op-funct), but for the @('OP-32') opcode."))
  (:addw ())
  (:subw ())
  (:sllw ())
  (:srlw ())
  (:sraw ())
  (:mulw ())
  (:divw ())
  (:divuw ())
  (:remw ())
  (:remuw ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum branch-funct
  :short "Fixtype of names of instructions with the @('BRANCH') opcode
          [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These instructions are encoded in the B-type format [ISA:2.4].
     They are designated by the @('funct3') field,
     which motivates the name of this fixtype."))
  (:beq ())
  (:bne ())
  (:blt ())
  (:bltu ())
  (:bge ())
  (:bgeu ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum load-funct
  :short "Fixtype of names of instructions with the @('LOAD') opcode
          [ISA:2.6] [ISA:4.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These instructions are encoded in the I-type format [ISA:2.4].
     They are designated by the @('funct3') field,
     which motivates the name of this fixtype."))
  (:lb ())
  (:lbu ())
  (:lh ())
  (:lhu ())
  (:lw ())
  (:lwu ())
  (:ld ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum store-funct
  :short "Fixtype of names of instructions with the @('STORE') opcode
          [ISA:2.6] [ISA:4.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These instructions are encoded in the S-type format [ISA:4.2].
     They are designated by the @('funct3') field,
     which motivates the name of this fixtype."))
  (:sb ())
  (:sh ())
  (:sw ())
  (:sd ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum instr
  :short "Fixtype of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The tags of the summands of this fixtype correspond to opcodes.
     The components of each summand correspond to the non-opcode fields.
     Register indices always consist of 5 bits,
     in order to designate the 32 registers of RV32I and RV64I;
     for RV32E and RV64E, only the low four bits are used,
     with the high bit needing to be 0 [ISA:3.2];
     we enforce that in @(tsee instr-validp).")
   (xdoc::p
    "The @('OP-IMM') opcode corresponds to
     @(':op-imm') for non-shift instructions,
     @(':op-imms32') for RV32I shift instructions, and
     @(':op-imms64') for RV64I shift instructions.
     They are distinct summands because the formats differ:
     non-shift instructions use the I-type format;
     shift instructions use a specialization of the I-type format,
     but a slightly different one in RV32I vs. RV64I,
     namely in the number of bits of the shift amount (5 vs. 6).")
   (xdoc::p
    "The @('OP-IMM-32') opcode corresponds to
     @(':op-imm-32') for non-shift instructions, and
     @(':op-imms-32') for shift instructions.
     They are distinct summands because the formats differ:
     non-shift instructions use the I-type format;
     shift instructions use a specialization of the I-type format.")
   (xdoc::p
    "The @('LUI') opcode [ISA:2.4.1] [ISA:4.2.1] corresponds to @(':lui').")
   (xdoc::p
    "The @('AUIPC') [ISA:2.4.1] [ISA:4.2.1] opcode corresponds to @(':auipc').")
   (xdoc::p
    "The @('OP') opcode corresponds to @(':op').")
   (xdoc::p
    "The @('OP-32') opcode corresponds to @(':op-32').")
   (xdoc::p
    "The @('JAL') opcode [ISA:2.5.1] corresponds to @(':jal').")
   (xdoc::p
    "The @('JALR') opcode [ISA:2.5.1] corresponds to @(':jalr').")
   (xdoc::p
    "The @('BRANCH') opcode corresponds to @(':branch').")
   (xdoc::p
    "The @('LOAD') opcode corresponds to @(':load').")
   (xdoc::p
    "The @('STORE') opcode corresponds to @(':store')."))
  (:op-imm ((funct op-imm-funct)
            (rd ubyte5)
            (rs1 ubyte5)
            (imm ubyte12)))
  (:op-imms32 ((funct op-imms-funct)
               (rd ubyte5)
               (rs1 ubyte5)
               (imm ubyte5)))
  (:op-imms64 ((funct op-imms-funct)
               (rd ubyte5)
               (rs1 ubyte5)
               (imm ubyte6)))
  (:op-imm-32 ((funct op-imm-32-funct)
               (rd ubyte5)
               (rs1 ubyte5)
               (imm ubyte12)))
  (:op-imms-32 ((funct op-imms-32-funct)
                (rd ubyte5)
                (rs1 ubyte5)
                (imm ubyte5)))
  (:lui ((rd ubyte5)
         (imm ubyte20)))
  (:auipc ((rd ubyte5)
           (imm ubyte20)))
  (:op ((funct op-funct)
        (rd ubyte5)
        (rs1 ubyte5)
        (rs2 ubyte5)))
  (:op-32 ((funct op-32-funct)
           (rd ubyte5)
           (rs1 ubyte5)
           (rs2 ubyte5)))
  (:jal ((rd ubyte5)
         (imm ubyte20)))
  (:jalr ((rd ubyte5)
          (rs1 ubyte5)
          (imm ubyte12)))
  (:branch ((funct branch-funct)
            (rs1 ubyte5)
            (rs2 ubyte5)
            (imm ubyte12)))
  (:load ((funct load-funct)
          (rd ubyte5)
          (rs1 ubyte5)
          (imm ubyte12)))
  (:store ((funct store-funct)
           (rs1 ubyte5)
           (rs2 ubyte5)
           (imm ubyte12)))
  :pred instrp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption instr-option
  instr
  :short "Fixtype of optional instructions."
  :pred instr-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define instr-validp ((instr instrp) (feat featp))
  :returns (yes/no booleanp)
  :short "Check if an instruction is valid with respect to given features."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certain instructions are only valid in RV32I/RV32E or RV64I/RV64E.")
   (xdoc::p
    "In RV32E/RV64E, register indices are only 4 bits.")
   (xdoc::p
    "Certain instructions are only valid with the M extension."))
  (b* (((feat feat) feat))
    (instr-case instr
                :op-imm (implies (feat-embedp feat)
                                 (and (ubyte4p instr.rd)
                                      (ubyte4p instr.rs1)))
                :op-imms32 (and (feat-32p feat)
                                (implies (feat-embedp feat)
                                         (and (ubyte4p instr.rd)
                                              (ubyte4p instr.rs1))))
                :op-imms64 (and (feat-64p feat)
                                (implies (feat-embedp feat)
                                         (and (ubyte4p instr.rd)
                                              (ubyte4p instr.rs1))))
                :op-imm-32 (and (feat-64p feat)
                                (implies (feat-embedp feat)
                                         (and (ubyte4p instr.rd)
                                              (ubyte4p instr.rs1))))
                :op-imms-32 (and (feat-64p feat)
                                 (implies (feat-embedp feat)
                                          (and (ubyte4p instr.rd)
                                               (ubyte4p instr.rs1))))
                :lui (implies (feat-embedp feat)
                              (ubyte4p instr.rd))
                :auipc (implies (feat-embedp feat)
                                (ubyte4p instr.rd))
                :op (and (implies (feat-embedp feat)
                                  (and (ubyte4p instr.rd)
                                       (ubyte4p instr.rs1)
                                       (ubyte4p instr.rs2)))
                         (implies (member-eq (op-funct-kind instr.funct)
                                             '(:mul :mulh :mulhu :mulhsu
                                               :div :divu :rem :remu))
                                  (feat-mp feat)))
                :op-32 (and (feat-64p feat)
                            (implies (feat-embedp feat)
                                     (and (ubyte4p instr.rd)
                                          (ubyte4p instr.rs1)
                                          (ubyte4p instr.rs2)))
                            (implies (member-eq (op-32-funct-kind instr.funct)
                                                '(:mulw
                                                  :divw :divuw :remw :remuw))
                                     (feat-mp feat)))
                :jal (implies (feat-embedp feat)
                              (ubyte4p instr.rd))
                :jalr (implies (feat-embedp feat)
                               (and (ubyte4p instr.rd)
                                    (ubyte4p instr.rs1)))
                :branch (implies (feat-embedp feat)
                                 (and (ubyte4p instr.rs1)
                                      (ubyte4p instr.rs2)))
                :load (and (load-funct-case instr.funct
                                            :lb t
                                            :lbu t
                                            :lh t
                                            :lhu t
                                            :lw t
                                            :lwu (feat-64p feat)
                                            :ld (feat-64p feat))
                           (implies (feat-embedp feat)
                                    (and (ubyte4p instr.rd)
                                         (ubyte4p instr.rs1))))
                :store (and (store-funct-case instr.funct
                                              :sb t
                                              :sh t
                                              :sw t
                                              :sd (feat-64p feat))
                            (implies (feat-embedp feat)
                                     (and (ubyte4p instr.rs1)
                                          (ubyte4p instr.rs2))))))
  :hooks (:fix))
