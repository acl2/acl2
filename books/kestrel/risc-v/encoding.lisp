; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "instructions")

(include-book "library-extensions")

(include-book "centaur/bitops/part-select" :dir :system)
(include-book "kestrel/fty/ubyte3" :dir :system)
(include-book "kestrel/fty/ubyte6" :dir :system)
(include-book "kestrel/fty/ubyte7" :dir :system)
(include-book "kestrel/fty/ubyte32" :dir :system)


(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ encoding
  :parents (riscv)
  :short "Encoding of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Instructions are encoded as specified in [ISA] and [ISAP].
     Here we define encoding as a mapping from "
    (xdoc::seetopic "instructions" "the instruction fixtypes")
    " to their encodings.")
   (xdoc::p
    "Without the C extension [ISA:26],
     instructions are encoded in 32 bits per instruction.
     So we define our mapping from instructions to 32-bit unsigned integers.
     We plan to model the C extension in the future:
     we will define a second encoding mapping,
     which maps certain instructions to 16 bits per instruction;
     the @(see features) will be also extended with
     an indication of whether the C extension is present.")
   (xdoc::p
    "Even without modeling the C extension yet,
     our encoding mapping depends on the @(see features),
     because it is only defined on instructions
     that are valid according to the @(see features)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-op-imm-funct ((funct op-imm-funct-p))
  :returns (funct3 ubyte3p)
  :short "Encode the name of
          a non-shift instruction with the @('OP-IMM') opcode
          into the @('funct3') field
          [ISA:2.4.1] [ISA:34]."
  (op-imm-funct-case
   funct
   :addi  #b000
   :slti  #b010
   :sltiu #b011
   :andi  #b111
   :ori   #b110
   :xori  #b100)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-op-imms32-funct ((funct op-imms-funct-p))
  :returns (mv (funct3 ubyte3p)
               (hi7imm ubyte7p))
  :short "Encode the name of
          a 32-bit shift instruction with the @('OP-IMM') opcode
          into the @('funct3') field and the high 7 immediate bits
          [ISA:2.4.1] [ISA:34]."
  (op-imms-funct-case
   funct
   :slli (mv #b001 #b0000000)
   :srli (mv #b101 #b0000000)
   :srai (mv #b101 #b0100000))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-op-imms64-funct ((funct op-imms-funct-p))
  :returns (mv (funct3 ubyte3p)
               (hi6imm ubyte6p))
  :short "Encode the name of
          a 64-bit shift instruction with the @('OP-IMM') opcode
          into the @('funct3') field and the high 6 immediate bits
          [ISA:4.2.1] [ISA:34]."
  (op-imms-funct-case
   funct
   :slli (mv #b001 #b000000)
   :srli (mv #b101 #b000000)
   :srai (mv #b101 #b010000))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-op-imm-32-funct ((funct op-imm-32-funct-p))
  :returns (funct3 ubyte3p)
  :short "Encode the name of
          a non-shift instruction with the @('OP-IMM-32') opcode
          into the @('funct3') field
          [ISA:4.2.1] [ISA:34]."
  (op-imm-32-funct-case
   funct
   :addiw #b000)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-op-imms-32-funct ((funct op-imms-32-funct-p))
  :returns (mv (funct3 ubyte3p)
               (hi6imm ubyte6p))
  :short "Encode the name of
          a shift instruction with the @('OP-IMM') opcode
          into the @('funct3') field and the high 6 immediate bits
          [ISA:4.2.1] [ISA:34]."
  (op-imms-32-funct-case
   funct
   :slliw (mv #b001 #b000000)
   :srliw (mv #b101 #b000000)
   :sraiw (mv #b101 #b010000))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-op-funct ((funct op-funct-p))
  :returns (mv (funct3 ubyte3p)
               (funct7 ubyte7p))
  :short "Encode the name of
          an instruction with the @('OP') opcode
          into the @('funct3') and @('funct7') fields
          [ISA:2.4.2] [ISA:13.1] [ISA:13.2] [ISA:34]."
  (op-funct-case
   funct
   :add    (mv #b000 #b0000000)
   :sub    (mv #b000 #b0100000)
   :slt    (mv #b010 #b0000000)
   :sltu   (mv #b011 #b0000000)
   :and    (mv #b111 #b0000000)
   :or     (mv #b110 #b0000000)
   :xor    (mv #b100 #b0000000)
   :sll    (mv #b001 #b0000000)
   :srl    (mv #b101 #b0000000)
   :sra    (mv #b101 #b0100000)
   :mul    (mv #b000 #b0000001)
   :mulh   (mv #b001 #b0000001)
   :mulhu  (mv #b011 #b0000001)
   :mulhsu (mv #b010 #b0000001)
   :div    (mv #b100 #b0000001)
   :divu   (mv #b101 #b0000001)
   :rem    (mv #b110 #b0000001)
   :remu   (mv #b111 #b0000001))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-op-32-funct ((funct op-32-funct-p))
  :returns (mv (funct3 ubyte3p)
               (funct7 ubyte7p))
  :short "Encode the name of
          an instruction with the @('OP-32') opcode
          into the @('funct3') and @('funct7') fields
          [ISA:4.2.2] [ISA:13.1] [ISA:13.2] [ISA:34]."
  (op-32-funct-case
   funct
   :addw  (mv #b000 #b0000000)
   :subw  (mv #b000 #b0100000)
   :sllw  (mv #b001 #b0000000)
   :srlw  (mv #b101 #b0000000)
   :sraw  (mv #b101 #b0100000)
   :mulw  (mv #b000 #b0000001)
   :divw  (mv #b100 #b0000001)
   :divuw (mv #b101 #b0000001)
   :remw  (mv #b110 #b0000001)
   :remuw (mv #b111 #b0000001))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-branch-funct ((funct branch-funct-p))
  :returns (funct3 ubyte3p)
  :short "Encode the name of
          an instruction with the @('BRANCH') opcode
          into the @('funct3') field
          [ISA:2.5.2] [ISA:34]."
  (branch-funct-case
   funct
   :beq  #b000
   :bne  #b001
   :blt  #b100
   :bge  #b101
   :bltu #b110
   :bgeu #b111)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-load-funct ((funct load-funct-p))
  :returns (funct3 ubyte3p)
  :short "Encode the name of
          an instruction with the @('LOAD') opcode
          into the @('func3') field
          [ISA:2.6] [ISA:4.3] [ISA:34]."
  (load-funct-case
   funct
   :lb  #b000
   :lbu #b100
   :lh  #b001
   :lhu #b101
   :lw  #b010
   :lwu #b110
   :ld  #b011)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode-store-funct ((funct store-funct-p))
  :returns (funct3 ubyte3p)
  :short "Encode the name of
          an instruction with the @('STORE') opcode
          into the @('funct3') field
          [ISA:2.6] [ISA:4.3] [ISA:34]."
  (store-funct-case
   funct
   :sb #b000
   :sh #b001
   :sw #b010
   :sd #b011)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define encode ((instr instrp) (feat featp))
  :guard (instr-validp instr feat)
  (declare (ignore feat))
  :returns (encoding ubyte32p
                     :hints (("Goal" :in-theory (enable ifix
                                                        ubyte32p
                                                        unsigned-byte-p
                                                        integer-range-p
                                                        loghead))))
  :short "Encode an instruction in the normal way (i.e. in 32 bits)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the fields and we concatenate them using @('logappn').")
   (xdoc::p
    "This is based on
     [ISA:2.4.1] [ISA:2.4.2] [ISA:2.5.1] [ISA:2.5.2] [ISA:2.6]
     [ISA:4.2.1] [ISA:4.2.2] [ISA:4.3]
     [ISA:34].")
   (xdoc::p
    "Note that the 20 immediate bits in @('JAL')
     are designated as bits 1 to 20 in [ISA:2.5.1], not 0 to 19.
     Thus, the indices passed to @(tsee part-select) and @(tsee logbit)
     are one less than the ones shown in the instruction format.
     A similar remark applies to the immediate bits
     in the @('BRANCH') instructions [ISA:2.5.2]."))
  (instr-case
   instr
   :op-imm (b* ((opcode #b0010011)
                (funct3 (encode-op-imm-funct instr.funct)))
             (logappn 7 opcode
                      5 instr.rd
                      3 funct3
                      5 instr.rs1
                      12 instr.imm))
   :op-imms32 (b* ((opcode #b0010011)
                   ((mv funct3 hi7imm) (encode-op-imms32-funct instr.funct)))
                (logappn 7 opcode
                         5 instr.rd
                         3 funct3
                         5 instr.rs1
                         5 instr.imm
                         7 hi7imm))
   :op-imms64 (b* ((opcode #b0010011)
                   ((mv funct3 hi6imm) (encode-op-imms64-funct instr.funct)))
                (logappn 7 opcode
                         5 instr.rd
                         3 funct3
                         5 instr.rs1
                         6 instr.imm
                         6 hi6imm))
   :op-imm-32 (b* ((opcode #b0011011)
                   (funct3 (encode-op-imm-32-funct instr.funct)))
                (logappn 7 opcode
                         5 instr.rd
                         3 funct3
                         5 instr.rs1
                         12 instr.imm))
   :op-imms-32 (b* ((opcode #b0011011)
                    ((mv funct3 hi6imm) (encode-op-imms-32-funct instr.funct)))
                 (logappn 7 opcode
                          5 instr.rd
                          3 funct3
                          5 instr.rs1
                          5 instr.imm
                          1 0
                          6 hi6imm))
   :lui (b* ((opcode #b0110111))
          (logappn 7 opcode
                   5 instr.rd
                   20 instr.imm))
   :auipc (b* ((opcode #b0010111))
            (logappn 7 opcode
                     5 instr.rd
                     10 instr.imm))
   :op (b* ((opcode #b0110011)
            ((mv funct3 funct7) (encode-op-funct instr.funct)))
         (logappn 7 opcode
                  5 instr.rd
                  3 funct3
                  5 instr.rs1
                  5 instr.rs2
                  7 funct7))
   :op-32 (b* ((opcode #b0111011)
               ((mv funct3 funct7) (encode-op-32-funct instr.funct)))
            (logappn 7 opcode
                     5 instr.rd
                     3 funct3
                     5 instr.rs1
                     5 instr.rs2
                     7 funct7))
   :jal (b* ((opcode #b1101111)
             (imm-10-1 (part-select instr.imm :low 0 :high 9))
             (imm-11 (logbit 10 instr.imm))
             (imm-19-12 (part-select instr.imm :low 11 :high 18))
             (imm-20 (logbit 19 instr.imm)))
          (logappn 7 opcode
                   5 instr.rd
                   8 imm-19-12
                   1 imm-11
                   10 imm-10-1
                   1 imm-20))
   :jalr (b* ((opcode #b1100111)
              (funct3 #b000))
           (logappn 7 opcode
                    5 instr.rd
                    3 funct3
                    5 instr.rs1
                    12 instr.imm))
   :branch (b* ((opcode #b1100011)
                (funct3 (encode-branch-funct instr.funct))
                (imm-4-1 (part-select instr.imm :low 0 :high 3))
                (imm-10-5 (part-select instr.imm :low 4 :high 9))
                (imm-11 (logbit 10 instr.imm))
                (imm-12 (logbit 11 instr.imm)))
             (logappn 7 opcode
                      1 imm-11
                      4 imm-4-1
                      3 funct3
                      5 instr.rs1
                      5 instr.rs2
                      6 imm-10-5
                      1 imm-12))
   :load (b* ((opcode #b0000011)
              (funct3 (encode-load-funct instr.funct)))
           (logappn 7 opcode
                    5 instr.rs1
                    3 funct3
                    5 instr.rs1
                    12 instr.imm))
   :store (b* ((opcode #b0100011)
               (funct3 (encode-store-funct instr.funct))
               (imm-4-0 (part-select instr.imm :low 0 :high 4))
               (imm-11-5 (part-select instr.imm :low 5 :high 11)))
            (logappn 7 opcode
                     5 imm-4-0
                     3 funct3
                     5 instr.rs1
                     5 instr.rs2
                     7 imm-11-5)))
  :guard-hints (("Goal" :in-theory (enable fix ifix)))
  :hooks (:fix))
