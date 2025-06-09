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

(include-book "instructions")

(include-book "logappn")

(include-book "centaur/bitops/part-select" :dir :system)
(include-book "kestrel/fty/ubyte3" :dir :system)
(include-book "kestrel/fty/ubyte7" :dir :system)
(include-book "kestrel/fty/ubyte32" :dir :system)

(local (include-book "library-extensions"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "kestrel/fty/ubyte5-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte6-ihs-theorems" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decoding-executable
  :parents (riscv)
  :short "Executable decoding of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Instructions are encoded as specified in [ISA] and [ISAP],
     and as formalized in @(see encoding).
     We define an executable decoder that maps the encodings of instructions
     to the corresponding instruction fixtypes
     defined in @(see instructions).")
   (xdoc::p
    "Currently we only cover the decoding of
     the instructions defined in @(see instructions).
     We only handle the normal encodings,
     i.e. not the compressed ones in the C extension [ISA:26];
     thus, our decoder operates on 32-bit encodings."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-opcode ((enc ubyte32p))
  :returns (opcode ubyte7p :hints (("Goal" :in-theory (enable ubyte7p))))
  :short "Retrieve the opcode field of an instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always in the low 7 bits of the 32-bit encoding
     [ISA:2.2] [ISA:2.3]."))
  (part-select enc :low 0 :high 6))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-rd ((enc ubyte32p))
  :returns (rd ubyte5p :hints (("Goal" :in-theory (enable ubyte5p))))
  :short "Retrieve the @('rd') field of an instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always in the bits 7-11 of the 32-bit encoding,
     for the formats with an @('rd') field [ISA:2.2] [ISA:2.3]."))
  (part-select enc :low 7 :high 11))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-rs1 ((enc ubyte32p))
  :returns (rs1 ubyte5p :hints (("Goal" :in-theory (enable ubyte5p))))
  :short "Retrieve the @('rs1') field of an instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always in the bits 15-19 of the 32-bit encoding,
     for the formats with an @('rs1') field [ISA:2.2] [ISA:2.3]."))
  (part-select enc :low 15 :high 19))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-rs2 ((enc ubyte32p))
  :returns (rs2 ubyte5p :hints (("Goal" :in-theory (enable ubyte5p))))
  :short "Retrieve the @('rs2') field of an instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always in the bits 20-24 of the 32-bit encoding,
     for the formats with an @('rs2') field [ISA:2.2] [ISA:2.3]."))
  (part-select enc :low 20 :high 24))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-funct3 ((enc ubyte32p))
  :returns (funct3 ubyte3p :hints (("Goal" :in-theory (enable ubyte3p))))
  :short "Retrieve the @('funct3') field of an instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always in the bits 12-14 of the 32-bit encoding,
     for the formats with an @('funct3') field [ISA:2.2] [ISA:2.3]."))
  (part-select enc :low 12 :high 14))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-funct7 ((enc ubyte32p))
  :returns (funct7 ubyte7p :hints (("Goal" :in-theory (enable ubyte7p))))
  :short "Retrieve the @('funct7') field of an instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always in the bits 25-31 of the 32-bit encoding,
     for the formats with an @('funct7') field [ISA:2.2] [ISA:2.3]."))
  (part-select enc :low 25 :high 31))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-itype ((enc ubyte32p))
  :returns (imm ubyte12p :hints (("Goal" :in-theory (enable ubyte12p))))
  :short "Retrieve the immediate field of an I-type instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the bits 20-31 of the 32-bit encoding [ISA:2.2],
     which directly form the bits @('imm[11:0]') of the immediate."))
  (part-select enc :low 20 :high 31))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-stype ((enc ubyte32p))
  :returns (imm ubyte12p :hints (("Goal" :in-theory (enable ubyte12p
                                                            unsigned-byte-p
                                                            ifix
                                                            integer-range-p))))
  :short "Retrieve the immediate field of an S-type instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of two chunks, in bits 7-11 and 25-31 [ISA:2.2],
     which, when joined, form the bits @('imm[11:0]') of the immediate."))
  (b* ((imm[4.0] (part-select enc :low 7 :high 11))
       (imm[11.5] (part-select enc :low 25 :high 31)))
    (logappn 5 imm[4.0]
             7 imm[11.5])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-btype ((enc ubyte32p))
  :returns (imm ubyte12p :hints (("Goal" :in-theory (enable ubyte12p
                                                            unsigned-byte-p
                                                            ifix
                                                            integer-range-p))))
  :short "Retrieve the immediate field of a B-type instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of four chunks, in bits 8-11, 25-30, 7, and 31 [ISA:2.2],
     which, when joined, form the bits @('imm[12:1]') of the immediate.
     We return those 12 bits,
     not @('imm[12:0]') with @('imm[0]') implicitly 0."))
  (b* ((imm[4.1] (part-select enc :low 8 :high 11))
       (imm[10.5] (part-select enc :low 25 :high 30))
       (imm[11] (part-select enc :low 7 :high 7))
       (imm[12] (part-select enc :low 31 :high 31)))
    (logappn 4 imm[4.1]
             6 imm[10.5]
             1 imm[11]
             1 imm[12])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-utype ((enc ubyte32p))
  :returns (imm ubyte20p :hints (("Goal" :in-theory (enable ubyte20p))))
  :short "Retrieve the immediate field of a U-type instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the bits 12-31 of the 32-bit encoding [ISA:2.2],
     which directly form the bits @('imm[31:12]') of the immediate.
     We return those 20 bits,
     not @('imm[31:0]') with @('imm[11:0]') implicitly 0."))
  (part-select enc :low 12 :high 31))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-jtype ((enc ubyte32p))
  :returns (imm ubyte20p :hints (("Goal" :in-theory (enable ubyte20p
                                                            unsigned-byte-p
                                                            ifix
                                                            integer-range-p))))
  :short "Retrieve the immediate field of a J-type instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of four chunks, in bits 21-30, 20, 12-19, and 31 [ISA:2.2],
     which, when joined, form the bits @('imm[20:1] of the immediate.
     We return those 20 bits,
     not @('imm[20:0') with @('imm[0]') implicitly 0."))
  (b* ((imm[10.1] (part-select enc :low 21 :high 30))
       (imm[11] (part-select enc :low 20 :high 20))
       (imm[19.12] (part-select enc :low 12 :high 19))
       (imm[20] (part-select enc :low 31 :high 31)))
    (logappn 10 imm[10.1]
             1 imm[11]
             8 imm[19.12]
             1 imm[20])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-fields-rtype ((enc ubyte32p))
  :returns (mv (funct3 ubyte3p)
               (funct7 ubyte7p)
               (rd ubyte5p)
               (rs1 ubyte5p)
               (rs2 ubyte5p))
  :short "Retrieve the non-opcode fields of an R-type instruction
          [ISA:2.2] [ISA:2.3]."
  (mv (get-funct3 enc)
      (get-funct7 enc)
      (get-rd enc)
      (get-rs1 enc)
      (get-rs2 enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-fields-itype ((enc ubyte32p))
  :returns (mv (funct3 ubyte3p)
               (rd ubyte5p)
               (rs1 ubyte5p)
               (imm ubyte12p))
  :short "Retrieve the non-opcode fields of an I-type instruction
          [ISA:2.2] [ISA:2.3]."
  (mv (get-funct3 enc)
      (get-rd enc)
      (get-rs1 enc)
      (get-imm-itype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-fields-stype ((enc ubyte32p))
  :returns (mv (funct3 ubyte3p)
               (rs1 ubyte5p)
               (rs2 ubyte5p)
               (imm ubyte12p))
  :short "Retrieve the non-opcode fields of an S-type instruction
          [ISA:2.2] [ISA:2.3]."
  (mv (get-funct3 enc)
      (get-rs1 enc)
      (get-rs2 enc)
      (get-imm-stype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-fields-utype ((enc ubyte32p))
  :returns (mv (rd ubyte5p)
               (imm ubyte20p))
  :short "Retrieve the non-opcode fields of a U-type instruction
          [ISA:2.2] [ISA:2.3]."
  (mv (get-rd enc)
      (get-imm-utype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-fields-btype ((enc ubyte32p))
  :returns (mv (funct3 ubyte3p)
               (rs1 ubyte5p)
               (rs2 ubyte5p)
               (imm ubyte12p))
  :short "Retrieve the non-opcode fields of a B-type instruction
          [ISA:2.3]."
  (mv (get-funct3 enc)
      (get-rs1 enc)
      (get-rs2 enc)
      (get-imm-btype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-fields-jtype ((enc ubyte32p))
  :returns (mv (rd ubyte5p)
               (imm ubyte20p))
  :short "Retrieve the non-opcode fields of a J-type instruction
          [ISA:2.3]."
  (mv (get-rd enc)
      (get-imm-jtype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decodex ((enc ubyte32p) (feat featp))
  :returns (instr? instr-optionp)
  :short "Executable instruction decoder."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('x') in the name stands for `executable'.")
   (xdoc::p
    "The first input is a 32-bit encoding of the instruction;
     the second input consists of the features, which affect decoding.
     If decoding is successful, we return the instruction.
     If decoding is unsuccessful, we return @('nil').")
   (xdoc::p
    "The values of the encoded fields, which we write in binary notation,
     are taken from the instruction listings in [ISA:34].")
   (xdoc::p
    "We retrieve the opcode, and we dispatch based on it.
     Each dispatch first retrieves the fields, based on the format,
     and then checks them to see whether they are valid,
     and to determine which instruction is encoded, if any.")
   (xdoc::p
    "With the @('OP-IMM') opcode,
     shift instructions are encoded in a specialization of the I-type format,
     where the low 5 or 6 bits of the immediate are the shift amount,
     while the high 7 or 6 bits need to have specific values.
     Whether the immediate is split into 5 low bits and 7 high bits,
     or into 6 low bits and 6 high bits,
     depends on whether we are in RV32I or RV64I mode,
     so we use the features passed as input to this function.
     We generate slightly different shift instructions, in the two cases.")
   (xdoc::p
    "With the @('OP-IMM-32') opcode,
     shift instructions are encoded in a specialization of the I-type format,
     where the low 5 bits of the immediate are the shift amount,
     while the high 7 bits need to have specific values."))
  (b* ((enc (ubyte32-fix enc)))
    (case (get-opcode enc)
      (#b0000011 ; LOAD [ISA:2.6] [ISA:4.3]
       (b* (((mv funct3 rd rs1 imm) (get-fields-itype enc))
            ((unless (or (not (feat-embedp feat))
                         (and (ubyte4p rd)
                              (ubyte4p rs1))))
             nil)
            (funct (case funct3
                     (#b000 (load-funct-lb))
                     (#b001 (load-funct-lh))
                     (#b010 (load-funct-lw))
                     (#b011 (if (feat-64p feat)
                                (load-funct-ld)
                              nil))
                     (#b100 (load-funct-lbu))
                     (#b101 (load-funct-lhu))
                     (#b110 (if (feat-64p feat)
                                (load-funct-lwu)
                              nil))
                     (#b111 nil)))
            ((unless funct) nil))
         (instr-load funct rd rs1 imm)))
      (#b0010011 ; OP-IMM [ISA:2.4.1]
       (b* (((mv funct3 rd rs1 imm) (get-fields-itype enc))
            ((unless (or (not (feat-embedp feat))
                         (and (ubyte4p rd)
                              (ubyte4p rs1))))
             nil)
            (funct (case funct3
                     (#b000 (op-imm-funct-addi))
                     (#b001 nil) ; could be SLLI, handled below
                     (#b010 (op-imm-funct-slti))
                     (#b011 (op-imm-funct-sltiu))
                     (#b100 (op-imm-funct-xori))
                     (#b101 nil) ; could be SRLI or SRAI, handled below
                     (#b110 (op-imm-funct-ori))
                     (#b111 (op-imm-funct-andi))))
            ((when funct) (instr-op-imm funct rd rs1 imm)))
         (if (feat-64p feat)
             (b* ((loimm (part-select imm :low 0 :high 5))
                  (hiimm (part-select imm :low 6 :high 11))
                  ((when (= funct3 #b001))
                   (if (= hiimm #b000000)
                       (instr-op-imms64 (op-imms-funct-slli) rd rs1 loimm)
                     nil)))
               (case hiimm
                 (#b000000 (instr-op-imms64 (op-imms-funct-srli) rd rs1 loimm))
                 (#b010000 (instr-op-imms64 (op-imms-funct-srai) rd rs1 loimm))
                 (t nil)))
           (b* ((loimm (part-select imm :low 0 :high 4))
                (hiimm (part-select imm :low 5 :high 11))
                ((when (= funct3 #b001))
                 (if (= hiimm #b0000000)
                     (instr-op-imms32 (op-imms-funct-slli) rd rs1 loimm)
                   nil)))
             (case hiimm
               (#b0000000 (instr-op-imms32 (op-imms-funct-srli) rd rs1 loimm))
               (#b0100000 (instr-op-imms32 (op-imms-funct-srai) rd rs1 loimm))
               (t nil))))))
      (#b0010111 ; AUIPC [ISA:2.4.1]
       (b* (((mv rd imm) (get-fields-utype enc))
            ((unless (or (not (feat-embedp feat))
                         (ubyte4p rd)))
             nil))
         (instr-auipc rd imm)))
      (#b0011011 ; OP-IMM-32 [ISA:4.2.1]
       (b* (((unless (feat-64p feat)) nil)
            ((mv funct3 rd rs1 imm) (get-fields-itype enc))
            ((unless (or (not (feat-embedp feat))
                         (and (ubyte4p rd)
                              (ubyte4p rs1))))
             nil)
            ((when (= funct3 #b000))
             (instr-op-imm-32 (op-imm-32-funct-addiw) rd rs1 imm))
            (loimm (part-select imm :low 0 :high 4))
            (hiimm (part-select imm :low 5 :high 11))
            ((when (= funct3 #b001))
             (if (= hiimm #b0000000)
                 (instr-op-imms-32 (op-imms-32-funct-slliw) rd rs1 loimm)
               nil))
            ((when (= funct3 #b101))
             (case hiimm
               (#b0000000 (instr-op-imms-32
                           (op-imms-32-funct-srliw) rd rs1 loimm))
               (#b0100000 (instr-op-imms-32
                           (op-imms-32-funct-sraiw) rd rs1 loimm))
               (t nil))))
         nil))
      (#b0100011 ; STORE [ISA:2.6] [ISA:4.3]
       (b* (((mv funct3 rs1 rs2 imm) (get-fields-stype enc))
            ((unless (or (not (feat-embedp feat))
                         (and (ubyte4p rs1)
                              (ubyte4p rs2))))
             nil)
            (funct (case funct3
                     (#b000 (store-funct-sb))
                     (#b001 (store-funct-sh))
                     (#b010 (store-funct-sw))
                     (#b011 (if (feat-64p feat)
                                (store-funct-sd)
                              nil))
                     (t nil)))
            ((unless funct) nil))
         (instr-store funct rs1 rs2 imm)))
      (#b0110011 ; OP [ISA:2.4.2] [ISA:13.1] [ISA:13.2]
       (b* (((mv funct3 funct7 rd rs1 rs2) (get-fields-rtype enc))
            ((unless (or (not (feat-embedp feat))
                         (and (ubyte4p rd)
                              (ubyte4p rs1)
                              (ubyte4p rs2))))
             nil)
            (funct (case funct3
                     (#b000 (case funct7
                              (#b0000000 (op-funct-add))
                              (#b0000001 (if (feat-mp feat)
                                             (op-funct-mul)
                                           nil))
                              (#b0100000 (op-funct-sub))
                              (t nil)))
                     (#b001 (case funct7
                              (#b0000000 (op-funct-sll))
                              (#b0000001 (if (feat-mp feat)
                                             (op-funct-mulh)
                                           nil))
                              (t nil)))
                     (#b010 (case funct7
                              (#b0000000 (op-funct-slt))
                              (#b0000001 (if (feat-mp feat)
                                             (op-funct-mulhsu)
                                           nil))
                              (t nil)))
                     (#b011 (case funct7
                              (#b0000000 (op-funct-sltu))
                              (#b0000001 (if (feat-mp feat)
                                             (op-funct-mulhu)
                                           nil))
                              (t nil)))
                     (#b100 (case funct7
                              (#b0000000 (op-funct-xor))
                              (#b0000001 (if (feat-mp feat)
                                             (op-funct-div)
                                           nil))
                              (t nil)))
                     (#b101 (case funct7
                              (#b0000000 (op-funct-srl))
                              (#b0000001 (if (feat-mp feat)
                                             (op-funct-divu)
                                           nil))
                              (#b0100000 (op-funct-sra))
                              (t nil)))
                     (#b110 (case funct7
                              (#b0000000 (op-funct-or))
                              (#b0000001 (if (feat-mp feat)
                                             (op-funct-rem)
                                           nil))
                              (t nil)))
                     (#b111 (case funct7
                              (#b0000000 (op-funct-and))
                              (#b0000001 (if (feat-mp feat)
                                             (op-funct-remu)
                                           nil))
                              (t nil)))))
            ((unless funct) nil))
         (instr-op funct rd rs1 rs2)))
      (#b0110111 ; LUI [ISA:2.4.1]
       (b* (((mv rd imm) (get-fields-utype enc))
            ((unless (or (not (feat-embedp feat))
                         (ubyte4p rd)))
             nil))
         (instr-lui rd imm)))
      (#b0111011 ; OP-32 [ISA:4.2.2]
       (b* (((unless (feat-64p feat)) nil)
            ((mv funct3 funct7 rd rs1 rs2) (get-fields-rtype enc))
            ((unless (or (not (feat-embedp feat))
                         (and (ubyte4p rd)
                              (ubyte4p rs1)
                              (ubyte4p rs2))))
             nil)
            (funct (case funct3
                     (#b000 (case funct7
                              (#b0000000 (op-32-funct-addw))
                              (#b0000001 (if (feat-mp feat)
                                             (op-32-funct-mulw)
                                           nil))
                              (#b0100000 (op-32-funct-subw))
                              (t nil)))
                     (#b001 (case funct7
                              (#b0000000 (op-32-funct-sllw))
                              (t nil)))
                     (#b010 nil)
                     (#b011 nil)
                     (#b100 (case funct7
                              (#b0000001 (if (feat-mp feat)
                                             (op-32-funct-divw)
                                           nil))
                              (t nil)))
                     (#b101 (case funct7
                              (#b0000000 (op-32-funct-srlw))
                              (#b0000001 (if (feat-mp feat)
                                             (op-32-funct-divuw)
                                           nil))
                              (#b0100000 (op-32-funct-sraw))
                              (t nil)))
                     (#b110 (case funct7
                              (#b0000001 (if (feat-mp feat)
                                             (op-32-funct-remw)
                                           nil))
                              (t nil)))
                     (#b111 (case funct7
                              (#b0000001 (if (feat-mp feat)
                                             (op-32-funct-remuw)
                                           nil))
                              (t nil)))))
            ((unless funct) nil))
         (instr-op-32 funct rd rs1 rs2)))
      (#b1100011 ; BRANCH [ISA:2.5.2]
       (b* (((mv funct3 rs1 rs2 imm) (get-fields-btype enc))
            ((unless (or (not (feat-embedp feat))
                         (and (ubyte4p rs1)
                              (ubyte4p rs2))))
             nil)
            (funct (case funct3
                     (#b000 (branch-funct-beq))
                     (#b001 (branch-funct-bne))
                     (#b010 nil)
                     (#b011 nil)
                     (#b100 (branch-funct-blt))
                     (#b101 (branch-funct-bge))
                     (#b110 (branch-funct-bltu))
                     (#b111 (branch-funct-bgeu))))
            ((unless funct) nil))
         (instr-branch funct rs1 rs2 imm)))
      (#b1100111 ; JALR [ISA:2.5.1]
       (b* (((mv funct3 rd rs1 imm) (get-fields-itype enc))
            ((unless (or (not (feat-embedp feat))
                         (and (ubyte4p rd)
                              (ubyte4p rs1))))
             nil)
            ((unless (= funct3 0)) nil))
         (instr-jalr rd rs1 imm)))
      (#b1101111 ; JAL [ISA:2.5.1]
       (b* (((mv rd imm) (get-fields-jtype enc))
            ((unless (or (not (feat-embedp feat))
                         (ubyte4p rd)))
             nil))
         (instr-jal rd imm)))
      (t nil)))
  :hooks (:fix)

  ///

  (defret instr-validp-of-decodex
    (implies instr?
             (instr-validp instr? feat))
    :hints (("Goal"
             :do-not '(preprocess) ; for speed
             :in-theory (enable instr-validp)))))
