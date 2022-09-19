; RISC-V Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (acoglio on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "bytes")
(include-book "library-extensions")

(include-book "instructions")

(include-book "centaur/bitops/part-select" :dir :system)
(include-book "kestrel/fty/ubyte32" :dir :system)

(local (include-book "ihs/logops-lemmas" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-opcode ((enc ubyte32p))
  :returns (opcode ubyte7p :hints (("Goal" :in-theory (enable ubyte7p))))
  (part-select enc :low 0 :high 6))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-rd ((enc ubyte32p))
  :returns (rd ubyte5p :hints (("Goal" :in-theory (enable ubyte5p))))
  (part-select enc :low 7 :high 11))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-rs1 ((enc ubyte32p))
  :returns (rs1 ubyte5p :hints (("Goal" :in-theory (enable ubyte5p))))
  (part-select enc :low 15 :high 19))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-rs2 ((enc ubyte32p))
  :returns (rs2 ubyte5p :hints (("Goal" :in-theory (enable ubyte5p))))
  (part-select enc :low 20 :high 24))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-funct3 ((enc ubyte32p))
  :returns (funct3 ubyte3p :hints (("Goal" :in-theory (enable ubyte3p))))
  (part-select enc :low 12 :high 14))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-funct7 ((enc ubyte32p))
  :returns (funct7 ubyte7p :hints (("Goal" :in-theory (enable ubyte7p))))
  (part-select enc :low 25 :high 31))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-itype ((enc ubyte32p))
  :returns (imm ubyte12p :hints (("Goal" :in-theory (enable ubyte12p))))
  (part-select enc :low 20 :high 31))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-stype ((enc ubyte32p))
  :returns (imm ubyte12p :hints (("Goal" :in-theory (enable ubyte12p))))
  (b* ((imm[4.0] (part-select enc :low 7 :high 11))
       (imm[11.5] (part-select enc :low 25 :high 31)))
    (+ imm[4.0]
       (ash imm[11.5] 5)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-btype ((enc ubyte32p))
  :returns (imm ubyte12p :hints (("Goal" :in-theory (enable ubyte12p))))
  (b* ((imm[4.1] (part-select enc :low 8 :width 4))
       (imm[10.5] (part-select enc :low 25 :width 6))
       (imm[11] (part-select enc :low 7 :width 1))
       (imm[12] (part-select enc :low 31 :width 1)))
    (+ imm[4.1]
       (ash imm[10.5] 4)
       (ash imm[11] 10)
       (ash imm[12] 11)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-utype ((enc ubyte32p))
  :returns (imm ubyte20p :hints (("Goal" :in-theory (enable ubyte20p))))
  (part-select enc :low 12 :high 31))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-imm-jtype ((enc ubyte32p))
  :returns (imm ubyte20p :hints (("Goal" :in-theory (enable ubyte20p))))
  (b* ((imm[10.1] (part-select enc :low 21 :width 10))
       (imm[11] (part-select enc :low 20 :width 1))
       (imm[19.12] (part-select enc :low 12 :width 8))
       (imm[20] (part-select enc :low 31 :width 1)))
    (+ imm[10.1]
       (ash imm[11] 10)
       (ash imm[19.12] 11)
       (ash imm[20] 19)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode-rtype ((enc ubyte32p))
  :returns (mv (funct3 ubyte3p)
               (funct7 ubyte7p)
               (rd ubyte5p)
               (rs1 ubyte5p)
               (rs2 ubyte5p))
  (mv (get-funct3 enc)
      (get-funct7 enc)
      (get-rd enc)
      (get-rs1 enc)
      (get-rs2 enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode-itype ((enc ubyte32p))
  :returns (mv (funct3 ubyte3p)
               (rd ubyte5p)
               (rs1 ubyte5p)
               (imm ubyte12p))
  (mv (get-funct3 enc)
      (get-rd enc)
      (get-rs1 enc)
      (get-imm-itype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode-stype ((enc ubyte32p))
  :returns (mv (funct3 ubyte3p)
               (rs1 ubyte5p)
               (rs2 ubyte5p)
               (imm ubyte12p))
  (mv (get-funct3 enc)
      (get-rs1 enc)
      (get-rs2 enc)
      (get-imm-stype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode-btype ((enc ubyte32p))
  :returns (mv (funct3 ubyte3p)
               (rs1 ubyte5p)
               (rs2 ubyte5p)
               (imm ubyte12p))
  (mv (get-funct3 enc)
      (get-rs1 enc)
      (get-rs2 enc)
      (get-imm-btype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode-utype ((enc ubyte32p))
  :returns (mv (rd ubyte5p)
               (imm ubyte20p))
  (mv (get-rd enc)
      (get-imm-utype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode-jtype ((enc ubyte32p))
  :returns (mv (rd ubyte5p)
               (imm ubyte20p))
  (mv (get-rd enc)
      (get-imm-jtype enc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decode ((enc ubyte32p))
  :returns (instr? maybe-instrp)
  (case (get-opcode enc)
    (#b0000011 (b* (((mv funct3 rd rs1 imm) (decode-itype enc))
                    (funct? (case funct3
                              (#b000 (load-funct-lb))
                              (#b001 (load-funct-lh))
                              (#b010 (load-funct-lw))
                              (#b011 (load-funct-ld))
                              (#b100 (load-funct-lbu))
                              (#b101 (load-funct-lhu))
                              (#b110 (load-funct-lwu))
                              (#b111 nil)))
                    ((unless funct?) nil))
                 (instr-load funct? rd rs1 imm)))
    (#b0010011 (b* (((mv funct3 rd rs1 imm) (decode-itype enc))
                    (funct? (case funct3
                              (#b000 (op-imm-funct-addi))
                              (#b010 (op-imm-funct-slti))
                              (#b011 (op-imm-funct-sltiu))
                              (#b100 (op-imm-funct-xori))
                              (#b110 (op-imm-funct-ori))
                              (#b111 (op-imm-funct-andi))
                              (t nil)))
                    ((when funct?) (instr-op-imm funct? rd rs1 imm))
                    (funct7 (get-funct7 enc))
                    (imm (loghead 6 imm))
                    ((when (= funct3 #b001))
                     (if (= funct7 #b000000)
                         (instr-op-imms (op-imms-funct-slli) rd rs1 imm)
                       nil)))
                 (case funct7
                   (#b000000 (instr-op-imms (op-imms-funct-srli) rd rs1 imm))
                   (#b010000 (instr-op-imms (op-imms-funct-srai) rd rs1 imm))
                   (t nil))))
    (#b0010111 (b* (((mv rd imm) (decode-utype enc)))
                 (instr-auipc rd imm)))
    (#b0011011 (b* (((mv funct3 rd rs1 imm) (decode-itype enc))
                    ((when (= funct3 #b000))
                     (instr-op-imm-32 (op-imm-32-funct-addiw) rd rs1 imm))
                    (funct7 (get-funct7 enc))
                    (imm (loghead 5 imm))
                    ((when (= funct3 #b001))
                     (if (= funct7 #b0000000)
                         (instr-op-imms-32 (op-imms-32-funct-slliw) rd rs1 imm)
                       nil))
                    ((unless (= funct3 #b101)) nil))
                 (case funct7
                   (#b0000000 (instr-op-imms-32
                               (op-imms-32-funct-srliw) rd rs1 imm))
                   (#b0100000 (instr-op-imms-32
                               (op-imms-32-funct-sraiw) rd rs1 imm))
                   (t nil))))
    (#b0100011 (b* (((mv funct3 rs1 rs2 imm) (decode-stype enc))
                    (funct? (case funct3
                              (#b000 (store-funct-sb))
                              (#b001 (store-funct-sh))
                              (#b010 (store-funct-sw))
                              (#b011 (store-funct-sd))
                              (t nil)))
                    ((unless funct?) nil))
                 (instr-store funct? rs1 rs2 imm)))
    (#b0110011 (b* (((mv funct3 funct7 rd rs1 rs2) (decode-rtype enc))
                    (funct? (case funct3
                              (#b000 (case funct7
                                       (#b0000000 (op-funct-add))
                                       (#b0100000 (op-funct-sub))
                                       (t nil)))
                              (#b001 (case funct7
                                       (#b0000000 (op-funct-sll))
                                       (t nil)))
                              (#b010 (case funct7
                                       (#b0000000 (op-funct-slt))
                                       (t nil)))
                              (#b011 (case funct7
                                       (#b0000000 (op-funct-sltu))
                                       (t nil)))
                              (#b100 (case funct7
                                       (#b0000000 (op-funct-xor))
                                       (t nil)))
                              (#b101 (case funct7
                                       (#b0000000 (op-funct-srl))
                                       (#b0100000 (op-funct-sra))
                                       (t nil)))
                              (#b110 (case funct7
                                       (#b0000000 (op-funct-or))
                                       (t nil)))
                              (#b111 (case funct7
                                       (#b0000000 (op-funct-and))
                                       (t nil)))))
                    ((unless funct?) nil))
                 (instr-op funct? rd rs1 rs2)))
    (#b0110111 (b* (((mv rd imm) (decode-utype enc)))
                 (instr-lui rd imm)))
    (#b0111011 (b* (((mv funct3 funct7 rd rs1 rs2) (decode-rtype enc))
                    (funct? (case funct3
                              (#b000 (case funct7
                                       (#b0000000 (op-32-funct-addw))
                                       (#b0100000 (op-32-funct-subw))
                                       (t nil)))
                              (#b001 (op-32-funct-sllw))
                              (#b101 (case funct7
                                       (#b0000000 (op-32-funct-srlw))
                                       (#b0100000 (op-32-funct-sraw))
                                       (t nil)))
                              (t nil)))
                    ((unless funct?) nil))
                 (instr-op-32 funct? rd rs1 rs2)))
    (#b1100011 (b* (((mv funct3 rs1 rs2 imm) (decode-btype enc))
                    (funct? (case funct3
                              (#b000 (branch-funct-beq))
                              (#b001 (branch-funct-bne))
                              (#b100 (branch-funct-blt))
                              (#b101 (branch-funct-bge))
                              (#b110 (branch-funct-bltu))
                              (#b111 (branch-funct-bgeu))
                              (t nil)))
                    ((unless funct?) nil))
                 (instr-branch funct? rs1 rs2 imm)))
    (#b1100111 (b* (((mv funct3 rd rs1 imm) (decode-itype enc))
                    ((unless (= funct3 0)) nil))
                 (instr-jalr rd rs1 imm)))
    (#b1101111 (b* (((mv rd imm) (decode-jtype enc)))
                 (instr-jal rd imm)))
    (t nil)))
