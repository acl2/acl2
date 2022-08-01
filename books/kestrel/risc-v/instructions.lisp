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

(include-book "kestrel/fty/ubyte1" :dir :system)
(include-book "kestrel/fty/ubyte3" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-imm-funct
  (:addi ())
  (:slti ())
  (:sltiu ())
  (:andi ())
  (:ori ())
  (:xori ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-imm-32-funct
  (:addiw ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-imms-funct
  (:slli ())
  (:srli ())
  (:srai ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-imms-32-funct
  (:slliw ())
  (:srliw ())
  (:sraiw ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-funct
  (:add ())
  (:slt ())
  (:sltu ())
  (:and ())
  (:or ())
  (:xor ())
  (:sll ())
  (:srl ())
  (:sra ())
  (:sub ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum op-32-funct
  (:addw ())
  (:sllw ())
  (:srlw ())
  (:sraw ())
  (:subw ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum branch-funct
  (:beq ())
  (:bne ())
  (:blt ())
  (:bltu ())
  (:bge ())
  (:bgeu ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum load-funct
  (:lb ())
  (:lbu ())
  (:lh ())
  (:lhu ())
  (:lw ())
  (:lwu ())
  (:ld ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum store-funct
  (:sb ())
  (:sh ())
  (:sw ())
  (:sd ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum instr
  (:op-imm ((funct op-imm-funct)
            (rd ubyte5)
            (rs1 ubyte5)
            (imm ubyte12)))
  (:op-imm-32 ((funct op-imm-32-funct)
               (rd ubyte5)
               (rs1 ubyte5)
               (imm ubyte12)))
  (:op-imms ((funct op-imms-funct)
             (rd ubyte5)
             (rs1 ubyte5)
             (imm ubyte6)))
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

(fty::defoption maybe-instr
  instr
  :pred maybe-instrp)
