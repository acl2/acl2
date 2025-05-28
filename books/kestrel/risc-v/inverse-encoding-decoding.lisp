; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "encoding")
(include-book "decoding")

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ inverse-encoding-decoding
  :parents (encoding decoding)
  :short "Theorems about encoding and decoding being inverses."
  :default-parent t
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-opcode-of-encode-of-instr
  :short "Theorems about @(tsee get-opcode) applied to
          the encoding of instructions."

  (defruled get-opcode-of-encode-of-instr-op-imm
    (equal (get-opcode (encode (instr-op-imm funct rd rs1 imm) feat))
           #b0010011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-op-imms32
    (equal (get-opcode (encode (instr-op-imms32 funct rd rs1 imm) feat))
           #b0010011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-op-imms64
    (equal (get-opcode (encode (instr-op-imms64 funct rd rs1 imm) feat))
           #b0010011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-op-imm-32
    (equal (get-opcode (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           #b0011011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-op-imms-32
    (equal (get-opcode (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           #b0011011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-lui
    (equal (get-opcode (encode (instr-lui rd imm) feat))
           #b0110111)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-auipc
    (equal (get-opcode (encode (instr-auipc rd imm) feat))
           #b0010111)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-op
    (equal (get-opcode (encode (instr-op funct rd rs1 imm) feat))
           #b0110011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-op-32
    (equal (get-opcode (encode (instr-op-32 funct rd rs1 imm) feat))
           #b0111011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-jal
    (equal (get-opcode (encode (instr-jal rd imm) feat))
           #b1101111)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-jalr
    (equal (get-opcode (encode (instr-jalr rd rs1 imm) feat))
           #b1100111)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-branch
    (equal (get-opcode (encode (instr-branch funct rs1 rs2 imm) feat))
           #b1100011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-load
    (equal (get-opcode (encode (instr-load funct rd rs1 imm) feat))
           #b0000011)
    :enable (encode
             get-opcode))

  (defruled get-opcode-of-encode-of-instr-store
    (equal (get-opcode (encode (instr-store funct rs1 rs2 imm) feat))
           #b0100011)
    :enable (encode
             get-opcode)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-rd-of-encode-of-instr
  :short "Theorems about @(tsee get-rd) applied to
          the encoding of instructions."

  (defruled get-rd-of-encode-instr-op-imm
    (equal (get-rd (encode (instr-op-imm funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-op-imms32
    (equal (get-rd (encode (instr-op-imms32 funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-op-imms64
    (equal (get-rd (encode (instr-op-imms64 funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-op-imm-32
    (equal (get-rd (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-op-imms-32
    (equal (get-rd (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-lui
    (equal (get-rd (encode (instr-lui rd imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-auipc
    (equal (get-rd (encode (instr-auipc rd imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-op
    (equal (get-rd (encode (instr-op funct rd rs1 rs2) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-op-32
    (equal (get-rd (encode (instr-op-32 funct rd rs1 rs2) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-jal
    (equal (get-rd (encode (instr-jal rd imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-jalr
    (equal (get-rd (encode (instr-jalr rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-instr-load
    (equal (get-rd (encode (instr-load funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-rs1-of-encode-of-instr
  :short "Theorems about @(tsee get-rs1) applied to
          the encoding of instructions."

  (defruled get-rs1-of-encode-instr-op-imm
    (equal (get-rs1 (encode (instr-op-imm funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-op-imms32
    (equal (get-rs1 (encode (instr-op-imms32 funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-op-imms64
    (equal (get-rs1 (encode (instr-op-imms64 funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-op-imm-32
    (equal (get-rs1 (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-op-imms-32
    (equal (get-rs1 (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-op
    (equal (get-rs1 (encode (instr-op funct rd rs1 rs2) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-op-32
    (equal (get-rs1 (encode (instr-op-32 funct rd rs1 rs2) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-jalr
    (equal (get-rs1 (encode (instr-jalr rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-branch
    (equal (get-rs1 (encode (instr-branch funct rs1 rs2 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-load
    (equal (get-rs1 (encode (instr-load funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-instr-store
    (equal (get-rs1 (encode (instr-store funct rs1 rs2 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-rs2-of-encode-of-instr
  :short "Theorems about @(tsee get-rs2) applied to
          the encoding of instructions."

  (defruled get-rs2-of-encode-instr-op
    (equal (get-rs2 (encode (instr-op funct rd rs1 rs2) feat))
           (ubyte5-fix rs2))
    :enable (encode
             get-rs2
             ubyte5-fix))

  (defruled get-rs2-of-encode-instr-op-32
    (equal (get-rs2 (encode (instr-op-32 funct rd rs1 rs2) feat))
           (ubyte5-fix rs2))
    :enable (encode
             get-rs2
             ubyte5-fix))

  (defruled get-rs2-of-encode-instr-branch
    (equal (get-rs2 (encode (instr-branch funct rs1 rs2 imm) feat))
           (ubyte5-fix rs2))
    :enable (encode
             get-rs2
             ubyte5-fix))

  (defruled get-rs2-of-encode-instr-store
    (equal (get-rs2 (encode (instr-store funct rs1 rs2 imm) feat))
           (ubyte5-fix rs2))
    :enable (encode
             get-rs2
             ubyte5-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-funct3-of-encode-instr
  :short "Theorems about @(tsee get-funct3) applied to
          the encoding of instructions."

  (defruled get-funct3-of-encode-instr-op-imm
    (equal (get-funct3 (encode (instr-op-imm funct rd rs1 imm) feat))
           (encode-op-imm-funct funct))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-op-imms32
    (equal (get-funct3 (encode (instr-op-imms32 funct rd rs1 imm) feat))
           (mv-nth 0 (encode-op-imms32-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-op-imms64
    (equal (get-funct3 (encode (instr-op-imms64 funct rd rs1 imm) feat))
           (mv-nth 0 (encode-op-imms64-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-op-imm-32
    (equal (get-funct3 (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           (encode-op-imm-32-funct funct))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-op-imms-32
    (equal (get-funct3 (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           (mv-nth 0 (encode-op-imms-32-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-op
    (equal (get-funct3 (encode (instr-op funct rd rs1 rs2) feat))
           (mv-nth 0 (encode-op-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-op-32
    (equal (get-funct3 (encode (instr-op-32 funct rd rs1 rs2) feat))
           (mv-nth 0 (encode-op-32-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-branch
    (equal (get-funct3 (encode (instr-branch funct rs1 rs2 imm) feat))
           (encode-branch-funct funct))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-load
    (equal (get-funct3 (encode (instr-load funct rd rs1 imm) feat))
           (encode-load-funct funct feat))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-instr-store
    (equal (get-funct3 (encode (instr-store funct rs1 rs2 imm) feat))
           (encode-store-funct funct feat))
    :enable (encode
             get-funct3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-funct7-of-encode-instr
  :short "Theorems about @(tsee get-funct7) applied to
          the encoding of instructions."

  (defruled get-funct7-of-encode-instr-op
    (equal (get-funct7 (encode (instr-op funct rd rs1 rs2) feat))
           (mv-nth 1 (encode-op-funct funct)))
    :enable (encode
             get-funct7))

  (defruled get-funct7-of-encode-instr-op-32
    (equal (get-funct7 (encode (instr-op-32 funct rd rs1 rs2) feat))
           (mv-nth 1 (encode-op-32-funct funct)))
    :enable (encode
             get-funct7)))
