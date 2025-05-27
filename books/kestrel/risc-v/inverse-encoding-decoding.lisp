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

(local (include-book "arithmetic-3/top" :dir :system))

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

(defsection get-opcode-of-encode-of-inst
  :short "Theorems about @(tsee get-opcode) applied to
          the encoding of instructions."

  (defruled get-opcode-of-encode-of-instr-op-imm
    (equal (get-opcode (encode (instr-op-imm funct rd rs1 imm) feat))
           #b0010011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-op-imms32
    (equal (get-opcode (encode (instr-op-imms32 funct rd rs1 imm) feat))
           #b0010011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-op-imms64
    (equal (get-opcode (encode (instr-op-imms64 funct rd rs1 imm) feat))
           #b0010011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-op-imm-32
    (equal (get-opcode (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           #b0011011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-op-imms-32
    (equal (get-opcode (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           #b0011011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-lui
    (equal (get-opcode (encode (instr-lui rd imm) feat))
           #b0110111)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-auipc
    (equal (get-opcode (encode (instr-auipc rd imm) feat))
           #b0010111)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-op
    (equal (get-opcode (encode (instr-op funct rd rs1 imm) feat))
           #b0110011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-op-32
    (equal (get-opcode (encode (instr-op-32 funct rd rs1 imm) feat))
           #b0111011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-jal
    (equal (get-opcode (encode (instr-jal rd imm) feat))
           #b1101111)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-jalr
    (equal (get-opcode (encode (instr-jalr rd rs1 imm) feat))
           #b1100111)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-branch
    (equal (get-opcode (encode (instr-branch funct rs1 rs2 imm) feat))
           #b1100011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-load
    (equal (get-opcode (encode (instr-load funct rd rs1 imm) feat))
           #b0000011)
    :enable (encode
             get-opcode
             ifix
             loghead))

  (defruled get-opcode-of-encode-of-instr-store
    (equal (get-opcode (encode (instr-store funct rs1 rs2 imm) feat))
           #b0100011)
    :enable (encode
             get-opcode
             ifix
             loghead)))
