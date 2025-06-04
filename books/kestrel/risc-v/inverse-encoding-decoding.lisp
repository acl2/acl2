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

(include-book "encoding")
(include-book "decoding")

(local (include-book "library-extensions"))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "kestrel/fty/ubyte3-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte7-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte12-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte20-ihs-theorems" :dir :system))

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

  (defruled get-rd-of-encode-of-instr-op-imm
    (equal (get-rd (encode (instr-op-imm funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-op-imms32
    (equal (get-rd (encode (instr-op-imms32 funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-op-imms64
    (equal (get-rd (encode (instr-op-imms64 funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-op-imm-32
    (equal (get-rd (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-op-imms-32
    (equal (get-rd (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-lui
    (equal (get-rd (encode (instr-lui rd imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-auipc
    (equal (get-rd (encode (instr-auipc rd imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-op
    (equal (get-rd (encode (instr-op funct rd rs1 rs2) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-op-32
    (equal (get-rd (encode (instr-op-32 funct rd rs1 rs2) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-jal
    (equal (get-rd (encode (instr-jal rd imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-jalr
    (equal (get-rd (encode (instr-jalr rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix))

  (defruled get-rd-of-encode-of-instr-load
    (equal (get-rd (encode (instr-load funct rd rs1 imm) feat))
           (ubyte5-fix rd))
    :enable (encode
             get-rd
             ubyte5-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-rs1-of-encode-of-instr
  :short "Theorems about @(tsee get-rs1) applied to
          the encoding of instructions."

  (defruled get-rs1-of-encode-of-instr-op-imm
    (equal (get-rs1 (encode (instr-op-imm funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-op-imms32
    (equal (get-rs1 (encode (instr-op-imms32 funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-op-imms64
    (equal (get-rs1 (encode (instr-op-imms64 funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-op-imm-32
    (equal (get-rs1 (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-op-imms-32
    (equal (get-rs1 (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-op
    (equal (get-rs1 (encode (instr-op funct rd rs1 rs2) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-op-32
    (equal (get-rs1 (encode (instr-op-32 funct rd rs1 rs2) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-jalr
    (equal (get-rs1 (encode (instr-jalr rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-branch
    (equal (get-rs1 (encode (instr-branch funct rs1 rs2 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-load
    (equal (get-rs1 (encode (instr-load funct rd rs1 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix))

  (defruled get-rs1-of-encode-of-instr-store
    (equal (get-rs1 (encode (instr-store funct rs1 rs2 imm) feat))
           (ubyte5-fix rs1))
    :enable (encode
             get-rs1
             ubyte5-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-rs2-of-encode-of-instr
  :short "Theorems about @(tsee get-rs2) applied to
          the encoding of instructions."

  (defruled get-rs2-of-encode-of-instr-op
    (equal (get-rs2 (encode (instr-op funct rd rs1 rs2) feat))
           (ubyte5-fix rs2))
    :enable (encode
             get-rs2
             ubyte5-fix))

  (defruled get-rs2-of-encode-of-instr-op-32
    (equal (get-rs2 (encode (instr-op-32 funct rd rs1 rs2) feat))
           (ubyte5-fix rs2))
    :enable (encode
             get-rs2
             ubyte5-fix))

  (defruled get-rs2-of-encode-of-instr-branch
    (equal (get-rs2 (encode (instr-branch funct rs1 rs2 imm) feat))
           (ubyte5-fix rs2))
    :enable (encode
             get-rs2
             ubyte5-fix))

  (defruled get-rs2-of-encode-of-instr-store
    (equal (get-rs2 (encode (instr-store funct rs1 rs2 imm) feat))
           (ubyte5-fix rs2))
    :enable (encode
             get-rs2
             ubyte5-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-funct3-of-encode-of-instr
  :short "Theorems about @(tsee get-funct3) applied to
          the encoding of instructions."

  (defruled get-funct3-of-encode-of-instr-op-imm
    (equal (get-funct3 (encode (instr-op-imm funct rd rs1 imm) feat))
           (encode-op-imm-funct funct))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-op-imms32
    (equal (get-funct3 (encode (instr-op-imms32 funct rd rs1 imm) feat))
           (mv-nth 0 (encode-op-imms32-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-op-imms64
    (equal (get-funct3 (encode (instr-op-imms64 funct rd rs1 imm) feat))
           (mv-nth 0 (encode-op-imms64-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-op-imm-32
    (equal (get-funct3 (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           (encode-op-imm-32-funct funct))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-op-imms-32
    (equal (get-funct3 (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           (mv-nth 0 (encode-op-imms-32-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-op
    (equal (get-funct3 (encode (instr-op funct rd rs1 rs2) feat))
           (mv-nth 0 (encode-op-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-op-32
    (equal (get-funct3 (encode (instr-op-32 funct rd rs1 rs2) feat))
           (mv-nth 0 (encode-op-32-funct funct)))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-branch
    (equal (get-funct3 (encode (instr-branch funct rs1 rs2 imm) feat))
           (encode-branch-funct funct))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-load
    (equal (get-funct3 (encode (instr-load funct rd rs1 imm) feat))
           (encode-load-funct funct feat))
    :enable (encode
             get-funct3))

  (defruled get-funct3-of-encode-of-instr-store
    (equal (get-funct3 (encode (instr-store funct rs1 rs2 imm) feat))
           (encode-store-funct funct feat))
    :enable (encode
             get-funct3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-funct7-of-encode-of-instr
  :short "Theorems about @(tsee get-funct7) applied to
          the encoding of instructions."

  (defruled get-funct7-of-encode-of-instr-op
    (equal (get-funct7 (encode (instr-op funct rd rs1 rs2) feat))
           (mv-nth 1 (encode-op-funct funct)))
    :enable (encode
             get-funct7))

  (defruled get-funct7-of-encode-of-instr-op-32
    (equal (get-funct7 (encode (instr-op-32 funct rd rs1 rs2) feat))
           (mv-nth 1 (encode-op-32-funct funct)))
    :enable (encode
             get-funct7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-imm-itype-of-encode-of-instr
  :short "Theorems about @(tsee get-imm-itype) applied to
          the encoding of instructions."

  (defruled get-imm-itype-of-encode-of-instr-op-imm
    (equal (get-imm-itype (encode (instr-op-imm funct rd rs1 imm) feat))
           (ubyte12-fix imm))
    :enable (get-imm-itype
             encode))

  (defruled get-imm-itype-of-encode-of-instr-op-imms32
    (equal (get-imm-itype (encode (instr-op-imms32 funct rd rs1 imm) feat))
           (logappn 5 (ubyte5-fix imm)
                    7 (mv-nth 1 (encode-op-imms32-funct funct))))
    :enable (get-imm-itype
             encode))

  (defruled get-imm-itype-of-encode-of-instr-op-imms64
    (equal (get-imm-itype (encode (instr-op-imms64 funct rd rs1 imm) feat))
           (logappn 6 (ubyte6-fix imm)
                    6 (mv-nth 1 (encode-op-imms64-funct funct))))
    :enable (get-imm-itype
             encode))

  (defruled get-imm-itype-of-encode-of-instr-op-imm-32
    (equal (get-imm-itype (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           (ubyte12-fix imm))
    :enable (get-imm-itype
             encode))

  (defruled get-imm-itype-of-encode-of-instr-op-imms-32
    (equal (get-imm-itype (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           (logappn 5 (ubyte5-fix imm)
                    1 0
                    6 (mv-nth 1 (encode-op-imms-32-funct funct))))
    :enable (get-imm-itype
             encode))

  (defruled get-imm-itype-of-encode-of-instr-jalr
    (equal (get-imm-itype (encode (instr-jalr rd rs1 imm) feat))
           (ubyte12-fix imm))
    :enable (get-imm-itype
             encode))

  (defruled get-imm-itype-of-encode-of-instr-load
    (equal (get-imm-itype (encode (instr-load funct rd rs1 imm) feat))
           (ubyte12-fix imm))
    :enable (get-imm-itype
             encode)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-imm-stype-of-encode-of-instr
  :short "Theorems about @(tsee get-imm-stype) applied to
          the encoding of instructions."

  (defruled get-imm-stype-of-encode-of-instr-store
    (equal (get-imm-stype (encode (instr-store funct rs1 rs2 imm) feat))
           (ubyte12-fix imm))
    :use (:instance lemma (imm (ubyte12-fix imm)))
    :prep-lemmas
    ((defruled lemma
       (implies (ubyte12p imm)
                (equal (get-imm-stype (encode (instr-store funct rs1 rs2 imm) feat))
                       imm))
       :enable (get-imm-stype
                encode)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-imm-btype-of-encode-of-instr
  :short "Theorems about @(tsee get-imm-btype) applied to
          the encoding of instructions."

  (local (include-book "arithmetic-5/top" :dir :system))

  (defrulel logbit-11-to-logtail-11-when-ubyte12p
    (implies (ubyte12p x)
             (equal (logbit 11 x)
                    (logtail 11 x)))
    :enable (logtail
             bool->bit
             logbitp
             ubyte12p
             unsigned-byte-p))

  (defrulel logapp-6-logtail-4-logtail-10
    (implies (integerp x)
             (equal (logapp 6 (logtail 4 x) (logtail 10 x))
                    (logtail 4 x)))
    :enable (logapp
             logtail
             loghead))

  (defruled get-imm-btype-of-instr-branch
    (equal (get-imm-btype (encode (instr-branch funct rs1 rs2 imm) feat))
           (ubyte12-fix imm))
    :use (:instance lemma (imm (ubyte12-fix imm)))
    :prep-lemmas
    ((defruled lemma
       (implies (ubyte12p imm)
                (equal (get-imm-btype
                        (encode (instr-branch funct rs1 rs2 imm) feat))
                       imm))
       :enable (get-imm-btype
                encode
                logbit-11-to-logtail-11-when-ubyte12p
                logapp-1-of-logbit-logtail
                logapp-6-logtail-4-logtail-10)
       :disable bitops::logbit-to-logbitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-imm-utype-of-encode-of-instr
  :short "Theorems about @(tsee get-imm-utype) applied to
          the encoding of instructions."

  (defruled get-imm-utype-of-encode-of-instr-lui
    (equal (get-imm-utype (encode (instr-lui rd imm) feat))
           (ubyte20-fix imm))
    :enable (get-imm-utype
             encode))

  (defruled get-imm-ubyte-of-encode-of-instr-auipc
    (equal (get-imm-utype (encode (instr-auipc rd imm) feat))
           (ubyte20-fix imm))
    :enable (get-imm-utype
             encode)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-fields-rtype-of-encode-of-instr
  :short "Theorems about @(tsee get-fields-rtype) applied to
          the encoding of instructions."

  (defruled get-fields-rtype-of-encode-of-instr-op
    (equal (get-fields-rtype (encode (instr-op funct rd rs1 rs2) feat))
           (mv (mv-nth 0 (encode-op-funct funct))
               (mv-nth 1 (encode-op-funct funct))
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (ubyte5-fix rs2)))
    :enable (get-fields-rtype
             get-funct3-of-encode-of-instr-op
             get-funct7-of-encode-of-instr-op
             get-rd-of-encode-of-instr-op
             get-rs1-of-encode-of-instr-op
             get-rs2-of-encode-of-instr-op))

  (defruled get-fields-rtype-of-encode-of-instr-op-32
    (equal (get-fields-rtype (encode (instr-op-32 funct rd rs1 rs2) feat))
           (mv (mv-nth 0 (encode-op-32-funct funct))
               (mv-nth 1 (encode-op-32-funct funct))
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (ubyte5-fix rs2)))
    :enable (get-fields-rtype
             get-funct3-of-encode-of-instr-op-32
             get-funct7-of-encode-of-instr-op-32
             get-rd-of-encode-of-instr-op-32
             get-rs1-of-encode-of-instr-op-32
             get-rs2-of-encode-of-instr-op-32)))
