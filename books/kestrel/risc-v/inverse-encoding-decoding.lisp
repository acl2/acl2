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
(local (include-book "kestrel/fty/ubyte5-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte6-ihs-theorems" :dir :system))
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
          the encoding of different instructions."

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
          the encoding of different instructions."

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
          the encoding of different instructions."

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
          the encoding of different instructions."

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
          the encoding of different instructions."

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

  (defruled get-funct3-of-encode-of-instr-jalr
    (equal (get-funct3 (encode (instr-jalr rd rs1 imm) feat))
           0)
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
          the encoding of different instructions."

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
          the encoding of different instructions."

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
             encode)
    :disable acl2::loghead-of-6-when-ubyte6p)

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
          the encoding of different instructions."

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
          the encoding of different instructions."

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

  (defruled get-imm-btype-of-encode-of-instr-branch
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
                logapp-1-of-logbit-logtail)
       :disable bitops::logbit-to-logbitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-imm-utype-of-encode-of-instr
  :short "Theorems about @(tsee get-imm-utype) applied to
          the encoding of different instructions."

  (defruled get-imm-utype-of-encode-of-instr-lui
    (equal (get-imm-utype (encode (instr-lui rd imm) feat))
           (ubyte20-fix imm))
    :enable (get-imm-utype
             encode))

  (defruled get-imm-utype-of-encode-of-instr-auipc
    (equal (get-imm-utype (encode (instr-auipc rd imm) feat))
           (ubyte20-fix imm))
    :enable (get-imm-utype
             encode)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-imm-jtype-of-encode-of-instr
  :short "Theorems about @(tsee get-imm-jtype) applied to
          the encoding of different instructions."

  (local (include-book "arithmetic-5/top" :dir :system))

  (defrulel logbit-19-to-logtail-19-when-ubyte20p
    (implies (ubyte20p x)
             (equal (logbit 19 x)
                    (logtail 19 x)))
    :enable (logtail
             bool->bit
             logbitp
             ubyte20p
             unsigned-byte-p))

  (defrulel logapp-8-logtail-11-logtail-19
    (implies (integerp x)
             (equal (logapp 8 (logtail 11 x) (logtail 19 x))
                    (logtail 11 x)))
    :enable (logapp
             logtail
             loghead))

  (defruled get-imm-jtype-of-encode-of-instr-jal
    (equal (get-imm-jtype (encode (instr-jal rd imm) feat))
           (ubyte20-fix imm))
    :use (:instance lemma (imm (ubyte20-fix imm)))
    :prep-lemmas
    ((defruled lemma
       (implies (ubyte20p imm)
                (equal (get-imm-jtype (encode (instr-jal rd imm) feat))
                       imm))
       :enable (get-imm-jtype
                encode
                logapp-1-of-logbit-logtail)
       :disable bitops::logbit-to-logbitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-fields-rtype-of-encode-of-instr
  :short "Theorems about @(tsee get-fields-rtype) applied to
          the encoding of different instructions."

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-fields-itype-of-encode-of-instr
  :short "Theorems about @(tsee get-fields-itype) applied to
          the encoding of different instructions."

  (defruled get-fields-itype-of-encode-of-instr-op-imm
    (equal (get-fields-itype (encode (instr-op-imm funct rd rs1 imm) feat))
           (mv (encode-op-imm-funct funct)
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (ubyte12-fix imm)))
    :enable (get-fields-itype
             get-funct3-of-encode-of-instr-op-imm
             get-rd-of-encode-of-instr-op-imm
             get-rs1-of-encode-of-instr-op-imm
             get-imm-itype-of-encode-of-instr-op-imm))

  (defruled get-fields-itype-of-encode-of-instr-op-imms32
    (equal (get-fields-itype (encode (instr-op-imms32 funct rd rs1 imm) feat))
           (mv (mv-nth 0 (encode-op-imms32-funct funct))
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (logappn 5 (ubyte5-fix imm)
                        7 (mv-nth 1 (encode-op-imms32-funct funct)))))
    :enable (get-fields-itype
             get-funct3-of-encode-of-instr-op-imms32
             get-rd-of-encode-of-instr-op-imms32
             get-rs1-of-encode-of-instr-op-imms32
             get-imm-itype-of-encode-of-instr-op-imms32))

  (defruled get-fields-itype-of-encode-of-instr-op-imms64
    (equal (get-fields-itype (encode (instr-op-imms64 funct rd rs1 imm) feat))
           (mv (mv-nth 0 (encode-op-imms64-funct funct))
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (logappn 6 (ubyte6-fix imm)
                        6 (mv-nth 1 (encode-op-imms64-funct funct)))))
    :enable (get-fields-itype
             get-funct3-of-encode-of-instr-op-imms64
             get-rd-of-encode-of-instr-op-imms64
             get-rs1-of-encode-of-instr-op-imms64
             get-imm-itype-of-encode-of-instr-op-imms64))

  (defruled get-fields-itype-of-encode-of-instr-op-imm-32
    (equal (get-fields-itype (encode (instr-op-imm-32 funct rd rs1 imm) feat))
           (mv (encode-op-imm-32-funct funct)
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (ubyte12-fix imm)))
    :enable (get-fields-itype
             get-funct3-of-encode-of-instr-op-imm-32
             get-rd-of-encode-of-instr-op-imm-32
             get-rs1-of-encode-of-instr-op-imm-32
             get-imm-itype-of-encode-of-instr-op-imm-32))

  (defruled get-fields-itype-of-encode-of-instr-op-imms-32
    (equal (get-fields-itype (encode (instr-op-imms-32 funct rd rs1 imm) feat))
           (mv (mv-nth 0 (encode-op-imms-32-funct funct))
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (logappn 5 (ubyte5-fix imm)
                        1 0
                        6 (mv-nth 1 (encode-op-imms-32-funct funct)))))
    :enable (get-fields-itype
             get-funct3-of-encode-of-instr-op-imms-32
             get-rd-of-encode-of-instr-op-imms-32
             get-rs1-of-encode-of-instr-op-imms-32
             get-imm-itype-of-encode-of-instr-op-imms-32))

  (defruled get-fields-itype-of-encode-of-instr-jalr
    (equal (get-fields-itype (encode (instr-jalr rd rs1 imm) feat))
           (mv 0
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (ubyte12-fix imm)))
    :enable (get-fields-itype
             get-funct3-of-encode-of-instr-jalr
             get-rd-of-encode-of-instr-jalr
             get-rs1-of-encode-of-instr-jalr
             get-imm-itype-of-encode-of-instr-jalr))

  (defruled get-fields-itype-of-encode-of-instr-load
    (equal (get-fields-itype (encode (instr-load funct rd rs1 imm) feat))
           (mv (encode-load-funct funct feat)
               (ubyte5-fix rd)
               (ubyte5-fix rs1)
               (ubyte12-fix imm)))
    :enable (get-fields-itype
             get-funct3-of-encode-of-instr-load
             get-rd-of-encode-of-instr-load
             get-rs1-of-encode-of-instr-load
             get-imm-itype-of-encode-of-instr-load)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-fields-stype-of-encode-of-instr
  :short "Theorems about @(tsee get-fields-stype) applied to
          the encoding of different instructions."

  (defruled get-fields-stype-of-encode-of-instr-store
    (equal (get-fields-stype (encode (instr-store funct rs1 rs2 imm) feat))
           (mv (encode-store-funct funct feat)
               (ubyte5-fix rs1)
               (ubyte5-fix rs2)
               (ubyte12-fix imm)))
    :enable (get-fields-stype
             get-funct3-of-encode-of-instr-store
             get-rs1-of-encode-of-instr-store
             get-rs2-of-encode-of-instr-store
             get-imm-stype-of-encode-of-instr-store)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-fields-utype-of-encode-of-instr
  :short "Theorems about @(tsee get-fields-utype) applied to
          the encoding of different instructions."

  (defruled get-fields-utype-of-encode-of-instr-lui
    (equal (get-fields-utype (encode (instr-lui rd imm) feat))
           (mv (ubyte5-fix rd)
               (ubyte20-fix imm)))
    :enable (get-fields-utype
             get-rd-of-encode-of-instr-lui
             get-imm-utype-of-encode-of-instr-lui))

  (defruled get-fields-utype-of-encode-of-instr-auipc
    (equal (get-fields-utype (encode (instr-auipc rd imm) feat))
           (mv (ubyte5-fix rd)
               (ubyte20-fix imm)))
    :enable (get-fields-utype
             get-rd-of-encode-of-instr-auipc
             get-imm-utype-of-encode-of-instr-auipc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-fields-btype-of-encode-of-instr
  :short "Theorems about @(tsee get-fields-btype) applied to
          the encoding of different instructions."

  (defruled get-fields-btype-of-encode-of-instr-branch
    (equal (get-fields-btype (encode (instr-branch funct rs1 rs2 imm) feat))
           (mv (encode-branch-funct funct)
               (ubyte5-fix rs1)
               (ubyte5-fix rs2)
               (ubyte12-fix imm)))
    :enable (get-fields-btype
             get-funct3-of-encode-of-instr-branch
             get-rs1-of-encode-of-instr-branch
             get-rs2-of-encode-of-instr-branch
             get-imm-btype-of-encode-of-instr-branch)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection get-fields-jtype-of-encode-of-instr
  :short "Theorems about @(tsee get-fields-utype) applied to
          the encoding of different instructions."

  (defruled get-fields-jtype-of-encode-of-instr-jal
    (equal (get-fields-jtype (encode (instr-jal rd imm) feat))
           (mv (ubyte5-fix rd)
               (ubyte20-fix imm)))
    :enable (get-fields-jtype
             get-rd-of-encode-of-instr-jal
             get-imm-jtype-of-encode-of-instr-jal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection decode-of-encode-of-instr
  :short "Theorems about @(tsee decode) applied to
          the encoding of different instructions."

  (defruled decode-of-encode-of-instr-op-imm
    (implies (instr-validp (instr-op-imm funct rd rs1 imm) feat)
             (equal (decode (encode (instr-op-imm funct rd rs1 imm) feat) feat)
                    (instr-op-imm funct rd rs1 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-op-imm
             get-fields-itype-of-encode-of-instr-op-imm
             instr-validp
             encode-op-imm-funct))

  (defruled decode-of-encode-of-instr-op-imms32
    (implies (instr-validp (instr-op-imms32 funct rd rs1 imm) feat)
             (equal (decode (encode (instr-op-imms32 funct rd rs1 imm) feat) feat)
                    (instr-op-imms32 funct rd rs1 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-op-imms32
             get-fields-itype-of-encode-of-instr-op-imms32
             instr-validp
             encode-op-imms32-funct
             feat-32p
             feat-64p))

  (defruled decode-of-encode-of-instr-op-imms64
    (implies (instr-validp (instr-op-imms64 funct rd rs1 imm) feat)
             (equal (decode (encode (instr-op-imms64 funct rd rs1 imm) feat) feat)
                    (instr-op-imms64 funct rd rs1 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-op-imms64
             get-fields-itype-of-encode-of-instr-op-imms64
             instr-validp
             encode-op-imms64-funct))

  (defruled decode-of-encode-of-instr-op-imm-32
    (implies (instr-validp (instr-op-imm-32 funct rd rs1 imm) feat)
             (equal (decode (encode (instr-op-imm-32 funct rd rs1 imm) feat) feat)
                    (instr-op-imm-32 funct rd rs1 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-op-imm-32
             get-fields-itype-of-encode-of-instr-op-imm-32
             instr-validp
             encode-op-imm-32-funct
             op-imm-32-funct-fix))

  (defruled decode-of-encode-of-instr-op-imms-32
    (implies (instr-validp (instr-op-imms-32 funct rd rs1 imm) feat)
             (equal (decode (encode (instr-op-imms-32 funct rd rs1 imm) feat) feat)
                    (instr-op-imms-32 funct rd rs1 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-op-imms-32
             get-fields-itype-of-encode-of-instr-op-imms-32
             instr-validp
             encode-op-imms-32-funct))

  (defruled decode-of-encode-of-instr-lui
    (implies (instr-validp (instr-lui rd imm) feat)
             (equal (decode (encode (instr-lui rd imm) feat) feat)
                    (instr-lui rd imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-lui
             get-fields-utype-of-encode-of-instr-lui
             instr-validp))

  (defruled decode-of-encode-of-instr-auipc
    (implies (instr-validp (instr-auipc rd imm) feat)
             (equal (decode (encode (instr-auipc rd imm) feat) feat)
                    (instr-auipc rd imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-auipc
             get-fields-utype-of-encode-of-instr-auipc
             instr-validp))

  (defruled decode-of-encode-of-instr-op
    (implies (instr-validp (instr-op funct rd rs1 rs2) feat)
             (equal (decode (encode (instr-op funct rd rs1 rs2) feat) feat)
                    (instr-op funct rd rs1 rs2)))
    :enable (decode
             get-opcode-of-encode-of-instr-op
             get-fields-rtype-of-encode-of-instr-op
             instr-validp
             encode-op-funct))

  (defruled decode-of-encode-of-instr-op-32
    (implies (instr-validp (instr-op-32 funct rd rs1 rs2) feat)
             (equal (decode (encode (instr-op-32 funct rd rs1 rs2) feat) feat)
                    (instr-op-32 funct rd rs1 rs2)))
    :enable (decode
             get-opcode-of-encode-of-instr-op-32
             get-fields-rtype-of-encode-of-instr-op-32
             instr-validp
             encode-op-32-funct))

  (defruled decode-of-encode-of-instr-jal
    (implies (instr-validp (instr-jal rd imm) feat)
             (equal (decode (encode (instr-jal rd imm) feat) feat)
                    (instr-jal rd imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-jal
             get-fields-jtype-of-encode-of-instr-jal
             instr-validp))

  (defruled decode-of-encode-of-instr-jalr
    (implies (instr-validp (instr-jalr rd rs1 imm) feat)
             (equal (decode (encode (instr-jalr rd rs1 imm) feat) feat)
                    (instr-jalr rd rs1 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-jalr
             get-fields-itype-of-encode-of-instr-jalr
             instr-validp))

  (defruled decode-of-encode-of-instr-branch
    (implies (instr-validp (instr-branch funct rs1 rs2 imm) feat)
             (equal (decode (encode (instr-branch funct rs1 rs2 imm) feat) feat)
                    (instr-branch funct rs1 rs2 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-branch
             get-fields-btype-of-encode-of-instr-branch
             instr-validp
             encode-branch-funct))

  (defruled decode-of-encode-of-instr-load
    (implies (instr-validp (instr-load funct rd rs1 imm) feat)
             (equal (decode (encode (instr-load funct rd rs1 imm) feat) feat)
                    (instr-load funct rd rs1 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-load
             get-fields-itype-of-encode-of-instr-load
             instr-validp
             encode-load-funct))

  (defruled decode-of-encode-of-instr-store
    (implies (instr-validp (instr-store funct rs1 rs2 imm) feat)
             (equal (decode (encode (instr-store funct rs1 rs2 imm) feat) feat)
                    (instr-store funct rs1 rs2 imm)))
    :enable (decode
             get-opcode-of-encode-of-instr-store
             get-fields-stype-of-encode-of-instr-store
             instr-validp
             encode-store-funct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled decode-of-encode
  :short "Decoding the encoding of a valid instruction
          yields the original instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, decoding is left inverse of encoding,
     and encoding is right inverse of decoding."))
  (implies (instr-validp instr feat)
           (equal (decode (encode instr feat) feat)
                  (instr-fix instr)))
  :use (:instance lemma (instr (instr-fix instr)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (instrp instr)
                   (instr-validp instr feat))
              (equal (decode (encode instr feat) feat)
                     instr))
     :cases ((equal (instr-kind instr) :op-imm)
             (equal (instr-kind instr) :op-imms32)
             (equal (instr-kind instr) :op-imms64)
             (equal (instr-kind instr) :op-imm-32)
             (equal (instr-kind instr) :op-imms-32)
             (equal (instr-kind instr) :lui)
             (equal (instr-kind instr) :auipc)
             (equal (instr-kind instr) :op)
             (equal (instr-kind instr) :op-32)
             (equal (instr-kind instr) :jal)
             (equal (instr-kind instr) :jalr)
             (equal (instr-kind instr) :branch)
             (equal (instr-kind instr) :load)
             (equal (instr-kind instr) :store))
     :use ((:instance decode-of-encode-of-instr-op-imm
                      (funct (instr-op-imm->funct instr))
                      (rd (instr-op-imm->rd instr))
                      (rs1 (instr-op-imm->rs1 instr))
                      (imm (instr-op-imm->imm instr)))
           (:instance decode-of-encode-of-instr-op-imms32
                      (funct (instr-op-imms32->funct instr))
                      (rd (instr-op-imms32->rd instr))
                      (rs1 (instr-op-imms32->rs1 instr))
                      (imm (instr-op-imms32->imm instr)))
           (:instance decode-of-encode-of-instr-op-imms64
                      (funct (instr-op-imms64->funct instr))
                      (rd (instr-op-imms64->rd instr))
                      (rs1 (instr-op-imms64->rs1 instr))
                      (imm (instr-op-imms64->imm instr)))
           (:instance decode-of-encode-of-instr-op-imm-32
                      (funct (instr-op-imm-32->funct instr))
                      (rd (instr-op-imm-32->rd instr))
                      (rs1 (instr-op-imm-32->rs1 instr))
                      (imm (instr-op-imm-32->imm instr)))
           (:instance decode-of-encode-of-instr-op-imms-32
                      (funct (instr-op-imms-32->funct instr))
                      (rd (instr-op-imms-32->rd instr))
                      (rs1 (instr-op-imms-32->rs1 instr))
                      (imm (instr-op-imms-32->imm instr)))
           (:instance decode-of-encode-of-instr-lui
                      (rd (instr-lui->rd instr))
                      (imm (instr-lui->imm instr)))
           (:instance decode-of-encode-of-instr-auipc
                      (rd (instr-auipc->rd instr))
                      (imm (instr-auipc->imm instr)))
           (:instance decode-of-encode-of-instr-op
                      (funct (instr-op->funct instr))
                      (rd (instr-op->rd instr))
                      (rs1 (instr-op->rs1 instr))
                      (rs2 (instr-op->rs2 instr)))
           (:instance decode-of-encode-of-instr-op-32
                      (funct (instr-op-32->funct instr))
                      (rd (instr-op-32->rd instr))
                      (rs1 (instr-op-32->rs1 instr))
                      (rs2 (instr-op-32->rs2 instr)))
           (:instance decode-of-encode-of-instr-jal
                      (rd (instr-jal->rd instr))
                      (imm (instr-jal->imm instr)))
           (:instance decode-of-encode-of-instr-jalr
                      (rd (instr-jalr->rd instr))
                      (rs1 (instr-jalr->rs1 instr))
                      (imm (instr-jalr->imm instr)))
           (:instance decode-of-encode-of-instr-branch
                      (funct (instr-branch->funct instr))
                      (rs1 (instr-branch->rs1 instr))
                      (rs2 (instr-branch->rs2 instr))
                      (imm (instr-branch->imm instr)))
           (:instance decode-of-encode-of-instr-load
                      (funct (instr-load->funct instr))
                      (rd (instr-load->rd instr))
                      (rs1 (instr-load->rs1 instr))
                      (imm (instr-load->imm instr)))
           (:instance decode-of-encode-of-instr-store
                      (funct (instr-store->funct instr))
                      (rs1 (instr-store->rs1 instr))
                      (rs2 (instr-store->rs2 instr))
                      (imm (instr-store->imm instr))))
     ; for speed:
     :disable (equal-of-instr-op-imm
               equal-of-instr-op-imms32
               equal-of-instr-op-imms64
               equal-of-instr-op-imm-32
               equal-of-instr-op-imms-32
               equal-of-instr-lui
               equal-of-instr-auipc
               equal-of-instr-op
               equal-of-instr-op-32
               equal-of-instr-jal
               equal-of-instr-jalr
               equal-of-instr-branch
               equal-of-instr-load
               equal-of-instr-store))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled encode-injective
  :short "Injectivity of encoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Different valid instructions are encoded differently.
     This is a direct consequence of @(tsee decode-of-encode):
     if two different instructions were encoded in the same way,
     the decoder would be unable to restore both at the same time."))
  (implies (and (instr-validp instr1 feat)
                (instr-validp instr2 feat))
           (equal (equal (encode instr1 feat)
                         (encode instr2 feat))
                  (equal (instr-fix instr1)
                         (instr-fix instr2))))
  :use ((:instance decode-of-encode (instr instr1))
        (:instance decode-of-encode (instr instr2))))
