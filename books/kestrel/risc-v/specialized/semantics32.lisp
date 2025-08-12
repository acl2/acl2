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

(include-book "states32")

(include-book "../specification/instructions")

(include-book "kestrel/utilities/digits-any-base/core" :dir :system)
(include-book "kestrel/utilities/digits-any-base/pow2" :dir :system)

(local (include-book "../library-extensions/logops-theorems"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "kestrel/fty/ubyte8-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte16-ihs-theorems" :dir :system))

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel dab-digit-list-of-256-when-ubyte8-listp
  (implies (ubyte8-listp x)
           (acl2::dab-digit-listp 256 x))
  :enable (ubyte8-listp ubyte8p acl2::dab-digitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics32
  :parents (rv32im)
  :short "Semantics of instructions for RV32IM."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define state-transforming functions that model
     the effect of each instruction on the RV32I state.")
   (xdoc::p
    "For now we only support little endian access to memory,
     in load and store instructions.
     Also, for now we do no alignment checks."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-addi ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('ADDI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to 32 bits,
     obtaining an unsigned 32-bit integer.
     We add the two unsigned 32-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (imm-operand (loghead 32 (logext 12 (ubyte12-fix imm))))
       (result (+ rs1-operand imm-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-slti ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SLTI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed 32-bit integer from @('rs1').
     We sign-extend the 12-bit immediate,
     obtaining a signed integer.
     We compare the two signed integers:
     if the first one is less than the second,
     the result is 1, otherwise it is 0.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (imm-operand (logext 12 (ubyte12-fix imm)))
       (result (if (< rs1-operand imm-operand) 1 0))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-sltiu ((rd ubyte5p)
                      (rs1 ubyte5p)
                      (imm ubyte12p)
                      (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SLTIU') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to 32 bits,
     obtaining an unsigned 32-bit integer.
     We compare the two unsigned integers:
     if the first one is less than the second,
     the result is 1, otherwise it is 0.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (imm-operand (loghead 32 (logext 12 (ubyte12-fix imm))))
       (result (if (< rs1-operand imm-operand) 1 0))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-andi ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('ANDI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to 32 bits,
     obtaining an unsigned 32-bit integer.
     We perform a bitwise `and' of the two unsigned 32-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (imm-operand (loghead 32 (logext 12 (ubyte12-fix imm))))
       (result (logand rs1-operand imm-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-ori ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('ORI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to 32 bits,
     obtaining an unsigned 32-bit integer.
     We perform a bitwise inclusive `or' of the two unsigned 32-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (imm-operand (loghead 32 (logext 12 (ubyte12-fix imm))))
       (result (logior rs1-operand imm-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-xori ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('XORI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to 32 bits,
     obtaining an unsigned 32-bit integer.
     We perform a bitwise exclusive `or' of the two unsigned 32-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (imm-operand (loghead 32 (logext 12 (ubyte12-fix imm))))
       (result (logxor rs1-operand imm-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-op-imm ((funct op-imm-funct-p)
                       (rd ubyte5p)
                       (rs1 ubyte5p)
                       (imm ubyte12p)
                       (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the non-shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1]."
  (op-imm-funct-case funct
                     :addi (exec32-addi rd rs1 imm stat)
                     :slti (exec32-slti rd rs1 imm stat)
                     :sltiu (exec32-sltiu rd rs1 imm stat)
                     :andi (exec32-andi rd rs1 imm stat)
                     :ori (exec32-ori rd rs1 imm stat)
                     :xori (exec32-xori rd rs1 imm stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-slli ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the SLLI instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer left by the shift amount.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand shift-amount))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-srli ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the SRLI instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer right by the shift amount;
     this is a logical shift, since the integer is unsigned.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-srai ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the SRAI instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer right by the shift amount;
     this is an arithmetic shift, since the integer is signed.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-op-imms ((funct op-imms-funct-p)
                        (rd ubyte5p)
                        (rs1 ubyte5p)
                        (imm ubyte5p)
                        (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1]."
  (op-imms-funct-case funct
                      :slli (exec32-slli rd rs1 imm stat)
                      :srli (exec32-srli rd rs1 imm stat)
                      :srai (exec32-srai rd rs1 imm stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-lui ((rd ubyte5p)
                    (imm ubyte20p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('LUI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the 20 bits of the immediate as
     the high bits of an unsigned 32-bit integer,
     whose low bits are 0.
     We write the integer to @('rd').
     We increment the program counter."))
  (b* ((result (ash (ubyte20-fix imm) 12))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-auipc ((rd ubyte5p)
                      (imm ubyte20p)
                      (pc ubyte32p)
                      (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('AUIPC') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the 20 bits of the immediate as
     the high bits of an unsigned 32-bit integer,
     whose low bits are 0.
     We add the integer to the address of the instruction,
     which is passed as the @('pc') input to this function.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((offset (ash (ubyte20-fix imm) 12))
       (result (+ (ubyte32-fix pc) offset))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-add ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('ADD') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We add them, and write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-signed rs2 stat))
       (result (+ rs1-operand rs2-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-sub ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SUB') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We subtract the second from the first, and write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (result (- rs1-operand rs2-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-slt ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SLT') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed 32-bit integers from @('rs1') and @('rs2').
     We compare the two signed integers:
     if the first one is less than the second,
     the result is 1, otherwise it is 0.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-signed rs2 stat))
       (result (if (< rs1-operand rs2-operand) 1 0))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-sltu ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SLTU') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We compare the two unsigned integers:
     if the first one is less than the second,
     the result is 1, otherwise it is 0.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (result (if (< rs1-operand rs2-operand) 1 0))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-and ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('AND') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We perform a bitwise `and' of the two unsigned 32-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (result (logand rs1-operand rs2-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-or ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('OR') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We perform a bitwise inclusive `or' of the two unsigned 32-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (result (logior rs1-operand rs2-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-xor ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('XOR') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We perform a bitwise exclusive `or' of the two unsigned 32-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (result (logxor rs1-operand rs2-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-sll ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SLL') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     The low 5 bits of the second integer are the shift amount, from 0 to 31.
     We shift the first integer left by the shift amount.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (shift-amount (loghead 5 rs2-operand))
       (result (ash rs1-operand shift-amount))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-srl ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SRL') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     The low 5 bits of the second integer are the shift amount, from 0 to 31.
     We shift the first integer right by the shift amount;
     this is a logical shift, since the integer is unsigned.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (shift-amount (loghead 5 rs2-operand))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-sra ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SRA') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed 32-bit integer from @('rs1')
     and an unsigned 32-bit integer from @('rs2').
     The low 5 bits of the second integer are the shift amount, from 0 to 31.
     We shift the first integer right by the shift amount;
     this is an arithmetic shift, since the integer is signed.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (shift-amount (loghead 5 rs2-operand))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-mul ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semanics of the @('MUL') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We multiply them, and write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (result (* rs1-operand rs2-operand))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-mulh ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semanics of the @('MULH') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed 32-bit integers from @('rs1') and @('rs2').
     We multiply them,
     we shift the product right by 32 bits,
     and we write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-signed rs2 stat))
       (product (* rs1-operand rs2-operand))
       (result (ash product 32))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-mulhu ((rd ubyte5p)
                      (rs1 ubyte5p)
                      (rs2 ubyte5p)
                      (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semanics of the @('MULHU') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We multiply them,
     we shift the product right by 32 bits,
     and we write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (product (* rs1-operand rs2-operand))
       (result (ash product 32))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-mulhsu ((rd ubyte5p)
                       (rs1 ubyte5p)
                       (rs2 ubyte5p)
                       (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semanics of the @('MULHSU') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed 32-bit integer from @('rs1')
     and an unsigned 32-bit integer from @('rs2').
     We multiply them,
     we shift the product right by 32 bits,
     and we write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (product (* rs1-operand rs2-operand))
       (result (ash product 32))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-div ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semanics of the @('DIV') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed 32-bit integers from @('rs1') and @('rs2').
     We divide the first by the second, rounding towards 0;
     if the divisor is 0, the result is -1
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-signed rs2 stat))
       (result (if (= rs2-operand 0)
                   -1
                 (truncate rs1-operand rs2-operand)))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-divu ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semanics of the @('DIVU') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We divide the first by the second, rounding towards 0;
     if the divisor is 0, the result is @($2^{32}-1$)
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (result (if (= rs2-operand 0)
                   (1- (expt 2 32))
                 (truncate rs1-operand rs2-operand)))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-rem ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semanics of the @('REM') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed 32-bit integers from @('rs1') and @('rs2').
     We calculate the remainder of the first by the second,
     based on division towards 0;
     if the divisor is 0, the result is the dividend
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-signed rs2 stat))
       (result (if (= rs2-operand 0)
                   rs1-operand
                 (rem rs1-operand rs2-operand)))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-remu ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semanics of the @('REMU') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We calculate the remainder of the first by the second,
     based on division towards 0;
     if the divisor is 0, the result is the dividend
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (result (if (= rs2-operand 0)
                   rs1-operand
                 (rem rs1-operand rs2-operand)))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-op ((funct op-funct-p)
                   (rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the instructions with the @('OP') opcode
          [ISA:2.4.2] [ISA:12.1] [ISA:12.2]."
  (op-funct-case funct
                 :add (exec32-add rd rs1 rs2 stat)
                 :sub (exec32-sub rd rs1 rs2 stat)
                 :slt (exec32-slt rd rs1 rs2 stat)
                 :sltu (exec32-sltu rd rs1 rs2 stat)
                 :and (exec32-and rd rs1 rs2 stat)
                 :or (exec32-or rd rs1 rs2 stat)
                 :xor (exec32-xor rd rs1 rs2 stat)
                 :sll (exec32-sll rd rs1 rs2 stat)
                 :srl (exec32-srl rd rs1 rs2 stat)
                 :sra (exec32-sra rd rs1 rs2 stat)
                 :mul (exec32-mul rd rs1 rs2 stat)
                 :mulh (exec32-mulh rd rs1 rs2 stat)
                 :mulhu (exec32-mulhu rd rs1 rs2 stat)
                 :mulhsu (exec32-mulhsu rd rs1 rs2 stat)
                 :div (exec32-div rd rs1 rs2 stat)
                 :divu (exec32-divu rd rs1 rs2 stat)
                 :rem (exec32-rem rd rs1 rs2 stat)
                 :remu (exec32-remu rd rs1 rs2 stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-jal ((rd ubyte5p)
                    (imm ubyte20p)
                    (pc ubyte32p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('JAL') instruction [ISA:2.5.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the 20 bits of the immediate as
     the high bits of an unsigned 21-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 21-bit integer is sign-extended to 32 bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the jump target.
     We write the address of the instruction just after this to @('rd');
     since instructions are 32-bit long,
     the address of the next instruction is obtained by adding 4 to @('pc').
     We write the jump target to the program counter."))
  (b* ((offset (loghead 32 (logext 21 (ash (ubyte20-fix imm) 1))))
       (pc (ubyte32-fix pc))
       (target-pc (+ pc offset))
       (next-pc (+ pc 4))
       (stat (write32-xreg rd next-pc stat))
       (stat (write32-pc target-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-jalr ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (pc ubyte32p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('JALR') instruction [ISA:2.5.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to 32 bits,
     obtaining an unsigned 32-bit offset.
     We add the offset to the integer from the register,
     and set the least significant bit to 0;
     this is the jump target.
     We write the address of the instruction just after this to @('rd');
     since instructions are 32-bit long,
     the address of the next instruction is obtained by adding 4 to @('pc'),
     which is the address of this instruction, passed as input to this function.
     We write the jump target to the program counter."))
  (b* ((base (read32-xreg-unsigned rs1 stat))
       (offset (loghead 32 (logext 12 (ubyte12-fix imm))))
       (target-pc (logand #xfffffffe
                          (+ base offset)))
       (next-pc (+ (ubyte32-fix pc) 4))
       (stat (write32-xreg rd next-pc stat))
       (stat (write32-pc target-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-beq ((rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (imm ubyte12p)
                    (pc ubyte32p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('BEQ') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to 32 bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two integers from the registers:
     if they are equal,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (offset (loghead 32 (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ (ubyte32-fix pc) offset))
       (stat (if (= rs1-operand rs2-operand)
                 (write32-pc target-pc stat)
               (inc32-pc stat))))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-bne ((rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (imm ubyte12p)
                    (pc ubyte32p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('BNE') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to 32 bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two integers from the registers:
     if they are not equal,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (offset (loghead 32 (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ (ubyte32-fix pc) offset))
       (stat (if (/= rs1-operand rs2-operand)
                 (write32-pc target-pc stat)
               (inc32-pc stat))))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-blt ((rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (imm ubyte12p)
                    (pc ubyte32p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('BLT') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed 32-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to 32 bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two signed integers from the registers:
     if the first one is less than the second one,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-signed rs2 stat))
       (offset (loghead 32 (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ (ubyte32-fix pc) offset))
       (stat (if (< rs1-operand rs2-operand)
                 (write32-pc target-pc stat)
               (inc32-pc stat))))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-bltu ((rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (imm ubyte12p)
                     (pc ubyte32p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('BLTU') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to 32 bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two unsigned integers from the registers:
     if the first one is less than the second one,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (offset (loghead 32 (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ (ubyte32-fix pc) offset))
       (stat (if (< rs1-operand rs2-operand)
                 (write32-pc target-pc stat)
               (inc32-pc stat))))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-bge ((rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (imm ubyte12p)
                    (pc ubyte32p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('BGE') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed 32-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to 32 bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two signed integers from the registers:
     if the first one is greater than or equal to the second one,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read32-xreg-signed rs1 stat))
       (rs2-operand (read32-xreg-signed rs2 stat))
       (offset (loghead 32 (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ (ubyte32-fix pc) offset))
       (stat (if (>= rs1-operand rs2-operand)
                 (write32-pc target-pc stat)
               (inc32-pc stat))))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-bgeu ((rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (imm ubyte12p)
                     (pc ubyte32p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('BGEU') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to 32 bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two unsigned integers from the registers:
     if the first one is greater than or equal to the second one,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read32-xreg-unsigned rs1 stat))
       (rs2-operand (read32-xreg-unsigned rs2 stat))
       (offset (loghead 32 (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ (ubyte32-fix pc) offset))
       (stat (if (>= rs1-operand rs2-operand)
                 (write32-pc target-pc stat)
               (inc32-pc stat))))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-branch ((funct branch-funct-p)
                       (rs1 ubyte5p)
                       (rs2 ubyte5p)
                       (imm ubyte12p)
                       (pc ubyte32p)
                       (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the instructions with the @('BRANCH') opcode
          [ISA:2.5.2]."
  (branch-funct-case funct
                     :beq (exec32-beq rs1 rs2 imm pc stat)
                     :bne (exec32-bne rs1 rs2 imm pc stat)
                     :blt (exec32-blt rs1 rs2 imm pc stat)
                     :bltu (exec32-bltu rs1 rs2 imm pc stat)
                     :bge (exec32-bge rs1 rs2 imm pc stat)
                     :bgeu (exec32-bgeu rs1 rs2 imm pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eff32-addr ((rs1 ubyte5p) (imm ubyte12p) (stat stat32ip))
  :returns (addr integerp)
  :short "Effective address for a load or store instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1'); this is the base.
     We sign-extend the 12-bit immediate to 32 bits; this is the offset.
     We return the sum of base and offset, as an integer;
     the functions to read and write memory
     use the low 32 bits of this integer."))
  (b* ((base (read32-xreg-unsigned rs1 stat))
       (offset (loghead 32 (logext 12 (ubyte12-fix imm)))))
    (+ base offset))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-lb ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('LB') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 8-bit integer from the effective address,
     and sign-extend it to 32 bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff32-addr rs1 imm stat))
       (result (loghead 32 (logext 8 (read32-mem-ubyte8 addr stat))))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-lbu ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('LBU') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 8-bit integer from the effective address,
     which is also implicitly zero-extended to 32 bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff32-addr rs1 imm stat))
       (result (read32-mem-ubyte8 addr stat))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-lh ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('LH') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only little endian is supported for now.")
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 16-bit integer from the effective address,
     and sign-extend it to 32 bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff32-addr rs1 imm stat))
       (result (loghead 32 (logext 16 (read32-mem-ubyte16-lendian addr stat))))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-lhu ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('LHU') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only little endian is supported for now.")
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 16-bit integer from the effective address,
     which is also implicitly zero-extended to 32 bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff32-addr rs1 imm stat))
       (result (read32-mem-ubyte16-lendian addr stat))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-lw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('LW') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only little endian is supported for now.")
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 32-bit integer from the effective address.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff32-addr rs1 imm stat))
       (result (read32-mem-ubyte32-lendian addr stat))
       (stat (write32-xreg rd result stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-load ((funct load-funct-p)
                     (rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the instructions with the @('LOAD') opcode [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the error flag for @('LWU') and @('LD'),
     which are only used in RV64I."))
  (load-funct-case funct
                   :lb (exec32-lb rd rs1 imm stat)
                   :lbu (exec32-lbu rd rs1 imm stat)
                   :lh (exec32-lh rd rs1 imm stat)
                   :lhu (exec32-lhu rd rs1 imm stat)
                   :lw (exec32-lw rd rs1 imm stat)
                   :lwu (error32 stat)
                   :ld (error32 stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-sb ((rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (imm ubyte12p)
                   (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SB') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read the low 8 bits of @('rs2') as an unsigned 8-bit integer.
     We write the integer to the effective address.
     We increment the program counter."))
  (b* ((addr (eff32-addr rs1 imm stat))
       (val (loghead 8 (read32-xreg-unsigned rs2 stat)))
       (stat (write32-mem-ubyte8 addr val stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-sh ((rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (imm ubyte12p)
                   (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SH') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only little endian is supported for now.")
   (xdoc::p
    "We calculate the effective address.
     We read the low 16 bits of @('rs2') as an unsigned 16-bit integer.
     We write the integer to the effective address.
     We increment the program counter."))
  (b* ((addr (eff32-addr rs1 imm stat))
       (val (loghead 16 (read32-xreg-unsigned rs2 stat)))
       (stat (write32-mem-ubyte16-lendian addr val stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-sw ((rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (imm ubyte12p)
                   (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the @('SW') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only little endian is supported for now.")
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 32-bit integer from the @('rs2').
     We write the integer to the effective address.
     We increment the program counter."))
  (b* ((addr (eff32-addr rs1 imm stat))
       (val (read32-xreg-unsigned rs2 stat))
       (stat (write32-mem-ubyte32-lendian addr val stat))
       (stat (inc32-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-store ((funct store-funct-p)
                      (rs1 ubyte5p)
                      (rs2 ubyte5p)
                      (imm ubyte12p)
                      (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of the instructions with the @('STORE') opcode [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the error flag for @('SD'), which is only used in RV64I."))
  (store-funct-case funct
                    :sb (exec32-sb rs1 rs2 imm stat)
                    :sh (exec32-sh rs1 rs2 imm stat)
                    :sw (exec32-sw rs1 rs2 imm stat)
                    :sd (error32 stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec32-instr ((instr instrp)
                      (pc ubyte32p)
                      (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Semantics of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the error flag for the RV64I instructions
     because here we are in RV32I mode."))
  (instr-case instr
              :op-imm (exec32-op-imm instr.funct
                                     instr.rd
                                     instr.rs1
                                     instr.imm
                                     stat)
              :op-imms32 (exec32-op-imms instr.funct
                                         instr.rd
                                         instr.rs1
                                         instr.imm
                                         stat)
              :op-imms64 (error32 stat)
              :op-imm-32 (error32 stat)
              :op-imms-32 (error32 stat)
              :lui (exec32-lui instr.rd
                               instr.imm
                               stat)
              :auipc (exec32-auipc instr.rd
                                   instr.imm
                                   pc
                                   stat)
              :op (exec32-op instr.funct
                             instr.rd
                             instr.rs1
                             instr.rs2
                             stat)
              :op-32 (error32 stat)
              :jal (exec32-jal instr.rd
                               instr.imm
                               pc
                               stat)
              :jalr (exec32-jalr instr.rd
                                 instr.rs1
                                 instr.imm
                                 pc
                                 stat)
              :branch (exec32-branch instr.funct
                                     instr.rs1
                                     instr.rs2
                                     instr.imm
                                     pc
                                     stat)
              :load (exec32-load instr.funct
                                 instr.rd
                                 instr.rs1
                                 instr.imm
                                 stat)
              :store (exec32-store instr.funct
                                   instr.rs1
                                   instr.rs2
                                   instr.imm
                                   stat))
  :hooks (:fix))
