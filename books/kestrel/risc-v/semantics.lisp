; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "semantics32")
(include-book "semantics64")
(include-book "states")

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics
  :parents (riscv)
  :short "Semantics of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we have two similar but slightly different semantics,
     one for RV32I and one for RV64I.
     We are in the process of consolidating them into one model for both;
     towards that end, we also provide
     a more generic semantics of instructions here."))
  :order-subtopics (semantics32
                    semantics64))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-addi ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Semantics of the @('ADDI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned @('XLEN')-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to @('XLEN') bits,
     obtaining an unsigned @('XLEN')-bit integer.
     We add the two unsigned @('XLEN')-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (imm-operand (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
       (result (+ rs1-operand imm-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slti ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Semantics of the @('SLTI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed @('XLEN')-bit integer from @('rs1').
     We sign-extend the 12-bit immediate,
     obtaining a signed integer.
     We compare the two signed integers:
     if the first one is less than the second,
     the result is 1, otherwise it is 0.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (imm-operand (logext 12 (ubyte12-fix imm)))
       (result (if (< rs1-operand imm-operand) 1 0))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sltiu ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat statp)
                    (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Semantics of the @('SLTIU') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned @('XLEN')-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to @('XLEN') bits,
     obtaining an unsigned @('XLEN')-bit integer.
     We compare the two unsigned integers:
     if the first one is less than the second,
     the result is 1, otherwise it is 0.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (imm-operand (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
       (result (if (< rs1-operand imm-operand) 1 0))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-andi ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Semantics of the @('ANDI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned @('XLEN')-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to @('XLEN') bits,
     obtaining an unsigned @('XLEN')-bit integer.
     We perform a bitwise `and' of
     the two unsigned @('XLEN')-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (imm-operand (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
       (result (logand rs1-operand imm-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ori ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat statp)
                  (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Semantics of the @('ORI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned @('XLEN')-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to @('XLEN') bits,
     obtaining an unsigned @('XLEN')-bit integer.
     We perform a bitwise inclusive `or' of
     the two unsigned @('XLEN')-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (imm-operand (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
       (result (logior rs1-operand imm-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-xori ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Semantics of the @('XORI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned @('XLEN')-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to @('XLEN') bits,
     obtaining an unsigned @('XLEN')-bit integer.
     We perform a bitwise exclusive `or' of
     the two unsigned @('XLEN')-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (imm-operand (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
       (result (logxor rs1-operand imm-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imm ((funct op-imm-funct-p)
                     (rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (stat statp)
                     (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Semantics of the non-shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1]."
  (op-imm-funct-case funct
                     :addi (exec-addi rd rs1 imm stat feat)
                     :slti (exec-slti rd rs1 imm stat feat)
                     :sltiu (exec-sltiu rd rs1 imm stat feat)
                     :andi (exec-andi rd rs1 imm stat feat)
                     :ori (exec-ori rd rs1 imm stat feat)
                     :xori (exec-xori rd rs1 imm stat feat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slli32 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-32p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the SLLI instruction [ISA:2.4.1] in 32-bit mode."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer left by the shift amount.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand shift-amount))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define exec-slli64 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte6p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the SLLI instruction [ISA:2.4.1] in 64-bit mode."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 64-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 63.
     We shift the integer left by the shift amount.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte6-fix imm))
       (result (ash rs1-operand shift-amount))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srli32 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-32p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the SRLI instruction [ISA:2.4.1] in 32-bit mode."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer right by the shift amount;
     this is a logical shift, since the integer is unsigned.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define exec-srli64 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte6p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the SRLI instruction [ISA:2.4.1] in 64-bit mode."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 64-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 63.
     We shift the integer right by the shift amount;
     this is a logical shift, since the integer is unsigned.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte6-fix imm))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srai32 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-32p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the SRAI instruction [ISA:2.4.1] in 32-bit mode."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer right by the shift amount;
     this is an arithmetic shift, since the integer is signed.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define exec-srai64 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte6p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the SRAI instruction [ISA:2.4.1] in 64-bit mode."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed 64-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 63.
     We shift the integer right by the shift amount;
     this is an arithmetic shift, since the integer is signed.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte6-fix imm))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imms32 ((funct op-imms-funct-p)
                        (rd ubyte5p)
                        (rs1 ubyte5p)
                        (imm ubyte5p)
                        (stat statp)
                        (feat featp))
  :guard (and (feat-32p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1] in 32-bit mode."
  (op-imms-funct-case funct
                      :slli (exec-slli32 rd rs1 imm stat feat)
                      :srli (exec-srli32 rd rs1 imm stat feat)
                      :srai (exec-srai32 rd rs1 imm stat feat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define exec-op-imms64 ((funct op-imms-funct-p)
                        (rd ubyte5p)
                        (rs1 ubyte5p)
                        (imm ubyte6p)
                        (stat statp)
                        (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1] in 64-bit mode."
  (op-imms-funct-case funct
                      :slli (exec-slli64 rd rs1 imm stat feat)
                      :srli (exec-srli64 rd rs1 imm stat feat)
                      :srai (exec-srai64 rd rs1 imm stat feat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-addiw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the @('ADDIW') instruction [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only valid in 64-bit mode.")
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to 32 bits,
     obtaining an unsigned 32-bit integer.
     We add the two unsigned 32-bit integers.
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (imm-operand (loghead 32 (logext 12 (ubyte12-fix imm))))
       (result (+ rs1-operand imm-operand))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imm-32 ((funct op-imm-32-funct-p)
                        (rd ubyte5p)
                        (rs1 ubyte5p)
                        (imm ubyte12p)
                        (stat statp)
                        (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the non-shift instructions with the @('OP-IMM-32') opcode
          [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are only valid in 64-bit mode."))
  (op-imm-32-funct-case funct
                        :addiw (exec-addiw rd rs1 imm stat feat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slliw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the @('SLLIW') instruction [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only valid in 64-bit mode.")
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer left by the shift amount.
     We write the result to @('rd'), as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand shift-amount))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srliw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the @('SRLIW') instruction [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only valid in 64-bit mode.")
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer right by the shift amount;
     this is a logical shift, because the integer is unsigned.
     We write the result to @('rd'), as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sraiw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of the @('SRAIW') instruction [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only valid in 64-bit mode.")
   (xdoc::p
    "We read a signed 32-bit integer from @('rs1').
     The immediate is the shift amount, from 0 to 31.
     We shift the integer right by the shift amount;
     this is an arithmetic shift, because the integer is signed.
     We write the result to @('rd'), as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed32 (ubyte5-fix rs1) stat feat))
       (shift-amount (ubyte5-fix imm))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imms-32 ((funct op-imms-32-funct-p)
                         (rd ubyte5p)
                         (rs1 ubyte5p)
                         (imm ubyte5p)
                         (stat statp)
                         (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of a shift instruction with the @('OP-IMM-32') opcode
          [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are only valid in 64-bit mode."))
  (op-imms-32-funct-case funct
                         :slliw (exec-slliw rd rs1 imm stat feat)
                         :srliw (exec-srliw rd rs1 imm stat feat)
                         :sraiw (exec-sraiw rd rs1 imm stat feat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lui ((rd ubyte5p)
                  (imm ubyte20p)
                  (stat statp)
                  (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Semantics of the @('LUI') instruction [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the 20 bits of the immediate as
     the high bits of an unsigned 32-bit integer,
     whose low bits are 0.
     In 32-bit mode, we write the integer to @('rd');
     in 64-bit mode, we write the integer to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((result (ash (ubyte20-fix imm) 12))
       (stat
        (cond ((feat-32p feat) (write-xreg (ubyte5-fix rd) result stat feat))
              ((feat-64p feat) (write-xreg-32 (ubyte5-fix rd) result stat feat))
              (t (impossible))))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p
                                           feat-32p
                                           feat-64p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-auipc ((rd ubyte5p)
                    (imm ubyte20p)
                    pc
                    (stat statp)
                    (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible))))
  :returns (new-stat statp)
  :short "Semantics of the @('AUIPC') instruction [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the 20 bits of the immediate as
     the high bits of an unsigned 32-bit integer,
     whose low bits are 0.
     In 64-bit mode,
     we extend the unsigned 32-bit integer to 64 bits,
     obtaining an unsigned 64-bit integer.
     We add the integer to the address of the instruction,
     which is passed as the @('pc') input to this function.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((offset (ash (ubyte20-fix imm) 12))
       (offset (if (feat-64p feat)
                   (loghead 64 (logext 32 offset))
                 offset))
       (pc (cond ((feat-32p feat) (ubyte32-fix pc))
                 ((feat-64p feat) (ubyte64-fix pc))
                 (t (impossible))))
       (result (+ pc offset))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p
                                           feat-32p
                                           feat-64p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add remaining ones
