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
(include-book "states")

(local (include-book "../library-extensions/theorems"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "kestrel/fty/ubyte8-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte16-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte32-ihs-theorems" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics
  :parents (specification)
  :short "Semantics of instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce functions that say how
     each instruction operates on the state.
     We restrict this to valid instructions in valid states
     with respect to the RISC-V features.")
   (xdoc::p
    "For some integer instructions, like @('SLT') and @('SLTU'),
     it is important whether the operands are read as signed or unsigned.
     For other instructions, like @('ADD') it does not matter,
     so long as they are both read signed or unsigned
     (not one signed and the other unsigned);
     for these instructions, we add theorem showing two definitions equivalent,
     one that reads signed operands and one that reads unsigned operands.")
   (xdoc::p
    "There is a fair amount of repetition in boilerplate in these functions.
     We could consider shortening them via suitable macros."))
  :default-parent t
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-addi ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('ADDI') instruction [ISA:2.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a (signed or unsigned) @('XLEN')-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to @('XLEN') bits,
     obtaining a (signed or unsigned) @('XLEN')-bit integer.
     We add the two integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (imm-operand (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
       (result (+ rs1-operand imm-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defruled exec-addi-alt-def
    (equal (exec-addi rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (imm-operand (logext 12 (ubyte12-fix imm)))
                (result (+ rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-addi
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc)
    :use (:instance lemma
                    (imm (ubyte12-fix imm))
                    (rs1 (ubyte5-fix rs1)))
    :prep-lemmas
    ((defruled lemma
       (equal (loghead (feat->xlen feat)
                       (+ (logext 12 imm)
                          (logext (feat->xlen feat)
                                  (read-xreg-unsigned rs1 stat feat))))
              (loghead (feat->xlen feat)
                       (+ (loghead (feat->xlen feat)
                                   (logext 12 imm))
                          (read-xreg-unsigned rs1 stat feat))))
       :use (lemma1 lemma2 lemma3)
       :disable bitops::loghead-of-+-of-loghead-same
       :cases ((feat-32p feat))
       :prep-lemmas
       ((defruled lemma1
          (equal (loghead (feat->xlen feat)
                          (+ (logext 12 imm)
                             (logext (feat->xlen feat)
                                     (read-xreg-unsigned rs1 stat feat))))
                 (loghead (feat->xlen feat)
                          (+ (logext (feat->xlen feat)
                                     (logext 12 imm))
                             (logext (feat->xlen feat)
                                     (read-xreg-unsigned rs1 stat feat)))))
          :cases ((feat-32p feat)))
        (defruled lemma2
          (equal (loghead (feat->xlen feat)
                          (+ (logext (feat->xlen feat)
                                     (logext 12 imm))
                             (logext (feat->xlen feat)
                                     (read-xreg-unsigned rs1 stat feat))))
                 (loghead (feat->xlen feat)
                          (+ (logext 12 imm)
                             (read-xreg-unsigned rs1 stat feat))))
          :enable (loghead-of-logext-plus-logext
                   ifix))
        (defruled lemma3
          (equal (loghead (feat->xlen feat)
                          (+ (logext 12 imm)
                             (read-xreg-unsigned rs1 stat feat)))
                 (loghead (feat->xlen feat)
                          (+ (loghead (feat->xlen feat)
                                      (logext 12 imm))
                             (loghead (feat->xlen feat)
                                      (read-xreg-unsigned rs1 stat feat))))))))))

  (defret stat-validp-of-exec-addi
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slti ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-slti
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sltiu ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat statp)
                    (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sltiu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-andi ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-andi
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ori ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-ori
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-xori ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-xori
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imm ((funct op-imm-funct-p)
                     (rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (stat statp)
                     (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-op-imm
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slli32 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-32p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-slli32
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;

(define exec-slli64 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte6p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-slli64
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srli32 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-32p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-srli32
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;

(define exec-srli64 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte6p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-srli64
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srai32 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte5p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-32p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-srai32
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;

(define exec-srai64 ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte6p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-srai64
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imms32 ((funct op-imms-funct-p)
                        (rd ubyte5p)
                        (rs1 ubyte5p)
                        (imm ubyte5p)
                        (stat statp)
                        (feat featp))
  :guard (and (feat-32p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1] in 32-bit mode."
  (op-imms-funct-case funct
                      :slli (exec-slli32 rd rs1 imm stat feat)
                      :srli (exec-srli32 rd rs1 imm stat feat)
                      :srai (exec-srai32 rd rs1 imm stat feat))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-op-imms32
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))))

;;;;;;;;;;;;;;;;;;;;

(define exec-op-imms64 ((funct op-imms-funct-p)
                        (rd ubyte5p)
                        (rs1 ubyte5p)
                        (imm ubyte6p)
                        (stat statp)
                        (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the shift instructions with the @('OP-IMM') opcode
          [ISA:2.4.1] in 64-bit mode."
  (op-imms-funct-case funct
                      :slli (exec-slli64 rd rs1 imm stat feat)
                      :srli (exec-srli64 rd rs1 imm stat feat)
                      :srai (exec-srai64 rd rs1 imm stat feat))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-op-imms64
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-addiw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-addiw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imm-32 ((funct op-imm-32-funct-p)
                        (rd ubyte5p)
                        (rs1 ubyte5p)
                        (imm ubyte12p)
                        (stat statp)
                        (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the non-shift instructions with the @('OP-IMM-32') opcode
          [ISA:4.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are only valid in 64-bit mode."))
  (op-imm-32-funct-case funct
                        :addiw (exec-addiw rd rs1 imm stat feat))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-op-imm-32
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slliw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-slliw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srliw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-srliw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sraiw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sraiw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imms-32 ((funct op-imms-32-funct-p)
                         (rd ubyte5p)
                         (rs1 ubyte5p)
                         (imm ubyte5p)
                         (stat statp)
                         (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
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
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-op-imms-32
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lui ((rd ubyte5p)
                  (imm ubyte20p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('LUI') instruction [ISA:2.4.1] [ISA:4.2.1]."
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
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-lui
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints
    (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-auipc ((rd ubyte5p)
                    (imm ubyte20p)
                    pc
                    (stat statp)
                    (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rd) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('AUIPC') instruction [ISA:2.4.1] [ISA:4.2.1]."
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
       (result (+ pc offset))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-auipc
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-add ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('ADD') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two (signed or unsigned) @('XLEN')-bit integers
     from @('rs1') and @('rs2').
     We add the two integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (+ rs1-operand rs2-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defruled exec-add-alt-def
    (equal (exec-add rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (result (+ rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-add
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc
             loghead-of-logext-plus-logext
             ifix))

  (defret stat-validp-of-exec-add
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sub ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SUB') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two (signed or unsigned) @('XLEN')-bit integers
     from @('rs1') and @('rs2').
     We subtract the second integer from the first integer.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (- rs1-operand rs2-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defruled exec-sub-alt-def
    (equal (exec-sub rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (result (- rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-sub
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc
             loghead-of-logext-minus-logext
             ifix))

  (defret stat-validp-of-exec-sub
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slt ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SLT') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed @('XLEN')-bit integers from @('rs1') and @('rs2').
     We compare the two signed integers:
     if the first one is less than the second,
     the result is 1, otherwise it is 0.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
       (result (if (< rs1-operand rs2-operand) 1 0))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-slt
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sltu ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SLTU') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We compare the two unsigned integers:
     if the first one is less than the second,
     the result is 1, otherwise it is 0.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (if (< rs1-operand rs2-operand) 1 0))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sltu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-and ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('AND') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We perform a bitwise `and' of
     the two unsigned @('XLEN')-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (logand rs1-operand rs2-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-and
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-or ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (stat statp)
                 (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('OR') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We perform a bitwise inclusive `or' of
     the two unsigned @('XLEN')-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (logior rs1-operand rs2-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-or
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-xor ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('XOR') instruction [ISA:2.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We perform a bitwise exclusive `or' of
     the two unsigned @('XLEN')-bit integers.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (logxor rs1-operand rs2-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-xor
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sll ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SLL') instruction [ISA:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     In 32-bit mode,
     the low 5 bits of the second integer are the shift amount, from 0 to 31;
     in 64-bit mode,
     the low 6 bits of the second integer are the shift amount, from 0 to 63.
     We shift the first integer left by the shift amount.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (shift-amount
        (cond ((feat-32p feat) (loghead 5 rs2-operand))
              ((feat-64p feat) (loghead 6 rs2-operand))
              (t (impossible))))
       (result (ash rs1-operand shift-amount))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sll
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srl ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SRL') instruction [ISA:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     In 32-bit mode,
     the low 5 bits of the second integer are the shift amount, from 0 to 31;
     in 64-bit mode,
     the low 6 bits of the second integer are the shift amount, from 0 to 63.
     We shift the first integer right by the shift amount;
     this is a logical shift, since the integer is unsigned.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (shift-amount
        (cond ((feat-32p feat) (loghead 5 rs2-operand))
              ((feat-64p feat) (loghead 6 rs2-operand))
              (t (impossible))))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-srl
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sra ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SRA') instruction [ISA:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed @('XLEN')-bit integer from @('rs1')
     and an unsigned @('XLEN')-bit integer from @('rs2').
     In 32-bit mode,
     the low 5 bits of the second integer are the shift amount, from 0 to 31;
     in 64-bit mode,
     the low 6 bits of the second integer are the shift amount, from 0 to 63.
     We shift the first integer right by the shift amount;
     this is an arithmetic shift, since the integer is signed.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (shift-amount
        (cond ((feat-32p feat) (loghead 5 rs2-operand))
              ((feat-64p feat) (loghead 6 rs2-operand))
              (t (impossible))))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sra
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-mul ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semanics of the @('MUL') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We multiply them, and write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (* rs1-operand rs2-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-mul
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-mulh ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semanics of the @('MULH') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed @('XLEN')-bit integers from @('rs1') and @('rs2').
     We multiply them,
     we shift the product right by @('XLEN') bits,
     and we write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
       (product (* rs1-operand rs2-operand))
       (result (ash product (feat->xlen feat)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-mulh
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-mulhu ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semanics of the @('MULHU') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We multiply them,
     we shift the product right by @('XLEN') bits,
     and we write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (product (* rs1-operand rs2-operand))
       (result (ash product (feat->xlen feat)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-mulhu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-mulhsu ((rd ubyte5p)
                     (rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (stat statp)
                     (feat featp))
  :guard (and (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semanics of the @('MULHSU') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed @('XLEN')-bit integer from @('rs1')
     and an unsigned @('XLEN')-bit integer from @('rs2').
     We multiply them,
     we shift the product right by @('XLEN') bits,
     and we write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (product (* rs1-operand rs2-operand))
       (result (ash product (feat->xlen feat)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-mulhsu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-div ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semanics of the @('DIV') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed @('XLEN')-bit integers from @('rs1') and @('rs2').
     We divide the first by the second, rounding towards 0;
     if the divisor is 0, the result is -1
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
       (result (if (= rs2-operand 0)
                   -1
                 (truncate rs1-operand rs2-operand)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-div
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-divu ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semanics of the @('DIVU') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We divide the first by the second, rounding towards 0;
     if the divisor is 0, the result is @($2^{\\mathtt{XLEN}}-1$)
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (if (= rs2-operand 0)
                   (1- (expt 2 (feat->xlen feat)))
                 (truncate rs1-operand rs2-operand)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-divu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-rem ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat statp)
                  (feat featp))
  :guard (and (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semanics of the @('REM') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed @('XLEN')-bit integers from @('rs1') and @('rs2').
     We calculate the remainder of the first by the second,
     based on division towards 0;
     if the divisor is 0, the result is the dividend
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
       (result (if (= rs2-operand 0)
                   rs1-operand
                 (rem rs1-operand rs2-operand)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-rem
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-remu ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semanics of the @('REMU') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We calculate the remainder of the first by the second,
     based on division towards 0;
     if the divisor is 0, the result is the dividend
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (result (if (= rs2-operand 0)
                   rs1-operand
                 (rem rs1-operand rs2-operand)))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-remu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op ((funct op-funct-p)
                 (rd ubyte5p)
                 (rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (stat statp)
                 (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat))
              (implies (member-eq (op-funct-kind funct)
                                  '(:mul :mulh :mulhu :mulhsu
                                    :div :divu :rem :remu))
                       (feat-mp feat)))
  :returns (new-stat statp)
  :short "Semantics of the instructions with the @('OP') opcode
          [ISA:2.4.2] [ISA:4.2.2] [ISA:12.1] [ISA:12.2]."
  (op-funct-case funct
                 :add (exec-add rd rs1 rs2 stat feat)
                 :sub (exec-sub rd rs1 rs2 stat feat)
                 :slt (exec-slt rd rs1 rs2 stat feat)
                 :sltu (exec-sltu rd rs1 rs2 stat feat)
                 :and (exec-and rd rs1 rs2 stat feat)
                 :or (exec-or rd rs1 rs2 stat feat)
                 :xor (exec-xor rd rs1 rs2 stat feat)
                 :sll (exec-sll rd rs1 rs2 stat feat)
                 :srl (exec-srl rd rs1 rs2 stat feat)
                 :sra (exec-sra rd rs1 rs2 stat feat)
                 :mul (exec-mul rd rs1 rs2 stat feat)
                 :mulh (exec-mulh rd rs1 rs2 stat feat)
                 :mulhu (exec-mulhu rd rs1 rs2 stat feat)
                 :mulhsu (exec-mulhsu rd rs1 rs2 stat feat)
                 :div (exec-div rd rs1 rs2 stat feat)
                 :divu (exec-divu rd rs1 rs2 stat feat)
                 :rem (exec-rem rd rs1 rs2 stat feat)
                 :remu (exec-remu rd rs1 rs2 stat feat))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-op
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-addw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('ADDW') instruction [ISA:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only valid in 64-bit mode.")
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We add the two unsigned 32-bit integers.
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned32 (ubyte5-fix rs2) stat feat))
       (result (+ rs1-operand rs2-operand))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-addw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-subw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SUBW') instruction [ISA:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We subtract the second from the first, and write the result to @('rd').
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned32 (ubyte5-fix rs2) stat feat))
       (result (- rs1-operand rs2-operand))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-subw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sllw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SLLW') instruction [ISA:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1')
     and an unsigned 32-bit integer from @('rs2').
     The low 5 bits of the second integer are the shift amount, from 0 to 31.
     We shift the first integer left by the shift amount.
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned32 (ubyte5-fix rs2) stat feat))
       (shift-amount (loghead 5 rs2-operand))
       (result (ash rs1-operand shift-amount))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sllw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srlw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SRLW') instruction [ISA:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned 32-bit integer from @('rs1')
     and an unsigned 32-bit integer from @('rs2').
     The low 5 bits of the second integer are the shift amount, from 0 to 31.
     We shift the first integer right by the shift amount;
     this is a logical shift, since the integer is unsigned.
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned32 (ubyte5-fix rs2) stat feat))
       (shift-amount (loghead 5 rs2-operand))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-srlw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sraw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SRAW') instruction [ISA:4.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read a signed 32-bit integer from @('rs1')
     and an unsigned 32-bit integer from @('rs2').
     The low 5 bits of the second integer are the shift amount, from 0 to 31.
     We shift the first integer right by the shift amount;
     this is an arithmetic shift, since the integer is signed.
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned32 (ubyte5-fix rs2) stat feat))
       (shift-amount (loghead 5 rs2-operand))
       (result (ash rs1-operand (- shift-amount)))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sraw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-mulw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-64p feat)
              (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('MULW') instruction [ISA:12.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We multiply the two unsigned 32-bit integers.
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned32 (ubyte5-fix rs2) stat feat))
       (result (* rs1-operand rs2-operand))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-mulw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-divw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-64p feat)
              (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('DIVW') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed 32-bit integers from @('rs1') and @('rs2').
     We divide the first by the second, rounding towards 0;
     if the divisor is 0, the result is -1
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-signed32 (ubyte5-fix rs2) stat feat))
       (result (if (= rs2-operand 0)
                   -1
                 (truncate rs1-operand rs2-operand)))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-divw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-divuw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('DIVUW') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We divide the first by the second, rounding towards 0;
     if the divisor is 0, the result is @($2^{32}-1$)
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned32 (ubyte5-fix rs2) stat feat))
       (result (if (= rs2-operand 0)
                   (1- (expt 2 32))
                 (truncate rs1-operand rs2-operand)))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-divuw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-remw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat statp)
                   (feat featp))
  :guard (and (feat-64p feat)
              (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('REMW') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed 32-bit integers from @('rs1') and @('rs2').
     We calculate the remainder of the first by the second,
     based on division towards 0;
     if the divisor is 0, the result is the dividend
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-signed32 (ubyte5-fix rs2) stat feat))
       (result (if (= rs2-operand 0)
                   rs1-operand
                 (rem rs1-operand rs2-operand)))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-remw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-remuw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (feat-mp feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('REMUW') instruction [ISA:12.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned 32-bit integers from @('rs1') and @('rs2').
     We calculate the remainder of the first by the second,
     based on division towards 0;
     if the divisor is 0, the result is the dividend
     (see Table 11 in [ISA:12.2]).
     We write the result to @('rd') as a signed 32-bit integer.
     We increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned32 (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned32 (ubyte5-fix rs2) stat feat))
       (result (if (= rs2-operand 0)
                   rs1-operand
                 (rem rs1-operand rs2-operand)))
       (stat (write-xreg-32 (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-remuw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-32 ((funct op-32-funct-p)
                    (rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat statp)
                    (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat))
              (implies (member-eq (op-32-funct-kind funct)
                                  '(:mulw
                                    :divw :divuw :remw :remuw))
                       (feat-mp feat)))
  :returns (new-stat statp)
  :short "Semantics of the instructions with the @('OP-32') opcode
          [ISA:4.2.2] [ISA:12.1] [ISA:12.2]."
  (op-32-funct-case funct
                    :addw (exec-addw rd rs1 rs2 stat feat)
                    :subw (exec-subw rd rs1 rs2 stat feat)
                    :sllw (exec-sllw rd rs1 rs2 stat feat)
                    :srlw (exec-srlw rd rs1 rs2 stat feat)
                    :sraw (exec-sraw rd rs1 rs2 stat feat)
                    :mulw (exec-mulw rd rs1 rs2 stat feat)
                    :divw (exec-divw rd rs1 rs2 stat feat)
                    :divuw (exec-divuw rd rs1 rs2 stat feat)
                    :remw (exec-remw rd rs1 rs2 stat feat)
                    :remuw (exec-remuw rd rs1 rs2 stat feat))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-op-32
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-jal ((rd ubyte5p)
                  (imm ubyte20p)
                  pc
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rd) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('JAL') instruction [ISA:2.5.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the 20 bits of the immediate as
     the high bits of an unsigned 21-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 21-bit integer is sign-extended to @('XLEN') bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the jump target.
     We write the address of the instruction just after this to @('rd');
     since instructions are 32-bit long,
     the address of the next instruction is obtained by adding 4 to @('pc').
     We write the jump target to the program counter."))
  (b* ((offset
        (loghead (feat->xlen feat) (logext 21 (ash (ubyte20-fix imm) 1))))
       (target-pc (+ pc offset))
       (next-pc (+ pc 4))
       (stat (write-xreg (ubyte5-fix rd) next-pc stat feat))
       (stat (write-pc target-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-jal
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-jalr ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   pc
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('JALR') instruction [ISA:2.5.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned @('XLEN')-bit integer from @('rs1').
     We sign-extend the 12-bit immediate to @('XLEN') bits,
     obtaining an unsigned @('XLEN')-bit offset.
     We add the offset to the integer from the register,
     and set the least significant bit to 0;
     this is the jump target.
     We write the address of the instruction just after this to @('rd');
     since instructions are 32-bit long,
     the address of the next instruction is obtained by adding 4 to @('pc'),
     which is the address of this instruction, passed as input to this function.
     We write the jump target to the program counter."))
  (b* ((base (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (offset (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
       (mask (cond ((feat-32p feat) #xfffffffe)
                   ((feat-64p feat) #xfffffffffffffffe)
                   (t (impossible))))
       (target-pc (logand mask (+ base offset)))
       (next-pc (+ pc 4))
       (stat (write-xreg (ubyte5-fix rd) next-pc stat feat))
       (stat (write-pc target-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-jalr
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-beq ((rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (imm ubyte12p)
                  pc
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('BEQ') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to @('XLEN') bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two integers from the registers:
     if they are equal,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (offset
        (loghead (feat->xlen feat) (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ pc offset))
       (stat (if (= rs1-operand rs2-operand)
                 (write-pc target-pc stat feat)
               (inc4-pc stat feat))))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-beq
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bne ((rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (imm ubyte12p)
                  pc
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('BNE') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to @('XLEN') bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two integers from the registers:
     if they are not equal,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (offset
        (loghead (feat->xlen feat) (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ pc offset))
       (stat (if (/= rs1-operand rs2-operand)
                 (write-pc target-pc stat feat)
               (inc4-pc stat feat))))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-bne
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-blt ((rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (imm ubyte12p)
                  pc
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('BLT') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed @('XLEN')-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to @('XLEN') bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two signed integers from the registers:
     if the first one is less than the second one,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
       (offset
        (loghead (feat->xlen feat) (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ pc offset))
       (stat (if (< rs1-operand rs2-operand)
                 (write-pc target-pc stat feat)
               (inc4-pc stat feat))))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-blt
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bltu ((rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (imm ubyte12p)
                   pc
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('BLTU') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to @('XLEN') bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two unsigned integers from the registers:
     if the first one is less than the second one,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (offset
        (loghead (feat->xlen feat) (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ pc offset))
       (stat (if (< rs1-operand rs2-operand)
                 (write-pc target-pc stat feat)
               (inc4-pc stat feat))))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-bltu
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bge ((rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (imm ubyte12p)
                  pc
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('BGE') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two signed @('XLEN')-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to @('XLEN') bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two signed integers from the registers:
     if the first one is greater than or equal to the second one,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
       (offset
        (loghead (feat->xlen feat) (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ pc offset))
       (stat (if (>= rs1-operand rs2-operand)
                 (write-pc target-pc stat feat)
               (inc4-pc stat feat))))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-bge
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bgeu ((rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (imm ubyte12p)
                   pc
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('BGEU') instruction [ISA:2.5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read two unsigned @('XLEN')-bit integers from @('rs1') and @('rs2').
     We use the 12 bits of the immediate as
     the high bits of a 13-bit integer,
     whose low bit is 0 (i.e. the immediate measures multiples of 2);
     the unsigned 13-bit integer is sign-extended to @('XLEN') bits,
     obtaining an offset.
     We add the offset to the address of the instruction,
     which is passed as the @('pc') input to this function;
     this is the branch target.
     We compare the two unsigned integers from the registers:
     if the first one is greater than or equal to the second one,
     we write the branch target to the program counter;
     otherwise, we increment the program counter."))
  (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (offset
        (loghead (feat->xlen feat) (logext 13 (ash (ubyte12-fix imm) 1))))
       (target-pc (+ pc offset))
       (stat (if (>= rs1-operand rs2-operand)
                 (write-pc target-pc stat feat)
               (inc4-pc stat feat))))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum ubyte5p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-bgeu
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-branch ((funct branch-funct-p)
                     (rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (imm ubyte12p)
                     pc
                     (stat statp)
                     (feat featp))
  :guard (and (stat-validp stat feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the instructions with the @('BRANCH') opcode
          [ISA:2.5.2]."
  (branch-funct-case funct
                     :beq (exec-beq rs1 rs2 imm pc stat feat)
                     :bne (exec-bne rs1 rs2 imm pc stat feat)
                     :blt (exec-blt rs1 rs2 imm pc stat feat)
                     :bltu (exec-bltu rs1 rs2 imm pc stat feat)
                     :bge (exec-bge rs1 rs2 imm pc stat feat)
                     :bgeu (exec-bgeu rs1 rs2 imm pc stat feat))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-branch
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eff-addr ((rs1 ubyte5p) (imm ubyte12p) (stat statp) (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (addr integerp)
  :short "Effective address for a load or store instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned @('XLEN')-bit integer from @('rs1'); this is the base.
     We sign-extend the 12-bit immediate to @('XLEN') bits; this is the offset.
     We return the sum of base and offset, as an integer;
     the functions to read and write memory
     use the low @('XLEN') bits of this integer."))
  (b* ((base (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
       (offset (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm)))))
    (+ base offset))
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lb ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (imm ubyte12p)
                 (stat statp)
                 (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('LB') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 8-bit integer from the effective address,
     and sign-extend it to @('XLEN') bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (result (loghead (feat->xlen feat)
                        (logext 8 (read-memory-unsigned8 addr stat feat))))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-lb
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lbu ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('LBU') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 8-bit integer from the effective address,
     which is also implicitly zero-extended to @('XLEN') bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (result (read-memory-unsigned8 addr stat feat))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-lbu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lh ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (imm ubyte12p)
                 (stat statp)
                 (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('LH') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 16-bit integer from the effective address,
     and sign-extend it to @('XLEN') bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (result (loghead (feat->xlen feat)
                        (logext 16 (read-memory-unsigned16 addr stat feat))))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-lh
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lhu ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat statp)
                  (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('LHU') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 16-bit integer from the effective address,
     which is also implicitly zero-extended to @('XLEN') bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (result (read-memory-unsigned16 addr stat feat))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-lhu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lw ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (imm ubyte12p)
                 (stat statp)
                 (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('LW') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 32-bit integer from the effective address.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (result (read-memory-unsigned32 addr stat feat))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-lw
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lwu ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat statp)
                  (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('LW') instruction [ISA:4.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only valid in 64-bit mode.")
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 32-bit integer from the effective address,
     which is also implicitly zero-extended to 64 bits.
     We write the result to @('rd').
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (result (read-memory-unsigned32 addr stat feat))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-lwu
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ld ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (imm ubyte12p)
                 (stat statp)
                 (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('LW') instruction [ISA:4.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only valid in 64-bit mode.")
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 64-bit integer from the effective address.
     We write the integer to @('rd').
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (result (read-memory-unsigned64 addr stat feat))
       (stat (write-xreg (ubyte5-fix rd) result stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-ld
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum ubyte5-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-load ((funct load-funct-p)
                   (rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat statp)
                   (feat featp))
  :guard (and (stat-validp stat feat)
              (implies (or (load-funct-case funct :lwu)
                           (load-funct-case funct :ld))
                       (feat-64p feat))
              (< (lnfix rd) (feat->xnum feat))
              (< (lnfix rs1) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the instructions with the @('LOAD') opcode
          [ISA:2.6] [ISA:4.3]."
  (load-funct-case funct
                   :lb (exec-lb rd rs1 imm stat feat)
                   :lbu (exec-lbu rd rs1 imm stat feat)
                   :lh (exec-lh rd rs1 imm stat feat)
                   :lhu (exec-lhu rd rs1 imm stat feat)
                   :lw (exec-lw rd rs1 imm stat feat)
                   :lwu (exec-lwu rd rs1 imm stat feat)
                   :ld (exec-ld rd rs1 imm stat feat))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-load
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix rd) (feat->xnum feat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sb ((rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (imm ubyte12p)
                 (stat statp)
                 (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SB') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read the low 8 bits of @('rs2') as an unsigned 8-bit integer.
     We write the integer to the effective address.
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (val (loghead 8 (read-xreg-unsigned (ubyte5-fix rs2) stat feat)))
       (stat (write-memory-unsigned8 addr val stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sb
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sh ((rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (imm ubyte12p)
                 (stat statp)
                 (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SH') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     We read the low 16 bits of @('rs2') as an unsigned 16-bit integer.
     We write the integer to the effective address.
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (val (loghead 16 (read-xreg-unsigned (ubyte5-fix rs2) stat feat)))
       (stat (write-memory-unsigned16 addr val stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sh
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sw ((rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (imm ubyte12p)
                 (stat statp)
                 (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SW') instruction [ISA:2.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We calculate the effective address.
     In 32-bit mode, we read an unsigned 32-bit integer from the @('rs2');
     in 64-bit mode, we read the low 32 bits of @('rs2')
     as an unsigned 32-bit integer.
     We write the integer to the effective address.
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (val (cond ((feat-32p feat)
                   (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
                  ((feat-64p feat)
                   (loghead 32 (read-xreg-unsigned (ubyte5-fix rs2) stat feat)))
                  (t (impossible))))
       (stat (write-memory-unsigned32 addr val stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sw
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sd ((rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (imm ubyte12p)
                 (stat statp)
                 (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the @('SD') instruction [ISA:4.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only valid in 64-bit mode.")
   (xdoc::p
    "We calculate the effective address.
     We read an unsigned 64-bit integer from @('rs2').
     We write the integer to the effective address.
     We increment the program counter."))
  (b* ((addr (eff-addr rs1 imm stat feat))
       (val (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
       (stat (write-memory-unsigned64 addr val stat feat))
       (stat (inc4-pc stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable feat->xnum)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-sd
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-store ((funct store-funct-p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (imm ubyte12p)
                    (stat statp)
                    (feat featp))
  :guard (and (stat-validp stat feat)
              (implies (store-funct-case funct :sd)
                       (feat-64p feat))
              (< (lnfix rs1) (feat->xnum feat))
              (< (lnfix rs2) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Semantics of the instructions with the @('STORE') opcode
          [ISA:2.6] [ISA:4.3]."
  (store-funct-case funct
                    :sb (exec-sb rs1 rs2 imm stat feat)
                    :sh (exec-sh rs1 rs2 imm stat feat)
                    :sw (exec-sw rs1 rs2 imm stat feat)
                    :sd (exec-sd rs1 rs2 imm stat feat))
  :hooks (:fix)

  ///

  (defret stat-validp-of-exec-store
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-instr ((instr instrp)
                    pc
                    (stat statp)
                    (feat featp))
  :guard (and (instr-validp instr feat)
              (cond ((feat-32p feat) (ubyte32p pc))
                    ((feat-64p feat) (ubyte64p pc))
                    (t (impossible)))
              (stat-validp stat feat))
  :returns (new-stat statp)
  :short "Semantics of instructions."
  (instr-case instr
              :op-imm (exec-op-imm instr.funct
                                   instr.rd
                                   instr.rs1
                                   instr.imm
                                   stat
                                   feat)
              :op-imms32 (exec-op-imms32 instr.funct
                                         instr.rd
                                         instr.rs1
                                         instr.imm
                                         stat
                                         feat)
              :op-imms64 (exec-op-imms64 instr.funct
                                         instr.rd
                                         instr.rs1
                                         instr.imm
                                         stat
                                         feat)
              :op-imm-32 (exec-op-imm-32 instr.funct
                                         instr.rd
                                         instr.rs1
                                         instr.imm
                                         stat
                                         feat)
              :op-imms-32 (exec-op-imms-32 instr.funct
                                           instr.rd
                                           instr.rs1
                                           instr.imm
                                           stat
                                           feat)
              :lui (exec-lui instr.rd
                             instr.imm
                             stat
                             feat)
              :auipc (exec-auipc instr.rd
                                 instr.imm
                                 pc
                                 stat
                                 feat)
              :op (exec-op instr.funct
                           instr.rd
                           instr.rs1
                           instr.rs2
                           stat
                           feat)
              :op-32 (exec-op-32 instr.funct
                                 instr.rd
                                 instr.rs1
                                 instr.rs2
                                 stat
                                 feat)
              :jal (exec-jal instr.rd
                             instr.imm
                             pc
                             stat
                             feat)
              :jalr (exec-jalr instr.rd
                               instr.rs1
                               instr.imm
                               pc
                               stat
                               feat)
              :branch (exec-branch instr.funct
                                   instr.rs1
                                   instr.rs2
                                   instr.imm
                                   pc
                                   stat
                                   feat)
              :load (exec-load instr.funct
                               instr.rd
                               instr.rs1
                               instr.imm
                               stat
                               feat)
              :store (exec-store instr.funct
                                 instr.rs1
                                 instr.rs2
                                 instr.imm
                                 stat
                                 feat))
  :guard-hints (("Goal"
                 :in-theory (enable instr-validp)
                 :cases ((feat-embedp feat))))
  :hooks (:fix)

  :prepwork
  ((defrulel lemma
     (implies (ubyte5p x)
              (< x 32))))

  ///

  (defret stat-validp-of-exec-instr
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (instr-validp instr feat))
    :hints (("Goal"
             :in-theory (enable instr-validp)
             :cases ((feat-embedp feat))))))
