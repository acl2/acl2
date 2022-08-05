; RISC-V Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (acoglio on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "library-extensions")
(include-book "instructions")
(include-book "state")

(include-book "kestrel/fty/ubyte4" :dir :system)

(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/sbyte64" :dir :system)

(include-book "kestrel/utilities/digits-any-base/core" :dir :system)
(include-book "kestrel/utilities/digits-any-base/pow2" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel dab-digit-list-of-256-when-ubyte8-listp
  (implies (ubyte8-listp x)
           (acl2::dab-digit-listp 256 x))
  :enable (ubyte8-listp ubyte8p acl2::dab-digitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signext-imm12 ((imm ubyte12p))
  :returns (val integerp :rule-classes (:rewrite :type-prescription))
  (logext 12 (ubyte12-fix imm))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signext-imm20 ((imm ubyte20p))
  :returns (val integerp :rule-classes (:rewrite :type-prescription))
  (logext 20 (ubyte20-fix imm))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eff-addr ((rs1 ubyte5p) (imm ubyte12p) (stat state64ip))
  :returns (addr integerp)
  (b* ((base (read-xreg-unsigned rs1 stat))
       (offset (signext-imm12 imm)))
    (+ base offset))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-addi ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (+ (read-xreg-signed rs1 stat)
                 (signext-imm12 imm))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slti ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (if (< (read-xreg-signed rs1 stat)
                     (signext-imm12 imm))
                  1
                0)
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sltiu ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (if (< (read-xreg-unsigned rs1 stat)
                     (loghead 64 (signext-imm12 imm)))
                  1
                0)
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-andi ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (logand (read-xreg-signed rs1 stat)
                      (signext-imm12 imm))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ori ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (logior (read-xreg-signed rs1 stat)
                      (signext-imm12 imm))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-xori ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (logxor (read-xreg-signed rs1 stat)
                      (signext-imm12 imm))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imm ((funct op-imm-funct-p)
                     (rd ubyte5p)
                     (rs1 ubyte5p)
                     (imm ubyte12p)
                     (stat state64ip))
  :returns (new-stat state64ip)
  (case (op-imm-funct-kind funct)
    (:addi (exec-addi rd rs1 imm stat))
    (:slti (exec-slti rd rs1 imm stat))
    (:sltiu (exec-sltiu rd rs1 imm stat))
    (:andi (exec-andi rd rs1 imm stat))
    (:ori (exec-ori rd rs1 imm stat))
    (:xori (exec-xori rd rs1 imm stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-addiw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte12p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (+ (read-xreg-signed32 rs1 stat)
                    (signext-imm12 imm))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imm-32 ((funct op-imm-32-funct-p)
                        (rd ubyte5p)
                        (rs1 ubyte5p)
                        (imm ubyte12p)
                        (stat state64ip))
  :returns (new-stat state64ip)
  (case (op-imm-32-funct-kind funct)
    (:addiw (exec-addiw rd rs1 imm stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slli ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte6p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (ash (read-xreg-unsigned rs1 stat)
                   (ubyte6-fix imm))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srli ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte6p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (ash (read-xreg-unsigned rs1 stat)
                   (- (ubyte6-fix imm)))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srai ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte6p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (ash (read-xreg-signed rs1 stat)
                   (- (ubyte6-fix imm)))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imms ((funct op-imms-funct-p)
                      (rd ubyte5p)
                      (rs1 ubyte5p)
                      (imm ubyte6p)
                      (stat state64ip))
  :returns (new-stat state64ip)
  (case (op-imms-funct-kind funct)
    (:slli (exec-slli rd rs1 imm stat))
    (:srli (exec-srli rd rs1 imm stat))
    (:srai (exec-srai rd rs1 imm stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slliw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (ash (read-xreg-unsigned32 rs1 stat)
                      (ubyte5-fix imm))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srliw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (ash (read-xreg-unsigned32 rs1 stat)
                      (- (ubyte5-fix imm)))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sraiw ((rd ubyte5p)
                    (rs1 ubyte5p)
                    (imm ubyte5p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (ash (read-xreg-signed32 rs1 stat)
                      (- (ubyte5-fix imm)))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-imms-32 ((funct op-imms-32-funct-p)
                         (rd ubyte5p)
                         (rs1 ubyte5p)
                         (imm ubyte5p)
                         (stat state64ip))
  :returns (new-stat state64ip)
  (case (op-imms-32-funct-kind funct)
    (:slliw (exec-slliw rd rs1 imm stat))
    (:srliw (exec-srliw rd rs1 imm stat))
    (:sraiw (exec-sraiw rd rs1 imm stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lui ((rd ubyte5p)
                  (imm ubyte20p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (ash (ubyte20-fix imm) 12)
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-auipc ((rd ubyte5p)
                    (imm ubyte20p)
                    (pc ubyte64p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (+ (ubyte64-fix pc)
                 (ash (signext-imm20 imm) 12))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-add ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (+ (read-xreg-signed rs1 stat)
                 (read-xreg-signed rs2 stat))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-slt ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (if (< (read-xreg-signed rs1 stat)
                     (read-xreg-signed rs2 stat))
                  1
                0)
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sltu ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (if (< (read-xreg-unsigned rs1 stat)
                     (read-xreg-unsigned rs2 stat))
                  1
                0)
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-and ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (logand (read-xreg-signed rs1 stat)
                      (read-xreg-signed rs2 stat))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-or ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (logior (read-xreg-signed rs1 stat)
                      (read-xreg-signed rs2 stat))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-xor ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (logxor (read-xreg-signed rs1 stat)
                      (read-xreg-signed rs2 stat))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sll ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (ash (read-xreg-unsigned rs1 stat)
                   (loghead 6 (read-xreg-unsigned rs2 stat)))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srl ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (ash (read-xreg-unsigned rs1 stat)
                   (- (loghead 6 (read-xreg-unsigned rs2 stat))))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sra ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (ash (read-xreg-signed rs1 stat)
                   (- (loghead 6 (read-xreg-unsigned rs2 stat))))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sub ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg rd
              (- (read-xreg-signed rs1 stat)
                 (read-xreg-signed rs2 stat))
              (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op ((funct op-funct-p)
                 (rd ubyte5p)
                 (rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (case (op-funct-kind funct)
    (:add (exec-add rd rs1 rs2 stat))
    (:slt (exec-slt rd rs1 rs2 stat))
    (:sltu (exec-sltu rd rs1 rs2 stat))
    (:and (exec-and rd rs1 rs2 stat))
    (:or (exec-or rd rs1 rs2 stat))
    (:xor (exec-xor rd rs1 rs2 stat))
    (:sll (exec-sll rd rs1 rs2 stat))
    (:srl (exec-srl rd rs1 rs2 stat))
    (:sra (exec-sra rd rs1 rs2 stat))
    (:sub (exec-sub rd rs1 rs2 stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-addw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (+ (read-xreg-signed32 rs1 stat)
                    (read-xreg-signed32 rs2 stat))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sllw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (ash (read-xreg-unsigned32 rs1 stat)
                      (loghead 5 (read-xreg-unsigned32 rs2 stat)))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-srlw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (ash (read-xreg-unsigned32 rs1 stat)
                      (- (loghead 5 (read-xreg-unsigned32 rs2 stat))))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sraw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (ash (read-xreg-signed32 rs1 stat)
                      (- (loghead 5 (read-xreg-unsigned32 rs2 stat))))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-subw ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg-32 rd
                 (- (read-xreg-signed32 rs1 stat)
                    (read-xreg-signed32 rs2 stat))
                 (inc-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-op-32 ((funct op-32-funct-p)
                    (rd ubyte5p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (case (op-32-funct-kind funct)
    (:addw (exec-addw rd rs1 rs2 stat))
    (:sllw (exec-sllw rd rs1 rs2 stat))
    (:srlw (exec-srlw rd rs1 rs2 stat))
    (:sraw (exec-sraw rd rs1 rs2 stat))
    (:subw (exec-subw rd rs1 rs2 stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-jal ((rd ubyte5p)
                  (imm ubyte20p)
                  (pc ubyte64p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((offset (ash (signext-imm20 imm) 1))
       (pc (ubyte64-fix pc))
       (new-pc (+ pc offset))
       (pc+4 (+ pc 4))
       (stat (write-xreg rd pc+4 stat))
       (stat (write-pc new-pc stat)))
    stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-jalr ((rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (pc ubyte64p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((offset (signext-imm12 imm))
       (base (read-xreg-unsigned rs1 stat))
       (base+offset (+ base offset))
       (new-pc (logandc1 1 base+offset))
       (pc+4 (+ (ubyte64-fix pc) 4))
       (stat (write-xreg rd pc+4 stat))
       (stat (write-pc new-pc stat)))
    stat)
  :prepwork
  ((defrulel verify-guards-lemma
     (implies (and (integerp x)
                   (integerp y))
              (integerp (+ x y)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-beq ((rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (imm ubyte12p)
                  (pc ubyte64p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((src1 (read-xreg-unsigned rs1 stat))
       (src2 (read-xreg-unsigned rs2 stat))
       (offset (ash (signext-imm12 imm) 1))
       (pc (ubyte64-fix pc))
       (target (+ pc offset))
       (pc+4 (+ pc 4))
       (new-pc (if (= src1 src2) target pc+4)))
    (write-pc new-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bne ((rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (imm ubyte12p)
                  (pc ubyte64p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((src1 (read-xreg-unsigned rs1 stat))
       (src2 (read-xreg-unsigned rs2 stat))
       (offset (ash (signext-imm12 imm) 1))
       (pc (ubyte64-fix pc))
       (target (+ pc offset))
       (pc+4 (+ pc 4))
       (new-pc (if (/= src1 src2) target pc+4)))
    (write-pc new-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-blt ((rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (imm ubyte12p)
                  (pc ubyte64p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((src1 (read-xreg-signed rs1 stat))
       (src2 (read-xreg-signed rs2 stat))
       (offset (ash (signext-imm12 imm) 1))
       (pc (ubyte64-fix pc))
       (target (+ pc offset))
       (pc+4 (+ pc 4))
       (new-pc (if (< src1 src2) target pc+4)))
    (write-pc new-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bltu ((rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (imm ubyte12p)
                   (pc ubyte64p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((src1 (read-xreg-unsigned rs1 stat))
       (src2 (read-xreg-unsigned rs2 stat))
       (offset (ash (signext-imm12 imm) 1))
       (pc (ubyte64-fix pc))
       (target (+ pc offset))
       (pc+4 (+ pc 4))
       (new-pc (if (< src1 src2) target pc+4)))
    (write-pc new-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bge ((rs1 ubyte5p)
                  (rs2 ubyte5p)
                  (imm ubyte12p)
                  (pc ubyte64p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((src1 (read-xreg-signed rs1 stat))
       (src2 (read-xreg-signed rs2 stat))
       (offset (ash (signext-imm12 imm) 1))
       (pc (ubyte64-fix pc))
       (target (+ pc offset))
       (pc+4 (+ pc 4))
       (new-pc (if (>= src1 src2) target pc+4)))
    (write-pc new-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bgeu ((rs1 ubyte5p)
                   (rs2 ubyte5p)
                   (imm ubyte12p)
                   (pc ubyte64p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((src1 (read-xreg-unsigned rs1 stat))
       (src2 (read-xreg-unsigned rs2 stat))
       (offset (ash (signext-imm12 imm) 1))
       (pc (ubyte64-fix pc))
       (target (+ pc offset))
       (pc+4 (+ pc 4))
       (new-pc (if (>= src1 src2) target pc+4)))
    (write-pc new-pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-branch ((funct branch-funct-p)
                     (rs1 ubyte5p)
                     (rs2 ubyte5p)
                     (imm ubyte12p)
                     (pc ubyte64p)
                     (stat state64ip))
  :returns (new-stat state64ip)
  (case (branch-funct-kind funct)
    (:beq (exec-beq rs1 rs2 imm pc stat))
    (:bne (exec-bne rs1 rs2 imm pc stat))
    (:blt (exec-blt rs1 rs2 imm pc stat))
    (:bltu (exec-bltu rs1 rs2 imm pc stat))
    (:bge (exec-bge rs1 rs2 imm pc stat))
    (:bgeu (exec-bgeu rs1 rs2 imm pc stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lb ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (imm ubyte12p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (logext 8 (read-mem-ubyte8 addr stat))))
    (write-xreg rd val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lbu ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (read-mem-ubyte8 addr stat)))
    (write-xreg rd val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lh ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (imm ubyte12p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (logext 16 (read-mem-ubyte16-lendian addr stat))))
    (write-xreg rd val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lhu ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (read-mem-ubyte16-lendian addr stat)))
    (write-xreg rd val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lw ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (imm ubyte12p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (logext 32 (read-mem-ubyte32-lendian addr stat))))
    (write-xreg rd val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lwu ((rd ubyte5p)
                  (rs1 ubyte5p)
                  (imm ubyte12p)
                  (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (read-mem-ubyte32-lendian addr stat)))
    (write-xreg rd val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ld ((rd ubyte5p)
                 (rs1 ubyte5p)
                 (imm ubyte12p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (read-mem-ubyte64-lendian addr stat)))
    (write-xreg rd val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-load ((funct load-funct-p)
                   (rd ubyte5p)
                   (rs1 ubyte5p)
                   (imm ubyte12p)
                   (stat state64ip))
  :returns (new-stat state64ip)
  (case (load-funct-kind funct)
    (:lb (exec-lb rd rs1 imm stat))
    (:lbu (exec-lbu rd rs1 imm stat))
    (:lh (exec-lh rd rs1 imm stat))
    (:lhu (exec-lhu rd rs1 imm stat))
    (:lw (exec-lw rd rs1 imm stat))
    (:lwu (exec-lwu rd rs1 imm stat))
    (:ld (exec-ld rd rs1 imm stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sb ((rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (imm ubyte12p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (loghead 8 (read-xreg-unsigned rs2 stat))))
    (write-mem-ubyte8 addr val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sh ((rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (imm ubyte12p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (loghead 16 (read-xreg-unsigned rs2 stat))))
    (write-mem-ubyte16-lendian addr val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sw ((rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (imm ubyte12p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (loghead 32 (read-xreg-unsigned rs2 stat))))
    (write-mem-ubyte32-lendian addr val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sd ((rs1 ubyte5p)
                 (rs2 ubyte5p)
                 (imm ubyte12p)
                 (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (eff-addr rs1 imm stat))
       (val (loghead 64 (read-xreg-unsigned rs2 stat))))
    (write-mem-ubyte64-lendian addr val (inc-pc stat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-store ((funct store-funct-p)
                    (rs1 ubyte5p)
                    (rs2 ubyte5p)
                    (imm ubyte12p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (case (store-funct-kind funct)
    (:sb (exec-sb rs1 rs2 imm stat))
    (:sh (exec-sh rs1 rs2 imm stat))
    (:sw (exec-sw rs1 rs2 imm stat))
    (:sd (exec-sd rs1 rs2 imm stat))
    (t (prog2$ (impossible) (state64i-fix stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-instr ((instr instrp)
                    (pc ubyte64p)
                    (stat state64ip))
  :returns (new-stat state64ip)
  (instr-case instr
              :op-imm (exec-op-imm instr.funct
                                   instr.rd
                                   instr.rs1
                                   instr.imm
                                   stat)
              :op-imm-32 (exec-op-imm-32 instr.funct
                                         instr.rd
                                         instr.rs1
                                         instr.imm
                                         stat)
              :op-imms (exec-op-imms instr.funct
                                     instr.rd
                                     instr.rs1
                                     instr.imm
                                     stat)
              :op-imms-32 (exec-op-imms-32 instr.funct
                                           instr.rd
                                           instr.rs1
                                           instr.imm
                                           stat)
              :lui (exec-lui instr.rd
                             instr.imm
                             stat)
              :auipc (exec-auipc instr.rd
                                 instr.imm
                                 pc
                                 stat)
              :op (exec-op instr.funct
                           instr.rd
                           instr.rs1
                           instr.rs2
                           stat)
              :op-32 (exec-op-32 instr.funct
                                 instr.rd
                                 instr.rs1
                                 instr.rs2
                                 stat)
              :jal (exec-jal instr.rd
                             instr.imm
                             pc
                             stat)
              :jalr (exec-jalr instr.rd
                               instr.rs1
                               instr.imm
                               pc
                               stat)
              :branch (exec-branch instr.funct
                                   instr.rs1
                                   instr.rs2
                                   instr.imm
                                   pc
                                   stat)
              :load (exec-load instr.funct
                               instr.rd
                               instr.rs1
                               instr.imm
                               stat)
              :store (exec-store instr.funct
                                 instr.rs1
                                 instr.rs2
                                 instr.imm
                                 stat))
  :hooks (:fix))
