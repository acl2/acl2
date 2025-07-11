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

(include-book "semantics")

(local (include-book "../library-extensions/theorems"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics-equivalences
  :parents (specification)
  :short "Equivalent semantic definitions for instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "For some integer instructions, like @('SLT') and @('SLTU'),
     it is important whether the operands are read as signed or unsigned.
     For other instructions, like @('ADD'), it does not matter.
     For the latter kinds of instructions, here we prove
     equivalent definitions that read signed operands."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-addi-alt-defs
  :short "Equivalent semantic definitions of @('ADDI')."

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
                                      (read-xreg-unsigned
                                       rs1 stat feat)))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-andi-alt-defs
  :short "Equivalent semantic definitions of @('ANDI')."

  (defruled exec-andi-alt-def-signed-signed
    (equal (exec-andi rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (imm-operand (logext 12 (ubyte12-fix imm)))
                (result (logand rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-andi
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc))

  (defruled exec-andi-alt-def-unsigned-signed
    (equal (exec-andi rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
                (imm-operand (logext 12 (ubyte12-fix imm)))
                (result (logand rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-andi
             write-xreg
             inc4-pc
             write-pc))

  (defruled exec-andi-alt-def-signed-unsigned
    (equal (exec-andi rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (imm-operand
                 (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
                (result (logand rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-andi
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-ori-alt-defs
  :short "Equivalent semantic definitions of @('ORI')."

  (defruled exec-ori-alt-def-signed-signed
    (equal (exec-ori rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (imm-operand (logext 12 (ubyte12-fix imm)))
                (result (logior rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-ori
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc))

  (defruled exec-ori-alt-def-unsigned-signed
    (equal (exec-ori rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
                (imm-operand (logext 12 (ubyte12-fix imm)))
                (result (logior rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-ori
             write-xreg
             inc4-pc
             write-pc))

  (defruled exec-ori-alt-def-signed-unsigned
    (equal (exec-ori rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (imm-operand
                 (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
                (result (logior rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-ori
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-xori-alt-defs
  :short "Equivalent semantic definitions of @('XORI')."

  (defruled exec-xori-alt-def-signed-signed
    (equal (exec-xori rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (imm-operand (logext 12 (ubyte12-fix imm)))
                (result (logxor rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-xori
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc))

  (defruled exec-xori-alt-def-unsigned-signed
    (equal (exec-xori rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
                (imm-operand (logext 12 (ubyte12-fix imm)))
                (result (logxor rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-xori
             write-xreg
             inc4-pc
             write-pc))

  (defruled exec-xori-alt-def-signed-unsigned
    (equal (exec-xori rd rs1 imm stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (imm-operand
                 (loghead (feat->xlen feat) (logext 12 (ubyte12-fix imm))))
                (result (logxor rs1-operand imm-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-xori
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-add-alt-defs
  :short "Equivalent semantic definitions of @('ADD')."

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
             ifix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-sub-alt-defs
  :short "Equivalent semantic definitions of @('SUB')."

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
             ifix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-and-alt-defs
  :short "Equivalent semantic definitions of @('AND')."

  (defruled exec-and-alt-def-signed-signed
    (equal (exec-and rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (result (logand rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-and
             read-xreg-signed
             write-xreg))

  (defruled exec-and-alt-def-unsigned-signed
    (equal (exec-and rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (result (logand rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-and
             read-xreg-signed
             write-xreg))

  (defruled exec-and-alt-def-signed-unsigned
    (equal (exec-and rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
                (result (logand rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-and
             read-xreg-signed
             write-xreg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-or-alt-defs
  :short "Equivalent semantic definitions of @('OR')."

  (defruled exec-or-alt-def-signed-signed
    (equal (exec-or rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (result (logior rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-or
             read-xreg-signed
             write-xreg))

  (defruled exec-or-alt-def-unsigned-signed
    (equal (exec-or rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (result (logior rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-or
             read-xreg-signed
             write-xreg))

  (defruled exec-or-alt-def-signed-unsigned
    (equal (exec-or rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
                (result (logior rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-or
             read-xreg-signed
             write-xreg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-xor-alt-defs
  :short "Equivalent semantic definitions of @('XOR')."

  (defruled exec-xor-alt-def-signed-signed
    (equal (exec-xor rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (result (logxor rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-xor
             read-xreg-signed
             write-xreg))

  (defruled exec-xor-alt-def-unsigned-signed
    (equal (exec-xor rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-unsigned (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (result (logxor rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-xor
             read-xreg-signed
             write-xreg))

  (defruled exec-xor-alt-def-signed-unsigned
    (equal (exec-xor rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-unsigned (ubyte5-fix rs2) stat feat))
                (result (logxor rs1-operand rs2-operand))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-xor
             read-xreg-signed
             write-xreg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-sll-alt-defs
  :short "Equivalent semantic definitions of @('SLL')."

  (defruled exec-sll-alt-def
    (equal (exec-sll rd rs1 rs2 stat feat)
           (b* ((rs1-operand (read-xreg-signed (ubyte5-fix rs1) stat feat))
                (rs2-operand (read-xreg-signed (ubyte5-fix rs2) stat feat))
                (shift-amount
                 (cond ((feat-32p feat) (loghead 5 rs2-operand))
                       ((feat-64p feat) (loghead 6 rs2-operand))
                       (t (impossible))))
                (result (ash rs1-operand shift-amount))
                (stat (write-xreg (ubyte5-fix rd) result stat feat))
                (stat (inc4-pc stat feat)))
             stat))
    :enable (exec-sll
             read-xreg-signed
             write-xreg
             inc4-pc
             write-pc
             bitops::loghead-of-ash
             loghead-upper-bound)
    :disable acl2::ash-to-floor))
