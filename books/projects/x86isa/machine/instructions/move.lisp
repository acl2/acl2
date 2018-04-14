;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: MOV
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-mov-Op/En-MR

  ;; Op/En: MR
  ;; [OP R/M, REG]
  ;; 88: MOV r/m8,  r8
  ;; 89: MOV r/m16, r16
  ;; 89: MOV r/m32, r32
  ;; 89: MOV r/m64, r64

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32)
                                        ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #x88 '(:nil nil)
                                      'x86-mov-Op/En-MR)
    (add-to-implemented-opcodes-table 'MOV #x89 '(:nil nil)
                                      'x86-mov-Op/En-MR))

  :body

  (b* ((ctx 'x86-mov-Op/En-MR)

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (the (unsigned-byte 8) (prefixes-slice :group-2-prefix prefixes)))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (equal opcode #x88)
            1
          ;; Intel manual, Mar'17, Volume 1, Table 3-4:
          (if (64-bit-modep x86)
              (if (logbitp #.*w* rex-byte)
                  8
                (if p3? 2 4))
            (b* ((cs-hidden (xr :seg-hidden *cs* x86))
                 (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
                 (cs.d
                  (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
              (if (= cs.d 1)
                  (if p3? 2 4)
                (if p3? 4 2))))))

       (register (rgfi-size operand-size (reg-index reg rex-byte #.*r*)
                            rex-byte x86))

       ((mv flg0
            (the (signed-byte 64) addr)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr p4? temp-rip rex-byte r/m mod sib
                              0 ;; No immediate operand
                              x86)))
       ((when flg0)
        (!!ms-fresh :x86-effective-addr-error flg0))

       (seg-reg (select-segment-register p2 p4? mod  r/m x86))

       ((mv flg temp-rip) (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
              temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
              start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:
       (inst-ac? t)
       ((mv flg2 x86)
        (x86-operand-to-reg/mem$ operand-size
                                 inst-ac?
                                 nil ;; Not a memory pointer operand
                                 register
                                 seg-reg
                                 addr
                                 rex-byte
                                 r/m
                                 mod
                                 x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
        (!!ms-fresh :x86-operand-to-reg/mem flg2))
       (x86 (write-*ip temp-rip x86)))
    x86))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-mov-Op/En-RM

  ;; Op/En: RM
  ;; [OP REG, R/M]
  ;; 8A: MOV r8,  r/m8
  ;; 8A: MOV r16, r/m16
  ;; 8B: MOV r32, r/m32
  ;; 8B: MOV r64, r/m64

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #x8A '(:nil nil)
                                      'x86-mov-Op/En-RM)
    (add-to-implemented-opcodes-table 'MOV #x8B '(:nil nil)
                                      'x86-mov-Op/En-RM))
  :body

  (b* ((ctx 'x86-mov-Op/En-RM)

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (equal opcode #x8A)
            1
          ;; Intel manual, Mar'17, Volume 1, Table 3-4:
          (if (64-bit-modep x86)
              (if (logbitp #.*w* rex-byte)
                  8
                (if p3? 2 4))
            (b* ((cs-hidden (xr :seg-hidden *cs* x86))
                 (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
                 (cs.d
                  (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
              (if (= cs.d 1)
                  (if p3? 2 4)
                (if p3? 4 2))))))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by) ?addr x86)
        (x86-operand-from-modr/m-and-sib-bytes$ #.*gpr-access*
                                                operand-size
                                                inst-ac?
                                                nil ;; Not a memory pointer operand
                                                seg-reg
                                                p4?
                                                temp-rip
                                                rex-byte
                                                r/m
                                                mod
                                                sib
                                                0 ;; No immediate operand
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg temp-rip) (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*r*)
                        reg/mem rex-byte x86))
       (x86 (write-*ip temp-rip x86)))
    x86))

(def-inst x86-mov-Op/En-FD

  ;; Op/En: FD
  ;; [OP rAX, Moffs]
  ;; A0: MOV AL,         moffs8
  ;; A1: MOV AX/EAX/RAX, moffs16/moffs32/moffs64

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #xA0 '(:nil nil)
                                      'x86-mov-Op/En-FD)
    (add-to-implemented-opcodes-table 'MOV #xA1 '(:nil nil)
                                      'x86-mov-Op/En-FD))
  :body

  (b* ((ctx 'x86-mov-Op/En-FD)

       ;; This instruction does not require a ModR/M byte.

       ;; Get prefixes:
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ;; The Intel manual says the following:

       ;; Under the MOV instruction description:

       ;; The moffs8, moffs16, moffs32 and moffs64 operands specify a
       ;; simple offset relative to the segment base, where 8, 16, 32
       ;; and 64 refer to the size of the data. The address-size
       ;; attribute of the instruction determines the size of the
       ;; offset, either 16, 32 or 64 bits.

       ;; Under the "Instruction Column in the Opcode Summary Table":

       ;; moffs8, moffs16, moffs32, moffs64   A simple memory variable
       ;; (memory offset) of type byte, word, or doubleword used by
       ;; some variants of the MOV instruction. The actual address is
       ;; given by a simple offset relative to the segment base. No
       ;; ModR/M byte is used in the instruction. The number shown
       ;; with moffs indicates its size, which is determined by the
       ;; address-size attribute of the instruction.

       ;; Under "Codes for Addressing Method":

       ;; O The instruction has no ModR/M byte. The offset of the
       ;; operand is coded as a word or double word (depending on
       ;; address size attribute) in the instruction. No base
       ;; register, index register, or scaling factor can be applied
       ;; (for example, MOV (A0 A3)).

       ((the (integer 1 8) operand-size)
        (if (equal opcode #xA0)
            1
          (if (and (equal opcode #xA1)
                   (logbitp #.*w* rex-byte))
              8
            (if p3? ;; See Table 3-4, P. 3-26, Intel Vol. 1.
                2
              4))))
       ((the (integer 1 8) offset-size)
        ;; See Table 3-4, P. 3-26, Intel Vol. 1.
        (if p4? 4 8))

       ;; Get the offset:
       ((mv flg offset x86)
        (riml-size offset-size temp-rip :x x86))
       ((when flg) (!!ms-fresh :riml-size-error flg))

       ;; Check if the above memory read caused any problems:
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip offset-size))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Get the segment base (which is zero for every segment but FS
       ;; and GS in the 64-bit mode):
       ((mv flg v-addr)
        (case p2
          (0 (mv nil offset))
          ;; I don't really need to check whether FS and GS base are
          ;; canonical or not.  On the real machine, if the MSRs
          ;; containing these bases are assigned non-canonical
          ;; addresses, an exception is raised.
          (#.*fs-override*
           (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
                  (fs-base (n64-to-i64 nat-fs-base)))
             (if (not (canonical-address-p fs-base))
                 (mv 'Non-Canonical-FS-Base fs-base)
               (mv nil (+ fs-base offset)))))
          (#.*gs-override*
           (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
                  (gs-base (n64-to-i64 nat-gs-base)))
             (if (not (canonical-address-p gs-base))
                 (mv 'Non-Canonical-GS-Base gs-base)
               (mv nil (+ gs-base offset)))))
          (t (mv 'Unidentified-P2 offset))))
       ((when flg)
        (!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg))
       ((when (not (canonical-address-p v-addr)))
        (!!ms-fresh :Non-Canonical-V-Addr v-addr))
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand v-addr (the (integer 0 15) (- operand-size 1)))
                               0))))
        (!!ms-fresh :memory-access-not-aligned v-addr))

       ;; Get data from v-addr:
       ((mv flg data x86)
        (rml-size operand-size v-addr :r x86))
       ((when flg) (!!ms-fresh :rml-size-error flg))

       ;; Write the data to rAX:
       (x86 (!rgfi-size operand-size *rax* data rex-byte x86))
       (x86 (!rip temp-rip x86)))
    x86))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-mov-Op/En-OI

  ;; Op/En: OI
  ;; [OP REG, IMM]
  ;; B0 + rb: MOV r8,  imm8
  ;; B8 + rw: MOV r16, imm16
  ;; B8 + rd: MOV r32, imm32
  ;; B8 + rd: MOV r64, imm64

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rme-size riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #xB0 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB1 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB2 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB3 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB4 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB5 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB6 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB7 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB8 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB9 '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBA '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBB '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBC '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBD '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBE '(:nil nil)
                                      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBF '(:nil nil)
                                      'x86-mov-Op/En-OI))

  :body

  (b* ((ctx 'x86-mov-Op/En-OI)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))

       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (and (<= #xB0 opcode) ;; B0+rb
                 (<= opcode #xB7))
            1
          ;; Intel manual, Mar'17, Volume 1, Table 3-4:
          (if (64-bit-modep x86)
              (if (logbitp #.*w* rex-byte)
                  8
                (if p3? 2 4))
            (b* ((cs-hidden (xr :seg-hidden *cs* x86))
                 (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
                 (cs.d
                  (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
              (if (= cs.d 1)
                  (if p3? 2 4)
                (if p3? 4 2))))))

       ;; We don't do any alignment check below when fetching the
       ;; immediate operand; reading the immediate operand is done
       ;; during code fetching, where alignment checks aren't supposed
       ;; to be done (see Intel Manuals, Volume 3, Section 6.15,
       ;; Exception and Interrupt Reference, Interrupt 17 Alignment
       ;; Check Exception (#AC) for details).
       ((mv flg0 imm x86)
        (rme-size operand-size temp-rip *cs* :x nil x86 :mem-ptr? nil))
       ((when flg0)
        (!!ms-fresh :imm-rml-size-error flg0))

       ((mv flg temp-rip) (add-to-*ip temp-rip operand-size x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       (reg (the (unsigned-byte 3) (logand 7 opcode)))
       ;; Update the x86 state:
       ;; See Intel Table 3.1, p.3-3, Vol. 2-A
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*b*)
                        imm rex-byte x86))
       (x86 (write-*ip temp-rip x86)))
      x86))

(def-inst x86-mov-Op/En-MI

  ;; Op/En: MI
  ;; [OP R/M, IMM]
  ;; C6/0: MOV r/m8, imm8
  ;; C7/0: MOV r/m16, imm16
  ;; C7/0: MOV r/m32, imm32
  ;; C7/0: MOV r/m64, imm32

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #xC6 '(:reg 0)
                                      'x86-mov-Op/En-MI)
    (add-to-implemented-opcodes-table 'MOV #xC7 '(:reg 0)
                                      'x86-mov-Op/En-MI))

  :body

  (b* ((ctx 'x86-mov-Op/En-MI)
       (mod (mrm-mod modr/m))
       (r/m (mrm-r/m modr/m))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))
       ((the (integer 1 8) imm-size)
        (if (equal opcode #xC6)
            1
          (if (logbitp #.*w* rex-byte)
              4
            (if p3?
                2
              4))))
       ((the (integer 1 8) reg/mem-size)
        (if (and (equal opcode #xC7)
                 (logbitp #.*w* rex-byte))
            8
          imm-size))

       ((mv flg0 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr p4? temp-rip rex-byte r/m mod sib
                              imm-size ;; bytes of immediate data
                              x86)))
       ((when flg0)
        (!!ms-fresh :x86-effective-addr-error flg0))
       ((mv flg1 v-addr)
        (case p2
          (0 (mv nil v-addr))
          ;; I don't really need to check whether FS and GS base are
          ;; canonical or not.  On the real machine, if the MSRs
          ;; containing these bases are assigned non-canonical
          ;; addresses, an exception is raised.
          (#.*fs-override*
           (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
                  (fs-base (n64-to-i64 nat-fs-base)))
             (if (not (canonical-address-p fs-base))
                 (mv 'Non-Canonical-FS-Base fs-base)
               (mv nil (+ fs-base v-addr)))))
          (#.*gs-override*
           (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
                  (gs-base (n64-to-i64 nat-gs-base)))
             (if (not (canonical-address-p gs-base))
                 (mv 'Non-Canonical-GS-Base gs-base)
               (mv nil (+ gs-base v-addr)))))
          (t (mv 'Unidentified-P2 v-addr))))
       ((when flg1)
        (!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg1))
       ((when (not (canonical-address-p v-addr)))
        (!!ms-fresh :v-addr-not-canonical v-addr))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((mv flg2 imm x86)
        (rml-size imm-size temp-rip :x x86))
       ((when flg2)
        (!!ms-fresh :imm-rml-size-error flg2))
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip imm-size))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))
       (imm (if (equal reg/mem-size 8)
                ;; Sign-extended
                (n64 (n32-to-i32 imm))
              imm))

       ;; Update the x86 state:
       (inst-ac? t)
       ((mv flg3 x86)
        (x86-operand-to-reg/mem
         reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         imm v-addr rex-byte r/m mod x86))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg3)
        (!!ms-fresh :x86-operand-to-reg/mem flg3))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LEA
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-lea

  ;; Op/En: RM
  ;; opcode = #x8D/r
  ;; LEA r16, m
  ;; LEA r32, m
  ;; LEA r64, m

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'LEA #x8D '(:nil nil) 'x86-lea)

  :body

  (b* ((ctx 'x86-lea)

       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ;; this is the operand size
       ;; in Intel manual, Mar'17, Vol 2, Tables 3-53 and 3-54:
       ((the (integer 2 8) register-size)
        (if (64-bit-modep x86)
            (if (logbitp #.*w* rex-byte)
                8
              (if p3? 2 4))
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       ((when (equal mod #b11))
        ;; See "M" in http://ref.x86asm.net/#Instruction-Operand-Codes
        (!!fault-fresh :ud nil ;; #UD
                       :x86-lea "Source operand is not a memory location"))

       ((mv ?flg0
            (the (signed-byte 64) M)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (x86-effective-addr p4?
                            temp-rip
                            rex-byte
                            r/m
                            mod
                            sib
                            0 ;; No immediate operand
                            x86))
       ((when flg0) (!!ms-fresh :x86-effective-addr-error flg0))

       ((mv flg temp-rip) (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
              temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
              start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; ((mv flg1 M)
       ;;  (case p2
       ;;    (0 (mv nil M))
       ;;    ;; I don't really need to check whether FS and GS base are
       ;;    ;; canonical or not.  On the real machine, if the MSRs
       ;;    ;; containing these bases are assigned non-canonical
       ;;    ;; addresses, an exception is raised.
       ;;    (#.*fs-override*
       ;;     (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
       ;;            (fs-base (n64-to-i64 nat-fs-base)))
       ;;       (if (not (canonical-address-p fs-base))
       ;;           (mv 'Non-Canonical-FS-Base fs-base)
       ;;         (mv nil (+ fs-base M)))))
       ;;    (#.*gs-override*
       ;;     (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
       ;;            (gs-base (n64-to-i64 nat-gs-base)))
       ;;       (if (not (canonical-address-p gs-base))
       ;;           (mv 'Non-Canonical-GS-Base gs-base)
       ;;         (mv nil (+ gs-base M)))))
       ;;    (t (mv 'Unidentified-P2 M))))
       ;; ((when flg1)
       ;;  (!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg1))

       (M (trunc register-size M))
       ;; Update the x86 state:
       (x86 (!rgfi-size
             register-size (reg-index reg rex-byte #.*r*) M rex-byte x86))
       (x86 (write-*ip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: MOVSXD/MOVSLQ
;; ======================================================================

(def-inst x86-one-byte-movsxd

  ;; Op/En: RM
  ;; [OP REG, R/M]
  ;; #x63: MOVSX  r16, r/m16 (Move word to word)
  ;;       MOVSXD r32, r/m32 (Move doubleword to doubleword)
  ;;       MOVSXD r64, r/m32 (Move doubleword to quadword with sign-extension)

  ;; I am not very confident about MOVSX's second operand being r/m16.
  ;; I haven't yet come across this instruction used with an
  ;; address-size override prefix.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'MOVSXD #x63 '(:nil nil) 'x86-one-byte-movsxd)

  :body

  (b* ((ctx 'x86-one-byte-movsxd)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))
       ((the (integer 1 8) reg/mem-size)
        (select-operand-size nil rex-byte t prefixes))
       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change
       ;; to an exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       (register-size (if (logbitp #.*w* rex-byte)
                          8
                        reg/mem-size))
       (reg/mem (if (equal register-size 8)
                    (n64 (n32-to-i32 reg/mem)) ;; sign-extended
                  reg/mem))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*) reg/mem
                        rex-byte x86))
       (x86 (!rip temp-rip x86)))
    x86))

(def-inst x86-two-byte-movsxd

  ;; Op/En: RM
  ;; [OP REG, R/M]

  ;; #x0F BE: MOVSX r16/32/64, r/m8
  ;; (Move byte to word/doubleword/quadword with sign-extension)

  ;; #x0F BF: MOVSX r16/32/64, r/m16
  ;; (Move word to word/doubleword/quadword with sign-extension)

  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32
                                               n08-to-i08
                                               n16-to-i16
                                               n32-to-i32
                                               n64-to-i64)
                                        ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOVSXD #x0FBE '(:nil nil)
                                      'x86-two-byte-movsxd)
    (add-to-implemented-opcodes-table 'MOVSXD #x0FBF '(:nil nil)
                                      'x86-two-byte-movsxd))
  :body

  (b* ((ctx 'x86-two-byte-movsxd)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))
       (reg/mem-size (if (equal opcode #xBE) 1 2))
       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       (register-size (select-operand-size nil rex-byte nil prefixes))
       (reg/mem (case reg/mem-size
                  (1
                   (mbe :logic (part-select (n08-to-i08 reg/mem)
                                            :low 0 :width (ash register-size 3))
                        :exec (logand (1- (ash 1 (the (integer 8 64)
                                                   (ash register-size 3))))
                                      (n08-to-i08 reg/mem))))
                  (2 (case register-size
                       (2 reg/mem)
                       (otherwise
                        (mbe :logic (part-select (n16-to-i16 reg/mem)
                                                 :low 0 :width (ash register-size 3))
                             :exec (logand (1- (ash 1 (the (integer 8 64)
                                                        (ash register-size 3))))
                                           (n16-to-i16 reg/mem))))))))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*) reg/mem
                        rex-byte x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: MOVZX
;; ======================================================================

(def-inst x86-movzx

  ;; Op/En: RM
  ;; [OP REG, R/M]

  ;; #x0F B6: MOVZX r16/32/64, r/m8
  ;; (Move byte to word/doubleword/quadword with zero-extension)

  ;; #x0F B7: MOVSX r16/32/64, r/m16
  ;; (Move word to word/doubleword/quadword with zero-extension)

  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOVZX #x0FB6 '(:nil nil)
                                      'x86-movzx)
    (add-to-implemented-opcodes-table 'MOVZX #x0FB7 '(:nil nil)
                                      'x86-movzx))
  :body

  (b* ((ctx 'x86-movzx)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (reg/mem-size (if (equal opcode #xB6) 1 2))
       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ((the (integer 1 8) register-size)
        (select-operand-size nil rex-byte nil prefixes))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*) reg/mem
                        rex-byte x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: MOV to/from Control Registers
;; ======================================================================

(def-inst x86-mov-control-regs-Op/En-MR

  ;; Move control register to GPR

  ;; Op/En: MR
  ;; [OP R/M, REG]
  ;; 0F 20/r:         MOV r64, CR0-CR7
  ;; REX.R + 0F 20/0: MOV r64, CR8

  ;; From Intel Manuals, Vol 2A, "MOV Move to/from Control
  ;; Register":

  ;; At the opcode level, the reg field within the ModR/M byte
  ;; specifies which of the control registers is loaded or read. The 2
  ;; bits in the mod field are ignored. The r/m field specifies the
  ;; general-purpose register loaded or read. Attempts to reference
  ;; CR1, CR5, CR6, CR7, and CR9 CR15 result in undefined opcode (#UD)
  ;; exceptions.

  ;; In 64-bit mode, the instruction s default operation size
  ;; is 64 bits. The REX.R prefix must be used to access
  ;; CR8. Use of REX.B permits access to additional registers
  ;; (R8-R15). Use of the REX.W prefix or 66H prefix is
  ;; ignored. Use of the REX.R prefix to specify a register
  ;; other than CR8 causes an invalid-opcode exception. See the
  ;; summary chart at the beginning of this section for encoding
  ;; data and limits.


  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d () ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'MOV #x0F20 '(:nil nil)
                                    'x86-mov-control-regs-Op/En-MR)

  :body

  (b* ((ctx 'x86-mov-control-regs-Op/En-MR)

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; The r/m field specifies the GPR (destination).
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       ;; MOD field is ignored.
       ;; The reg field specifies the control register (source).
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!ms-fresh :lock-prefix prefixes))
       (cpl (cpl x86))
       ((when (not (equal 0 cpl)))
        (!!ms-fresh :cpl!=0 cpl))
       ;; *operand-size-override* and REX.W are ignored.

       ;; Get value from the control register
       ((mv flg ctr-index)
        (if (logbitp #.*r* rex-byte)
            (if (equal reg 0)
                (mv nil *cr8*)
              (mv t reg))
          (if (and (not (equal reg #.*cr1*))
                   (not (equal reg #.*cr5*))
                   (not (equal reg #.*cr6*))
                   (not (equal reg #.*cr7*)))
              (mv nil reg)
            (mv t reg))))
       ((when flg)
        ;; #UD Exception (if an attempt is made to access CR1, CR5,
        ;; CR6, or CR7 or if the REX.R prefix is used to specify a
        ;; register other than CR8)
        (!!ms-fresh :ctr-index-illegal (cons 'ModR/M.reg reg)))
       (ctr-val (the (unsigned-byte 64) (ctri ctr-index x86)))

       ;; Update the x86 state:
       (x86
        (!rgfi-size 8 (reg-index r/m rex-byte #.*b*) ctr-val rex-byte x86))
       ;; The OF, SF, ZF, AF, PF, and CF flags are undefined.
       (x86 (!flgi-undefined #.*cf* x86))
       (x86 (!flgi-undefined #.*pf* x86))
       (x86 (!flgi-undefined #.*af* x86))
       (x86 (!flgi-undefined #.*zf* x86))
       (x86 (!flgi-undefined #.*sf* x86))
       (x86 (!flgi-undefined #.*of* x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
