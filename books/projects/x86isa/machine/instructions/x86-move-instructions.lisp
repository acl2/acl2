;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../x86-decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: MOV
;; ======================================================================

(def-inst x86-mov-Op/En-MR

  ;; Op/En: MR
  ;; [OP R/M, REG]
  ;; 88: MOV r/m8,  r8
  ;; 89: MOV r/m16, r16
  ;; 89: MOV r/m32, r32
  ;; 89: MOV r/m64, r64

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

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
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (the (unsigned-byte 8) (prefixes-slice :group-2-prefix prefixes)))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (equal opcode #x88)
            1
          (if (and (equal opcode #x89)
                   (logbitp #.*w* rex-byte))
              8
            (if p3?
                ;; See Table 3-4, P. 3-26, Intel Vol. 1.
                2 ; 16-bit operand-size
              4))))

       (register (rgfi-size operand-size (reg-index reg rex-byte #.*r*)
                            rex-byte x86))

       ((mv flg0 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86)))
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

       ;; Update the x86 state:
       (inst-ac? t)
       ((mv flg2 x86)
        (x86-operand-to-reg/mem
         operand-size inst-ac? register v-addr rex-byte r/m mod x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
        (!!ms-fresh :x86-operand-to-reg/mem flg2))
       (x86 (!rip temp-rip x86)))
    x86))

(def-inst x86-mov-Op/En-RM

  ;; Op/En: RM
  ;; [OP REG, R/M]
  ;; 8A: MOV r8,  r/m8
  ;; 8A: MOV r16, r/m16
  ;; 8B: MOV r32, r/m32
  ;; 8B: MOV r64, r/m64

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

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
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
        (if (equal opcode #x8A)
            1
          (if (and (equal opcode #x8B)
                   (logbitp #.*w* rex-byte))
              8
            (if p3?
                ;; See Table 3-4, P. 3-26, Intel Vol. 1.
                2 ;; 16-bit operand-size
              4))))

       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))
       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by) ?v-addr x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*rgf-access* operand-size inst-ac? p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
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

       ;; Update the x86 state:
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*r*)
                        reg/mem rex-byte x86))
       (x86 (!rip temp-rip x86)))
    x86))

(def-inst x86-mov-Op/En-OI

  ;; Op/En: OI
  ;; [OP REG, IMM]
  ;; B0 + rb: MOV r8,  imm8
  ;; B8 + rw: MOV r16, imm16
  ;; B8 + rd: MOV r32, imm32
  ;; B8 + rd: MOV r64, imm64

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

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
          (if (and (<= #xB8 opcode) ;; B8 +rw
                   (<= opcode #xBE) ;; CUONG: Change to bf?
                   (logbitp #.*w* rex-byte))
              8
            (if p3?
                ;; See Table 3-4, P. 3-26, Intel Vol. 1.
                2 ; 16-bit operand-size
              4))))

       ((mv flg0 imm x86)
        (rm-size operand-size temp-rip :x x86))
       ((when flg0)
        (!!ms-fresh :imm-rm-size-error flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip operand-size))
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

       (reg (the (unsigned-byte 3) (logand 7 opcode)))
       ;; Update the x86 state:
       ;; See Intel Table 3.1, p.3-3, Vol. 2-A
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*b*)
                        imm rex-byte x86))
       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-mov-Op/En-MI

  ;; Op/En: MI
  ;; [OP R/M, IMM]
  ;; C6/0: MOV r/m8, imm8
  ;; C7/0: MOV r/m16, imm16
  ;; C7/0: MOV r/m32, imm32
  ;; C7/0: MOV r/m64, imm32

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

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
       ((the (integer 1 8) operand-size)
        (if (equal opcode #xC6)
            1
          (if p3?
              ;; See Table 3-4, P. 3-26, Intel Vol. 1.
              2 ;; 16-bit operand-size
            4)))
       ((the (integer 1 8) reg/mem-size)
        (if (and (equal opcode #xC7)
                 (logbitp #.*w* rex-byte))
            8
          operand-size))

       ((mv flg0 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr p4? temp-rip rex-byte r/m mod sib
                              operand-size x86)))
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
        (rm-size operand-size temp-rip :x x86))
       ((when flg2)
        (!!ms-fresh :imm-rm-size-error flg2))
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip operand-size))
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
         reg/mem-size inst-ac? imm v-addr rex-byte r/m mod x86))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg3)
        (!!ms-fresh :x86-operand-to-reg/mem flg3))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LEA
;; ======================================================================

(def-inst x86-lea

  ;; Op/En: RM
  ;; opcode = #x8D/r
  ;; LEA r16, m
  ;; LEA r32, m
  ;; LEA r64, m

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

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
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 2 8) register-size)
        (if (logbitp #.*w* rex-byte)
            8
          (if p3?
              2
            4)))

       ((mv ?flg0 (the (signed-byte 64) M) (the (unsigned-byte 3) increment-RIP-by) x86)
        (if (equal mod #b11)
            ;; See "M" in http://ref.x86asm.net/#Instruction-Operand-Codes
            (mv "Source operand is not a memory location" 0 0 x86)
          (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86)))
       ((when flg0)
        (!!ms-fresh :x86-effective-addr-error flg0))

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

       ((mv flg1 M)
        (case p2
          (0 (mv nil M))
          ;; I don't really need to check whether FS and GS base are
          ;; canonical or not.  On the real machine, if the MSRs
          ;; containing these bases are assigned non-canonical
          ;; addresses, an exception is raised.
          (#.*fs-override*
           (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
                  (fs-base (n64-to-i64 nat-fs-base)))
             (if (not (canonical-address-p fs-base))
                 (mv 'Non-Canonical-FS-Base fs-base)
               (mv nil (+ fs-base M)))))
          (#.*gs-override*
           (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
                  (gs-base (n64-to-i64 nat-gs-base)))
             (if (not (canonical-address-p gs-base))
                 (mv 'Non-Canonical-GS-Base gs-base)
               (mv nil (+ gs-base M)))))
          (t (mv 'Unidentified-P2 M))))
       ((when flg1)
        (!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg1))

       (M (trunc register-size M))
       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*)
                        M rex-byte x86))
       (x86 (!rip temp-rip x86)))
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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

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
         #.*rgf-access* reg/mem-size inst-ac? p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32
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
         #.*rgf-access* reg/mem-size inst-ac? p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

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
         #.*rgf-access* reg/mem-size inst-ac? p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
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
