;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :Dir :system))

;; ======================================================================
;; INSTRUCTION: BT
;; ======================================================================

(def-inst x86-bt-0F-BA

  ;; 0F BA/4: BT r/m16/32/64, imm8

  ;; If the bitBase is a register, the BitOffset can be in the range 0
  ;; to [15, 31, 63] depending on the mode and register size.  If the
  ;; bitBase is a memory address and bitOffset is an immediate operand,
  ;; then also the bitOffset can be in the range 0 to [15, 31, 63].

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'BT #x0FBA '(:reg 4) 'x86-bt-0F-BA)

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-bt-0f-ba)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       ((the (integer 1 8) operand-size)
        (select-operand-size nil rex-byte nil prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (inst-ac? t)
       ((mv flg0 bitBase (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* operand-size inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         1 ;; One-byte immediate data
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
        (!!ms-fresh :temp-rip-not-canonical temp-rip))
       ((mv flg1 (the (unsigned-byte 8) bitOffset) x86)
        (rml-size 1 temp-rip :x x86))
       ((when flg1)
        (!!ms-fresh :rml-size-error flg1))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ 1 temp-rip))
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

       ((the (integer 0 64) bitOffset)
        (mod bitOffset (the (integer 0 64) (ash operand-size 3))))

       ;; Update the x86 state:
       ;; CF affected. ZF unchanged. PF, AF, SF, and OF undefined.
       (x86
        (let* ((x86 (!flgi #.*cf* (the (unsigned-byte 1) (acl2::logbit bitOffset bitBase)) x86))
               (x86 (!flgi-undefined #.*pf* x86))
               (x86 (!flgi-undefined #.*af* x86))
               (x86 (!flgi-undefined #.*sf* x86))
               (x86 (!flgi-undefined #.*of* x86)))
          x86))

       (x86 (!rip temp-rip x86)))
    x86))

(def-inst x86-bt-0F-A3
  ;; TO-DO: Speed this up!

  ;; 0F A3: BT r/m16/32/64, r16/32/64

  ;; If the bitBase is a register operand, the bitOffset can be in the
  ;; range 0 to [15, 31, 63] depending on the mode and register size.
  ;; If the bitBase is a memory address and bitOffset is a register
  ;; operand, the bitOffset can be:

  ;; Operand Size   Register bitOffset
  ;;      2          -2^15 to 2^15-1
  ;;      4          -2^31 to 2^31-1
  ;;      8          -2^63 to 2^63-1

  :parents (two-byte-opcodes)
  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :prepwork
  ((local
    (in-theory (e/d ()
                    (acl2::mod-minus
                     unsigned-byte-p)))))

  :implemented
  (add-to-implemented-opcodes-table 'BT #x0FA3 '(:nil nil) 'x86-bt-0F-A3)

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-bt-0f-a3)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))

       ((the (integer 1 8) operand-size)
        (select-operand-size nil rex-byte nil prefixes))
       (bitOffset (rgfi-size operand-size (reg-index reg rex-byte #.*r*)
                             rex-byte x86))
       ((mv flg0 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (let ((p4? (equal #.*addr-size-override*
                            (prefixes-slice :group-4-prefix prefixes))))
            (x86-effective-addr p4? temp-rip rex-byte r/m mod sib
                                0 ;; No immediate operand
                                x86))))
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
        (!!ms-fresh :Non-Canonical-V-Addr v-addr))

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

       ((mv flg2 bitOffset bitBase x86)
        (if (equal mod #b11)
            ;; bitBase is a register operand.
            (mv nil (mod bitOffset (ash operand-size 3))
                (rgfi-size operand-size (reg-index r/m rex-byte #.*b*) rex-byte
                           x86)
                x86)
          ;; bitBase is a memory operand.
          (b* ((bitOffset-int (case operand-size
                                (1 (n08-to-i08 bitOffset))
                                (2 (n16-to-i16 bitOffset))
                                (4 (n32-to-i32 bitOffset))
                                (t (n64-to-i64 bitOffset))))
               (bitOffset-int-abs (abs bitOffset-int))
               (bitNumber (mod bitOffset-int-abs 8))
               (byte-v-addr (+ (the (signed-byte
                                     #.*max-linear-address-size*) v-addr)
                               (floor bitOffset-int 8)))
               ;; Alignment Check
               (inst-ac? (alignment-checking-enabled-p x86))
               ((when
                    (and inst-ac?
                         (not (equal
                               (logand byte-v-addr
                                       (the (integer 0 15) (- operand-size 1)))
                               0))))
                (mv (cons 'memory-access-not-aligned byte-v-addr) 0 0 x86))
               ((mv flg1 byte x86)
                (if (canonical-address-p byte-v-addr)
                    (rml-size 1 byte-v-addr :r x86)
                  (mv (cons 'virtual-address-error byte-v-addr) 0 x86))))
            (mv flg1 bitNumber byte x86))))
       ((when flg2)
        (!!ms-fresh :rml-size-error flg2))

       ;; Update the x86 state:
       ;; CF affected. ZF unchanged. PF, AF, SF, and OF undefined.
       (x86
        (let* ((x86 (!flgi #.*cf*
                           (the (unsigned-byte 1) (acl2::logbit bitOffset bitBase))
                           x86))
               (x86 (!flgi-undefined #.*pf* x86))
               (x86 (!flgi-undefined #.*af* x86))
               (x86 (!flgi-undefined #.*sf* x86))
               (x86 (!flgi-undefined #.*of* x86)))
          x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
