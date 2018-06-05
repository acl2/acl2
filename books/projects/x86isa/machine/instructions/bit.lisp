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

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-bt-0F-BA

  ;; 0F BA/4: BT r/m16/32/64, imm8

  ;; If the bitBase is a register, the BitOffset can be in the range 0
  ;; to [15, 31, 63] depending on the mode and register size.  If the
  ;; bitBase is a memory address and bitOffset is an immediate operand,
  ;; then also the bitOffset can be in the range 0 to [15, 31, 63].

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08)))

  :implemented
  (add-to-implemented-opcodes-table 'BT #x0FBA '(:reg 4) 'x86-bt-0F-BA)

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-bt-0f-ba)

       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       ((the (integer 1 8) operand-size)
        (select-operand-size nil rex-byte nil prefixes x86))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       (inst-ac? t)
       ((mv flg0
            bitBase
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
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
                                                1 ;; One-byte immediate data
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       ((mv flg1 (the (unsigned-byte 8) bitOffset) x86)
        (rme-size 1 temp-rip *cs* :x nil x86))
       ((when flg1) (!!ms-fresh :rme-size-error flg1))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((the (integer 0 64) bitOffset)
        (mod bitOffset (the (integer 0 64) (ash operand-size 3))))

       ;; Update the x86 state:
       ;; CF affected. ZF unchanged. PF, AF, SF, and OF undefined.
       (x86
        (let* ((x86 (!flgi #.*cf*
                           (the (unsigned-byte 1)
                                (acl2::logbit bitOffset bitBase))
                           x86))
               (x86 (!flgi-undefined #.*pf* x86))
               (x86 (!flgi-undefined #.*af* x86))
               (x86 (!flgi-undefined #.*sf* x86))
               (x86 (!flgi-undefined #.*of* x86)))
          x86))

       (x86 (write-*ip temp-rip x86)))
    x86))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
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
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       ((the (integer 1 8) operand-size)
        (select-operand-size nil rex-byte nil prefixes x86))

       (bitOffset (rgfi-size operand-size
                             (reg-index reg rex-byte #.*r*)
                             rex-byte
                             x86))

       ((mv flg0
            (the (signed-byte 64) addr)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (let ((p4? (equal #.*addr-size-override*
                            (prefixes-slice :group-4-prefix prefixes))))
            (x86-effective-addr p4?
                                temp-rip
                                rex-byte
                                r/m
                                mod
                                sib
                                0 ;; No immediate operand
                                x86))))
       ((when flg0) (!!ms-fresh :x86-effective-addr-error flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg2 bitOffset bitBase x86)
        (if (equal mod #b11)
            ;; bitBase is a register operand.
            (mv nil
                (mod bitOffset (ash operand-size 3))
                (rgfi-size operand-size
                           (reg-index r/m rex-byte #.*b*)
                           rex-byte
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
               (byte-addr (+ addr
                             (floor bitOffset-int 8)))
               (inst-ac? t)
               ((mv flg byte x86)
                (if (signed-byte-p 64 byte-addr)
                    (rme-size 1 byte-addr seg-reg :r inst-ac? x86)
                  (mv (cons 'effective-address-error byte-addr) 0 x86))))
            (mv flg bitNumber byte x86))))
       ((when flg2)
        (!!ms-fresh :rme-size-error flg2))

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
       (x86 (write-*ip temp-rip x86)))
    x86))

;; ======================================================================
