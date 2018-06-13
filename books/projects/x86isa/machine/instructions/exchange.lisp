;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "arith-and-logic-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: XCHG
;; ======================================================================

(local
 (defthm-sb i49p-mv-nth-3-x86-operand-from-modr/m-and-sib-bytes
   ;; Useful in guard proofs
   :hyp (forced-and (x86p x86))
   :bound 49
   :concl (mv-nth 3 (x86-operand-from-modr/m-and-sib-bytes
                     reg-type operand-size inst-ac? memory-ptr?
                     p2 p4 temp-rip rex-byte r/m mod sib num-imm-bytes x86))
   :hints (("Goal"
            :use
            ((:instance i48p-x86-operand-from-modr/m-and-sib-bytes))
            :in-theory
            (e/d* () (signed-byte-p
                      i48p-x86-operand-from-modr/m-and-sib-bytes))))
   :gen-linear t))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-xchg

  ;; Note that for XCHG, the Op/En RM and MR are essentially the same.
  ;; In our model, we arbitrarily choose the MR encoding to represent
  ;; both of them.

  ;; Op/En: RM
  ;; 86: XCHG r8, r/m8
  ;; 87: XCHG r16/r32/r64, r/m16/r/m32/r/m64

  ;; Op/En: MR
  ;; 86: XCHG r/m8, r8
  ;; 87: XCHG r/m16/r/m32/r/m64, r16/r32/r64

  ;; Op/En: O
  ;; 90 +rw: XCHG ax, r16
  ;; 90 +rd: XCHG eax/rax, r32/r64

  ;; Note that opcode #x90 with REX.B = 0 is XCHG rAX, rAX, i.e., NOP.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d* () (not))))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'XCHG #x86 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x87 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x90 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x91 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x92 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x93 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x94 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x95 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x96 '(:nil nil)
                                      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x97 '(:nil nil)
                                      'x86-xchg))
  :body

  (b* ((ctx 'x86-xchg)

       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       (reg (mrm-reg modr/m))

       (lock (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ;; only memory operands allow a LOCK prefix:
       ((when (and lock
                   (or (eql (ash opcode -4) 9) ;; #x90+rw/rd ; 90H through 97H
                       (eql mod 3)))) ;; register operand
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #x86))
       (reg/mem-size
        (select-operand-size select-byte-operand rex-byte nil prefixes x86))

       (seg-reg (select-segment-register p2 p4? mod  r/m x86))

       (inst-ac? t)
       ;; Fetch the first operand and put it in val1.
       ;; If the opcode is #x90+rw/rd, we let rax be the first operand.
       ;; For other opcodes, we let the operand specified by the r/m field to
       ;; be the first operand.
       ((mv flg0
            val1
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) addr)
            x86)
        (if (equal (ash opcode -4) 9) ;; #x90+rw/rd
            (mv nil (rgfi-size reg/mem-size *rax* rex-byte x86) 0 0 x86)
          (x86-operand-from-modr/m-and-sib-bytes$ #.*gpr-access*
                                                  reg/mem-size
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
                                                  x86)))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Fetch the second operand and put it in val2.
       ;; If the opcode is #x90+rw/rd, we let the contents of the register
       ;; chosen by rw/rd be the second operand.
       ;; For other opcodes, we let the operand specified by the reg field to
       ;; be the second operand.
       (rw/rd (the (unsigned-byte 3) (logand #x7 opcode)))
       (val2
        (if (equal (ash opcode -4) 9) ;; #x90+rw/rd
            ;; See Intel Table 3.1, p.3-3, Vol. 2-A
            (rgfi-size reg/mem-size (reg-index rw/rd rex-byte #.*b*)
                       rex-byte x86)
          (rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*)
                     rex-byte x86)))

       ;; Update the x86 state:

       ;; Put val2 in the place of val1.
       ((mv flg2 x86)
        (if (equal (ash opcode -4) 9)
            (let ((x86 (!rgfi-size reg/mem-size *rax* val2 rex-byte x86)))
              (mv nil x86))
          (x86-operand-to-reg/mem$ reg/mem-size
                                   inst-ac?
                                   nil ;; Not a memory pointer operand
                                   val2
                                   seg-reg
                                   (the (signed-byte 64) addr)
                                   rex-byte
                                   r/m
                                   mod
                                   x86)))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
        (!!ms-fresh :x86-operand-to-reg/mem-error flg2))

       ;; Put val1 in the place of val2.
       (x86
        (if (equal (the (unsigned-byte 4) (ash opcode -4)) 9) ;; #x90+rw/rd
            ;; See Intel Table 3.1, p.3-3, Vol. 2-A
            (!rgfi-size reg/mem-size (reg-index rw/rd rex-byte #.*b*) val1
                        rex-byte x86)
          (!rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*) val1 rex-byte
                      x86)))

       (x86 (write-*ip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: CMPXCHG
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-cmpxchg

  ;; Op/En: MR
  ;; 0F B0: CMPXCHG r/m8, r8
  ;; 0F B1: CMPXCHG r/m16/32/64, r16/32/64

  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CMPXCHG #x0FB0 '(:nil nil)
                                      'x86-cmpxchg)
    (add-to-implemented-opcodes-table 'CMPXCHG #x0FB1 '(:nil nil)
                                      'x86-cmpxchg))
  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-cmpxchg)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       (reg (mrm-reg modr/m))

       ;; If the lock prefix is used but the destination is not a memory
       ;; operand, then the #UD exception is raised.
       ((when (and lock? (equal mod #b11)))
        (!!fault-fresh
         :ud nil ;; #UD
         :lock-prefix-but-destination-not-a-memory-operand prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xB0))
       ((the (integer 1 8) reg/mem-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes x86))

       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       (inst-ac? t)
       ;; Fetch the first (destination) operand:
       ((mv flg0
            reg/mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes$ #.*gpr-access*
                                                reg/mem-size
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Computing the flags and the result:
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv result
            (the (unsigned-byte 32) output-rflags)
            (the (unsigned-byte 32) undefined-flags))
        (gpr-arith/logic-spec reg/mem-size #.*OP-CMP* reg/mem rAX input-rflags))

       ;; Update the x86 state:
       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ((mv flg1 x86)
        (if (equal result 0) ;; rAX == reg/mem or ZF == 1
            ;; Fetch the second operand and put it in the destination operand.
            (let ((register (rgfi-size reg/mem-size
                                       (reg-index reg rex-byte #.*r*) rex-byte
                                       x86)))
              (x86-operand-to-reg/mem$ reg/mem-size
                                       inst-ac?
                                       nil ;; Not a memory pointer operand
                                       register
                                       seg-reg
                                       (the (signed-byte 64) addr)
                                       rex-byte
                                       r/m
                                       mod
                                       x86))
          ;; rAX != reg/mem or ZF == 0
          ;; Put the destination operand into the accumulator.
          (let ((x86 (!rgfi-size reg/mem-size *rax* reg/mem rex-byte x86)))
            (mv nil x86))))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg1)
        (!!ms-fresh :x86-operand-to-reg/mem-error flg1))

       (x86 (write-*ip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: NOP
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-two-byte-nop

  ;; Op/En: NP
  ;; 0F 1F/0

  ;; The Intel manual (Vol. 2B, NOP specification) has a note on the recommended
  ;; multi-byte NOP sequences, and the address-size override prefix is
  ;; absent from all of them.  However, since the operand for the
  ;; multi-byte NOP is an r/m operand, we account for the effect of that
  ;; prefix anyway.

  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'NOP #x0F1F '(:reg 0) 'x86-two-byte-nop)

  :body

  (b* ((ctx 'x86-two-byte-nop)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0
            (the (signed-byte 64) ?addr)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr p4?
                              temp-rip
                              rex-byte
                              r/m
                              mod
                              sib
                              0 ;; No immediate operand
                              x86)))
       ((when flg0)
        (!!ms-fresh :x86-effective-addr flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :next-rip-invalid temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (x86 (write-*ip temp-rip x86)))
    x86))

;; (def-inst x86-nop

;;   ;; Note: With operand-size override prefix (#x66), the single byte
;;   ;; NOP instruction is equivalent to XCHG ax, ax.

;;   ;; Op/En: NP
;;   ;; 90

;;   :parents (one-byte-opcodes)
;;   :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

;;   :returns (x86 x86p :hyp (and (x86p x86)
;;                                (canonical-address-p temp-rip)))
;;   :implemented
;;   (add-to-implemented-opcodes-table 'NOP #x90 '(:nil nil) 'x86-nop)

;;   :body


;;   (b* ((ctx 'x86-nop)
;;        (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
;;        ((when lock?)
;;         (!!ms-fresh :lock-prefix prefixes)))

;;     ;; We don't need to check for valid length for one-byte
;;     ;; instructions.  The length will be more than 15 only if
;;     ;; get-prefixes fetches 15 prefixes, and that error will be
;;     ;; caught in x86-fetch-decode-execute, that is, before control
;;     ;; reaches this function.

;;     ;; Update the x86 state:
;;     (!rip temp-rip x86)))

;; ======================================================================
