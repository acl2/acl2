;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "arith-and-logic"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: MOVS/MOVSB/MOVSW/MOVSD/MOVSQ
;; ======================================================================

(def-inst x86-movs

  ;; A4 MOVSB: Move  byte from address (R/E)SI to (R/E)DI
  ;; A5 MOVSW: Move  word from address (R/E)SI to (R/E)DI
  ;; A5 MOVSD: Move dword from address (R/E)SI to (R/E)DI
  ;; A5 MOVSQ: Move qword from address (R/E)SI to (R/E)DI

  ;; After the move operation, the (E)SI and (E)DI registers are
  ;; incremented or decremented automatically according to the setting
  ;; of the DF flag in the EFLAGS register.  If the DF flag is 0, the
  ;; registers are incremented; if the DF flag is 1, the registers are
  ;; decremented.

  ;; The following repeat prefixes can be used in conjunction with a
  ;; count in the ECX register to cause a string instruction to
  ;; repeat:
  ;; REP (F3): Repeats a string operation until the rCX register
  ;; equals 0.
  ;; REPE/REPZ (F3): Repeats a string operation until the rCX register
  ;; equals 0 or the ZF is cleared.
  ;; REPNE/REPNZ (F2): Repeats a string operation until the rCX
  ;; register equals 0 or the ZF is set to 1.

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOVS #xA4 '(:nil nil) 'x86-movs)
    (add-to-implemented-opcodes-table 'MOVS #xA5 '(:nil nil) 'x86-movs))

  :body

  (b* ((ctx 'x86-movs)
       (group-1-prefix (the (unsigned-byte 8) (prefixes-slice :group-1-prefix prefixes)))
       (lock? (equal #.*lock* group-1-prefix))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ((the (unsigned-byte 1) df) (flgi #.*df* x86))

       ((the (integer 4 8) counter/addr-size)
        (if p4?
            4 ;; ECX is chosen
          8   ;; RCX is chosen
          ))

       (select-byte-operand (equal #xA4 opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes))

       (src-addr (if p4?
                     (rgfi-size counter/addr-size *rsi* rex-byte x86)
                   (rgfi *rsi* x86)))

       ((when (and (not p4?)
                   ;; A 32-bit address is always canonical.
                   (not (canonical-address-p src-addr))))
        (!!ms-fresh :src-addr-not-canonical src-addr))
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when
            ;; Check alignment for memory accesses.
            (and inst-ac?
                 (not (equal (logand
                              (the (signed-byte #.*max-linear-address-size*) src-addr)
                              (the (integer 0 15)
                                (- operand-size 1)))
                             0))))
        (!!ms-fresh :src-addr-not-aligned src-addr))

       ((mv flg0 src x86)
        (rml-size operand-size
                 (the (signed-byte #.*max-linear-address-size*) src-addr)
                 :r x86))
       ((when flg0)
        (!!ms-fresh :src-rml-size-error flg0))

       (dst-addr (if p4?
                     (rgfi-size counter/addr-size *rdi* rex-byte x86)
                   (rgfi *rdi* x86)))

       ((when (and (not p4?)
                   ;; A 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))
       ((when
            ;; Check alignment for memory accesses.
            (and inst-ac?
                 (not (equal (logand
                              (the (signed-byte #.*max-linear-address-size*) dst-addr)
                              (the (integer 0 15)
                                (- operand-size 1)))
                             0))))
        (!!ms-fresh :dst-addr-not-aligned dst-addr))
       (original-dst-addr dst-addr)

       ;; A repeating string operation can be suspended by an exception or
       ;; interrupt. When this happens, the state of the register is preserved
       ;; to allow the string operation to be resumed upon a return from the
       ;; exception or interrupt handler.

       ((mv (the (signed-byte #.*max-linear-address-size+1*) src-addr)
            (the (signed-byte #.*max-linear-address-size+1*) dst-addr))

        (case operand-size
          (1 (if (equal df 0)
                 (mv (+ 1 (the (signed-byte #.*max-linear-address-size*)
                            src-addr))
                     (+ 1
                        (the (signed-byte #.*max-linear-address-size*)
                          dst-addr)))
               (mv (+ -1
                      (the (signed-byte #.*max-linear-address-size*)
                        src-addr))
                   (+ -1
                      (the (signed-byte #.*max-linear-address-size*)
                        dst-addr)))))

          (2 (if (equal df 0)
                 (mv (+ 2 (the (signed-byte #.*max-linear-address-size*)
                            src-addr))
                     (+ 2 (the (signed-byte #.*max-linear-address-size*)
                            dst-addr)))
               (mv (+ -2 (the (signed-byte #.*max-linear-address-size*)
                           src-addr))
                   (+ -2 (the (signed-byte #.*max-linear-address-size*)
                           dst-addr)))))

          (4 (if (equal df 0)
                 (mv (+ 4 (the (signed-byte #.*max-linear-address-size*)
                            src-addr))
                     (+ 4 (the (signed-byte #.*max-linear-address-size*)
                            dst-addr)))
               (mv (+ -4 (the (signed-byte #.*max-linear-address-size*)
                           src-addr))
                   (+ -4 (the (signed-byte #.*max-linear-address-size*)
                           dst-addr)))))
          (otherwise (if (equal df 0)
                         (mv (+ 2 (the (signed-byte #.*max-linear-address-size*)
                                    src-addr))
                             (+ 2 (the (signed-byte #.*max-linear-address-size*)
                                    dst-addr)))
                       (mv (+ -2 (the (signed-byte #.*max-linear-address-size*)
                                   src-addr))
                           (+ -2 (the (signed-byte #.*max-linear-address-size*)
                                   dst-addr)))))))

       ;; Update the x86 state:
       ((mv flg1 x86)
        (wml-size operand-size original-dst-addr src x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg1)
        (!!ms-fresh :wml-size-error flg1))

       ;; REP prefix: Updating rCX and RIP:

       (x86 (case group-1-prefix
              (#.*repe*
               (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 0))
                     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
                            (x86 (!rip temp-rip x86)))
                       x86)
                   (let* ((x86 (!rip temp-rip x86)))
                     x86))))
              (#.*repne*
               (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 1))
                     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
                            (x86 (!rip temp-rip x86)))
                       x86)
                   (let* ((x86 (!rip temp-rip x86)))
                     x86))))
              (otherwise ;; no rep prefix present
               (!rip temp-rip x86))))

       ;; Updating rSI and rDI:
       (x86 (if p4?
                (!rgfi-size counter/addr-size *rsi*
                            (n32 (the (signed-byte
                                       #.*max-linear-address-size+1*) src-addr))
                            rex-byte x86)
              (!rgfi *rsi* (the (signed-byte
                                 #.*max-linear-address-size+1*)
                             src-addr) x86)))
       (x86 (if p4?
                (!rgfi-size counter/addr-size *rdi*
                            (n32 (the
                                     (signed-byte
                                      #.*max-linear-address-size+1*)
                                   dst-addr))
                            rex-byte x86)
              (!rgfi *rdi* (the (signed-byte
                                 #.*max-linear-address-size+1*)
                             dst-addr) x86))))
    x86))

;; ======================================================================
;; INSTRUCTION: CMPS/CMPSB/CMPSW/CMPSD/CMPSQ
;; ======================================================================

(def-inst x86-cmps

  ;; A6 CMPSB: Compare  byte from address (R/E)SI to (R/E)DI
  ;; A7 CMPSW: Compare  word from address (R/E)SI to (R/E)DI
  ;; A7 CMPSD: Compare dword from address (R/E)SI to (R/E)DI
  ;; A7 CMPSQ: Compare qword from address (R/E)SI to (R/E)DI

  ;; After the compare operation, the (E)SI and (E)DI registers are
  ;; incremented or decremented automatically according to the setting
  ;; of the DF flag in the EFLAGS register.  If the DF flag is 0, the
  ;; registers are incremented; if the DF flag is 1, the registers are
  ;; decremented.

  ;; The following repeat prefixes can be used in conjunction with a
  ;; count in the ECX register to cause a string instruction to
  ;; repeat:
  ;; REP (F3): Repeats a string operation until the rCX register
  ;; equals 0.
  ;; REPE/REPZ (F3): Repeats a string operation until the rCX register
  ;; equals 0 or the ZF is cleared.
  ;; REPNE/REPNZ (F2): Repeats a string operation until the rCX
  ;; register equals 0 or the ZF is set to 1.

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CMPS #xA6 '(:nil nil) 'x86-cmps)
    (add-to-implemented-opcodes-table 'CMPS #xA7 '(:nil nil) 'x86-cmps))

  :body

  (b* ((ctx 'x86-cmps)
       (group-1-prefix (the (unsigned-byte 8) (prefixes-slice :group-1-prefix prefixes)))
       (lock? (equal #.*lock* group-1-prefix))
       ((when lock?) (!!ms-fresh :lock-prefix prefixes))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ((the (unsigned-byte 1) df) (flgi #.*df* x86))
       ((the (integer 4 8) counter/addr-size)
        (if p4?
            4 ;; ECX is chosen
          8   ;; RCX is chosen
          ))

       (select-byte-operand (equal #xA6 opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes))

       (src-addr (if p4?
                     (rgfi-size counter/addr-size *rsi* rex-byte x86)
                   (rgfi *rsi* x86)))
       ((when (and (not p4?)
                   ;; A 32-bit address is always canonical.
                   (not (canonical-address-p src-addr))))
        (!!ms-fresh :src-addr-not-canonical src-addr))
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when
            ;; Check alignment for memory accesses.
            (and inst-ac?
                 (not (equal (logand
                              (the (signed-byte #.*max-linear-address-size*) src-addr)
                              (the (integer 0 15)
                                (- operand-size 1)))
                             0))))
        (!!ms-fresh :src-addr-not-aligned src-addr))
       ((mv flg0 src x86)
        (rml-size operand-size src-addr :r x86))
       ((when flg0)
        (!!ms-fresh :src-rml-size-error flg0))

       (dst-addr (if p4?
                     (rgfi-size counter/addr-size *rdi* rex-byte x86)
                   (rgfi *rdi* x86)))
       ((when (and (not p4?)
                   ;; A 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))
       ((when
            ;; Check alignment for memory accesses.
            (and inst-ac?
                 (not (equal (logand
                              (the (signed-byte #.*max-linear-address-size*) dst-addr)
                              (the (integer 0 15)
                                (- operand-size 1)))
                             0))))
        (!!ms-fresh :dst-addr-not-aligned dst-addr))
       ((mv flg0 dst x86)
        (rml-size operand-size dst-addr :r x86))
       ((when flg0)
        (!!ms-fresh :dst-rml-size-error flg0))

       ;; From the AMD Manual: "To perform the comparison, the instruction
       ;; subtracts the second operand from the first operand and sets the
       ;; status flags in the same manner as the SUB instruction, but does not
       ;; alter the first operand. The two operands must be of the same size."

       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv ?result
            (the (unsigned-byte 32) output-rflags)
            (the (unsigned-byte 32) undefined-flags))
        (gpr-arith/logic-spec operand-size #.*OP-SUB* dst src input-rflags))

       ;; Update the x86 state:

       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ;; A repeating string operation can be suspended by an exception or
       ;; interrupt. When this happens, the state of the register is preserved
       ;; to allow the string operation to be resumed upon a return from the
       ;; exception or interrupt handler.

       ((mv (the (signed-byte #.*max-linear-address-size+1*) src-addr)
            (the (signed-byte #.*max-linear-address-size+1*) dst-addr))
        (case operand-size
          (1 (if (equal df 0)
                 (mv (+ (the (signed-byte
                              #.*max-linear-address-size+1*) src-addr) 1)
                     (+ (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 1))
               (mv (- (the (signed-byte #.*max-linear-address-size+1*)
                        src-addr) 1)
                   (- (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 1))))
          (2 (if (equal df 0)
                 (mv (+ (the (signed-byte
                              #.*max-linear-address-size+1*) src-addr) 2)
                     (+ (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 2))
               (mv (- (the (signed-byte #.*max-linear-address-size+1*)
                        src-addr) 2)
                   (- (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 2))))
          (4 (if (equal df 0)
                 (mv (+ (the (signed-byte
                              #.*max-linear-address-size+1*) src-addr) 4)
                     (+ (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 4))
               (mv (- (the (signed-byte #.*max-linear-address-size+1*)
                        src-addr) 4)
                   (- (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 4))))
          (otherwise (if (equal df 0)
                         (mv (+ (the (signed-byte
                                      #.*max-linear-address-size+1*) src-addr) 2)
                             (+ (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 2))
                       (mv (- (the (signed-byte
                                    #.*max-linear-address-size+1*) src-addr) 2)
                           (- (the (signed-byte
                                    #.*max-linear-address-size+1*) dst-addr) 2))))))

       ;; REP prefix: Updating rCX and RIP:

       (x86 (case group-1-prefix
              (#.*repe*
               (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 0))
                     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
                            (x86 (!rip temp-rip x86)))
                       x86)
                   (let* ((x86 (!rip temp-rip x86)))
                     x86))))
              (#.*repne*
               (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 1))
                     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
                            (x86 (!rip temp-rip x86)))
                       x86)
                   (let* ((x86 (!rip temp-rip x86)))
                     x86))))
              (otherwise ;; no rep prefix present
               (!rip temp-rip x86))))

       ;; Updating rSI and rDI:

       (x86 (if p4?
                (!rgfi-size counter/addr-size *rsi*
                            (n32 (the (signed-byte
                                       #.*max-linear-address-size+1*) src-addr))
                            rex-byte x86)
              (!rgfi *rsi* (the (signed-byte
                                 #.*max-linear-address-size+1*)
                             src-addr) x86)))
       (x86 (if p4?
                (!rgfi-size counter/addr-size *rdi*
                            (n32 (the
                                     (signed-byte
                                      #.*max-linear-address-size+1*)
                                   dst-addr))
                            rex-byte x86)
              (!rgfi *rdi* (the (signed-byte
                                 #.*max-linear-address-size+1*)
                             dst-addr) x86))))
    x86))

;; ======================================================================
;; INSTRUCTION: STOS/STOSB/STOSW/STOSD/STOSQ
;; ======================================================================

(def-inst x86-stos

  ;; AA STOSB:             Store AL at address EDI or RDI
  ;; AB STOSW/STOSD/STOSQ: Store AX/EAX/RDX at address EDI or RDI

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'STOS #xAA '(:nil nil) 'x86-stos)
    (add-to-implemented-opcodes-table 'STOS #xAB '(:nil nil) 'x86-stos))

  :body

  (b* ((ctx 'x86-stos)
       (group-1-prefix (the (unsigned-byte 8) (prefixes-slice :group-1-prefix prefixes)))
       (lock? (equal #.*lock* group-1-prefix))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (unsigned-byte 1) df) (flgi #.*df* x86))
       ((the (integer 4 8) counter/addr-size)
        (if p4?
            4 ;; EDI and ECX are chosen.
          8   ;; RDI and RDX are chosen.
          ))

       (dst-addr
        (if p4?
            (rgfi-size counter/addr-size *rdi* rex-byte x86)
          (rgfi *rdi* x86)))
       ((when (and (not p4?)
                   ;; A 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))

       (select-byte-operand (equal #xAA opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes))

       (rAX (rgfi-size operand-size *rax* rex-byte x86))

       ;; Update the x86 state:

       ;; Writing rAX to the memory:
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when
            ;; Check alignment for memory accesses.
            (and inst-ac?
                 (not (equal (logand
                              (the (signed-byte #.*max-linear-address-size*) dst-addr)
                              (the (integer 0 15)
                                (- operand-size 1)))
                             0))))
        (!!ms-fresh :dst-addr-not-aligned dst-addr))
       ((mv flg0 x86)
        (wml-size operand-size dst-addr rAX x86))
       ((when flg0)
        (!!ms-fresh :wml-size-error flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) dst-addr)
        (case operand-size
          (1 (if (equal df 0)
                 (+ 1 (the (signed-byte
                            #.*max-linear-address-size*) dst-addr))
               (+ -1 (the (signed-byte
                           #.*max-linear-address-size*) dst-addr))))
          (2 (if (equal df 0)
                 (+ 2 (the (signed-byte
                            #.*max-linear-address-size*) dst-addr))
               (+ -2 (the (signed-byte
                           #.*max-linear-address-size*) dst-addr))))
          (4 (if (equal df 0)
                 (+ 4 (the (signed-byte
                            #.*max-linear-address-size*) dst-addr))
               (+ -4 (the (signed-byte
                           #.*max-linear-address-size*) dst-addr))))
          (otherwise (if (equal df 0)
                         (+ 8 (the (signed-byte
                                    #.*max-linear-address-size*) dst-addr))
                       (+ -8 (the (signed-byte
                                   #.*max-linear-address-size*) dst-addr))))))

       ;; REPE/REPNE prefixes: updating the counter rCX and the RIP:

       (x86 (case group-1-prefix
              (#.*repe*
               (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 0))
                     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
                            (x86 (!rip temp-rip x86)))
                       x86)
                   (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86)))
                     x86))))
              (#.*repne*
               (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 1))
                     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
                            (x86 (!rip temp-rip x86)))
                       x86)
                   (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86)))
                     x86))))
              (otherwise ;; no rep prefix present
               (!rip temp-rip x86))))

       ;; Updating the rDI:
       (x86 (if p4?
                (!rgfi-size counter/addr-size *rdi*
                            (n32 (the
                                     (signed-byte
                                      #.*max-linear-address-size+1*)
                                   dst-addr))
                            rex-byte x86)
              (!rgfi *rdi* (the (signed-byte
                                 #.*max-linear-address-size+1*)
                             dst-addr) x86))))

    x86))

;; ======================================================================
