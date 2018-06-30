; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

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

  :returns (x86 x86p
                :hyp (and (x86p x86)
                          (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOVS #xA4 '(:nil nil) 'x86-movs)
    (add-to-implemented-opcodes-table 'MOVS #xA5 '(:nil nil) 'x86-movs))

  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08
                                           rme-size-of-2-to-rme16
                                           rme-size-of-4-to-rme32
                                           rme-size-of-8-to-rme64
                                           select-address-size)))

  :body

  (b* ((ctx 'x86-movs)

       (group-1-prefix (the (unsigned-byte 8)
                            (prefixes-slice :group-1-prefix prefixes)))

       (lock? (equal #.*lock* group-1-prefix))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       ;; TODO: is the following already checked by GET-PREFIXES?
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       ((the (unsigned-byte 1) df) (flgi #.*df* x86))

       ((the (integer 2 8) counter/addr-size)
        (select-address-size p4? x86)) ; CX or ECX or RCX

       (select-byte-operand (equal #xA4 opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes x86))

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       (src-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size *rsi* rex-byte x86)
                   (rgfi *rsi* x86)))
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 32-bit address is always canonical.
                   (not (canonical-address-p src-addr))))
        (!!ms-fresh :src-addr-not-canonical src-addr))

       (inst-ac? (alignment-checking-enabled-p x86))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       ((mv flg0 src x86)
        (rme-size
         operand-size (the (signed-byte 64) src-addr) seg-reg :r inst-ac? x86))
       ((when flg0)
        (!!ms-fresh :src-rme-size-error flg0))

       (dst-addr (if counter/addr-size-2/4?
                     ;; (if (or (eql counter/addr-size 2)
                     ;;         (eql counter/addr-size 4))
                     (rgfi-size counter/addr-size *rdi* rex-byte x86)
                   (rgfi *rdi* x86)))
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))

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

          ;; TODO: should the following add/subtract 8 instead of 2?
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
        (wme-size operand-size original-dst-addr *es* src inst-ac? x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg1)
        (!!ms-fresh :wme-size-error flg1))

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
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             *rsi*
                             (n16 (the (signed-byte
                                        #.*max-linear-address-size+1*) src-addr))
                             rex-byte x86))
              (4 (!rgfi-size 4
                             *rsi*
                             (n32 (the (signed-byte
                                        #.*max-linear-address-size+1*) src-addr))
                             rex-byte x86))
              (t (!rgfi *rsi* (the (signed-byte
                                    #.*max-linear-address-size+1*)
                                   src-addr) x86))))
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             *rdi*
                             (n16 (the
                                   (signed-byte
                                    #.*max-linear-address-size+1*) dst-addr))
                             rex-byte x86))
              (4 (!rgfi-size 4
                             *rdi*
                             (n32 (the
                                   (signed-byte
                                    #.*max-linear-address-size+1*) dst-addr))
                             rex-byte x86))
              (t (!rgfi *rdi* (the (signed-byte
                                    #.*max-linear-address-size+1*)
                                   dst-addr) x86)))))

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

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ((the (unsigned-byte 1) df) (flgi #.*df* x86))
       ((the (integer 4 8) counter/addr-size)
        (if p4?
            4 ;; ECX is chosen
          8   ;; RCX is chosen
          ))

       (select-byte-operand (equal #xA6 opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes x86))

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

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

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
        (select-operand-size select-byte-operand rex-byte nil prefixes x86))

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
