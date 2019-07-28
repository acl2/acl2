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

(include-book "arith-and-logic-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ----------------------------------------------------------------------

;; Some helpful guard lemmas:
(local
 (encapsulate
   ()

   (defthm signed-byte-p-lemmas-about-rr32-1
     (and (signed-byte-p 64 (rr32 reg x86))
          (signed-byte-p 48 (rr32 reg x86))))

   (defthm signed-byte-p-lemmas-about-rr32-2
     (implies (and (integerp n)
                   (<= -8 n)
                   (<= n 8))
              (signed-byte-p 49 (+ n (rr32 reg x86)))))

   (defthm signed-byte-p-lemmas-about-rr16-1
     (and (signed-byte-p 64 (rr16 reg x86))
          (signed-byte-p 48 (rr16 reg x86))))

   (defthm signed-byte-p-lemmas-about-rr16-2
     (implies (and (integerp n)
                   (<= -8 n)
                   (<= n 8))
              (signed-byte-p 49 (+ n (rr16 reg x86)))))

   (defthm signed-byte-p-lemmas-about-xr-rgf
     (implies (and (integerp n)
                   (<= -8 n)
                   (<= n 8)
                   (signed-byte-p 48 (xr :rgf reg x86)))
              (and (signed-byte-p 49 (+ n (xr :rgf reg x86)))
                   (signed-byte-p 64 (+ n (xr :rgf reg x86)))))
     :hints (("Goal" :in-theory (e/d () (force (force))))))))

(local (in-theory (e/d (ea-to-la) ())))

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
                :hyp (x86p x86)
                :hints
                (("Goal" :in-theory (e/d ()
                                         (rme-size
                                          !rgfi-size
                                          unsigned-byte-p
                                          signed-byte-p)))
                 (if (and (consp id)
                          (consp (car id))
                          (equal (caar id) 1))
                     ;; Top-level goals in a forcing round:
                     '(:in-theory (e/d ()
                                       (segment-base-and-bounds
                                        rme-size
                                        !rgfi-size
                                        signed-byte-p
                                        unsigned-byte-p)))
                   nil)))

  :guard-hints (("Goal" :in-theory (e/d (rme-size
                                         select-address-size)
                                        (segment-base-and-bounds
                                         signed-byte-p
                                         unsigned-byte-p
                                         force (force)))))

  :prepwork
  ((local (in-theory (e/d () (not (tau-system))))))

  :modr/m t

  :body

  (b* ((group-1-prefix (the (unsigned-byte 8) (prefixes->rep prefixes)))

       ;; TODO: is the following already checked by GET-PREFIXES?
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (p2 (the (unsigned-byte 8) (prefixes->seg prefixes)))
       (p4? (equal #.*addr-size-override*
                   (the (unsigned-byte 8) (prefixes->adr prefixes))))

       ((the (unsigned-byte 1) df) (flgi :df x86))

       ((the (integer 2 8) counter/addr-size)
        (select-address-size proc-mode p4? x86)) ; CX or ECX or RCX

       (select-byte-operand (equal #xA4 opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       (src-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rsi* rex-byte x86)
                   (rgfi #.*rsi* x86)))
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p src-addr))))
        (!!ms-fresh :src-addr-not-canonical src-addr))

       (inst-ac? (alignment-checking-enabled-p x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((mv flg0 src x86)
        (rme-size-opt
         proc-mode operand-size
         (the (signed-byte 64) src-addr)
         seg-reg :r inst-ac? x86))
       ((when flg0)
        (!!ms-fresh :src-rme-size-error flg0))

       (dst-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rdi* rex-byte x86)
                   (rgfi #.*rdi* x86)))
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))

       ((the (signed-byte #.*max-linear-address-size*) original-dst-addr)
        dst-addr)

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
                         (mv (+ 8 (the (signed-byte #.*max-linear-address-size*)
                                    src-addr))
                             (+ 8 (the (signed-byte #.*max-linear-address-size*)
                                    dst-addr)))
                       (mv (+ -8 (the (signed-byte #.*max-linear-address-size*)
                                   src-addr))
                           (+ -8 (the (signed-byte #.*max-linear-address-size*)
                                   dst-addr)))))))

       ;; Update the x86 state:
       ((mv flg1 x86)
        (wme-size
         proc-mode operand-size original-dst-addr #.*es* src inst-ac? x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg1)
        (!!ms-fresh :wme-size-error flg1))

       ;; REP prefix: Updating rCX and RIP:

       (x86 (case group-1-prefix
              (#.*repe*
               (let* ((counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi :zf x86)) 0))
                     (let* ((x86 (!rgfi-size
                                  counter/addr-size #.*rcx* counter rex-byte x86)))
                       x86)
                   (let* ((x86 (!rgfi-size
                                counter/addr-size #.*rcx* counter rex-byte x86))
                          (x86 (write-*ip proc-mode temp-rip x86)))
                     x86))))
              (#.*repne*
               (let* ((counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi :zf x86)) 1))
                     (let* ((x86 (!rgfi-size
                                  counter/addr-size #.*rcx* counter rex-byte x86))
                            (x86 (write-*ip proc-mode temp-rip x86)))
                       x86)
                   (let* ((x86 (!rgfi-size
                                counter/addr-size #.*rcx* counter rex-byte x86)))
                     x86))))
              (otherwise ;; no rep prefix present
               (write-*ip proc-mode temp-rip x86))))

       ;; Updating rSI and rDI:
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rsi*
                             (n16 (the (signed-byte
                                        #.*max-linear-address-size+1*) src-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rsi*
                             (n32 (the (signed-byte
                                        #.*max-linear-address-size+1*) src-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rsi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                          src-addr)
                        x86))))
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rdi*
                             (n16 (the
                                      (signed-byte
                                       #.*max-linear-address-size+1*) dst-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rdi*
                             (n32 (the
                                      (signed-byte
                                       #.*max-linear-address-size+1*) dst-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rdi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                          dst-addr)
                        x86)))))

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

  :returns (x86 x86p
                :hyp (x86p x86)
                :hints
                (("Goal" :in-theory (e/d ()
                                         (rme-size
                                          !rgfi-size
                                          unsigned-byte-p
                                          signed-byte-p
                                          force (force)
                                          !rgfi-size)))
                 (if (and (consp id)
                          (consp (car id))
                          (equal (caar id) 1))
                     ;; Top-level goals in a forcing round:
                     '(:in-theory (e/d ()
                                       (segment-base-and-bounds
                                        rme-size
                                        !rgfi-size
                                        signed-byte-p
                                        unsigned-byte-p)))
                   nil)))

  :guard-hints (("Goal" :in-theory (e/d (rme-size select-address-size)
                                        (segment-base-and-bounds
                                         signed-byte-p
                                         unsigned-byte-p
                                         force (force)))))

  :prepwork
  ((local (in-theory (e/d () (not (tau-system))))))

  :modr/m t

  :body

  (b* ((group-1-prefix (the (unsigned-byte 8) (prefixes->rep prefixes)))

       ;; TODO: is the following already checked by GET-PREFIXES?
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (p2 (the (unsigned-byte 8) (prefixes->seg prefixes)))
       (p4? (equal #.*addr-size-override*
                   (the (unsigned-byte 8) (prefixes->adr prefixes))))

       ((the (unsigned-byte 1) df) (flgi :df x86))

       ((the (integer 2 8) counter/addr-size)
        (select-address-size proc-mode p4? x86)) ; CX or ECX or RCX

       (select-byte-operand (equal #xA6 opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       (src-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rsi* rex-byte x86)
                   (rgfi #.*rsi* x86)))
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p src-addr))))
        (!!ms-fresh :src-addr-not-canonical src-addr))

       (inst-ac? (alignment-checking-enabled-p x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((mv flg0 src x86)
        (rme-size-opt proc-mode operand-size src-addr seg-reg :r inst-ac? x86))
       ((when flg0)
        (!!ms-fresh :src-rme-size-error flg0))

       (dst-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rdi* rex-byte x86)
                   (rgfi #.*rdi* x86)))
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))

       ((mv flg0 dst x86)
        (rme-size-opt proc-mode operand-size dst-addr #.*es* :r inst-ac? x86))
       ((when flg0)
        (!!ms-fresh :dst-rme-size-error flg0))

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
                              #.*max-linear-address-size*) src-addr) 1)
                     (+ (the (signed-byte
                              #.*max-linear-address-size*) dst-addr) 1))
               (mv (- (the (signed-byte
                            #.*max-linear-address-size*) src-addr) 1)
                   (- (the (signed-byte
                            #.*max-linear-address-size*) dst-addr) 1))))
          (2 (if (equal df 0)
                 (mv (+ (the (signed-byte
                              #.*max-linear-address-size*) src-addr) 2)
                     (+ (the (signed-byte
                              #.*max-linear-address-size*) dst-addr) 2))
               (mv (- (the (signed-byte
                            #.*max-linear-address-size*) src-addr) 2)
                   (- (the (signed-byte
                            #.*max-linear-address-size*) dst-addr) 2))))
          (4 (if (equal df 0)
                 (mv (+ (the (signed-byte
                              #.*max-linear-address-size*) src-addr) 4)
                     (+ (the (signed-byte
                              #.*max-linear-address-size*) dst-addr) 4))
               (mv (- (the (signed-byte
                            #.*max-linear-address-size*) src-addr) 4)
                   (- (the (signed-byte
                            #.*max-linear-address-size*) dst-addr) 4))))
          (otherwise (if (equal df 0)
                         (mv (+ (the (signed-byte
                                      #.*max-linear-address-size*) src-addr) 8)
                             (+ (the (signed-byte
                                      #.*max-linear-address-size*) dst-addr) 8))
                       (mv (- (the (signed-byte
                                    #.*max-linear-address-size*) src-addr) 8)
                           (- (the (signed-byte
                                    #.*max-linear-address-size*) dst-addr) 8))))))

       ;; REP prefix: Updating rCX and RIP:

       (x86 (case group-1-prefix
              (#.*repe*
               (let* ((counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi :zf x86)) 0))
                     (let* ((x86 (!rgfi-size
                                  counter/addr-size #.*rcx* counter rex-byte x86)))
                       x86)
                   (let* ((x86 (!rgfi-size
                                counter/addr-size #.*rcx* counter rex-byte x86))
                          (x86 (write-*ip proc-mode temp-rip x86)))
                     x86))))
              (#.*repne*
               (let* ((counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi :zf x86)) 1))
                     (let* ((x86 (!rgfi-size
                                  counter/addr-size #.*rcx* counter rex-byte x86))
                            (x86 (write-*ip proc-mode temp-rip x86)))
                       x86)
                   (let* ((x86 (!rgfi-size
                                counter/addr-size #.*rcx* counter rex-byte x86)))
                     x86))))
              (otherwise ;; no rep prefix present
               (write-*ip proc-mode temp-rip x86))))

       ;; Updating rSI and rDI:

       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rsi*
                             (n16 (the (signed-byte
                                        #.*max-linear-address-size+1*) src-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rsi*
                             (n32 (the (signed-byte
                                        #.*max-linear-address-size+1*) src-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rsi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                          src-addr)
                        x86))))
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rdi*
                             (n16 (the
                                      (signed-byte
                                       #.*max-linear-address-size+1*)
                                    dst-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rdi*
                             (n32 (the
                                      (signed-byte
                                       #.*max-linear-address-size+1*)
                                    dst-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rdi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                          dst-addr)
                        x86)))))
    x86))

;; ======================================================================
;; INSTRUCTION: STOS/STOSB/STOSW/STOSD/STOSQ
;; ======================================================================

(def-inst x86-stos

  ;; AA STOSB:             Store AL         at address DI or EDI or RDI
  ;; AB STOSW/STOSD/STOSQ: Store AX/EAX/RDX at address DI or EDI or RDI

  :parents (one-byte-opcodes)

  :returns (x86 x86p
                :hyp (x86p x86)
                :hints
                (("Goal" :in-theory (e/d ()
                                         (trunc
                                          rme-size
                                          !rgfi-size
                                          !rgfi-size
                                          unsigned-byte-p
                                          signed-byte-p
                                          (force) force)))
                 (if (and (consp id)
                          (consp (car id))
                          (equal (caar id) 1))
                     ;; Top-level goals in a forcing round:
                     '(:in-theory (e/d ()
                                       (rme-size
                                        !rgfi-size
                                        unsigned-byte-p
                                        segment-base-and-bounds
                                        signed-byte-p)))
                   nil)))

  :guard-hints (("Goal" :in-theory (e/d (rme-size select-address-size)
                                        (segment-base-and-bounds
                                         signed-byte-p
                                         unsigned-byte-p
                                         force (force)))))

  :prepwork
  ((local (in-theory (e/d () (not (tau-system))))))

  :body

  (b* ((group-1-prefix (the (unsigned-byte 8) (prefixes->seg prefixes)))

       ;; TODO: is the following already checked by GET-PREFIXES?
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (p4? (equal #.*addr-size-override*
                   (the (unsigned-byte 8) (prefixes->adr prefixes))))

       ((the (unsigned-byte 1) df) (flgi :df x86))

       ((the (integer 2 8) counter/addr-size)
        (select-address-size proc-mode p4? x86)) ; CX or ECX or RCX

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       (dst-addr
        (if counter/addr-size-2/4?
            (rgfi-size counter/addr-size #.*rdi* rex-byte x86)
          (rgfi #.*rdi* x86)))
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))

       (select-byte-operand (equal #xAA opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (rAX (rgfi-size operand-size #.*rax* rex-byte x86))

       ;; Update the x86 state:

       ;; Writing rAX to the memory:
       (inst-ac? (alignment-checking-enabled-p x86))
       ((mv flg0 x86)
        (wme-size proc-mode operand-size dst-addr #.*es* rAX inst-ac? x86))
       ((when flg0)
        (!!ms-fresh :wme-size-error flg0))

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
               (let* ((counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi :zf x86)) 0))
                     (let* ((x86 (!rgfi-size counter/addr-size
                                             #.*rcx*
                                             counter
                                             rex-byte
                                             x86)))
                       x86)
                   (let* ((x86 (!rgfi-size counter/addr-size
                                           #.*rcx*
                                           counter
                                           rex-byte
                                           x86))
                          (x86 (write-*ip proc-mode temp-rip x86)))
                     x86))))
              (#.*repne*
               (let* ((counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))
                      (counter (trunc counter/addr-size (1- counter))))
                 (if (or (equal counter 0)
                         (equal (the (unsigned-byte 1) (flgi :zf x86)) 1))
                     (let* ((x86 (!rgfi-size counter/addr-size
                                             #.*rcx*
                                             counter
                                             rex-byte
                                             x86))
                            (x86 (write-*ip proc-mode temp-rip x86)))
                       x86)
                   (let* ((x86 (!rgfi-size counter/addr-size
                                           #.*rcx*
                                           counter
                                           rex-byte
                                           x86)))
                     x86))))
              (otherwise ;; no rep prefix present
               (write-*ip proc-mode temp-rip x86))))

       ;; Updating rDI:
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rdi*
                             (n16 (the
                                      (signed-byte
                                       #.*max-linear-address-size+1*)
                                    dst-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rdi*
                             (n32 (the
                                      (signed-byte
                                       #.*max-linear-address-size+1*)
                                    dst-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rdi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                          dst-addr)
                        x86)))))

    x86))

;; ======================================================================
