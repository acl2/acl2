; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail
; Copyright (C) May 2024 - August 2024, Intel Corporation
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
; Yahya Sohail        <yahya.sohail@intel.com>

(in-package "X86ISA")

;; ======================================================================

(include-book "arith-and-logic-spec")
(include-book "../decoding-and-spec-utils")

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

  :parents (one-byte-opcodes)

  :short "MOVS/MOVSB/MOVSW/MOVSD/MOVSQ: move data from string to string."

  :long
  (xdoc::topstring
   (xdoc::p
    "See Intel manual Mar 2026, Volume 1, Section 7.3.9,
     for an overview of string operations,
     including the use of repetition prefixes.
     Also see REP instruction prefix listed under `R'
     in Intel manual Mar 2026, Volume 2, alphabetical instruction list.")
   (xdoc::p
    "The distinction between MOVS and the others is just at the assembly level,
     as explained in the Intel manual;
     the m8, m16, m32, and m64 assembly-level operands are
     just a way to specify the operand size,
     but not the actual operands, which are always implicit."))

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

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (e/d (rme-size-of-1-to-rme08
                                         rme-size-of-2-to-rme16
                                         rme-size-of-4-to-rme32
                                         rme-size-of-8-to-rme64)
                                        (signed-byte-p
                                         not))))

  :modr/m t

  :body

  (b* (;; Only the REP prefix is valid for these instructions.
       (group-1-prefix (the (unsigned-byte 8) (prefixes->rep prefixes)))

       (p2 (the (unsigned-byte 8) (prefixes->seg prefixes)))
       (p4? (equal #.*addr-size-override*
                   (the (unsigned-byte 8) (prefixes->adr prefixes))))

       ((the (integer 2 8) counter/addr-size) ; CX or ECX or RCX
        (select-address-size proc-mode p4? x86))

       (counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))

       ;; If REP is used and rCX is 0, continue to the next instruction.
       ((when (and (equal group-1-prefix #.*rep*)
                   (equal counter 0)))
        (write-*ip proc-mode temp-rip x86))

       (select-byte-operand (equal #xA4 opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       ;; Read data from the source.
       (src-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rsi* rex-byte x86) ; SI/ESI
                   (rgfi #.*rsi* x86))) ; RSI
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p src-addr))))
        (!!ms-fresh :src-addr-not-canonical src-addr))
       (inst-ac? (alignment-checking-enabled-p x86))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
       ((mv flg0 src x86) (rme-size-opt proc-mode
                                        operand-size
                                        (the (signed-byte 64) src-addr)
                                        seg-reg
                                        :r
                                        inst-ac?
                                        x86))
       ((when flg0)
        (!!ms-fresh :src-rme-size-error flg0))

       ;; Write data to the destination. This is always in segment ES.
       (dst-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rdi* rex-byte x86) ; DI/EDI
                   (rgfi #.*rdi* x86))) ; RDI
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))
       ((mv flg1 x86) (wme-size proc-mode
                                operand-size
                                dst-addr
                                #.*es*
                                src
                                inst-ac?
                                x86))
       ((when flg1)
        (!!ms-fresh :wme-size-error flg1))

       ;; If there is a REP prefix, decrement rCX and leave the rIP unchanged,
       ;; so that we can (attempt to) repeat this instruction;
       ;; note that if we get here rCX is not 0, because we tested it above.
       ;; If there is no REP prefix, advance rIP to the next instructions.
       (x86 (if (equal group-1-prefix #.*rep*)
                (!rgfi-size counter/addr-size #.*rcx* (1- counter) rex-byte x86)
              (write-*ip proc-mode temp-rip x86)))

       ;; A repeating string operation can be suspended by an exception or
       ;; interrupt. When this happens, the state of the register is preserved
       ;; to allow the string operation to be resumed upon a return from the
       ;; exception or interrupt handler.

       ;; Update rSI and rDI.
       ((the (unsigned-byte 1) df) (flgi :df x86))
       ((mv (the (signed-byte #.*max-linear-address-size+1*) src-addr)
            (the (signed-byte #.*max-linear-address-size+1*) dst-addr))
        (case operand-size
          (1 (if (equal df 0)
                 (mv (+ 1 (the (signed-byte #.*max-linear-address-size*)
                               src-addr))
                     (+ 1 (the (signed-byte #.*max-linear-address-size*)
                               dst-addr)))
               (mv (+ -1 (the (signed-byte #.*max-linear-address-size*)
                              src-addr))
                   (+ -1 (the (signed-byte #.*max-linear-address-size*)
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

  :parents (one-byte-opcodes)

  :short "CMPS/CMPSB/CMPSW/CMPSD/CMPSQ: compare string operands."

  :long
  (xdoc::topstring
   (xdoc::p
    "See Intel manual Mar 2026, Volume 1, Section 7.3.9,
     for an overview of string operations,
     including the use of repetition prefixes.
     Also see REPE/REPZ and REPNE/REPNZ instruction prefixes listed under `R`
     in Intel manual Mar 206, Volume 2, alphabetical instruction list.")
   (xdoc::p
    "The distinction between CMPS and the others is just at the assembly level,
     as explained in the Intel manual;
     the m8, m16, m32, and m64 assembly-level operands are
     just a way to specify the operand size,
     but not the actual operands, which are always implicit."))

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

  ;; Only the REP prefix is valid for CMPS

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (e/d (rme-size-of-1-to-rme08
                                         rme-size-of-2-to-rme16
                                         rme-size-of-4-to-rme32
                                         rme-size-of-8-to-rme64)
                                        (signed-byte-p
                                         not))))

  :modr/m t

  :body

  (b* (;; Only the REPE/REPZ and REPNE/REPNZ are valid for these instructions.
       (group-1-prefix (the (unsigned-byte 8) (prefixes->rep prefixes)))

       (p2 (the (unsigned-byte 8) (prefixes->seg prefixes)))
       (p4? (equal #.*addr-size-override*
                   (the (unsigned-byte 8) (prefixes->adr prefixes))))

       ((the (integer 2 8) counter/addr-size) ; CX or ECX or RCX
        (select-address-size proc-mode p4? x86))

       (counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))

       ;; If REPE/REPZ or REPNE/REPZ is used and rCX is 0,
       ;; continue to the next instruction.
       ((when (and (or (equal group-1-prefix #.*repe*) ; REPE/REPZ
                       (equal group-1-prefix #.*repne*)) ; REPNE/REPNZ
                   (equal counter 0)))
        (write-*ip proc-mode temp-rip x86))

       (select-byte-operand (equal #xA6 opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       ;; Read data from the first source.
       (src1-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rsi* rex-byte x86) ; SI/ESI
                   (rgfi #.*rsi* x86))) ; RSI
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p src1-addr))))
        (!!ms-fresh :src1-addr-not-canonical src1-addr))
       (inst-ac? (alignment-checking-enabled-p x86))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
       ((mv flg0 src1 x86) (rme-size-opt proc-mode
                                        operand-size
                                        (the (signed-byte 64) src1-addr)
                                        seg-reg
                                        :r
                                        inst-ac?
                                        x86))
       ((when flg0)
        (!!ms-fresh :src1-rme-size-error flg0))

       ;; Read data from the second source.
       (src2-addr (if counter/addr-size-2/4?
                      (rgfi-size counter/addr-size #.*rdi* rex-byte x86) ; DI/EDI
                    (rgfi #.*rdi* x86))) ; RDI
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p src2-addr))))
        (!!ms-fresh :src2-addr-not-canonical src2-addr))

       ((mv flg0 src2 x86) (rme-size-opt proc-mode
                                         operand-size
                                         src2-addr
                                         #.*es*
                                         :r
                                         inst-ac?
                                         x86))
       ((when flg0)
        (!!ms-fresh :src2-rme-size-error flg0))

       ;; From the AMD Manual: "To perform the comparison, the instruction
       ;; subtracts the second operand from the first operand and sets the
       ;; status flags in the same manner as the SUB instruction, but does not
       ;; alter the first operand. The two operands must be of the same size."
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv ?result
            (the (unsigned-byte 32) output-rflags)
            (the (unsigned-byte 32) undefined-flags))
        (gpr-arith/logic-spec operand-size #.*OP-SUB* src1 src2 input-rflags))
       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ;; If there is a REPE/REPZ or REPNE/REPNZ prefix,
       ;; decrement rCX and leave the rIP unchanged,
       ;; so that we can (attempt to) repeat this instruction
       ;; (unless the ZF flag, checked below, stops the repetition);
       ;; note that if we get here rCX is not 0, because we tested it above.
       ;; If there is no REPE/REPZ or REPNE/REPNZ prefix,
       ;; advance rIP to the next instructions.
       (x86 (if (or (equal group-1-prefix #.*repe*) ; REPE/REPZ
                    (equal group-1-prefix #.*repne*)) ; REPNE/REPNZ
                (!rgfi-size counter/addr-size #.*rcx* (1- counter) rex-byte x86)
              (write-*ip proc-mode temp-rip x86)))

       ;; If there is a REPE/REPZ prefix and ZF is 0, stop repetition.
       ;; If there is a REPNE/REPNZ prefix and ZF is 1, stop repetition.
       ;; Note that ZF is set by the comparison performed above.
       ;; If the repetition stops, we update rIP,
       ;; so that the next execution step is on the next instruction;
       ;; otherwise, rIP stays as is,
       ;; and the next step re-executes this instruction.
       (stop-repeat (or (and (equal group-1-prefix #.*repe*)
                             (= (rflagsbits->zf output-rflags) 0))
                        (and (equal group-1-prefix #.*repne*)
                             (= (rflagsbits->zf output-rflags) 1))))
       (x86 (if stop-repeat
                (write-*ip proc-mode temp-rip x86)
              x86))

       ;; A repeating string operation can be suspended by an exception or
       ;; interrupt. When this happens, the state of the register is preserved
       ;; to allow the string operation to be resumed upon a return from the
       ;; exception or interrupt handler.

       ;; Update rSI and rDI.
       ((the (unsigned-byte 1) df) (flgi :df x86))
       ((mv (the (signed-byte #.*max-linear-address-size+1*) src1-addr)
            (the (signed-byte #.*max-linear-address-size+1*) src2-addr))
        (case operand-size
          (1 (if (equal df 0)
                 (mv (+ 1 (the (signed-byte #.*max-linear-address-size*)
                               src1-addr))
                     (+ 1 (the (signed-byte #.*max-linear-address-size*)
                               src2-addr)))
               (mv (+ -1 (the (signed-byte #.*max-linear-address-size*)
                              src1-addr))
                   (+ -1 (the (signed-byte #.*max-linear-address-size*)
                              src2-addr)))))
          (2 (if (equal df 0)
                 (mv (+ 2 (the (signed-byte
                                #.*max-linear-address-size*) src1-addr))
                     (+ 2 (the (signed-byte
                                #.*max-linear-address-size*) src2-addr)))
               (mv (+ -2 (the (signed-byte #.*max-linear-address-size*)
                              src1-addr))
                   (+ -2 (the (signed-byte #.*max-linear-address-size*)
                              src2-addr)))))
          (4 (if (equal df 0)
                 (mv (+ 4 (the (signed-byte #.*max-linear-address-size*)
                               src1-addr))
                     (+ 4 (the (signed-byte #.*max-linear-address-size*)
                               src2-addr)))
               (mv (+ -4 (the (signed-byte #.*max-linear-address-size*)
                              src1-addr))
                   (+ -4 (the (signed-byte #.*max-linear-address-size*)
                              src2-addr)))))
          (otherwise (if (equal df 0)
                         (mv (+ 8 (the (signed-byte #.*max-linear-address-size*)
                                       src1-addr))
                             (+ 8 (the (signed-byte #.*max-linear-address-size*)
                                       src2-addr)))
                       (mv (+ -8 (the (signed-byte #.*max-linear-address-size*)
                                      src1-addr))
                           (+ -8 (the (signed-byte #.*max-linear-address-size*)
                                      src2-addr)))))))
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rsi*
                             (n16 (the (signed-byte
                                        #.*max-linear-address-size+1*) src1-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rsi*
                             (n32 (the (signed-byte
                                        #.*max-linear-address-size+1*) src1-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rsi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                             src1-addr)
                        x86))))
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rdi*
                             (n16 (the
                                   (signed-byte
                                    #.*max-linear-address-size+1*)
                                   src2-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rdi*
                             (n32 (the
                                   (signed-byte
                                    #.*max-linear-address-size+1*)
                                   src2-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rdi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                             src2-addr)
                        x86)))))

    x86))

;; ======================================================================
;; INSTRUCTION: SCAS/SCASB/SCASW/SCASD/SCASQ
;; ======================================================================

(def-inst x86-scas

  :parents (one-byte-opcodes)

  :short "SCAS/SCASB/SCASW/SCASD/SCASQ: scan string."

  :long
  (xdoc::topstring
   (xdoc::p
    "See Intel manual Mar 2026, Volume 1, Section 7.3.9,
     for an overview of string operations,
     including the use of repetition prefixes.
     Also see REPE/REPZ and REPNE/REPNZ instruction prefixes listed under `R`
     in Intel manual Mar 206, Volume 2, alphabetical instruction list.")
   (xdoc::p
    "The distinction between SCAS and the others is just at the assembly level,
     as explained in the Intel manual;
     the m8, m16, m32, and m64 assembly-level operands are
     just a way to specify the operand size,
     but not the actual operands, which are always implicit."))

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (e/d (rme-size-of-1-to-rme08
                                         rme-size-of-2-to-rme16
                                         rme-size-of-4-to-rme32
                                         rme-size-of-8-to-rme64)
                                        (signed-byte-p
                                         not))))

  :body

  (b* (;; Only the REPE/REPZ and REPNE/REPNZ are valid for these instructions.
       (group-1-prefix (the (unsigned-byte 8) (prefixes->rep prefixes)))

       (p4? (equal #.*addr-size-override*
                   (the (unsigned-byte 8) (prefixes->adr prefixes))))

       ((the (integer 2 8) counter/addr-size) ; CX or ECX or RCX
        (select-address-size proc-mode p4? x86))

       (counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))

       ;; If REPE/REPZ or REPNE/REPZ is used and rCX is 0,
       ;; continue to the next instruction.
       ((when (and (or (equal group-1-prefix #.*repe*) ; REPE/REPZ
                       (equal group-1-prefix #.*repne*)) ; REPNE/REPNZ
                   (equal counter 0)))
        (write-*ip proc-mode temp-rip x86))

       (select-byte-operand (equal #xAE opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       ;; Read data from the source.
       (src-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rdi* rex-byte x86) ; DI/EDI
                   (rgfi #.*rdi* x86))) ; RDI
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p src-addr))))
        (!!ms-fresh :src-addr-not-canonical src-addr))
       (inst-ac? (alignment-checking-enabled-p x86))
       ((mv flg0 src x86) (rme-size-opt proc-mode
                                        operand-size
                                        (the (signed-byte 64) src-addr)
                                        #.*es*
                                        :r
                                        inst-ac?
                                        x86))
       ((when flg0)
        (!!ms-fresh :src-rme-size-error flg0))

       ;; Read rAX.
       (al/ax/eax/rax (rgfi-size operand-size #.*rax* 0 x86))

       ;; Perform the comparison.
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv ?result
            (the (unsigned-byte 32) output-rflags)
            (the (unsigned-byte 32) undefined-flags))
        (gpr-arith/logic-spec
         operand-size #.*OP-SUB* al/ax/eax/rax src input-rflags))
       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ;; If there is a REPE/REPZ or REPNE/REPNZ prefix,
       ;; decrement rCX and leave the rIP unchanged,
       ;; so that we can (attempt to) repeat this instruction
       ;; (unless the ZF flag, checked below, stops the repetition);
       ;; note that if we get here rCX is not 0, because we tested it above.
       ;; If there is no REPE/REPZ or REPNE/REPNZ prefix,
       ;; advance rIP to the next instructions.
       (x86 (if (or (equal group-1-prefix #.*repe*) ; REPE/REPZ
                    (equal group-1-prefix #.*repne*)) ; REPNE/REPNZ
                (!rgfi-size counter/addr-size #.*rcx* (1- counter) rex-byte x86)
              (write-*ip proc-mode temp-rip x86)))

       ;; If there is a REPE/REPZ prefix and ZF is 0, stop repetition.
       ;; If there is a REPNE/REPNZ prefix and ZF is 1, stop repetition.
       ;; Note that ZF is set by the comparison performed above.
       ;; If the repetition stops, we update rIP,
       ;; so that the next execution step is on the next instruction;
       ;; otherwise, rIP stays as is,
       ;; and the next step re-executes this instruction.
       (stop-repeat (or (and (equal group-1-prefix #.*repe*) ; REPE/REPZ
                             (= (rflagsbits->zf output-rflags) 0))
                        (and (equal group-1-prefix #.*repne*) ; REPNE/REPNZ
                             (= (rflagsbits->zf output-rflags) 1))))
       (x86 (if stop-repeat
                (write-*ip proc-mode temp-rip x86)
              x86))

       ;; Update rDI.
       ((the (unsigned-byte 1) df) (flgi :df x86))
       ((the (signed-byte #.*max-linear-address-size+1*) src-addr)
        (case operand-size
          (1 (if (equal df 0)
                 (+ 1 (the (signed-byte #.*max-linear-address-size*) src-addr))
               (+ -1 (the (signed-byte #.*max-linear-address-size*) src-addr))))
          (2 (if (equal df 0)
                 (+ 2 (the (signed-byte #.*max-linear-address-size*) src-addr))
               (+ -2 (the (signed-byte #.*max-linear-address-size*) src-addr))))
          (4 (if (equal df 0)
                 (+ 4 (the (signed-byte #.*max-linear-address-size*) src-addr))
               (+ -4 (the (signed-byte #.*max-linear-address-size*) src-addr))))
          (otherwise
           (if (equal df 0)
               (+ 8 (the (signed-byte #.*max-linear-address-size*) src-addr))
             (+ -8 (the (signed-byte #.*max-linear-address-size*) src-addr))))))
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rdi*
                             (n16 (the
                                   (signed-byte
                                    #.*max-linear-address-size+1*)
                                   src-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rdi*
                             (n32 (the
                                   (signed-byte
                                    #.*max-linear-address-size+1*)
                                   src-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rdi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                             src-addr)
                        x86)))))

    x86))

;; ======================================================================
;; INSTRUCTION: STOS/STOSB/STOSW/STOSD/STOSQ
;; ======================================================================

(def-inst x86-stos

  :parents (one-byte-opcodes)

  :short "STOS/STOSB/STOSW/STOSD/STOSQ: store string."

  :long
  (xdoc::topstring
   (xdoc::p
    "See Intel manual Mar 2026, Volume 1, Section 7.3.9,
     for an overview of string operations,
     including the use of repetition prefixes.
     Also see REP instruction prefix listed under `R'
     in Intel manual Mar 2026, Volume 2, alphabetical instruction list.")
   (xdoc::p
    "The distinction between STOS and the others is just at the assembly level,
     as explained in the Intel manual;
     the m8, m16, m32, and m64 assembly-level operands are
     just a way to specify the operand size,
     but not the actual operands, which are always implicit."))

  ;; AA STOSB:             Store AL         at address DI or EDI or RDI
  ;; AB STOSW/STOSD/STOSQ: Store AX/EAX/RDX at address DI or EDI or RDI

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (e/d (rme-size-of-1-to-rme08
                                         rme-size-of-2-to-rme16
                                         rme-size-of-4-to-rme32
                                         rme-size-of-8-to-rme64)
                                        (signed-byte-p
                                         not))))

  :body

  (b* (;; Only the REP prefix is valid for these instructions.
       (group-1-prefix (the (unsigned-byte 8) (prefixes->rep prefixes)))

       (p4? (equal #.*addr-size-override*
                   (the (unsigned-byte 8) (prefixes->adr prefixes))))

       ((the (integer 2 8) counter/addr-size) ; CX or ECX or RCX
        (select-address-size proc-mode p4? x86))

       (counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))

       ;; If REP is used and rCX is 0, continue to the next instruction.
       ((when (and (equal group-1-prefix *rep*)
                   (equal counter 0)))
        (write-*ip proc-mode temp-rip x86))

       (select-byte-operand (equal #xAA opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       ;; Read rAX.
       (al/ax/eax/rax (rgfi-size operand-size #.*rax* 0 x86))

       ;; Write data to the destination. This is always in segment ES.
       (dst-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rdi* rex-byte x86) ; DI/EDI
                   (rgfi #.*rdi* x86))) ; RDI
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p dst-addr))))
        (!!ms-fresh :dst-addr-not-canonical dst-addr))
       (inst-ac? (alignment-checking-enabled-p x86))
       ((mv flg0 x86) (wme-size proc-mode
                                operand-size
                                dst-addr
                                #.*es*
                                al/ax/eax/rax
                                inst-ac?
                                x86))
       ((when flg0)
        (!!ms-fresh :wme-size-error flg0))

       ;; If there is a REP prefix, decrement rCX and leave the rIP unchanged,
       ;; so that we can (attempt to) repeat this instruction;
       ;; note that if we get here rCX is not 0, because we tested it above.
       ;; If there is no REP prefix, advance rIP to the next instructions.
       (x86 (if (equal group-1-prefix *repe*)
                (!rgfi-size counter/addr-size #.*rcx* (1- counter) rex-byte x86)
              (write-*ip proc-mode temp-rip x86)))

       ;; Update rDI.
       ((the (unsigned-byte 1) df) (flgi :df x86))
       ((the (signed-byte #.*max-linear-address-size+1*) dst-addr)
        (case operand-size
          (1 (if (equal df 0)
                 (+ 1 (the (signed-byte #.*max-linear-address-size*) dst-addr))
               (+ -1 (the (signed-byte #.*max-linear-address-size*) dst-addr))))
          (2 (if (equal df 0)
                 (+ 2 (the (signed-byte #.*max-linear-address-size*) dst-addr))
               (+ -2 (the (signed-byte #.*max-linear-address-size*) dst-addr))))
          (4 (if (equal df 0)
                 (+ 4 (the (signed-byte #.*max-linear-address-size*) dst-addr))
               (+ -4 (the (signed-byte #.*max-linear-address-size*) dst-addr))))
          (otherwise
           (if (equal df 0)
               (+ 8 (the (signed-byte #.*max-linear-address-size*) dst-addr))
             (+ -8 (the (signed-byte #.*max-linear-address-size*) dst-addr))))))
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
;; INSTRUCTION: LODS/LODSB/LODSW/LODSD/LODSQ
;; ======================================================================

(def-inst x86-lods

  :parents (one-byte-opcodes)

  :short "LODS/LODSB/LODSW/LODSD/LODSQ: load string."

  :long
  (xdoc::topstring
   (xdoc::p
    "See Intel manual Mar 2026, Volume 1, Section 7.3.9,
     for an overview of string operations,
     including the use of repetition prefixes.
     Also see REP instruction prefix listed under `R'
     in Intel manual Mar 2026, Volume 2, alphabetical instruction list.")
   (xdoc::p
    "The distinction between LODS and the others is just at the assembly level,
     as explained in the Intel manual;
     the m8, m16, m32, and m64 assembly-level operands are
     just a way to specify the operand size,
     but not the actual operands, which are always implicit."))

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (e/d (rme-size-of-1-to-rme08
                                         rme-size-of-2-to-rme16
                                         rme-size-of-4-to-rme32
                                         rme-size-of-8-to-rme64)
                                        (signed-byte-p
                                         not))))

  :modr/m t

  :body

  (b* (;; Only the REP prefix is valid for these instructions.
       (group-1-prefix (the (unsigned-byte 8) (prefixes->rep prefixes)))

       (p2 (the (unsigned-byte 8) (prefixes->seg prefixes)))
       (p4? (equal #.*addr-size-override*
                   (the (unsigned-byte 8) (prefixes->adr prefixes))))


       ((the (integer 2 8) counter/addr-size) ; CX or ECX or RCX
        (select-address-size proc-mode p4? x86))

       (counter (rgfi-size counter/addr-size #.*rcx* rex-byte x86))

       ;; If REP is used and rCX is 0, continue to the next instruction.
       ((when (and (equal group-1-prefix *rep*)
                   (equal counter 0)))
        (write-*ip proc-mode temp-rip x86))

       (select-byte-operand (equal #xAC opcode))
       ((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (counter/addr-size-2/4? (or (eql counter/addr-size 2)
                                   (eql counter/addr-size 4)))

       ;; Read source operand from memory.
       (src-addr (if counter/addr-size-2/4?
                     (rgfi-size counter/addr-size #.*rsi* rex-byte x86) ; SI/ESI
                   (rgfi #.*rsi* x86))) ; RSI
       ((when (and (not counter/addr-size-2/4?)
                   ;; A 16-bit or 32-bit address is always canonical.
                   (not (canonical-address-p src-addr))))
        (!!ms-fresh :src-addr-not-canonical src-addr))
       (inst-ac? (alignment-checking-enabled-p x86))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
       ((mv flg0 src x86) (rme-size-opt proc-mode
                                        operand-size
                                        (the (signed-byte 64) src-addr)
                                        seg-reg
                                        :r
                                        inst-ac?
                                        x86))
       ((when flg0)
        (!!ms-fresh :src-rme-size-error flg0))

       ;; Write source operand to rAX.
       (x86 (!rgfi-size operand-size #.*rax* src 0 x86))

       ;; If there is a REP prefix, decrement rCX and leave the rIP unchanged,
       ;; so that we can (attempt to) repeat this instruction;
       ;; note that if we get here rCX is not 0, because we tested it above.
       ;; If there is no REP prefix, advance rIP to the next instructions.
       (x86 (if (equal group-1-prefix *repe*)
                (!rgfi-size counter/addr-size #.*rcx* (1- counter) rex-byte x86)
              (write-*ip proc-mode temp-rip x86)))

       ;; Update rSI.
       ((the (unsigned-byte 1) df) (flgi :df x86))
       ((the (signed-byte #.*max-linear-address-size+1*) src-addr)
        (case operand-size
          (1 (if (equal df 0)
                 (+ 1 (the (signed-byte #.*max-linear-address-size*) src-addr))
               (+ -1 (the (signed-byte #.*max-linear-address-size*) src-addr))))
          (2 (if (equal df 0)
                 (+ 2 (the (signed-byte #.*max-linear-address-size*) src-addr))
               (+ -2 (the (signed-byte #.*max-linear-address-size*) src-addr))))
          (4 (if (equal df 0)
                 (+ 4 (the (signed-byte #.*max-linear-address-size*) src-addr))
               (+ -4 (the (signed-byte #.*max-linear-address-size*) src-addr))))
          (otherwise
           (if (equal df 0)
               (+ 8 (the (signed-byte #.*max-linear-address-size*) src-addr))
             (+ -8 (the (signed-byte #.*max-linear-address-size*) src-addr))))))
       (x86 (case counter/addr-size
              (2 (!rgfi-size 2
                             #.*rsi*
                             (n16 (the
                                   (signed-byte
                                    #.*max-linear-address-size+1*)
                                   src-addr))
                             rex-byte
                             x86))
              (4 (!rgfi-size 4
                             #.*rsi*
                             (n32 (the
                                   (signed-byte
                                    #.*max-linear-address-size+1*)
                                   src-addr))
                             rex-byte
                             x86))
              (t (!rgfi #.*rsi*
                        (the (signed-byte
                              #.*max-linear-address-size+1*)
                             src-addr)
                        x86)))))

    x86))

;; ======================================================================
