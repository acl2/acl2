; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, May - August 2023, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
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

(include-book "../decoding-and-spec-utils")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: CALL
;; ======================================================================

;; From Intel manual, Mar'17, Volume 1, Section 6.3.7:

;; In 64-bit mode, the operand size for all near branches (CALL, RET,
;; JCC, JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions
;; update the 64-bit RIP without the need for a REX operand-size
;; prefix.

;; The following aspects of near branches are controlled by the
;; effective operand size:
;;   Truncation of the size of the instruction pointer
;;   Size of a stack pop or push, due to a CALL or RET
;;   Size of a stack-pointer increment or decrement, due to a CALL or RET
;;   Indirect-branch operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits
;; regardless of operand size prefixes (operand size prefixes are
;; silently ignored). However, the displacement field for relative
;; branches is still limited to 32 bits and the address size for near
;; branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they
;; also impact the address calculation for memory indirect
;; branches. Such addresses are 64 bits by default; but they can be
;; overridden to 32 bits by an address size prefix.

(def-inst x86-call-E8-Op/En-M

  ;; Call near, displacement relative to the next instruction
  ;; Op/En: M
  ;; E8 cw (CALL rel16)
  ;; E8 cd (CALL rel32)
  ;; Note E8 cw (CALL rel16) is N.S. in 64-bit mode.

  ;; The address-size override prefix will not have any effect here
  ;; since we have no memory operands.

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08
                                         riml32
                                         rime-size-of-2-to-rime16
                                         rime-size-of-4-to-rime32
                                         select-address-size)
                                        ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (((the (integer 0 4) offset-size)
        (select-operand-size proc-mode nil rex-byte nil prefixes nil t t x86))

       ;; AC is not done during code fetches. Fetching rel16 or rel32 from the
       ;; instruction stream still qualifies as a code fetch.
       ((mv flg0 (the (signed-byte 32) rel16/32) x86)
        (rime-size-opt proc-mode offset-size temp-rip #.*cs* :x nil x86))
       ((when flg0) (!!ms-fresh :rime-size-opt-error flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size+1*) next-rip))
        (add-to-*ip proc-mode temp-rip offset-size x86))
       ((when flg) (!!ms-fresh :rip-increment-error next-rip))

       (badlength? (check-instruction-length start-rip next-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg (the (signed-byte #.*max-linear-address-size*) call-rip))
        (add-to-*ip proc-mode next-rip rel16/32 x86))
       ((when flg) (!!ms-fresh :call-rip-invalid call-rip))

       (rsp (read-*sp proc-mode x86))
       ((the (integer 2 8) addr-size) (select-address-size proc-mode nil x86))
       ((mv flg new-rsp) (add-to-*sp proc-mode rsp (- addr-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :call flg)) ;; #SS(0)

       ((mv flg x86)
        ;; Note that instruction pointers are modeled as signed in 64-bit mode,
        ;; but unsigned in 32-bit mode.
        (if (equal proc-mode #.*64-bit-mode*)
            (wime-size-opt
             #.*64-bit-mode* addr-size
             (the (signed-byte #.*max-linear-address-size*) new-rsp)
             #.*ss*
             next-rip
             (alignment-checking-enabled-p x86)
             x86)
          (wme-size-opt
           proc-mode addr-size
           (the (signed-byte #.*max-linear-address-size*) new-rsp)
           #.*ss*
           ;; the following coercions (N16 and N32) should not be
           ;; necessary, but they make the guard proofs easier for now:
           (if (= addr-size 2)
               (n16 next-rip)
             (n32 next-rip))
           (alignment-checking-enabled-p x86)
           x86)))
       ((when flg) (!!ms-fresh :stack-writing-error flg))

       ;; Update the rip to point to the called procedure.
       (x86 (write-*ip proc-mode call-rip x86))
       ;; Decrement the stack pointer.
       (x86 (write-*sp proc-mode new-rsp x86)))
      x86))

(def-inst x86-call-FF/2-Op/En-M

  ;; Call near, absolute indirect, address given in r/m16/32/64.
  ;; Op/En: M
  ;; FF/2 r/m16
  ;; FF/2 r/m32
  ;; FF/2 r/m64
  ;; Note that FF/2 r/m16 and r/m32 are N.E. in 64-bit mode.

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08
                                         riml32
                                         select-address-size)
                                        ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (integer 2 8) operand-size)
        (select-operand-size proc-mode nil rex-byte nil prefixes t t t x86))

       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; Note that the reg field serves as an opcode extension for
       ;; this instruction.  The reg field will always be 2 when this
       ;; function is called.
       (inst-ac? t)
       ((mv flg0
            call-rip
            (the (unsigned-byte 3) increment-rip-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         proc-mode #.*gpr-access* operand-size inst-ac?
         nil ;; Not a memory pointer operand
         seg-reg p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) next-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error next-rip))

       (badlength? (check-instruction-length start-rip next-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Note that instruction pointers are modeled as signed in 64-bit mode,
       ;; but unsigned in 32-bit mode.
       (call-rip (if (equal proc-mode #.*64-bit-mode*)
                     (i64 call-rip)
                   call-rip))
       ;; Ensure that the return address is canonical (for 64-bit mode) and
       ;; within code segment limits (for 32-bit mode). See pseudocode in Intel
       ;; manual.
       ((unless (if (equal proc-mode #.*64-bit-mode*)
                    (canonical-address-p call-rip)
                  (and (<= 0 call-rip)
                       (<= call-rip
                           (the (unsigned-byte 32)
                             (seg-hidden-limiti #.*cs* x86))))))
        (!!fault-fresh :gp 0 :bad-return-address call-rip)) ;; #GP(0)

       (rsp (read-*sp proc-mode x86))

       ;; The size of the RIP/EIP/IP is determined by
       ;; the processor mode and the CS.D bit (see READ-*IP).
       ;; It is not (necessarily) the result of SELECT-ADDRESS-SIZE,
       ;; which may be subject to address size overrides.
       (rip-size (case proc-mode
                   (#.*64-bit-mode* 8)
                   (#.*compatibility-mode*
                    (b* (((the (unsigned-byte 16) cs-attr)
                          (seg-hidden-attri #.*cs* x86))
                         (cs.d (code-segment-descriptor-attributesbits->d
                                cs-attr)))
                      (if (= cs.d 1) 4 2)))
                   (t 0))) ; other modes not implemented yet

       ((mv flg new-rsp) (add-to-*sp proc-mode rsp (- rip-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :call flg)) ;; #SS(0)

       ;; Update the x86 state:
       ;; Push the return address on the stack.
       (check-alignment? (alignment-checking-enabled-p x86))
       ((mv flg x86)
        ;; Note that instruction pointers are modeled as signed in 64-bit mode,
        ;; but unsigned in 32-bit mode.
        (case rip-size
          ;; Note that we need check-canonicity t only for rip-size = 8,
          ;; because we get this size only in 64-bit mode.
          (8 (wime-size-opt proc-mode
                            rip-size
                            new-rsp
                            #.*ss*
                            next-rip
                            check-alignment?
                            x86
                            :check-canonicity t))
          ;; It should be an invariant that, if rip-size = 4,
          ;; next-rip is 32 bits, but since at the moment
          ;; we don't have that invariant, we coerce next-rip.
          (4 (wme-size-opt proc-mode
                           rip-size
                           new-rsp
                           #.*ss*
                           (n32 next-rip)
                           check-alignment?
                           x86))
          (2 (wme-size-opt proc-mode
                           rip-size
                           new-rsp
                           #.*ss*
                           (n16 next-rip)
                           check-alignment?
                           x86))
          (t (mv :not-implemented x86))))
       ((when flg) (!!ms-fresh :stack-writing-error flg))
       ;; Update the rip to point to the called procedure.
       (x86 (write-*ip proc-mode call-rip x86))
       ;; Decrement the stack pointer.
       (x86 (write-*sp proc-mode new-rsp x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: RET
;; ======================================================================

;; From Intel manual, Mar'17, Volume 1, Section 6.3.7:

;; In 64-bit mode, the operand size for all near branches (CALL, RET,
;; JCC, JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions
;; update the 64-bit RIP without the need for a REX operand-size
;; prefix.

;; The following aspects of near branches are controlled by the
;; effective operand size:
;;   Truncation of the size of the instruction pointer
;;   Size of a stack pop or push, due to a CALL or RET
;;   Size of a stack-pointer increment or decrement, due to a CALL or RET
;;   Indirect-branch operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits
;; regardless of operand size prefixes (operand size prefixes are
;; silently ignored). However, the displacement field for relative
;; branches is still limited to 32 bits and the address size for near
;; branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they
;; also impact the address calculation for memory indirect
;; branches. Such addresses are 64 bits by default; but they can be
;; overridden to 32 bits by an address size prefix.

;; End of quoted text from the Intel manual.

;; In 32-bit mode, the operand size should be the size of the code address,
;; i.e. 32 bits if CS.D = 1 and 16 bits if CS.D = 0: in other words, the
;; operand size override prefix P3 should have no effect here. Thus, we pass 0
;; as the PREFIXES argument to SELECT-OPERAND-SIZE; note that this function
;; only accesses the P3 prefix out of all the prefixes, so passing 0 as the
;; prefixes has no adverse effect.

;; Note that also in 64-bit mode (see above) the operand size (64 bits) is
;; equal to the size of the code address (64 bits, even though in our model we
;; only model the low 48 bits due to the invariant of instruction pointers
;; being canonical).

(def-inst x86-ret

          ;; Op/En: #xC2 iw: I:  Near return to calling procedure and pop imm16 bytes from
          ;;                     stack
          ;;        #xC3:    NP: Near return to calling procedure
          ;;        #xCB:    ZO: Far return to calling procedure

          :parents (one-byte-opcodes)

          :guard-hints (("Goal" :in-theory (e/d (rime-size rme-size) ())))

          :returns (x86 x86p :hyp (x86p x86))

          :body

          (b* ((rsp (read-*sp proc-mode x86))

               ((the (integer 2 8) operand-size)
                (select-operand-size proc-mode nil rex-byte nil 0 t t t x86))

               ((mv flg (the (signed-byte #.*max-linear-address-size*) new-rsp) x86)
                (if (not (equal opcode #xC2))
                  (b* (((mv flg1 new-rsp)
                        (add-to-*sp proc-mode rsp operand-size x86))
                       ((when flg1) (mv flg1 0 x86)))
                      (mv nil new-rsp x86))
                  ;; We don't do any alignment check below when fetching the
                  ;; immediate operand; reading the immediate operand is done
                  ;; during code fetching, where alignment checks aren't supposed
                  ;; to be done (see Intel Manuals, Volume 3, Section 6.15,
                  ;; Exception and Interrupt Reference, Interrupt 17 Alignment
                  ;; Check Exception (#AC) for details).
                  (b* (((mv flg1 (the (unsigned-byte 16) imm16) x86)
                        (rme16-opt proc-mode temp-rip #.*cs* :x nil x86))
                       ((when flg1) (mv flg1 0 x86))
                       ((mv flg1 new-rsp)
                        (add-to-*sp proc-mode rsp (+ operand-size imm16) x86))
                       ((when flg1) (mv flg1 0 x86)))
                      (mv nil new-rsp x86))))
               ((when flg)
                (!!ms-fresh :imm-rml16-error flg))

               ;; For #xC3: We don't need to check for valid length for
               ;; one-byte instructions.  The length will be more than 15 only
               ;; if get-prefixes fetches 15 prefixes, and that error will be
               ;; caught in x86-fetch-decode-execute, that is, before control
               ;; reaches this function.
               ;; For #xC2: We add 2 to temp-rip to account for imm16.
               (badlength? (and (eql opcode #xC2)
                                (check-instruction-length start-rip temp-rip 2)))
               ((when badlength?)
                (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

               ;; Note that instruction pointers are modeled as signed in 64-bit mode,
               ;; but unsigned in 32-bit mode.
               (check-alignment? (alignment-checking-enabled-p x86))
               ((mv flg (the (signed-byte 64) tos) x86)
                (if (= operand-size 8)
                  (rime-size-opt
                    ;; Note that we need check-canonicity t only for operand-size = 8,
                    ;; because we get this size only in 64-bit mode.
                    proc-mode operand-size rsp #.*ss* :r check-alignment? x86
                    :mem-ptr? nil
                    :check-canonicity t)
                  (rme-size-opt
                    proc-mode operand-size rsp #.*ss* :r check-alignment? x86
                    :mem-ptr? nil)))
               ((when flg)
                (cond
                  ((and (consp flg) (eql (car flg) :non-canonical-address))
                   (!!fault-fresh :ss 0 :riml64-error flg)) ;; #SS(0)
                  ((and (consp flg) (eql (car flg) :unaligned-linear-address))
                   (!!fault-fresh :ac 0 :memory-access-unaligned rsp)) ;; #AC(0)
                  (t ;; Unclassified error!
                    (!!fault-fresh flg))))

               ;; Ensure that the return address is canonical (for 64-bit mode) and
               ;; within code segment limits (for 32-bit mode near return). See pseudocode in Intel
               ;; manual.
               ((unless (if (equal proc-mode #.*64-bit-mode*)
                          (canonical-address-p tos)
                          (b* (((the (unsigned-byte 32) cs.limit)
                                (seg-hidden-limiti #.*cs* x86)))
                              (or (equal opcode #xCB)
                                  (and (<= 0 tos) (<= tos cs.limit))))))
                (!!fault-fresh :gp 0 :bad-return-address tos)) ;; #GP(0)

               ;; Update the x86 state:

               ;; Handle the far return case
               ((mv new-rsp x86)
                (if (equal opcode #xCB)
                  (b* (((mv flg cs-selector x86)
                        (rme-size-opt
                          proc-mode operand-size new-rsp #.*ss* :r check-alignment? x86
                          :mem-ptr? nil))
                       ((when flg)
                        (b* ((x86 (cond
                                    ((and (consp flg) (eql (car flg) :non-canonical-address))
                                     (!!fault-fresh :ss 0 :riml64-error flg)) ;; #SS(0)
                                    ((and (consp flg) (eql (car flg) :unaligned-linear-address))
                                     (!!fault-fresh :ac 0 :memory-access-unaligned rsp)) ;; #AC(0)
                                    (t ;; Unclassified error!
                                      (!!fault-fresh flg)))))
                            (mv 0 x86)))
                       (cs-selector (loghead 16 cs-selector))
                       ((mv flg cs-descriptor x86)
                        (get-segment-descriptor #.*cs* cs-selector x86))
                       ((when flg)
                        (b* (((when (equal flg t))
                              (b* ((x86 (!!ms-fresh :get-segment-descriptor)))
                                  (mv 0 x86)))
                             (x86 (!!fault-fresh (car flg) (cadr flg) (caddr flg))))
                            (mv 0 x86)))
                       (x86 (load-segment-reg #.*cs* cs-selector cs-descriptor x86))
                       ((mv flg new-rsp)
                        (add-to-*sp proc-mode new-rsp operand-size x86))
                       ((when flg)
                        (b* ((x86 (!!fault-fresh :ss 0 :pop flg)))
                            (mv 0 x86))))
                      (mv new-rsp x86))
                  (mv new-rsp x86)))
               ((when (or (fault x86)
                          (ms x86))) x86)

               ;; Increment the stack pointer.
               (x86 (write-*sp proc-mode new-rsp x86))

               ;; Update the rip to point to the return address.
               ;; The pseudocode for RET in Intel manual, Mar'17, Volume 2
               ;; says that a 16-bit return instruction pointer
               ;; should be zero-extended and stored into EIP.
               ;; Thus, we do not use WRITE-*IP here,
               ;; which has a different treatment for 16-bit instruction pointers.
               ;; This seems inconsistent, and it is an ambiguous aspect
               ;; of the Intel and AMD manuals.
               (x86 (!rip (the (signed-byte #.*max-linear-address-size*) tos) x86)))

              x86))

;; ======================================================================
;; INSTRUCTION: LEAVE
;; ======================================================================

(def-inst x86-leave

  ;; The LEAVE instruction releases the stack frame set up by an
  ;; earlier ENTER instruction.

  ;; Op/En: NP
  ;; C9
  ;; rSP := rBP
  ;; rBP := Pop() (i.e. get bytes from the stack, also considering the
  ;; operand-size override prefix, and put them in rBP, and then
  ;; increment the stack pointer appropriately)

  ;; According to the pseudocode in Intel manual, Jun 2026, Volume 2A, LEAVE
  ;; specification, the size of rSP and rBP in the assignment rSP := rBP is
  ;; determined by StackAddressSize, while the size of rBP in the assignment
  ;; rBP := Pop() is determined by OperandSize. That is, the stack address
  ;; size determines the width at which rBP is used as an address: it is the
  ;; new value of rSP, and also the address from which the pop reads. The
  ;; operand size determines the width of the data transfer into rBP: the
  ;; number of bytes popped, and the slice of rBP that receives them. The two
  ;; sizes may differ: e.g. LEAVE with a 66H prefix in 64-bit mode pops 16
  ;; bits of data from the address in the full 64-bit rBP. This reading of
  ;; the pseudocode is confirmed by the Description section of the ENTER
  ;; specification, which says that the OperandSize attribute determines "the
  ;; data being transferred from SP/ESP/RSP register into the BP/EBP/RBP
  ;; register" (in ENTER, the transfer opposite to LEAVE's), and which makes
  ;; software responsible for ensuring that, after a 66H ENTER (whose rBP
  ;; write updates only BP, leaving the high bits of rBP stale), the value of
  ;; rBP "remains a valid address in the stack" so that a 66H LEAVE works:
  ;; this implies that LEAVE uses the full stack-address-size-wide rBP as the
  ;; address of the pop. Thus, below we read rBP at the stack address size,
  ;; and we use the operand size for the pop's data.

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (;;riml08
                                         ;;riml32
                                         rme-size-of-2-to-rme16
                                         rme-size-of-4-to-rme32
                                         rme-size-of-8-to-rme64
                                         rme16
                                         rme32
                                         rme64)
                                        ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (((the (integer 2 8) operand-size)
        (select-operand-size proc-mode nil rex-byte nil prefixes t t nil x86))

       ;; We read rBP at the stack address size (not the operand size),
       ;; because this value is used as an address, namely the new value of
       ;; rSP, from which the pop below reads; see the comments at the
       ;; beginning of this function.
       ((the (integer 2 8) stack-address-size)
        (select-stack-address-size proc-mode x86))
       (rbp/ebp/bp (rgfi-size stack-address-size *rbp* 0 x86))

       ;; RBP/EBP/BP is the new value of RSP/ESP/SP now, but we cannot write it
       ;; into the state yet. However, we use it, below, to pop the new value
       ;; of RBP/EBP/BP: as we do that, we implicitly check it to be canonical
       ;; (in 64-bit mode) or within the stack segment limits (in 32-bit mode),
       ;; so there's no need to make these checks explicitly here.

       (inst-ac? (alignment-checking-enabled-p x86))
       ((mv flg val x86) (rme-size-opt
                          proc-mode
                          operand-size
                          (the (signed-byte 64) (i64 rbp/ebp/bp))
                          #.*ss*
                          :r
                          inst-ac?
                          x86
                          :mem-ptr? nil
                          :check-canonicity t))
       ((when flg) (!!fault-fresh :ss 0 :pop-error flg)) ;; #SS(0)

       ((mv flg (the (signed-byte 64) new-rsp))
        (add-to-*sp proc-mode (i64 rbp/ebp/bp) operand-size x86))
       ((when flg) (!!ms-fresh :invalid-rsp new-rsp))

       ;; We don't need to check for valid length for one-byte
       ;; instructions.  The length will be more than 15 only if
       ;; get-prefixes fetches 15 prefixes, and that error will be
       ;; caught in x86-fetch-decode-execute, that is, before control
       ;; reaches this function.

       ;; Update the x86 state:
       ;; We chose to write the value val into the register using !rgfi-size
       ;; rather than !rgfi since val is a n64p value and !rgfi expects an i64p
       ;; value.

       (x86 (!rgfi-size operand-size *rbp* val rex-byte x86))
       (x86 (write-*sp proc-mode new-rsp x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: ENTER
;; ======================================================================

(define x86-enter-copy-nested-frame-pointers
  ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
   (count            :type (integer 0 31))
   (operand-size     :type (integer 2 8))
   (frame-ptr        :type (signed-byte 64))
   (rsp              :type (signed-byte 64))
   (check-alignment? booleanp)
   x86)
  :guard (member operand-size '(2 4 8))
  :returns (mv flg
               (new-rsp i64p :hyp (i64p rsp))
               (x86 x86p :hyp (x86p x86)))
  :parents (x86-enter)
  :short "Copy the nested frame pointers onto the stack,
          as part of the ENTER instruction with nesting level greater than 0."
  :long
  "<p>
   This is the loop in the pseudocode of the ENTER instruction
   (Intel manual, Jun 2026, Volume 2A):
   when the nesting level is greater than 0,
   after pushing the (old) frame pointer rBP,
   @('NestingLevel - 1') further frame pointers are copied onto the stack,
   by repeatedly decrementing @('frame-ptr') (initially rBP)
   and reading the frame pointer at that stack address.
   The @('count') argument is @('NestingLevel - 1'),
   i.e. the number of frame pointers still to be copied.
   The @('rsp') argument is the running stack pointer,
   which is decremented and written to on each iteration.
   </p>
   <p>
   Per the ENTER specification, the operand size is
   the size of each frame pointer copied by the loop,
   i.e. the size of the data read and written by each iteration,
   and thus also the amount by which
   @('frame-ptr') and @('rsp') are decremented.
   </p>"
  (if (mbe :logic (zp count) :exec (eql count 0))
      (mv nil (the (signed-byte 64) rsp) x86)
    (b* ( ;; frame-ptr := frame-ptr - operand-size
         ((mv flg (the (signed-byte 64) frame-ptr))
          (add-to-*sp proc-mode frame-ptr (- operand-size) x86))
         ((when flg) (mv flg 0 x86))
         ;; read the frame pointer at [frame-ptr]
         ((mv flg val x86) (rme-size-opt proc-mode
                                         operand-size
                                         frame-ptr
                                         #.*ss*
                                         :r
                                         check-alignment?
                                         x86
                                         :mem-ptr? nil))
         ((when flg) (mv flg 0 x86))
         ;; push it, i.e. rsp := rsp - operand-size and [rsp] := val
         ((mv flg (the (signed-byte 64) rsp))
          (add-to-*sp proc-mode rsp (- operand-size) x86))
         ((when flg) (mv flg 0 x86))
         ((mv flg x86) (wme-size-opt proc-mode
                                     operand-size
                                     rsp
                                     #.*ss*
                                     val
                                     check-alignment?
                                     x86
                                     :mem-ptr? nil))
         ((when flg) (mv flg 0 x86)))
      (x86-enter-copy-nested-frame-pointers proc-mode
                                            (- count 1)
                                            operand-size
                                            frame-ptr
                                            rsp
                                            check-alignment?
                                            x86)))
  :measure (nfix count)
  :guard-hints (("Goal"
                 :in-theory (e/d (rme-size-of-2-to-rme16
                                  rme-size-of-4-to-rme32
                                  rme-size-of-8-to-rme64)
                                 ())
                 :cases ((eql operand-size 2)
                         (eql operand-size 4)
                         (eql operand-size 8))))

  ///

  ;; The returned stack pointer is a 64-bit signed integer.  We generate the
  ;; type-prescription and linear rules (in addition to the rewrite rule that
  ;; :RETURNS provides), so that the guards of the caller (X86-ENTER), which
  ;; passes the returned stack pointer to operations such as ADD-TO-*SP, can be
  ;; verified.
  (defthm-signed-byte-p
    signed-byte-p-64-of-mv-nth-1-x86-enter-copy-nested-frame-pointers
    :hyp (i64p rsp)
    :bound 64
    :concl (mv-nth 1 (x86-enter-copy-nested-frame-pointers proc-mode
                                                           count
                                                           operand-size
                                                           frame-ptr
                                                           rsp
                                                           check-alignment?
                                                           x86))
    :gen-type t
    :gen-linear t
    :hints (("Goal"
             :induct t
             :in-theory (enable x86-enter-copy-nested-frame-pointers)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-enter

  ;; The ENTER instruction creates a stack frame for a procedure,
  ;; which is later released by the LEAVE instruction (see X86-LEAVE).

  ;; Op/En: II
  ;; C8 iw ib   ENTER imm16, imm8
  ;; imm16 (the first operand) is the number of bytes reserved on the stack
  ;; for the local variables of the procedure; imm8 (the second operand) is
  ;; the lexical nesting level, whose low 5 bits are used (i.e. it is taken
  ;; modulo 32).

  ;; See the pseudocode in the Intel manual, Jun 2026, Volume 2A, ENTER
  ;; specification, as well as the helper function
  ;; X86-ENTER-COPY-NESTED-FRAME-POINTERS above.

  ;; rBP is used at two different widths in this instruction (cf. the
  ;; comments in X86-LEAVE about the roles of the operand size and of the
  ;; stack address size). As data, rBP is operand-size wide: the Description
  ;; section of the ENTER specification says that the OperandSize attribute
  ;; determines the size of each frame pointer copied onto the stack, and
  ;; "the data being transferred from SP/ESP/RSP register into the BP/EBP/RBP
  ;; register"; accordingly, Push(rBP) below pushes the operand-size-wide
  ;; rBP, and rBP := FrameTemp writes the low operand-size-wide part of
  ;; FrameTemp into rBP. As an address, rBP is stack-address-size wide: the
  ;; loop in the pseudocode decrements RBP, EBP, or BP according to
  ;; StackSize (notably, the full RBP when StackSize = 64 and OperandSize =
  ;; 16); accordingly, the base address from which the nested frame pointers
  ;; are copied below is the stack-address-size-wide rBP.

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (rme-size-of-2-to-rme16
                                         rme-size-of-4-to-rme32
                                         rme-size-of-8-to-rme64
                                         rme64)
                                        ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (((the (integer 2 8) operand-size)
        (select-operand-size proc-mode nil rex-byte nil prefixes t t nil x86))

       ;; Read the two immediate operands:
       ;; the allocation size (imm16) and the nesting level (imm8).
       ;; These are fetched from the instruction stream, so, like other code
       ;; fetches, no alignment checking is done here.

       ((mv flg (the (unsigned-byte 16) alloc-size) x86)
        (rme16-opt proc-mode temp-rip #.*cs* :x nil x86))
       ((when flg) (!!ms-fresh :alloc-size-read-error flg))
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 2 x86))
       ((when flg)
        (!!fault-fresh :gp 0 :temp-rip-not-canonical temp-rip)) ;; #GP(0)

       ((mv flg (the (unsigned-byte 8) nesting-byte) x86)
        (rme08-opt proc-mode temp-rip #.*cs* :x x86))
       ((when flg) (!!ms-fresh :nesting-level-read-error flg))
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg)
        (!!fault-fresh :gp 0 :temp-rip-not-canonical temp-rip)) ;; #GP(0)

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; NestingLevel := imm8 MOD 32.
       ((the (integer 0 31) nesting-level) (loghead 5 nesting-byte))

       (check-alignment? (alignment-checking-enabled-p x86))

       ;; Push rBP. The value pushed is the operand-size-wide rBP;
       ;; see the comments at the beginning of this function.
       ((the (unsigned-byte 64) rbp) (rgfi-size operand-size *rbp* 0 x86))
       (rsp (read-*sp proc-mode x86))
       ((mv flg (the (signed-byte 64) rsp))
        (add-to-*sp proc-mode rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push-rbp flg)) ;; #SS(0)
       ((mv flg x86) (wme-size-opt proc-mode
                                   operand-size
                                   rsp
                                   #.*ss*
                                   rbp
                                   check-alignment?
                                   x86
                                   :mem-ptr? nil))
       ;; The COND below is analogous to the one after the nesting block
       ;; further down (see the comment there about the possible errors),
       ;; with two differences:
       ;; the #SS case omits the error tags :NON-CANONICAL-STACK-ADDRESS
       ;; and :OUT-OF-SEGMENT-STACK-ADDRESS,
       ;; which can only arise from ADD-TO-*SP,
       ;; whose failure for this push of rBP
       ;; is already mapped to #SS just above;
       ;; the #SS case also omits the error symbols RML16 etc.,
       ;; which can only arise from reads, while this is a write.
       ((when flg)
        (cond
         ((or (and (consp flg) (eql (car flg) :segment-limit-fail))
              (member-eq flg '(wml16 wml32 wml64)))
          (!!fault-fresh :ss 0 :stack-writing-error flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned flg)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!ms-fresh :stack-writing-error flg))))

       ;; FrameTemp := rSP, i.e. the stack pointer just after pushing rBP.
       ((the (signed-byte 64) frame-temp) rsp)

       ;; If NestingLevel > 0, copy the NestingLevel - 1 nested frame pointers
       ;; onto the stack (see X86-ENTER-COPY-NESTED-FRAME-POINTERS) and then
       ;; push FrameTemp.  If NestingLevel = 0, none of this is done: the
       ;; pseudocode in the Intel manual jumps to the CONTINUE label below.
       ((mv flg (the (signed-byte 64) rsp) x86)
        (if (eql nesting-level 0)
            (mv nil rsp x86)
          (b* (;; The base address from which the nested frame pointers are
               ;; copied is the stack-address-size-wide rBP;
               ;; see the comments at the beginning of this function.
               ((the (integer 2 8) stack-address-size)
                (select-stack-address-size proc-mode x86))
               ((the (signed-byte 64) frame-ptr)
                (i64 (rgfi-size stack-address-size *rbp* 0 x86)))
               ((mv flg (the (signed-byte 64) rsp) x86)
                (x86-enter-copy-nested-frame-pointers proc-mode
                                                      (1- nesting-level)
                                                      operand-size
                                                      frame-ptr
                                                      rsp
                                                      check-alignment?
                                                      x86))
               ((when flg) (mv flg rsp x86))
               ;; Push FrameTemp.
               ((mv flg (the (signed-byte 64) rsp))
                (add-to-*sp proc-mode rsp (- operand-size) x86))
               ((when flg) (mv flg rsp x86))
               ((mv flg x86) (wme-size-opt proc-mode
                                           operand-size
                                           rsp
                                           #.*ss*
                                           (loghead (ash operand-size 3)
                                                    frame-temp)
                                           check-alignment?
                                           x86
                                           :mem-ptr? nil))
               ((when flg) (mv flg rsp x86)))
            (mv nil rsp x86))))
       ;; In the COND below:
       ;; the error tags :NON-CANONICAL-STACK-ADDRESS
       ;; and :OUT-OF-SEGMENT-STACK-ADDRESS come from ADD-TO-*SP;
       ;; the error tag :SEGMENT-LIMIT-FAIL comes from EA-TO-LA
       ;; (via RME-SIZE and WME-SIZE), in 32-bit mode,
       ;; for an access that starts within the stack segment limits
       ;; but ends past them;
       ;; the error symbols RML16 etc. and WML16 etc.
       ;; come from the functions with those names
       ;; (via RME-SIZE and WME-SIZE), in 64-bit mode,
       ;; for an access that starts at a canonical address
       ;; but ends past the canonical address space.
       ;; The last two kinds of errors are possible because ADD-TO-*SP
       ;; only checks the start address of an access.
       ;; All the aforementioned errors are stack faults (#SS);
       ;; an :UNALIGNED-LINEAR-ADDRESS error from RME-SIZE or WME-SIZE
       ;; is instead an alignment check fault (#AC).
       ((when flg)
        (cond
         ((or (and (consp flg)
                   (or (eql (car flg) :non-canonical-stack-address)
                       (eql (car flg) :out-of-segment-stack-address)
                       (eql (car flg) :segment-limit-fail)))
              (member-eq flg '(rml16 rml32 rml64 wml16 wml32 wml64)))
          (!!fault-fresh :ss 0 :enter-stack-error flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned flg)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!ms-fresh :enter-error flg))))

       ;; Update the x86 state:

       ;; Calculate rSP - AllocSize.
       ;; We calculate the new rSP, but we write it a few lines below.
       ;; We calculate this before writing to rBP because
       ;; this calculation can cause a #SS fault,
       ;; and according to Intel manual, Jun 2026, Vol. 3, Section 7.5,
       ;; a fault must leave the processor state
       ;; in the same state as at the start of
       ;; the instruction that caused the fault;
       ;; Table 7-1 in Chapter 7 classifies #SS as a fault.
       ((mv flg (the (signed-byte 64) rsp))
        (add-to-*sp proc-mode rsp (- alloc-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :alloc-error flg)) ;; #SS(0)

       ;; rBP := FrameTemp.
       ;; We use !rgfi-size (rather than !rgfi) since it expects an unsigned
       ;; value, so we take the low bits of FrameTemp accordingly.
       (x86 (!rgfi-size operand-size *rbp*
                        (loghead (ash operand-size 3)
                                 frame-temp)
                        rex-byte x86))
       ;; rSP := rSP - AllocSize.
       ;; The calculation was done above, for the reason explained above.
       (x86 (write-*sp proc-mode rsp x86))

       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))

;; ======================================================================
