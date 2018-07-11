; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
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

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
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

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
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

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'CALL #xE8 '(:nil nil) 'x86-call-E8-Op/En-M)

  :body

  (b* ((ctx 'x86-call-E8-Op/En-M)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 0 4) offset-size)
        (if (64-bit-modep x86)
            4 ; always 32 bits (rel32) -- 16 bits (rel16) not supported
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d (code-segment-descriptor-attributes-layout-slice
                      :d cs-attr)))
            ;; 16 or 32 bits (rel16 or rel32):
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       ;; AC is not done during code fetches. Fetching rel16 or rel32 from the
       ;; instruction stream still qualifies as a code fetch.
       ((mv flg0 (the (signed-byte 32) rel16/32) x86)
        (rime-size offset-size temp-rip *cs* :x nil x86))
       ((when flg0) (!!ms-fresh :rime-size-error flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size+1*) next-rip))
        (add-to-*ip temp-rip offset-size x86))
       ((when flg) (!!ms-fresh :rip-increment-error next-rip))

       (badlength? (check-instruction-length start-rip next-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg (the (signed-byte #.*max-linear-address-size*) call-rip))
        (add-to-*ip next-rip rel16/32 x86))
       ((when flg) (!!ms-fresh :call-rip-invalid call-rip))

       (rsp (read-*sp x86))
       ((the (integer 2 8) addr-size) (select-address-size nil x86))
       ((mv flg new-rsp) (add-to-*sp rsp (- addr-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :call flg)) ;; #SS(0)

       ((mv flg x86)
        ;; Note that instruction pointers are modeled as signed in 64-bit mode,
        ;; but unsigned in 32-bit mode.
        (if (64-bit-modep x86)
            (wime-size addr-size
                       (the (signed-byte #.*max-linear-address-size*) new-rsp)
                       *ss*
                       next-rip
                       (alignment-checking-enabled-p x86)
                       x86)
          (wme-size addr-size
                    (the (signed-byte #.*max-linear-address-size*) new-rsp)
                    *ss*
                    ;; the following coercions (N16 and N32) should not be
                    ;; necessary, but they make the guard proofs easier for now:
                    (if (= addr-size 2)
                        (n16 next-rip)
                      (n32 next-rip))
                    (alignment-checking-enabled-p x86)
                    x86)))
       ((when flg) (!!ms-fresh :stack-writing-error flg))

       ;; Update the rip to point to the called procedure.
       (x86 (write-*ip call-rip x86))
       ;; Decrement the stack pointer.
       (x86 (write-*sp new-rsp x86)))
      x86))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
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

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'CALL #xFF '(:reg 2)
                                    'x86-call-FF/2-Op/En-M)

  :body

  (b* ((ctx ' x86-call-FF/2-Op/En-M)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       ((the (integer 2 8) operand-size)
        (if (64-bit-modep x86)
            8 ; Intel manual, Mar'17, Volume 1, Section 6.3.7
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d (code-segment-descriptor-attributes-layout-slice
                      :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       ;; Note that the reg field serves as an opcode extension for
       ;; this instruction.  The reg field will always be 2 when this
       ;; function is called.
       (inst-ac? t)
       ((mv flg0
            call-rip
            (the (unsigned-byte 3) increment-rip-by)
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
                                                0 ;; No immediate operand
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) next-rip))
        (add-to-*ip temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error next-rip))

       (badlength? (check-instruction-length start-rip next-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Note that instruction pointers are modeled as signed in 64-bit mode,
       ;; but unsigned in 32-bit mode.
       (call-rip (if (64-bit-modep x86)
                     (i64 call-rip)
                   call-rip))
       ;; Ensure that the return address is canonical (for 64-bit mode) and
       ;; within code segment limits (for 32-bit mode). See pseudocode in Intel
       ;; manual.
       ((unless (if (64-bit-modep x86)
                    (canonical-address-p call-rip)
                  (b* ((cs-hidden (xr :seg-hidden *cs* x86))
                       (cs.limit (hidden-seg-reg-layout-slice :limit cs-hidden)))
                    (and (<= 0 call-rip) (<= call-rip cs.limit)))))
        (!!fault-fresh :gp 0 :bad-return-address call-rip)) ;; #GP(0)

       (rsp (read-*sp x86))
       ((the (integer 2 8) addr-size) (select-address-size nil x86))
       ((mv flg new-rsp) (add-to-*sp rsp (- addr-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :call flg)) ;; #SS(0)

       ;; Update the x86 state:
       ;; Push the return address on the stack.
       (check-alignment? (alignment-checking-enabled-p x86))
       ((mv flg x86)
        ;; Note that instruction pointers are modeled as signed in 64-bit mode,
        ;; but unsigned in 32-bit mode.
        (if (= operand-size 8)
            (wime-size operand-size rsp *ss* call-rip check-alignment? x86)
          (wme-size operand-size rsp *ss* call-rip check-alignment? x86)))
       ((when flg) (!!ms-fresh :stack-writing-error flg))
       ;; Update the rip to point to the called procedure.
       (x86 (write-*ip call-rip x86))
       ;; Decrement the stack pointer.
       (x86 (write-*sp new-rsp x86)))
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

;; In 32-bit mode, the operand size should be the size of the code address,
;; i.e. 32 bits if CS.D = 1 and 16 bits if CS.D = 0. Note that also in 64-bit
;; mode (see above) the operand size (64 bits) is equal to the size of the code
;; address (64 bits, even though in our model we only model the low 48 bits due
;; to the invariant of instruction pointers being canonical).

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-ret

  ;; Op/En: #xC2 iw: I:  Near return to calling procedure and pop imm16 bytes from
  ;;                     stack
  ;;        #xC3:    NP: Near return to calling procedure

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rime-size rml16 rme-size rme16) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'RET #xC2 '(:nil nil) 'x86-ret)
    (add-to-implemented-opcodes-table 'RET #xC3 '(:nil nil) 'x86-ret))

  :body

  (b* ((ctx 'x86-ret)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (rsp (read-*sp x86))

       ((the (integer 2 8) operand-size)
        (if (64-bit-modep x86)
            8
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1) 4 2))))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) new-rsp) x86)
        (if (equal opcode #xC3)
            (b* (((mv flg1 new-rsp)
                  (add-to-*sp rsp operand-size x86))
                 ((when flg1) (mv flg1 0 x86)))
              (mv nil new-rsp x86))
          ;; We don't do any alignment check below when fetching the
          ;; immediate operand; reading the immediate operand is done
          ;; during code fetching, where alignment checks aren't supposed
          ;; to be done (see Intel Manuals, Volume 3, Section 6.15,
          ;; Exception and Interrupt Reference, Interrupt 17 Alignment
          ;; Check Exception (#AC) for details).
          (b* (((mv flg1 (the (unsigned-byte 16) imm16) x86)
                (rme16 temp-rip *cs* :x nil x86))
               ((when flg1) (mv flg1 0 x86))
               ((mv flg1 new-rsp)
                (add-to-*sp rsp (+ operand-size imm16) x86))
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
            (rime-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil)
          (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil)))
       ((when flg)
        (cond
         ((and (consp flg) (eql (car flg) :non-canonical-address))
          (!!fault-fresh :ss 0 :riml64-error flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned rsp)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg))))

       ;; Ensure that the return address is canonical (for 64-bit mode) and
       ;; within code segment limits (for 32-bit mode). See pseudocode in Intel
       ;; manual.
       ((unless (if (64-bit-modep x86)
                    (canonical-address-p tos)
                  (b* ((cs-hidden (xr :seg-hidden *cs* x86))
                       (cs.limit (hidden-seg-reg-layout-slice :limit cs-hidden)))
                    (and (<= 0 tos) (<= tos cs.limit)))))
        (!!fault-fresh :gp 0 :bad-return-address tos)) ;; #GP(0)

       ;; Update the x86 state:

       ;; Increment the stack pointer.
       (x86 (write-*sp new-rsp x86))

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
  ;; RSP := RBP
  ;; rBP := Pop() (i.e. get bytes from the stack, also considering the
  ;; operand-size override prefix, and put them in rBP, and then
  ;; increment the stack pointer appropriately)

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'LEAVE #xC9 '(:nil nil) 'x86-leave)

  :body

  (b* ((ctx 'x86-leave)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p3 (equal #.*operand-size-override*
                  (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 2 8) pop-bytes)
        (if p3
            2
          8))
       (rbp (rgfi *rbp* x86))
       ((when (not (canonical-address-p rbp)))
        (!!ms-fresh :rbp-not-canonical rbp))
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac? (not (equal (logand rbp 7) 0))))
        (!!ms-fresh :memory-access-unaligned rbp))
       ((mv flg val x86)
        (rml-size pop-bytes
                 (the (signed-byte #.*max-linear-address-size*) rbp)
                 :r x86))
       ((when flg)
        (!!ms-fresh :rml-size-error flg))
       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
        (+ (the (signed-byte #.*max-linear-address-size*) rbp) pop-bytes))
       ((when (mbe :logic (not (canonical-address-p new-rsp))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               new-rsp))))
        (!!ms-fresh :invalid-rsp new-rsp))

       ;; We don't need to check for valid length for one-byte
       ;; instructions.  The length will be more than 15 only if
       ;; get-prefixes fetches 15 prefixes, and that error will be
       ;; caught in x86-fetch-decode-execute, that is, before control
       ;; reaches this function.


       ;; Update the x86 state:
       ;; We chose to write the value val into the register using !rgfi-size
       ;; rather than !rgfi since val is a n64p value and !rgfi expects an i64p
       ;; value.

       (x86 (!rgfi-size pop-bytes *rbp* val rex-byte x86))
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
