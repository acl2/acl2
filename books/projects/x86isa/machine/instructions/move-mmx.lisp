; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2026, Kestrel Technology LLC
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
; Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils" :ttags ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; MOVQ

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-movq-to-mmx/mem

  :parents (two-byte-opcodes)

  :short "Move quadword from register to register or memory (MMX variant)."

  :long
  "<code>
   NP 0F 7F /r    MOVQ mm/m64, mm
   </code>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The source operand (Operand 2 in the Intel manual)
       ;; is the MMX register specified in Reg.
       ;; Since there are only 8 MMX registers, the REX byte is not used.
       ((the (unsigned-byte 64) src) (mmx reg x86))

       ;; The destination operand (Operand 1 in the Intel manual)
       ;; is the MMX register, or memory operand, specified in Mod and R/M.
       ((mv flg0
            (the (signed-byte 64) addr)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (if (int= mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr proc-mode p4? temp-rip rex-byte r/m mod sib
                              0 ;; No immediate operand
                              x86)))
       ((when flg0)
        (!!ms-fresh :x86-effective-addr-error flg0))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Store the value into the destination.
       (inst-ac? t)
       ((mv flg1 x86) (x86-operand-to-mmx/mem proc-mode
                                              inst-ac?
                                              src
                                              seg-reg
                                              addr
                                              r/m
                                              mod
                                              x86))
       ((when flg1) (!!ms-fresh :x86-operand-to-xmm/mem flg1))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-movq-from-mmx/mem

  :parents (two-byte-opcodes)

  :short "Move quadword from register or memory to register (MMX variant)."

  :long
  "<code>
   NP 0F 6F /r    MOVQ mm, mm/m64
   </code>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The source operand (Operand 2 in the Intel manual)
       ;; is the MMX register, or memory operand, specified in Mod and R/M.
       (inst-ac? t)
       ((mv flg0
            src
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (if (int= mod #b11)
            (mv nil (mmx r/m x86) 0 0 x86)
          (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                 #.*gpr-access* ; irrelevant
                                                 8
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

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Store the value into the destination.
       ;; The destination operand (Operand 1 in the Intel manual)
       ;; is the MMX register specified in Reg.
       ;; Since there are only 8 MMX registers, the REX byte is not used.
       (x86 (!mmx reg src x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; MOVD/MOVQ

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-movd/movq-to-mmx

  :parents (two-byte-opcodes)

  :short "Move doubleword / move quadword
          from memory or a general-purpose register to an MMX register."

  :long
  "<code>
   NP         0F 6E /r    MOVD mm, r/m32
   NP REX.W + 0F 6E /r    MOVQ mm, r/m64
   </code>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is 32 or 64 bits, based on REX.W.
       ((the (integer 4 8) operand-size)
        (if (logbitp #.*w* rex-byte)
            8
          4))

       ;; The source operand (Operand 2 in the Intel manual, Op/En A)
       ;; is the general-purpose register, or memory operans,
       ;; specified in Mod and R/M.
       (inst-ac? t)
       ((mv flg0 src (the (unsigned-byte 3) increment-RIP-by) ?addr x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               #.*gpr-access*
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

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Store the value into the destination.
       ;; The destination operand (Operand 1 in the Intel manual, Op/En A)
       ;; is the MMX register specified in Reg.
       ;; If the operand size is 32 bits, then src is 32 bits,
       ;; and when we store it into the register
       ;; we implicitly zero-extend it, as required.
       (x86 (!mmx reg src x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-movd/movq-from-mmx

  :parents (two-byte-opcodes)

  :short "Move doubleword / move quadword
          from a MMX register to memory or a general-purpose register."

  :long
  "<code>
   NP         0F 7E /r    MOVD r/m32, mm
   NP REX.W + 0F 7E /r    MOVQ r/m64, mm
   </code>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is 32 or 64 bits, based on REX.W.
       ((the (integer 4 8) operand-size)
        (if (logbitp #.*w* rex-byte)
            8
          4))

       ;; The source operand (Operand 2 in the Intel manual, Op/En B)
       ;; is the MMX register specified in Reg.
       ;; If the operand size is 32 bits, we keep the low 32 bits.
       (src (if (= operand-size 4)
                (loghead 32 (mmx reg x86))
              (mmx reg x86)))

       ;; The destination operand (Operand 1 in the Intel manual, Op/En B)
       ;; is the general-purpose register, or memory operand,
       ;; specified in Mod and R/M.
       ;; We obtain the memory address, if the operand is in memory.
       ((mv flg0
            (the (signed-byte 64) addr)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr proc-mode p4? temp-rip rex-byte r/m mod sib
                              0 ;; No immediate operand
                              x86)))
       ((when flg0)
        (!!ms-fresh :x86-effective-addr-error flg0))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Store the value into the destination.
       (inst-ac? t)
       ((mv flg1 x86) (x86-operand-to-reg/mem proc-mode
                                              operand-size
                                              inst-ac?
                                              nil ; not a memory pointer
                                              src
                                              seg-reg
                                              addr
                                              rex-byte
                                              r/m
                                              mod
                                              x86))
       ((when flg1) (!!ms-fresh :x86-operand-to-reg/mem flg1))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))
