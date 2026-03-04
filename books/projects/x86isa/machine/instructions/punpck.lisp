; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2024, Yahya Sohail
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
; Yahya Sohail        <yahya@yahyasohail.com>
; Contributing Author(s):
; Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils" :ttags (:undef-flg))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define punpckl ((result-width natp)
                 (el-width posp)
                 (a natp)
                 (b natp))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  :guard (equal (mod result-width (* 2 el-width)) 0)
  :returns (result (unsigned-byte-p result-width result)
                   :hyp (and (natp result-width)
                             (<= (* 2 (pos-fix el-width)) result-width)
                             (equal (mod result-width
                                         (* 2 (pos-fix el-width))) 0))
                   :hints
                   (("Goal"
                     :in-theory (disable unsigned-byte-p
                                         acl2::prefer-positive-addends-<))))
  :measure (nfix result-width)
  (b* ((result-width (nfix result-width))
       (el-width (pos-fix el-width))
       (a (nfix a))
       (b (nfix b))
       ((when (zp result-width)) 0))
    (logapp el-width a
            (logapp el-width b
                    (punpckl (- result-width (* 2 el-width)) el-width
                             (logtail el-width a) (logtail el-width b))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-punpckl-mmx

  :parents (two-byte-opcodes)

  :short "Unpack low data (MMX variants)."

  :long
  "<code>
  NP 0F 60 /r    PUNPCKLBW mm, mm/m32
  NP 0F 61 /r    PUNPCKLWD mm, mm/m32
  NP 0F 62 /r    PUNPCKLDQ mm, mm/m32
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 64 bits, i.e. 8 bytes.
       (operand-size 8)

       ;; The first source operand (Operand 1 in the Intel manual, Op/En A)
       ;; is the MMX register specified in Reg.
       ;; This is also the destination operand,
       ;; and thus we obtain the index for later use.
       ;; Since there are only 8 MMX registers, the REX byte is not used.
       ;; We only keep the low 32 bits.
       ((the (unsigned-byte 4) src1/dst-index) reg)
       ((the (unsigned-byte 64) src1) (mmx src1/dst-index x86))
       ((the (unsigned-byte 32) src1) (loghead 32 src1))

       ;; The second source operand (Operand 2 in the Intel manual, Op/En A)
       ;; is the MMX register, or memory operand, specified in Mod and R/M.
       ;; But for a memory operand we must only read 32 bits (see Intel manual),
       ;; so we case-split based on Mod;
       ;; note that x86-operand-from-modr/m-and-sib-bytes is called
       ;; only for a memory operand, which justifies the operand size.
       (inst-ac? t) ; Intel Manual Volume 2 Table 2-21 (Dec 2023)
       ((mv flg
            (the (unsigned-byte 32) src2)
            (the (integer 0 4) increment-rip-by)
            ?addr
            x86)
        (if (= mod #b11) ; register
            (b* (((the (unsigned-byte 64) src2) (mmx r/m x86)))
              (mv nil
                  (the (unsigned-byte 32) (loghead 32 src2))
                  0 ; increment-rip-by
                  0 ; addr
                  x86))
          ;; The following call is performed only if Mod is not 11,
          ;; and thus the exact register access parameter is irrelevant,
          ;; as noted in the comment below.
          ;; We use *gpr-access* instead of *mmx-access*
          ;; so we can use (in the guard proof) the theorem saying that
          ;; this function returns a value of the given operand size.
          (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                 #.*gpr-access* ; irrelevant
                                                 4 ; operand-size
                                                 inst-ac?
                                                 nil ; not a memory operand
                                                 seg-reg
                                                 p4?
                                                 temp-rip
                                                 rex-byte
                                                 r/m
                                                 mod
                                                 sib
                                                 0 ; no immediate operand
                                                 x86)))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result.
       (result (case opcode
                 (#x60 (punpckl (* 8 operand-size) 08 src1 src2))
                 (#x61 (punpckl (* 8 operand-size) 16 src1 src2))
                 (#x62 (punpckl (* 8 operand-size) 32 src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!mmx src1/dst-index result x86))
       (x86 (mmx-instruction-updates x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-punpckh-mmx

  :parents (two-byte-opcodes)

  :short "Unpack high data (MMX variants)."

  :long
  "<code>
  NP 0F 60 /r    PUNPCKHBW mm, mm/m64
  NP 0F 61 /r    PUNPCKHWD mm, mm/m64
  NP 0F 62 /r    PUNPCKHDQ mm, mm/m64
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 64 bits, i.e. 8 bytes.
       (operand-size 8)

       ;; The first source operand (Operand 1 in the Intel manual, Op/En A)
       ;; is the MMX register specified in Reg.
       ;; This is also the destination operand,
       ;; and thus we obtain the index for later use.
       ;; Since there are only 8 MMX registers, the REX byte is not used.
       ;; We only keep the high 32 bits.
       ((the (unsigned-byte 4) src1/dst-index) reg)
       ((the (unsigned-byte 64) src1) (mmx src1/dst-index x86))
       ((the (unsigned-byte 32) src1) (logtail 32 src1))

       ;; The second source operand (Operand 2 in the Intel manual, Op/En A)
       ;; is the MMX register, or memory operand, specified in Mod and R/M.
       ;; Unlike the PUNPCKL* instructions, 64 bits are read from memory.
       ;; We keep the hight 32 bits from the register or memory.
       (inst-ac? t) ; Intel Manual Volume 2 Table 2-21 (Dec 2023)
       ((mv flg
            (the (unsigned-byte 64) src2)
            (the (integer 0 4) increment-rip-by)
            ?addr
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               #.*mmx-access*
                                               operand-size
                                               inst-ac?
                                               nil ; not a memory operand
                                               seg-reg
                                               p4?
                                               temp-rip
                                               rex-byte
                                               r/m
                                               mod
                                               sib
                                               0 ; no immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))
       ((the (unsigned-byte 32) src2) (logtail 32 src2))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result.
       ;; Since we already shifted src1 and src2, so the high order bytes are
       ;; now lower order bytes, we can use punpckl.
       (result (case opcode
                 (#x68 (punpckl (* 8 operand-size) 08 src1 src2))
                 (#x69 (punpckl (* 8 operand-size) 16 src1 src2))
                 (#x6A (punpckl (* 8 operand-size) 32 src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!mmx src1/dst-index result x86))
       (x86 (mmx-instruction-updates x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-punpckl-sse

  :parents (two-byte-opcodes)

  :short "Unpack low data (SSE variants)."

  :long
  "<code>
  PUNPCKLBW xmm1, xmm2/m128
  PUNPCKLWD xmm1, xmm2/m128
  PUNPCKLDQ xmm1, xmm2/m128
  PUNPCKLQDQ xmm1, xmm2/m128
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 128 bits, i.e. 16 bytes.
       (operand-size 16)

       ;; The first source operand (Operand 1 in the Intel manual)
       ;; is the XMM register specified in Reg.
       ;; This is also the destination operand,
       ;; and thus we obtain the index for later use.
       ((the (unsigned-byte 4) src1/dst-index)
        (reg-index reg rex-byte #.*r*))
       ((the (unsigned-byte 128) src1)
        (xmmi-size operand-size src1/dst-index x86))

       ;; The second source operand (Operand 2 in the Intel manual)
       ;; is the XMM register, or memory operand, specified in Mod and R/M.
       (inst-ac? t) ; Intel Manual Volume 2 Table 2-21 (Dec 2023)
       ((mv flg
            (the (unsigned-byte 128) src2)
            (the (integer 0 4) increment-rip-by)
            ?addr
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               #.*xmm-access*
                                               operand-size
                                               inst-ac?
                                               nil ; not a memory operand
                                               seg-reg
                                               p4?
                                               temp-rip
                                               rex-byte
                                               r/m
                                               mod
                                               sib
                                               0 ; no immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result.
       (result (case opcode
                 (#x60 (punpckl (* 8 operand-size) 08 src1 src2))
                 (#x61 (punpckl (* 8 operand-size) 16 src1 src2))
                 (#x62 (punpckl (* 8 operand-size) 32 src1 src2))
                 (#x6C (punpckl (* 8 operand-size) 64 src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size src1/dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-punpckh-sse

  :parents (two-byte-opcodes)

  :short "Unpack high data (SSE variants)."

  :long
  "<code>
  PUNPCKHBW xmm1, xmm2/m128
  PUNPCKHWD xmm1, xmm2/m128
  PUNPCKHDQ xmm1, xmm2/m128
  PUNPCKHQDQ xmm1, xmm2/m128
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 128 bits, i.e. 16 bytes.
       (operand-size 16)

       ;; The first source operand (Operand 1 in the Intel manual)
       ;; is the XMM register specified in Reg.
       ;; This is also the destination operand,
       ;; and thus we obtain the index for later use.
       ((the (unsigned-byte 4) src1/dst-index)
        (reg-index reg rex-byte #.*r*))
       ((the (unsigned-byte 128) src1)
        (xmmi-size operand-size src1/dst-index x86))
       ((the (unsigned-byte 64) src1) (logtail 64 src1))

       ;; The second source operand (Operand 2 in the Intel manual)
       ;; is the XMM register, or memory operand, specified in Mod and R/M.
       (inst-ac? t) ; Intel Manual Volume 2 Table 2-21 (Dec 2023)
       ((mv flg
            (the (unsigned-byte 128) src2)
            (the (integer 0 4) increment-rip-by)
            ?addr
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               #.*xmm-access*
                                               operand-size
                                               inst-ac?
                                               nil ; not a memory operand
                                               seg-reg
                                               p4?
                                               temp-rip
                                               rex-byte
                                               r/m
                                               mod
                                               sib
                                               0 ; no immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))
       ((the (unsigned-byte 64) src2) (logtail 64 src2))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result.
       ;; Since we already shifted src1 and src2, so the high order bytes are
       ;; now lower order bytes, we can use punpckl.
       (result (case opcode
                 (#x68 (punpckl (* 8 operand-size) 08 src1 src2))
                 (#x69 (punpckl (* 8 operand-size) 16 src1 src2))
                 (#x6A (punpckl (* 8 operand-size) 32 src1 src2))
                 (#x6D (punpckl (* 8 operand-size) 64 src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size src1/dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))
