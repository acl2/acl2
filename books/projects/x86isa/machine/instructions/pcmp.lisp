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

(include-book "../decoding-and-spec-utils"
              :ttags (:undef-flg))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pcmpeq ((result-width natp)
                (el-width posp)
                (a natp)
                (b natp))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  :guard (equal (mod result-width el-width) 0)
  :returns (result (unsigned-byte-p result-width result)
                   :hyp (and (natp result-width)
                             (<= (pos-fix el-width) result-width)
                             (equal (mod result-width (pos-fix el-width)) 0))
                   :hints (("Goal"
                            :in-theory
                            (disable unsigned-byte-p
                                     bitops::logapp-of-i-0
                                     acl2::prefer-positive-addends-<))))
  :measure (nfix result-width)
  (b* ((el-width (mbe :logic (pos-fix el-width) :exec el-width))
       (a (lnfix a))
       (b (lnfix b))
       ((when (zp result-width)) 0)
       (el-equal? (equal (loghead el-width a)
                         (loghead el-width b))))
      (logapp el-width (if el-equal? -1 0)
              (pcmpeq (- result-width el-width) el-width
                      (logtail el-width a) (logtail el-width b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-pcmpeqb/pcmpeqw/pcmpeqd/pcmpeqq-sse
  :parents (two-byte-opcodes)
  :long
  "<code>
  PCMPEQB xmm1, xmm2/m128
  PCMPEQW xmm1, xmm2/m128
  PCMPEQD xmm1, xmm2/m128
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))
  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))

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
                 (#x74 (pcmpeq (* 8 operand-size) 08 src1 src2))
                 (#x75 (pcmpeq (* 8 operand-size) 16 src1 src2))
                 (#x76 (pcmpeq (* 8 operand-size) 32 src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size src1/dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-vpcmpeqb/vpcmpeqw/vpcmpeqd/vpcmpeqq-vex

  :parents (two-byte-opcodes)

  :short "Compare packed integers for equality (VEX variants)."

  :long
  "<code>
   VPCMPB xmm1, xmm2, xmm3/m128
   VPCMPW xmm1, xmm2, xmm3/m128
   VPCMPD xmm1, xmm2, xmm3/m128
   VPCMPQ xmm1, xmm2, xmm3/m128

   VPCMPB ymm1, ymm2, ymm3/m256
   VPCMPW ymm1, ymm2, ymm3/m256
   VPCMPD ymm1, ymm2, ymm3/m256
   VPCMPQ ymm1, ymm2, ymm3/m256
   </code>"

  :vex t

  :modr/m t

  :guard (vex-prefixes-byte0-p vex-prefixes)

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (rex-byte (rex-byte-from-vex-prefixes vex-prefixes))

       ;; The operand size is determined by VEX.L,
       ;; based on the VEX.128 and VEX.256 notation
       ;; (see Intel Manual Volume 2 Section 3.1.1.2 (Jun 2025)).
       ((the (integer 16 32) operand-size)
        (if (equal (vex->l vex-prefixes) 1)
            32
          16))

       ;; The first source operand (Operand 2 in the Intel Manual)
       ;; is the XMM or YMM register specified in VEX.vvvv.
       ((the (unsigned-byte 4) src1-index)
        (vex-vvvv-reg-index (vex->vvvv vex-prefixes)))
       ((the (unsigned-byte 256) src1) (zmmi-size operand-size src1-index x86))

       ;; The second source operand (Operand 3 in the Intel Manual)
       ;; is the XMM or YMM register, or memory operand,
       ;; specified in the ModR/M byte.
       ;; There is no alignment checking
       ;; (see Intel Manual Volume 2 Table 2-21 (Jun 2025)).
       (inst-ac? nil) ; Exceptions Type 4
       ((mv flg
            src2
            (the (integer 0 4) increment-rip-by)
            (the (signed-byte 64) addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               (if (= operand-size 16)
                                                   #.*VEX-XMM-ACCESS*
                                                 #.*YMM-ACCESS*)
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

       ;; The destination operand (Operand 1 in the Intel Manual)
       ;; is the XMM or YMM register specified in the reg bits of ModR/M.
       ((the (unsigned-byte 4) dst-index) (reg-index reg rex-byte #.*r*))

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
                 (#x74 (pcmpeq (* 8 operand-size) 08 src1 src2))
                 (#x75 (pcmpeq (* 8 operand-size) 16 src1 src2))
                 (#x76 (pcmpeq (* 8 operand-size) 32 src1 src2))
                 (#x29 (pcmpeq (* 8 operand-size) 64 src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!zmmi-size operand-size
                        dst-index
                        result
                        x86
                        :regtype (if (= operand-size 16)
                                     #.*vex-xmm-access*
                                   #.*ymm-access*)))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pcmpgt ((result-width natp)
                (el-width posp)
                (a natp)
                (b natp))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  :guard (equal (mod result-width el-width) 0)
  :returns (result (unsigned-byte-p result-width result)
                   :hyp (and (natp result-width)
                             (<= (pos-fix el-width) result-width)
                             (equal (mod result-width (pos-fix el-width)) 0))
                   :hints (("Goal"
                            :in-theory
                            (disable unsigned-byte-p
                                     bitops::logapp-of-i-0
                                     acl2::prefer-positive-addends-<))))
  :measure (nfix result-width)
  (b* ((result-width (nfix result-width))
       (el-width (pos-fix el-width))
       (a (nfix a))
       (b (nfix b))
       ((when (zp result-width)) 0)
       (el-greater? (> (logext el-width a)
                       (logext el-width b))))
    (logapp el-width (if el-greater? -1 0)
            (pcmpgt (- result-width el-width) el-width
                    (logtail el-width a) (logtail el-width b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-pcmpgt-sse
  :parents (two-byte-opcodes)
  :long
  "<code>
  PCMPGTB xmm1, xmm2/m128
  PCMPGTW xmm1, xmm2/m128
  PCMPGTD xmm1, xmm2/m128
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))
  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))

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
                 (#x64 (pcmpgt (* 8 operand-size) 08 src1 src2))
                 (#x65 (pcmpgt (* 8 operand-size) 16 src1 src2))
                 (#x66 (pcmpgt (* 8 operand-size) 32 src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size src1/dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
