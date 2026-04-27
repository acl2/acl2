; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2026, Kestrel Technology, LLC
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

; Authors:
;   Cuong Chau        <ckcuong@cs.utexas.edu>
;   Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; MMX variants

(def-inst x86-pand/pandn/por/pxor-mmx

  :parents (two-byte-opcodes)

  :short "Logical instructions (MMX variants)."

  :long
  "<code>
   NP 0F DB /r    PAND  mm, mm/m64
   NP 0F DF /r    PANDN mm, mm/m64
   NP 0F EB /r    POR   mm, mm/m64
   NP 0F EF /r    PXOR  mm, mm/m64
   </code>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 64 bits, i.e. 8 bytes.
       (operand-size 8)

       ;; The first source operand (Operand 1 in the Intel manual)
       ;; is the MMX register specified in Reg.
       ;; This is also the destination operand,
       ;; and thus we obtain the index for later use.
       ;; Since there are only 8 MMX registers, the REX byte is not used.
       ((the (unsigned-byte 4) src1/dst-index) reg)
       ((the (unsigned-byte 64) src1) (mmx src1/dst-index x86))

       ;; The second source operand (Operand 2 in the Intel manual)
       ;; is the MMX register, or memory operand, specified in Mod and R/M.
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
                 (#xdb (logand src1 src2))
                 (#xdf (logand (lognot src1) src2))
                 (#xeb (logior src1 src2))
                 (#xef (logxor src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!mmx src1/dst-index result x86))
       (x86 (mmx-instruction-updates x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; SSE variants

(def-inst x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM

  :parents (two-byte-opcodes)

  :short "Logical instructions (SSE variants)."

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
     0F 54: ANDPS  xmm1, xmm2/m128<br/>
     0F 55: ANDNPS xmm1, xmm2/m128<br/>
     0F 56: ORPS   xmm1, xmm2/m128<br/>
     0F 57: XORPS  xmm1, xmm2/m128<br/>

  66 0F 54: ANDPD  xmm1, xmm2/m128<br/>
  66 0F 55: ANDNPD xmm1, xmm2/m128<br/>
  66 0F 56: ORPD   xmm1, xmm2/m128<br/>
  66 0F 57: XORPD  xmm1, xmm2/m128<br/>

  66 0F DB: PAND  xmm1, xmm2/m128<br/>
  66 0F DF: PANDN xmm1, xmm2/m128<br/>
  66 0F EB: POR   xmm1, xmm2/m128<br/>
  66 0F EF: PXOR  xmm1, xmm2/m128<br/>"

  :operation t

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t
  :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       ((the (unsigned-byte 128) xmm)
        (xmmi-size 16 xmm-index x86))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override*
                 (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 4
        nil)
       ((mv flg0
            (the (unsigned-byte 128) xmm/mem)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                #.*xmm-access*
                                                16
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
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Raise an error if addr is not 16-byte aligned.
       ;; In case the second operand is an XMM register, addr = 0.
       ((when (not (eql (mod addr 16) 0)))
        (!!ms-fresh :memory-address-is-not-16-byte-aligned addr))

       (result (case operation
                 (#.*OP-AND*  (logand xmm xmm/mem))
                 (#.*OP-ANDN* (logand (lognot xmm) xmm/mem))
                 (#.*OP-OR*   (logior xmm xmm/mem))
                 (#.*OP-XOR*  (logxor xmm xmm/mem))
                 ;; Should not reach here.
                 (otherwise 0)))

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; AVX variants

(def-inst x86-vandp?/vandnp?/vorp?/vxorp?/vpand/vpandn/vpor/vpxor-vex

  :parents (two-byte-opcodes)

  :short "VEX-encoded logical instructions."

  :long
  "<code>
   VANDPD  xmm1, xmm2, xmm3/m128
   VANDPD  ymm1, ymm2, ymm3/m256

   VANDPS  xmm1, xmm2, xmm3/m128
   VANDPS  ymm1, ymm2, ymm3/m256

   VANDNPD xmm1, xmm2, xmm3/m128
   VANDNPD ymm1, ymm2, ymm3/m256

   VANDNPS xmm1, xmm2, xmm3/m128
   VANDNPS ymm1, ymm2, ymm3/m256

   VORPD   xmm1, xmm2, xmm3/m128
   VORPD   ymm1, ymm2, ymm3/m256

   VORPS   xmm1, xmm2, xmm3/m128
   VORPS   ymm1, ymm2, ymm3/m256

   VXORPD  xmm1, xmm2, xmm3/m128
   VXORPD  ymm1, ymm2, ymm3/m256

   VXORPS  xmm1, xmm2, xmm3/m128
   VXORPS  ymm1, ymm2, ymm3/m256

   VPAND   xmm1, xmm2, xmm3/m128
   VPAND   ymm1, ymm2, ymm3/m256

   VPANDN  xmm1, xmm2, xmm3/m128
   VPANDN  ymm1, ymm2, ymm3/m256

   VPOR    xmm1, xmm2, xmm3/m128
   VPOR    ymm1, ymm2, ymm3/m256

   VPXOR   xmm1, xmm2, xmm3/m128
   VPXOR   ymm1, ymm2, ymm3/m256
   </code>"

  :modr/m t

  :operation t

  :vex t

  :guard (vex-prefixes-byte0-p vex-prefixes)

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (rex-byte (rex-byte-from-vex-prefixes vex-prefixes))

       ;; The operand size is determined by VEX.L,
       ;; based on the VEX.128 and VEX.256 notation
       ;; (see Intel Manual Volume 2 Section 3.1.1.2 (Dec 2023)).
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
       ;; (see Intel Manual Volume 2 Table 2-21 (Dec 2023)).
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

       ;; Apply the logical operation to the source operands,
       ;; and only keep the appropriate number of bits.
       (result (case operation
                 (#.*OP-AND*  (logand src1 src2))
                 (#.*OP-ANDN* (logand (lognot src1) src2))
                 (#.*OP-OR*   (logior src1 src2))
                 (#.*OP-XOR*  (logxor src1 src2))
                 (otherwise 0))) ; unreachable
       (result (if (= operand-size 16)
                   (n128 result)
                 (n256 result)))

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

  :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))

  :prepwork
  ((defrulel verify-guards-lemma
     (implies (unsigned-byte-p 4 x)
              (unsigned-byte-p 5 x)))))
