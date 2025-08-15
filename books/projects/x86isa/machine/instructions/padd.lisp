; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2024, Kestrel Technology LLC
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

(include-book "../decoding-and-spec-utils"
              :ttags (:undef-flg))

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simd-add-spec ((total-size natp)
                       (chunk-size posp)
                       (x (unsigned-byte-p total-size x))
                       (y (unsigned-byte-p total-size y)))
  :guard (integerp (/ total-size chunk-size))
  :returns (result (unsigned-byte-p total-size result)
                   :hyp :guard
                   :hints
                   (("Goal" :induct (simd-add-spec total-size chunk-size x y))
                    '(:cases ((>= total-size chunk-size)))))
  :parents (instruction-semantic-functions)
  :short "Specification for the SIMD addition instructions."
  :long
  "<p>
   This is for the (V)PADDB/(V)PADDW/(V)PADDD/(V)PADDQ instructions.
   </p>
   <p>
   Given @('x') and @('y'), each of size @('total-size') in bits,
   we add each chunk of size @('chunk-size') in bits,
   independently from the other chunks,
   keeping the low @('chunk-size') bits of each result,
   and putting the resulting chunks together, in the same order,
   to obtain the final result of size @('total-size').
   This kind of operation is illustrated in
   Intel Manual Volume 1 Figure 9-4 (Dec 2023).
   </p>
   <p>
   The @('total-size') must be a multiple of @('chunk-size').
   For instance, for the VEX form of VPADDW,
   @('total-size') is 128 and @('chunk-size') is 16.
   </p>"
  (b* (((when (zp total-size)) 0)
       ((unless (mbt (posp chunk-size))) 0)
       (x-lo (loghead chunk-size x))
       (y-lo (loghead chunk-size y))
       (result-lo (loghead chunk-size (+ x-lo y-lo)))
       (x-hi (logtail chunk-size x))
       (y-hi (logtail chunk-size y))
       (result-hi
        (simd-add-spec (- total-size chunk-size) chunk-size x-hi y-hi)))
    (logapp chunk-size result-lo result-hi))
  :measure (nfix total-size))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-paddb/paddw/paddd/paddq-sse

  :parents (two-byte-opcodes)

  :short "Add packed integers (SSE variants)."

  :long
  "<code>
   PADDB xmm1, xmm2/m128
   PADDW xmm1, xmm2/m128
   PADDD xmm1, xmm2/m128
   PADDQ xmm1, xmm2/m128
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
                 (#xfc (simd-add-spec (* 8 operand-size) 08 src1 src2))
                 (#xfd (simd-add-spec (* 8 operand-size) 16 src1 src2))
                 (#xfe (simd-add-spec (* 8 operand-size) 32 src1 src2))
                 (#xd4 (simd-add-spec (* 8 operand-size) 64 src1 src2))
                 (t 0))) ; unreachable

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size src1/dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-vpaddb/vpaddw/vpaddd/vpaddq-vex

  :parents (two-byte-opcodes)

  :short "Add packed integers (VEX variants)."

  :long
  "<code>
   VPADDB xmm1, xmm2, xmm3/m128
   VPADDW xmm1, xmm2, xmm3/m128
   VPADDD xmm1, xmm2, xmm3/m128
   VPADDQ xmm1, xmm2, xmm3/m128

   VPADDB ymm1, ymm2, ymm3/m256
   VPADDW ymm1, ymm2, ymm3/m256
   VPADDD ymm1, ymm2, ymm3/m256
   VPADDQ ymm1, ymm2, ymm3/m256
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

       ;; Calculate the result.
       (result (case opcode
                 (#xfc (simd-add-spec (* 8 operand-size) 08 src1 src2))
                 (#xfd (simd-add-spec (* 8 operand-size) 16 src1 src2))
                 (#xfe (simd-add-spec (* 8 operand-size) 32 src1 src2))
                 (#xd4 (simd-add-spec (* 8 operand-size) 64 src1 src2))
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

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))

  :prepwork
  ((defrulel verify-guards-lemma
     (implies (unsigned-byte-p 4 x)
              (unsigned-byte-p 5 x)))))
