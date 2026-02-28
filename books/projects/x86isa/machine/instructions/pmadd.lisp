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

(include-book "../decoding-and-spec-utils" :ttags (:undef-flg))

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simd-muladd-spec ((total-size natp)
                          (chunk-size posp)
                          (x (unsigned-byte-p total-size x))
                          (y (unsigned-byte-p total-size y)))
  :guard (and (integerp (/ total-size chunk-size))
              (evenp chunk-size))
  :returns (result (unsigned-byte-p total-size result)
                   :hyp :guard
                   :hints
                   (("Goal"
                     :induct (simd-muladd-spec total-size chunk-size x y))
                    '(:cases ((>= total-size chunk-size)))))
  :parents (instruction-semantic-functions)
  :short "Specification for the SIMD multiplication-addition instructions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the (V)PMADDWD instructions.")
   (xdoc::p
    "Given @('x') and @('y'), each of size @('total-size') in bits,
     for each chunk of even size @('chunk-size') in bits,
     independently from the other chunks,
     we multiply each half chunk in @('x')
     with the corresponding half chunk in @('y'),
     obtaining two full chunks, which we add together,
     obtaining the corresponding chunk of the result.
     This kind of operation is illustrated in
     Intel Manual Volume 2 Figure 4-11 (Feb 2026).")
   (xdoc::p
    "The @('total-size') must be a multiple of @('chunk-size'),
     and @('chunk-size') must be even.
     For instance, for the MMX form of PMADDWD,
     @('total-size') is 64 and @('chunk-size') is 32;
     each half-chunk is 16 bits."))
  (b* (((when (zp total-size)) 0)
       ((unless (mbt (and (posp chunk-size)
                          (evenp chunk-size))))
        0)
       (half-chunk-size (/ chunk-size 2))
       (x0-lo (logext half-chunk-size x))
       (x1-lo (logext half-chunk-size (ash x (- half-chunk-size))))
       (y0-lo (logext half-chunk-size y))
       (y1-lo (logext half-chunk-size (ash y (- half-chunk-size))))
       (result-lo (loghead chunk-size (+ (* x0-lo y0-lo)
                                         (* x1-lo y1-lo))))
       (x-hi (logtail chunk-size x))
       (y-hi (logtail chunk-size y))
       (result-hi
        (simd-muladd-spec (- total-size chunk-size) chunk-size x-hi y-hi)))
    (logapp chunk-size result-lo result-hi))
  :measure (nfix total-size)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable evenp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-pmaddwd-mmx

  :parents (two-byte-opcodes)

  :short "Multiply and add packed integers (MMX variant)."

  :long
  "<code>
   PMADDWD mm, mm/m64
   </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))

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
       (result (simd-muladd-spec (* 8 operand-size) 16 src1 src2))

       ;; Store the result into the destination register.
       (x86 (!mmx src1/dst-index result x86))
       (x86 (mmx-instruction-updates x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))
