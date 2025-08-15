; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2024, Kestrel Technology, LLC
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
; Cuong Chau          <ckcuong@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio (www.alessandrocoglio.info)

(in-package "X86ISA")

;; ======================================================================

(include-book "../../decoding-and-spec-utils"
              :ttags (:undef-flg))
(include-book "base"
              :ttags (:undef-flg))
(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; =============================================================================
; INSTRUCTION: SSE/SSE2 Data Movement Instructions
; =============================================================================

(def-inst x86-movss/movsd-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move scalar single/double precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  F3 0F 10: MOVSS xmm1, xmm2/m32<br/>
  F2 0F 10: MOVSD xmm1, xmm2/m64<br/>"

  :sp/dp t

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (integer 4 8) operand-size)
        (if (equal sp/dp #.*OP-DP*) 8 4))

       ((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 5
        t)
       ((mv flg0
            xmm/mem
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                #.*xmm-access*
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; From Intel manual, Vol. 2A: For non-VEX encoded syntax and when the
       ;; source and destination operands are XMM registers, the high
       ;; doublewords/quadword of the destination operand remains
       ;; unchanged. When the source operand is a memory location and
       ;; destination operand is an XMM register, the high doublewords/quadword
       ;; of the destination operand is cleared to all 0s.
       (operand-size (if (= mod #b11) operand-size 16))

       ;; Update the x86 state:
       (x86 (!xmmi-size operand-size xmm-index xmm/mem x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-movss/movsd-Op/En-MR

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move scalar single/double precision floating-point values"

  :long
  "<h3>Op/En = MR: \[OP XMM/M, XMM\]</h3>
  F3 0F 11: MOVSS xmm2/m32, xmm1<br/>
  F2 0F 11: MOVSD xmm2/m64, xmm1<br/>"

  :sp/dp t

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (integer 4 8) operand-size)
        (if (equal sp/dp #.*OP-DP*) 8 4))

       ((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))
       (xmm (xmmi-size operand-size xmm-index x86))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (inst-ac? ;; Exceptions Type 5
        t)
       ((mv flg1 x86)
        (x86-operand-to-xmm/mem proc-mode
                                 operand-size
                                 inst-ac?
                                 xmm
                                 seg-reg
                                 addr
                                 rex-byte
                                 r/m
                                 mod
                                 x86))
       ((when flg1)
        (!!ms-fresh :x86-operand-to-xmm/mem flg1))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-movaps/movapd-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move aligned packed single/double precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
     0F 28: MOVAPS xmm1, xmm2/m128<br/>
  66 0F 28: MOVAPD xmm1, xmm2/m128<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 1
        t)
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

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index xmm/mem x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-movaps/movapd-Op/En-MR

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move aligned packed single/double precision floating-point values"

  :long
  "<h3>Op/En = MR: \[OP XMM/M, XMM\]</h3>
     0F 29: MOVAPS xmm2/m128, xmm1<br/>
  66 0F 29: MOVAPD xmm2/m128, xmm1<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))
       ((the (unsigned-byte 128) xmm)
        (xmmi-size 16 xmm-index x86))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (inst-ac? ;; Exceptions Type 1
        t)
       ((mv flg1 x86)
        (x86-operand-to-xmm/mem proc-mode
                                 16
                                 inst-ac?
                                 xmm
                                 seg-reg
                                 addr
                                 rex-byte
                                 r/m
                                 mod
                                 x86))
       ((when flg1)
        (!!ms-fresh :x86-operand-to-xmm/mem flg1))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-movups/movupd/movdqu-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
     0F 10: MOVUPS xmm1, xmm2/m128<br/>
  66 0F 10: MOVUPD xmm1, xmm2/m128<br/>
  F3 0F 6F: MOVDQU xmm1, xmm2/m128<br/>

<p>Note: The MOVDQU, MOVUPS, and MOVUPD instructions perform 128-bit
 unaligned loads or stores. They do not generate general-protection
 exceptions (#GP) when operands are not aligned on a 16-byte
 boundary. If alignment checking is enabled, alignment-check
 exceptions (#AC) may or may not be generated depending on processor
 implementation when data addresses are not aligned on an 8-byte
 boundary.</p>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac?
        ;; Exceptions Type 4 but treatment of #AC varies. For now, we
        ;; check the alignment.
        t)
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

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index xmm/mem x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))


(def-inst x86-movups/movupd/movdqu-Op/En-MR

  :parents (two-byte-opcodes fp-opcodes)

  :long
  "<h3>Op/En = MR: \[OP XMM/M, XMM\]</h3>
     0F 11: MOVUPS xmm2/m128, xmm1<br/>
  66 0F 11: MOVUPD xmm2/m128, xmm1<br/>
  F3 0F 7F: MOVDQU xmm2/m128, xmm1<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))
       ((the (unsigned-byte 128) xmm)
        (xmmi-size 16 xmm-index x86))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override*
                 (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (inst-ac? ;; Exceptions Type 4, but treatment of #AC
        ;; varies. For now, we do alignment checking.
        t)
       ((mv flg1 x86)
        (x86-operand-to-xmm/mem proc-mode
                                 16
                                 inst-ac?
                                 xmm
                                 seg-reg
                                 addr
                                 rex-byte
                                 r/m
                                 mod
                                 x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg1)
        (!!ms-fresh :x86-operand-to-xmm/mem flg1))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))


(def-inst x86-movlps/movlpd-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move low packed single/double precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, M\]</h3>
     0F 12: MOVLPS xmm, m64<br/>
  66 0F 12: MOVLPD xmm, m64<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))

       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 5
        t)
       ((mv flg0
            (the (unsigned-byte 64) mem)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                #.*xmm-access*
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
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (x86 (!xmmi-size 8 xmm-index mem x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))


(def-inst x86-movlps/movlpd-Op/En-MR

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move low packed single/double precision floating-point values"

  :long
  "<h3>Op/En = MR: \[OP M, XMM\]</h3>
     0F 13: MOVLPS m64, xmm<br/>
  66 0F 13: MOVLPD m64, xmm<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))
       ((the (unsigned-byte 64) xmm)
        (xmmi-size 8 xmm-index x86))

       (p2 (prefixes->seg prefixes))

       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((mv flg0
            (the (signed-byte 64) addr)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (x86-effective-addr proc-mode p4? temp-rip rex-byte r/m mod sib
                            0 ;; No immediate operand
                            x86))
       ((when flg0)
        (!!ms-fresh :x86-effective-addr-error flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (inst-ac? ;; Exceptions Type 5
        t)
       ((mv flg1 x86)
        (x86-operand-to-xmm/mem proc-mode
                                 8
                                 inst-ac?
                                 xmm
                                 seg-reg
                                 addr
                                 rex-byte
                                 r/m
                                 mod
                                 x86))
       ((when flg1)
        (!!ms-fresh :x86-operand-to-xmm/mem flg1))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))


(def-inst x86-movhps/movhpd-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move high packed single/double precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, M\]</h3>
     0F 16: MOVHPS xmm, m64<br/>
  66 0F 16: MOVHPD xmm, m64<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))

       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 5
        t)
       ((mv flg0
            (the (unsigned-byte 64) mem)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?v-addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                #.*xmm-access*
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
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       ((the (unsigned-byte 64) low-qword)
        (xmmi-size 8 xmm-index x86))
       (result (merge-2-u64s mem low-qword))
       (x86 (!xmmi-size 16 xmm-index result x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-movhps/movhpd-Op/En-MR

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move high packed single/double precision floating-point values"

  :long
  "<h3>Op/En = MR: \[OP M, XMM\]</h3>
     0F 17: MOVHPS m64, xmm<br/>
  66 0F 17: MOVHPD m64, xmm<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))
       ((the (unsigned-byte 128) xmm)
        (xmmi-size 16 xmm-index x86))

       (high-qword (mbe :logic (part-select xmm :low 64 :high 127)
                        :exec  (the (unsigned-byte 64)
                                 (logand #uxFFFF_FFFF_FFFF_FFFF
                                         (ash xmm -64)))))

       (p2 (prefixes->seg prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((mv flg0
            (the (signed-byte 64) addr)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (x86-effective-addr proc-mode p4? temp-rip rex-byte r/m mod sib
                            0 ;; No immediate operand
                            x86))
       ((when flg0)
        (!!ms-fresh :x86-effective-addr-error flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (inst-ac? ;; Exceptions Type 5
        t)
       ((mv flg1 x86)
        (x86-operand-to-xmm/mem proc-mode
                                 8
                                 inst-ac?
                                 high-qword
                                 seg-reg
                                 addr
                                 rex-byte
                                 r/m
                                 mod
                                 x86))
       ((when flg1)
        (!!ms-fresh :x86-operand-to-xmm/mem flg1))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-movhlps-sse

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move Packed Single Precision Floating-Point Values High to Low"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM\]</h3>
  NP 0F 12: MOVHLPS xmm1, xmm2<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 5
        t)
       ((mv flg0
            (the (unsigned-byte 128) xmm)
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

       (high-qword (mbe :logic (part-select xmm :low 64 :high 127)
                        :exec  (the (unsigned-byte 64)
                                 (logand #uxFFFF_FFFF_FFFF_FFFF
                                         (ash xmm -64)))))

       ;; Update the x86 state:
       (x86 (!xmmi-size 8 xmm-index high-qword x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

; =============================================================================
; INSTRUCTION: AVX Data Movement Instructions
; =============================================================================

(def-inst x86-vmovups/vmovupd/vmovdqu-vex-a

  :parents (two-byte-opcodes fp-opcodes)

  :short "VMOVUPS, VMOVUPD, VMMOVDQU:
          move unaligned packed single/double-precision floating-point values
          and unaligned packed integer values
          (VEX encoding, Op/En A)."

  :long
  "<p>
   These instructions are listed under MOVUPS, MOVUPD, and MOVDQU
   in Intel Manual Volume 2 (Jun 2025).
   </p>
   <p>
   This semantic function covers the two VEX-encoded variants
   (of each of VMOVUPS, MOVUPD, and VMOVDQU)
   that move from register or memory to register (i.e. Op/En A).
   </p>
   <p>
   The three instructions behave in the same way at the ISA level,
   but they have different encodings,
   and are used with different types at the assembly and higher levels;
   there may also be performance differences at the level lower than the ISA.
   </p>
   <code>
   VMOVUPS xmm1, xmm2/m128
   VMOVUPS ymm1, ymm2/m256
   </code>
   <code>
   VMOVUPD xmm1, xmm2/m128
   VMOVUPD ymm1, ymm2/m256
   </code>
   <code>
   VMOVDQU xmm1, xmm2/m128
   VMOVDQU ymm1, ymm2/m256
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

       ;; The operand size is determined by VEX.L, regardless of processor mode.
       ((the (integer 16 32) operand-size)
        (if (equal (vex->l vex-prefixes) 1)
            32
          16))

       ;; Read the value from register or memory.
       ;; There is no alignment check, since it is an 'unaligned' move.
       ;; Also see Intel Manual Volume 1 (Jun 2025), Table 14-23.
       (inst-ac? nil)
       ((mv flg
            (the (unsigned-byte 256) reg/mem-value)
            (the (integer 0 4) increment-rip-by)
            & ; address of the operand
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               (if (= operand-size 16)
                                                   #.*vex-xmm-access*
                                                 #.*ymm-access*)
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
       ((when flg)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the destination register.
       ;; Note that this operation zeros the upper bits,
       ;; as required in the pseudocode of the instruction.
       ;; In our model, MAXVL is 512,
       ;; because our model of the x86 state has just the ZMM registers,
       ;; whose lower bits are aliased to YMM and XMM.
       (x86 (!zmmi-size operand-size
                        (reg-index reg rex-byte #.*r*)
                        reg/mem-value
                        x86
                        :regtype (if (= operand-size 16)
                                     #.*vex-xmm-access*
                                   #.*ymm-access*)))

       ;; Update the instruction pointer in the state.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))

;; ======================================================================

(def-inst x86-vmovups/vmovupd/vmovdqu-vex-b

  :parents (two-byte-opcodes fp-opcodes)

  :short "VMOVUPS, VMOVUPD, VMMOVDQU:
          move unaligned packed single/double-precision floating-point values
          and unaligned packed integer values
          (VEX encoding, Op/En B)"

  :long
  "<p>
   These instructions are listed under MOVUPS, MOVUPD, and MOVDQU
   in Intel Manual Volume 2 (Jun 2025).
   </p>
   <p>
   This semantic function covers the two VEX-encoded variants
   (of each of VMOVUPS, MOVUPD, and VMOVDQU)
   that move from register to to register or memory (i.e. Op/En B).
   </p>
   <p>
   The three instructions behave in the same way at the ISA level,
   but they have different encodings,
   and are used with different types at the assembly and higher levels;
   there may also be performance differences at the level lower than the ISA.
   </p>
   <code>
   VMOVUPS xmm2/m128, xmm1
   VMOVUPS ymm2/m256, ymm1
   </code>
   <code>
   VMOVUPD xmm2/m128, xmm1
   VMOVUPD ymm2/m256, ymm1
   </code>
   <code>
   VMOVDQU xmm2/m128, xmm1
   VMOVDQU ymm2/m256, ymm1
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

       ;; The operand size is determined by VEX.L, regardless of processor mode.
       ((the (integer 16 32) operand-size)
        (if (equal (vex->l vex-prefixes) 1)
            32
          16))

       ;; Read the value from register.
       ((the (unsigned-byte 256) reg-value)
        (zmmi-size operand-size
                   (reg-index reg rex-byte #.*r*)
                   x86))

       ;; Obtain the address of the destination operand, if in memory.
       ;; Read the value from register or memory.
       ;; There is no alignment check, since it is an 'unaligned' move.
       ;; Also see Intel Manual Volume 1 (Jun 2025), Table 14-23.
       (inst-ac? nil)
       ((mv flg
            & ; old value of the operand
            (the (integer 0 4) increment-rip-by)
            (the (signed-byte 64) addr) ; 0 if destination is register
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               (if (= operand-size 16)
                                                   #.*vex-xmm-access*
                                                 #.*ymm-access*)
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
       ((when flg)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the destination operand, register or memory.
       ;; Note that this operation zeros the upper bits,
       ;; as required in the pseudocode of the instruction.
       ;; In our model, MAXVL is 512,
       ;; because our model of the x86 state has just the ZMM registers,
       ;; whose lower bits are aliased to YMM and XMM.
       ((mv flg x86)
        (x86-operand-to-zmm/mem proc-mode
                                (if (= operand-size 16)
                                    #.*vex-xmm-access*
                                  #.*ymm-access*)
                                operand-size
                                inst-ac?
                                reg-value
                                seg-reg
                                addr
                                rex-byte
                                r/m
                                mod
                                x86))
       ((when flg) (!!ms-fresh :x86-operand-to-zmm/mem flg))

       ;; Update the instruction pointer in the state.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))

;; ======================================================================

(def-inst x86-vmovaps/vmovapd/vmovdqa-vex-a

  :parents (two-byte-opcodes fp-opcodes)

  :short "VMOVAPS, VMOVAPD, VMMOVDQA:
          move aligned packed single/double-precision floating-point values
          and aligned packed integer values
          (VEX encoding, Op/En A)."

  :long
  "<p>
   These instructions are listed under MOVAPS, MOVAPD, and MOVDQA
   in Intel Manual Volume 2 (Jun 2025).
   </p>
   <p>
   This semantic function covers the two VEX-encoded variants
   (of each of VMOVAPS, MOVAPD, and VMOVDQA)
   that move from register or memory to register (i.e. Op/En A).
   </p>
   <p>
   The three instructions behave in the same way at the ISA level,
   but they have different encodings,
   and are used with different types at the assembly and higher levels;
   there may also be performance differences at the level lower than the ISA.
   </p>
   <code>
   VMOVAPS xmm1, xmm2/m128
   VMOVAPS ymm1, ymm2/m256
   </code>
   <code>
   VMOVAPD xmm1, xmm2/m128
   VMOVAPD ymm1, ymm2/m256
   </code>
   <code>
   VMOVDQA xmm1, xmm2/m128
   VMOVDQA ymm1, ymm2/m256
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

       ;; The operand size is determined by VEX.L, regardless of processor mode.
       ((the (integer 16 32) operand-size)
        (if (equal (vex->l vex-prefixes) 1)
            32
          16))

       ;; Read the value from register or memory.
       ;; There is an alignment check, since it is an 'aligned' move.
       ;; Also see Intel Manual Volume 1 (Jun 2025), Table 14-22.
       (inst-ac? t)
       ((mv flg
            (the (unsigned-byte 256) reg/mem-value)
            (the (integer 0 4) increment-rip-by)
            & ; address of the operand
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               (if (= operand-size 16)
                                                   #.*vex-xmm-access*
                                                 #.*ymm-access*)
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
       ((when flg)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the destination register.
       ;; Note that this operation zeros the upper bits,
       ;; as required in the pseudocode of the instruction.
       ;; In our model, MAXVL is 512,
       ;; because our model of the x86 state has just the ZMM registers,
       ;; whose lower bits are aliased to YMM and XMM.
       (x86 (!zmmi-size operand-size
                        (reg-index reg rex-byte #.*r*)
                        reg/mem-value
                        x86
                        :regtype (if (= operand-size 16)
                                     #.*vex-xmm-access*
                                   #.*ymm-access*)))

       ;; Update the instruction pointer in the state.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))

;; ======================================================================

(def-inst x86-vmovaps/vmovapd/vmovdqa-vex-b

  :parents (two-byte-opcodes fp-opcodes)

  :short "VMOVUPS, VMOVUPD, VMMOVDQU:
          move unaligned packed single/double-precision floating-point values
          and unaligned packed integer values
          (VEX encoding, Op/En B)"

  :long
  "<p>
   These instructions are listed under MOVUPS, MOVUPD, and MOVDQU
   in Intel Manual Volume 2 (Jun 2025).
   </p>
   <p>
   This semantic function covers the two VEX-encoded variants
   (of each of VMOVUPS, MOVUPD, and VMOVDQU)
   that move from register to to register or memory (i.e. Op/En B).
   </p>
   <p>
   The three instructions behave in the same way at the ISA level,
   but they have different encodings,
   and are used with different types at the assembly and higher levels;
   there may also be performance differences at the level lower than the ISA.
   </p>
   <code>
   VMOVUPS xmm2/m128, xmm1
   VMOVUPS ymm2/m256, ymm1
   </code>
   <code>
   VMOVUPD xmm2/m128, xmm1
   VMOVUPD ymm2/m256, ymm1
   </code>
   <code>
   VMOVDQU xmm2/m128, xmm1
   VMOVDQU ymm2/m256, ymm1
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

       ;; The operand size is determined by VEX.L, regardless of processor mode.
       ((the (integer 16 32) operand-size)
        (if (equal (vex->l vex-prefixes) 1)
            32
          16))

       ;; Read the value from register.
       ((the (unsigned-byte 256) reg-value)
        (zmmi-size operand-size
                   (reg-index reg rex-byte #.*r*)
                   x86))

       ;; Obtain the address of the destination operand, if in memory.
       ;; Read the value from register or memory.
       ;; There is an alignment check, since it is an 'aligned' move.
       ;; Also see Intel Manual Volume 1 (Jun 2025), Table 14-22.
       (inst-ac? t)
       ((mv flg
            & ; old value of the operand
            (the (integer 0 4) increment-rip-by)
            (the (signed-byte 64) addr) ; 0 if destination is register
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               (if (= operand-size 16)
                                                   #.*vex-xmm-access*
                                                 #.*ymm-access*)
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
       ((when flg)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the destination operand, register or memory.
       ;; Note that this operation zeros the upper bits,
       ;; as required in the pseudocode of the instruction.
       ;; In our model, MAXVL is 512,
       ;; because our model of the x86 state has just the ZMM registers,
       ;; whose lower bits are aliased to YMM and XMM.
       ((mv flg x86)
        (x86-operand-to-zmm/mem proc-mode
                                (if (= operand-size 16)
                                    #.*vex-xmm-access*
                                  #.*ymm-access*)
                                operand-size
                                inst-ac?
                                reg-value
                                seg-reg
                                addr
                                rex-byte
                                r/m
                                mod
                                x86))
       ((when flg) (!!ms-fresh :x86-operand-to-zmm/mem flg))

       ;; Update the instruction pointer in the state.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))
