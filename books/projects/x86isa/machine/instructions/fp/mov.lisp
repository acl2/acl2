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
; Cuong Chau          <ckcuong@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "base"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
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

;; ======================================================================
