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
(include-book "arith-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "sqrt-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; =============================================================================
; INSTRUCTION: SSE/SSE2 Arithmetic Instructions
; =============================================================================

(def-inst x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Add/Sub/Mul/Div/Max/Min scalar single/double precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  F3 0F 58: ADDSS xmm1, xmm2/m32<br/>
  F3 0F 59: MULSS xmm1, xmm2/m32<br/>
  F3 0F 5C: SUBSS xmm1, xmm2/m32<br/>
  F3 0F 5D: MINSS xmm1, xmm2/m32<br/>
  F3 0F 5E: DIVSS xmm1, xmm2/m32<br/>
  F3 0F 5F: MAXSS xmm1, xmm2/m32<br/>

  F2 0F 58: ADDSD xmm1, xmm2/m64<br/>
  F2 0F 59: MULSD xmm1, xmm2/m64<br/>
  F2 0F 5C: SUBSD xmm1, xmm2/m64<br/>
  F2 0F 5D: MINSD xmm1, xmm2/m64<br/>
  F2 0F 5E: DIVSD xmm1, xmm2/m64<br/>
  F2 0F 5F: MAXSD xmm1, xmm2/m64<br/>"

  :operation t

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

       (inst-ac?
        ;; Exceptions Type 3
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

       ((mv flg1 result (the (unsigned-byte 32) mxcsr))
        (if (equal sp/dp #.*OP-DP*)
            (dp-sse-add/sub/mul/div/max/min operation xmm xmm/mem (mxcsr x86))
          (sp-sse-add/sub/mul/div/max/min operation xmm xmm/mem (mxcsr x86))))

       ((when flg1)
        (if (equal sp/dp #.*OP-DP*)
            (!!fault-fresh :fp-exception :dp-sse-add/sub/mul/div/max/min flg1)
          (!!fault-fresh :fp-exception :sp-sse-add/sub/mul/div/max/min flg1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size operand-size xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

(def-inst x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Add/Sub/Mul/Div/Max/Min packed single-precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  0F 58: ADDPS xmm1, xmm2/m128<br/>
  0F 5C: SUBPS xmm1, xmm2/m128<br/>
  0F 59: MULPS xmm1, xmm2/m128<br/>
  0F 5E: DIVPS xmm1, xmm2/m128<br/>
  0F 5F: MAXPS xmm1, xmm2/m128<br/>
  0F 5D: MINPS xmm1, xmm2/m128<br/>"

  :operation t

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

       (inst-ac?
        ;; Exceptions Type 2
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

       ((mv flg (the (signed-byte #.*max-linear-address-size+1*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Raise an error if addr is not 16-byte aligned.
       ;; In case the second operand is an XMM register, addr = 0.
       ((when (not (eql (mod addr 16) 0)))
        (!!ms-fresh :memory-address-is-not-16-byte-aligned addr))

       (xmm0 (mbe :logic (part-select xmm :low 0 :high 31)
                  :exec  (the (unsigned-byte 32) (logand #uxFFFF_FFFF xmm))))
       (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 31)
                      :exec  (the (unsigned-byte 32) (logand #uxFFFF_FFFF xmm/mem))))

       (xmm1 (mbe :logic (part-select xmm :low 32 :high 63)
                  :exec  (the (unsigned-byte 32) (logand #uxFFFF_FFFF (ash xmm -32)))))
       (xmm/mem1 (mbe :logic (part-select xmm/mem :low 32 :high 63)
                      :exec  (the (unsigned-byte 32) (logand #uxFFFF_FFFF (ash xmm/mem -32)))))

       (xmm2 (mbe :logic (part-select xmm :low 64 :high 95)
                  :exec  (the (unsigned-byte 32) (logand #uxFFFF_FFFF (ash xmm -64)))))
       (xmm/mem2 (mbe :logic (part-select xmm/mem :low 64 :high 95)
                      :exec  (the (unsigned-byte 32) (logand #uxFFFF_FFFF (ash xmm/mem -64)))))

       (xmm3 (mbe :logic (part-select xmm :low 96 :high 127)
                  :exec  (the (unsigned-byte 32) (logand #uxFFFF_FFFF (ash xmm -96)))))
       (xmm/mem3 (mbe :logic (part-select xmm/mem :low 96 :high 127)
                      :exec  (the (unsigned-byte 32) (logand #uxFFFF_FFFF (ash xmm/mem -96)))))

       (mxcsr (the (unsigned-byte 32) (mxcsr x86)))

       ((mv flg1
            (the (unsigned-byte 32) result0)
            (the (unsigned-byte 32) mxcsr0))
        (sp-sse-add/sub/mul/div/max/min operation xmm0 xmm/mem0 mxcsr))

       ((when flg1)
        (!!ms-fresh :sp-sse-add/sub/mul/div/max/min flg1))

       ((mv flg2
            (the (unsigned-byte 32) result1)
            (the (unsigned-byte 32) mxcsr1))
        (sp-sse-add/sub/mul/div/max/min operation xmm1 xmm/mem1 mxcsr))

       ((when flg2)
        (!!ms-fresh :sp-sse-add/sub/mul/div/max/min flg2))

       ((mv flg3
            (the (unsigned-byte 32) result2)
            (the (unsigned-byte 32) mxcsr2))
        (sp-sse-add/sub/mul/div/max/min operation xmm2 xmm/mem2 mxcsr))

       ((when flg3)
        (!!ms-fresh :sp-sse-add/sub/mul/div/max/min flg3))

       ((mv flg4
            (the (unsigned-byte 32) result3)
            (the (unsigned-byte 32) mxcsr3))
        (sp-sse-add/sub/mul/div/max/min operation xmm3 xmm/mem3 mxcsr))

       ((when flg4)
        (!!ms-fresh :sp-sse-add/sub/mul/div/max/min flg4))

       (result (merge-4-u32s result3 result2 result1 result0))

       (mxcsr (the (unsigned-byte 32)
                (logior mxcsr0 mxcsr1 mxcsr2 mxcsr3)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Add/Sub/Mul/Div/Max/Min packed double-precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  66 0F 58: ADDPD xmm1, xmm2/m128<br/>
  66 0F 59: MULPD xmm1, xmm2/m128<br/>
  66 0F 5C: SUBPD xmm1, xmm2/m128<br/>
  66 0F 5D: MINPD xmm1, xmm2/m128<br/>
  66 0F 5E: DIVPD xmm1, xmm2/m128<br/>
  66 0F 5F: MAXPD xmm1, xmm2/m128<br/>"

  :operation t

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

       (inst-ac?
        ;; Exceptions Type 2
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

       (xmm0 (mbe :logic (part-select xmm :low 0 :high 63)
                  :exec  (the (unsigned-byte 64)
                           (logand #uxFFFF_FFFF_FFFF_FFFF xmm))))
       (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 63)
                      :exec  (the (unsigned-byte 64)
                               (logand #uxFFFF_FFFF_FFFF_FFFF xmm/mem))))

       (xmm1 (mbe :logic (part-select xmm :low 64 :high 127)
                  :exec  (the (unsigned-byte 64)
                           (logand #uxFFFF_FFFF_FFFF_FFFF (ash xmm -64)))))
       (xmm/mem1 (mbe :logic (part-select xmm/mem :low 64 :high 127)
                      :exec  (the (unsigned-byte 64)
                               (logand #uxFFFF_FFFF_FFFF_FFFF (ash xmm/mem -64)))))

       (mxcsr (the (unsigned-byte 32) (mxcsr x86)))

       ((mv flg1
            (the (unsigned-byte 64) result0)
            (the (unsigned-byte 32) mxcsr0))
        (dp-sse-add/sub/mul/div/max/min operation xmm0 xmm/mem0 mxcsr))

       ((when flg1)
        (!!ms-fresh :dp-sse-add/sub/mul/div/max/min flg1))

       ((mv flg2
            (the (unsigned-byte 64) result1)
            (the (unsigned-byte 32) mxcsr1))
        (dp-sse-add/sub/mul/div/max/min operation xmm1 xmm/mem1 mxcsr))

       ((when flg2)
        (!!ms-fresh :dp-sse-add/sub/mul/div/max/min flg2))

       (result (merge-2-u64s result1 result0))

       (mxcsr (the (unsigned-byte 32)
                (logior mxcsr0 mxcsr1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================

(def-inst x86-sqrts?-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Square root of scalar single/double precision floating-point value"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  F3 0F 51: SQRTSS xmm1, xmm2/m32<br/>
  F2 0F 51: SQRTSD xmm1, xmm2/m64<br/>"

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

       (inst-ac?
        ;; Exceptions Type 3
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

       ((mv flg1 result (the (unsigned-byte 32) mxcsr))
        (if (equal sp/dp #.*OP-DP*)
            (dp-sse-sqrt xmm/mem (mxcsr x86))
          (sp-sse-sqrt xmm/mem (mxcsr x86))))

       ((when flg1)
        (if (equal sp/dp #.*OP-DP*)
            (!!ms-fresh :dp-sse-sqrt flg1)
          (!!ms-fresh :sp-sse-sqrt flg1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size operand-size xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

(def-inst x86-sqrtps-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Square roots of packed single-precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  0F 51: SQRTPS xmm1, xmm2/m128<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))

       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac?
        ;; Exceptions Type 2
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

       (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 31)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF xmm/mem))))

       (xmm/mem1 (mbe :logic (part-select xmm/mem :low 32 :high 63)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -32)))))

       (xmm/mem2 (mbe :logic (part-select xmm/mem :low 64 :high 95)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -64)))))

       (xmm/mem3 (mbe :logic (part-select xmm/mem :low 96 :high 127)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -96)))))

       (mxcsr (the (unsigned-byte 32) (mxcsr x86)))

       ((mv flg1
            (the (unsigned-byte 32) result0)
            (the (unsigned-byte 32) mxcsr0))
        (sp-sse-sqrt xmm/mem0 mxcsr))

       ((when flg1)
        (!!ms-fresh :sp-sse-sqrt flg1))

       ((mv flg2
            (the (unsigned-byte 32) result1)
            (the (unsigned-byte 32) mxcsr1))
        (sp-sse-sqrt xmm/mem1 mxcsr))

       ((when flg2)
        (!!ms-fresh :sp-sse-sqrt flg2))

       ((mv flg3
            (the (unsigned-byte 32) result2)
            (the (unsigned-byte 32) mxcsr2))
        (sp-sse-sqrt xmm/mem2 mxcsr))

       ((when flg3)
        (!!ms-fresh :sp-sse-sqrt flg3))

       ((mv flg4
            (the (unsigned-byte 32) result3)
            (the (unsigned-byte 32) mxcsr3))
        (sp-sse-sqrt xmm/mem3 mxcsr))

       ((when flg4)
        (!!ms-fresh :sp-sse-sqrt flg4))

       (result (merge-4-u32s result3 result2 result1 result0))

       (mxcsr (the (unsigned-byte 32)
                (logior mxcsr0 mxcsr1 mxcsr2 mxcsr3)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-sqrtpd-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Square roots packed double-precision floating-point values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  66 0F 51: SQRTPD xmm1, xmm2/m128<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))

       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac?
        ;; Exceptions Type 2
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

       (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 63)
                      :exec  (the (unsigned-byte 64)
                               (logand #uxFFFF_FFFF_FFFF_FFFF xmm/mem))))

       (xmm/mem1 (mbe :logic (part-select xmm/mem :low 64 :high 127)
                      :exec  (the (unsigned-byte 64)
                               (logand #uxFFFF_FFFF_FFFF_FFFF (ash xmm/mem -64)))))

       (mxcsr (the (unsigned-byte 32) (mxcsr x86)))

       ((mv flg1
            (the (unsigned-byte 64) result0)
            (the (unsigned-byte 32) mxcsr0))
        (dp-sse-sqrt xmm/mem0 mxcsr))

       ((when flg1)
        (!!ms-fresh :dp-sse-sqrt flg1))

       ((mv flg2
            (the (unsigned-byte 64) result1)
            (the (unsigned-byte 32) mxcsr1))
        (dp-sse-sqrt xmm/mem1 mxcsr))

       ((when flg2)
        (!!ms-fresh :dp-sse-sqrt flg2))

       (result (merge-2-u64s result1 result0))

       (mxcsr (the (unsigned-byte 32)
                (logior mxcsr0 mxcsr1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
