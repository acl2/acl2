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
(include-book "cmp-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (defthm lemma-1
   (implies (and (unsigned-byte-p 128 x)
                 (unsigned-byte-p 128 y))
            (< (logxor x y)
               (expt 2 128)))
   :hints (("Goal"
            :in-theory (disable unsigned-byte-p-of-logxor)
            :use (:instance unsigned-byte-p-of-logxor
                            (n 128) (i x) (j y))))
   :rule-classes :linear))

; =============================================================================
; INSTRUCTION: SSE/SSE2 Logical Instructions
; =============================================================================

(def-inst x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

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

;; ======================================================================
;; INSTRUCTION: SSE/SSE2 Comparison Instructions
;; ======================================================================

(def-inst x86-cmpss/cmpsd-Op/En-RMI

  :parents (two-byte-opcodes fp-opcodes)

  :short "Compare scalar single/double precision floating-point values"

  :long
  "<h3>Op/En = RMI: \[OP XMM, XMM/M, IMM\]</h3>
  F3 0F C2: CMPSS xmm1, xmm2/m32, imm8<br/>
  F2 0F C2: CMPSD xmm1, xmm2/m64, imm8<br/>"

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
       (p4? (eql #.*addr-size-override*
                 (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 3
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
                                                1 ;; One-byte immediate operand
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ((mv flg1 (the (unsigned-byte 8) imm) x86)
        (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg1)
        (!!ms-fresh :imm-rme-size-error flg1))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg2 result (the (unsigned-byte 32) mxcsr))
        (if (equal sp/dp #.*OP-DP*)
            (dp-sse-cmp (n02 imm) xmm xmm/mem (mxcsr x86))
          (sp-sse-cmp (n02 imm) xmm xmm/mem (mxcsr x86))))

       ((when flg2)
        (if (equal sp/dp #.*OP-DP*)
            (!!ms-fresh :dp-sse-cmp flg2)
          (!!ms-fresh :sp-sse-cmp flg2)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size operand-size xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86)

  :guard-hints (("Goal" :in-theory (e/d (rme-size) (unsigned-byte-p)))))

(def-inst x86-cmpps-Op/En-RMI

  :parents (two-byte-opcodes fp-opcodes)

  :short "Compare packed single-precision floating-point values"

  :long
  "<h3>Op/En = RMI: \[OP XMM, XMM/M, IMM\]</h3>
  0F C2: CMPPS xmm1, xmm2/m128, imm8<br/>"

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

       (inst-ac? ;; Exceptions Type 2
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
                                                1 ;; One-byte immediate operand
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ((mv flg1 (the (unsigned-byte 8) imm) x86)
        (rme-size-opt proc-mode 1
                      (the (signed-byte #.*max-linear-address-size*) temp-rip)
                      #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg1)
        (!!ms-fresh :imm-rme-size-error flg1))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Raise an error if addr is not 16-byte aligned.
       ;; In case the second operand is an XMM register, addr = 0.
       ((when (not (eql (mod addr 16) 0)))
        (!!ms-fresh :memory-address-is-not-16-byte-aligned addr))

       (xmm0 (mbe :logic (part-select xmm :low 0 :high 31)
                  :exec  (the (unsigned-byte 32)
                           (logand #uxFFFF_FFFF xmm))))
       (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 31)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF xmm/mem))))

       (xmm1 (mbe :logic (part-select xmm :low 32 :high 63)
                  :exec  (the (unsigned-byte 32)
                           (logand #uxFFFF_FFFF (ash xmm -32)))))
       (xmm/mem1 (mbe :logic (part-select xmm/mem :low 32 :high 63)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -32)))))

       (xmm2 (mbe :logic (part-select xmm :low 64 :high 95)
                  :exec  (the (unsigned-byte 32)
                           (logand #uxFFFF_FFFF (ash xmm -64)))))
       (xmm/mem2 (mbe :logic (part-select xmm/mem :low 64 :high 95)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -64)))))

       (xmm3 (mbe :logic (part-select xmm :low 96 :high 127)
                  :exec  (the (unsigned-byte 32)
                           (logand #uxFFFF_FFFF (ash xmm -96)))))
       (xmm/mem3 (mbe :logic (part-select xmm/mem :low 96 :high 127)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -96)))))

       (mxcsr (the (unsigned-byte 32) (mxcsr x86)))

       (operation (the (unsigned-byte 3) (n02 imm)))

       ((mv flg2
            (the (unsigned-byte 32) result0)
            (the (unsigned-byte 32) mxcsr0))
        (sp-sse-cmp operation xmm0 xmm/mem0 mxcsr))

       ((when flg2)
        (!!ms-fresh :sp-sse-cmp flg2))

       ((mv flg3
            (the (unsigned-byte 32) result1)
            (the (unsigned-byte 32) mxcsr1))
        (sp-sse-cmp operation xmm1 xmm/mem1 mxcsr))

       ((when flg3)
        (!!ms-fresh :sp-sse-cmp flg3))

       ((mv flg4
            (the (unsigned-byte 32) result2)
            (the (unsigned-byte 32) mxcsr2))
        (sp-sse-cmp operation xmm2 xmm/mem2 mxcsr))

       ((when flg4)
        (!!ms-fresh :sp-sse-cmp flg4))

       ((mv flg5
            (the (unsigned-byte 32) result3)
            (the (unsigned-byte 32) mxcsr3))
        (sp-sse-cmp operation xmm3 xmm/mem3 mxcsr))

       ((when flg5)
        (!!ms-fresh :sp-sse-cmp flg5))

       (result (merge-4-u32s result3 result2 result1 result0))

       (mxcsr (the (unsigned-byte 32)
                (logior mxcsr0 mxcsr1 mxcsr2 mxcsr3)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86)

  :guard-hints (("Goal" :in-theory (e/d (rme-size) (unsigned-byte-p)))))

(def-inst x86-cmppd-Op/En-RMI

  :parents (two-byte-opcodes fp-opcodes)

  :short "Compare packed double-precision floating-point values"

  :long
  "<h3>Op/En = RMI: \[OP XMM, XMM/M, IMM\]</h3>
  66 0F C2: CMPPD xmm1, xmm2/m128, imm8<br/>"

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

       (inst-ac? ;; Exceptions Type 2
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
                                                1 ;; One-byte immediate operand
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ((mv flg1 (the (unsigned-byte 8) imm) x86)
        (rme-size-opt proc-mode 1
                      (the (signed-byte #.*max-linear-address-size*) temp-rip)
                      #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg1)
        (!!ms-fresh :imm-rme-size-error flg1))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
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

       (operation (the (unsigned-byte 3) (n02 imm)))

       ((mv flg2
            (the (unsigned-byte 64) result0)
            (the (unsigned-byte 32) mxcsr0))
        (dp-sse-cmp operation xmm0 xmm/mem0 mxcsr))

       ((when flg2)
        (!!ms-fresh :dp-sse-cmp flg2))

       ((mv flg3
            (the (unsigned-byte 64) result1)
            (the (unsigned-byte 32) mxcsr1))
        (dp-sse-cmp operation xmm1 xmm/mem1 mxcsr))

       ((when flg3)
        (!!ms-fresh :dp-sse-cmp flg3))

       (result (merge-2-u64s result1 result0))

       (mxcsr (the (unsigned-byte 32)
                (logior mxcsr0 mxcsr1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
      x86)

  :guard-hints (("Goal" :in-theory (e/d (rme-size) (unsigned-byte-p)))))

(def-inst x86-comis?/ucomis?-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Order/Unordered compare scalar single/double precision floating-point
  values and set EFLAGS"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
     0F 2E: UCOMISS xmm1, xmm2/m32<br/>
     0F 2F: COMISS  xmm1, xmm2/m32<br/>

  66 0F 2E: UCOMISD xmm1, xmm2/m64<br/>
  66 0F 2F: COMISD  xmm1, xmm2/m64<br/>"

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
       (p4? (eql #.*addr-size-override*
                 (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 3
        t)
       ((mv flg0
            xmm/mem
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?v-addr)
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
            (dp-sse-cmp operation xmm xmm/mem (mxcsr x86))
          (sp-sse-cmp operation xmm xmm/mem (mxcsr x86))))

       ((when flg1)
        (if (equal sp/dp #.*OP-DP*)
            (!!ms-fresh :dp-sse-cmp flg1)
          (!!ms-fresh :sp-sse-cmp flg1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       ;; Set ZF, PF, CF flags according to the comis?/ucomis? result.
       (x86
        (case result
          (0 (let* ((x86 (!flgi :cf 0 x86))
                    (x86 (!flgi :pf 0 x86))
                    (x86 (!flgi :zf 0 x86))
                    (x86 (!flgi :af 0 x86))
                    (x86 (!flgi :sf 0 x86))
                    (x86 (!flgi :of 0 x86)))
               x86))
          (1 (let* ((x86 (!flgi :cf 1 x86))
                    (x86 (!flgi :pf 0 x86))
                    (x86 (!flgi :zf 0 x86))
                    (x86 (!flgi :af 0 x86))
                    (x86 (!flgi :sf 0 x86))
                    (x86 (!flgi :of 0 x86)))
               x86))
          (7 (let* ((x86 (!flgi :cf 1 x86))
                    (x86 (!flgi :pf 1 x86))
                    (x86 (!flgi :zf 1 x86))
                    (x86 (!flgi :af 0 x86))
                    (x86 (!flgi :sf 0 x86))
                    (x86 (!flgi :of 0 x86)))
               x86))
          (otherwise ;; Must only be 4.
           (let* ((x86 (!flgi :cf 0 x86))
                  (x86 (!flgi :pf 0 x86))
                  (x86 (!flgi :zf 1 x86))
                  (x86 (!flgi :af 0 x86))
                  (x86 (!flgi :sf 0 x86))
                  (x86 (!flgi :of 0 x86)))
             x86))))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
