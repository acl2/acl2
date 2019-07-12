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
; INSTRUCTION: SSE2 64-Bit SIMD Integer Instructions
; =============================================================================

(def-inst x86-pcmpeqb-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Compare packed bytes for equal"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  66 0F 74: PCMPEQB xmm1, xmm2/m128<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork

  ((define pcmpeqb32 ((xmm n32p)
                      (xmm/mem n32p))
     :inline t
     :no-function t

     (let* ((xmm0 (mbe :logic (part-select xmm :low 0 :high 7)
                       :exec  (the (unsigned-byte 8)
                                (logand #xFF xmm))))
            (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 7)
                           :exec  (the (unsigned-byte 8)
                                    (logand #xFF xmm/mem))))

            (xmm1 (mbe :logic (part-select xmm :low 8 :high 15)
                       :exec  (the (unsigned-byte 8)
                                (logand #xFF (ash xmm -8)))))
            (xmm/mem1 (mbe :logic (part-select xmm/mem :low 8 :high 15)
                           :exec  (the (unsigned-byte 8)
                                    (logand #xFF (ash xmm/mem -8)))))

            (xmm2 (mbe :logic (part-select xmm :low 16 :high 23)
                       :exec  (the (unsigned-byte 8)
                                (logand #xFF (ash xmm -16)))))
            (xmm/mem2 (mbe :logic (part-select xmm/mem :low 16 :high 23)
                           :exec  (the (unsigned-byte 8)
                                    (logand #xFF (ash xmm/mem -16)))))

            (xmm3 (mbe :logic (part-select xmm :low 24 :high 31)
                       :exec  (the (unsigned-byte 8)
                                (logand #xFF (ash xmm -24)))))
            (xmm/mem3 (mbe :logic (part-select xmm/mem :low 24 :high 31)
                           :exec  (the (unsigned-byte 8)
                                    (logand #xFF (ash xmm/mem -24)))))

            (byte0 (the (unsigned-byte 8)
                     (if (int= xmm0 xmm/mem0) #xFF 0)))
            (byte1 (the (unsigned-byte 8)
                     (if (int= xmm1 xmm/mem1) #xFF 0)))
            (byte2 (the (unsigned-byte 8)
                     (if (int= xmm2 xmm/mem2) #xFF 0)))
            (byte3 (the (unsigned-byte 8)
                     (if (int= xmm3 xmm/mem3) #xFF 0)))

            (dword (merge-4-u8s byte3 byte2 byte1 byte0)))
       dword)

     ///

     (defthm-unsigned-byte-p n32p-pcmpeqb32
       :bound 32
       :concl (pcmpeqb32 xmm xmm/mem)
       :gen-type t
       :gen-linear t)))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))
       ((the (unsigned-byte 128) xmm)
        (xmmi-size 16 xmm-index x86))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; Cuong: Although this requirement is not specified in the
       ;; Intel manual, I got a segmentation fault when trying with
       ;; non 16-byte aligned addresses on a real machine.
       (inst-ac? ;; Exceptions Type 4
        t) ;; This should be nil according to the Intel manuals, but
       ;; see comment above.
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

       (dword0 (the (unsigned-byte 32)
                 (pcmpeqb32 xmm0 xmm/mem0)))
       (dword1 (the (unsigned-byte 32)
                 (pcmpeqb32 xmm1 xmm/mem1)))
       (dword2 (the (unsigned-byte 32)
                 (pcmpeqb32 xmm2 xmm/mem2)))
       (dword3 (the (unsigned-byte 32)
                 (pcmpeqb32 xmm3 xmm/mem3)))

       (result (merge-4-u32s dword3 dword2 dword1 dword0))

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

(def-inst x86-pmovmskb-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move byte mask"

  :long
  "<h3>Op/En = RM: \[OP REG, XMM\]</h3>
  66 0F D7: PMOVMSKB reg, xmm<br/>"

  :guard-hints (("Goal" :in-theory (enable reg-index merge-2-u8s)))

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork

  ((define pmovmskb8 ((xmm n64p))
     :inline t
     :no-function t

     (let* ((bit0  (logbit   7 xmm))
            (bit1  (logbit  15 xmm))
            (bit2  (logbit  23 xmm))
            (bit3  (logbit  31 xmm))
            (bit4  (logbit  39 xmm))
            (bit5  (logbit  47 xmm))
            (bit6  (logbit  55 xmm))
            (bit7  (logbit  63 xmm))

            (two-bit0 (the (unsigned-byte 2)
                        (logior (the (unsigned-byte 2) (ash bit1 1))
                                bit0)))
            (two-bit1 (the (unsigned-byte 2)
                        (logior (the (unsigned-byte 2) (ash bit3 1))
                                bit2)))
            (two-bit2 (the (unsigned-byte 2)
                        (logior (the (unsigned-byte 2) (ash bit5 1))
                                bit4)))
            (two-bit3 (the (unsigned-byte 2)
                        (logior (the (unsigned-byte 2) (ash bit7 1))
                                bit6)))

            (four-bit0 (the (unsigned-byte 4)
                         (logior (the (unsigned-byte 4) (ash two-bit1 2))
                                 two-bit0)))
            (four-bit1 (the (unsigned-byte 4)
                         (logior (the (unsigned-byte 4) (ash two-bit3 2))
                                 two-bit2)))

            (byte (the (unsigned-byte 8)
                    (logior (the (unsigned-byte 8) (ash four-bit1 4))
                            four-bit0))))
       byte)

     ///

     (defthm-unsigned-byte-p n08p-pmovmskb8
       :bound 8
       :concl (pmovmskb8 xmm)
       :gen-type t
       :gen-linear t)))

  :modr/m t

  :body

  (b* (((the (unsigned-byte 4) rgf-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? ;; Exceptions Type 7
        nil)
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

       (xmm0 (mbe :logic (part-select xmm :low 0 :high 63)
                  :exec  (the (unsigned-byte 64)
                           (logand #uxFFFF_FFFF_FFFF_FFFF xmm))))
       (xmm1 (mbe :logic (part-select xmm :low 64 :high 127)
                  :exec  (the (unsigned-byte 64)
                           (logand #uxFFFF_FFFF_FFFF_FFFF
                                   (ash xmm -64)))))

       (byte0 (the (unsigned-byte 8) (pmovmskb8 xmm0)))
       (byte1 (the (unsigned-byte 8) (pmovmskb8 xmm1)))

       (result (merge-2-u8s byte1 byte0))

       ;; Update the x86 state:
       (x86 (!rgfi-size 8 rgf-index result rex-byte x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
