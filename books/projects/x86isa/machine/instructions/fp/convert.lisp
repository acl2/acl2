; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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

(in-package "X86ISA")

;; ======================================================================

(include-book "../../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "cvt-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; =============================================================================
; INSTRUCTION: SSE/SSE2 Conversion Instructions
; =============================================================================

(def-inst x86-cvts?2si/cvtts?2si-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Convert scalar single/double precision FP value to integer"

  :long
  "<h3>Op/En = RM: \[OP REG, XMM/M\]</h3>
  F3       0F 2C: CVTTSS2SI r32, xmm2/m32<br/>
  F3 REX.W 0F 2C: CVTTSS2SI r64, xmm2/m32<br/>
  F3       0F 2D: CVTSS2SI  r32, xmm2/m32<br/>
  F3 REX.W 0F 2D: CVTSS2SI  r64, xmm2/m32<br/>

  F2       0F 2C: CVTTSD2SI r32, xmm2/m64<br/>
  F2 REX.W 0F 2C: CVTTSD2SI r64, xmm2/m64<br/>
  F2       0F 2D: CVTSD2SI  r32, xmm2/m64<br/>
  F2 REX.W 0F 2D: CVTSD2SI  r64, xmm2/m64<br/>"

  :sp/dp t

  :trunc t

  :guard-hints (("Goal" :in-theory (enable reg-index
                                           sp-sse-cvt-fp-to-int
                                           dp-sse-cvt-fp-to-int)))

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-cvts?2si/cvtts?2si-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (integer 4 8) reg-size)
        (if (logbitp #.*w* rex-byte) 8 4))

       ((the (integer 4 8) xmm/mem-size)
        (if (equal sp/dp #.*OP-DP*) 8 4))

       ((the (unsigned-byte 4) rgf-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       (inst-ac? ;; Exceptions Type 3
        t)
       ((mv flg0 xmm/mem (the (integer 0 4) increment-RIP-by) (the (signed-byte 64) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*xmm-access* xmm/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))

       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg1 result (the (unsigned-byte 32) mxcsr))
        (if (equal sp/dp #.*OP-DP*)
            (dp-sse-cvt-fp-to-int reg-size xmm/mem (mxcsr x86) trunc)
          (sp-sse-cvt-fp-to-int reg-size xmm/mem (mxcsr x86) trunc)))

       ((when flg1)
        (if (equal sp/dp #.*OP-DP*)
            (!!ms-fresh :dp-sse-cvt-fp-to-int flg1)
          (!!ms-fresh :sp-sse-cvt-fp-to-int flg1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!rgfi-size reg-size rgf-index result rex-byte x86))

       (x86 (!rip temp-rip x86)))
      x86)

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CVTTSS2SI #x0F2C
                                      '(:misc
                                        (eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes)))
                                      'x86-cvts?2si/cvtts?2si-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTTSS2SI #x0F2C
                                      '(:misc
                                        (eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
                                        (logbitp #.*w* rex-byte))
                                      'x86-cvts?2si/cvtts?2si-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTTSD2SI #x0F2C
                                      '(:misc
                                        (eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes)))
                                      'x86-cvts?2si/cvtts?2si-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTTSD2SI #x0F2C
                                      '(:misc
                                        (eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
                                        (logbitp #.*w* rex-byte))
                                      'x86-cvts?2si/cvtts?2si-Op/En-RM)

    (add-to-implemented-opcodes-table 'CVTSS2SI #x0F2D
                                      '(:misc
                                        (eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes)))
                                      'x86-cvts?2si/cvtts?2si-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTSS2SI #x0F2D
                                      '(:misc
                                        (eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes))
                                        (logbitp #.*w* rex-byte))
                                      'x86-cvts?2si/cvtts?2si-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTSD2SI #x0F2D
                                      '(:misc
                                        (eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes)))
                                      'x86-cvts?2si/cvtts?2si-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTSD2SI #x0F2D
                                      '(:misc
                                        (eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes))
                                        (logbitp #.*w* rex-byte))
                                      'x86-cvts?2si/cvtts?2si-Op/En-RM)))

(def-inst x86-cvtsi2s?-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Convert integer to scalar single/double precision FP value"

  :long
  "<h3>Op/En = RM: \[OP XMM, R/M\]</h3>
  F3       0F 2A: CVTSI2SS xmm, r/m32<br/>
  F3 REX.W 0F 2A: CVTSI2SS xmm, r/m64<br/>

  F2       0F 2A: CVTSI2SD xmm, r/m32<br/>
  F2 REX.W 0F 2A: CVTSI2SD xmm, r/m64<br/>"

  :sp/dp t

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-cvtsi2s?-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (integer 4 8) reg/mem-size)
        (if (logbitp #.*w* rex-byte) 8 4))

       ((the (integer 4 8) xmm-size)
        (if (equal sp/dp #.*OP-DP*) 8 4))

       ((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       (inst-ac? ;; Exceptions Type 3
        t)
       ((mv flg0 reg/mem (the (integer 0 4) increment-RIP-by) (the (signed-byte 64) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))

       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (reg/mem (if (int= reg/mem-size 4)
                    (n32-to-i32 reg/mem)
                  (n64-to-i64 reg/mem)))

       ((mv flg1 result (the (unsigned-byte 32) mxcsr))
        (if (equal sp/dp #.*OP-DP*)
            (dp-sse-cvt-int-to-fp reg/mem (mxcsr x86))
          (sp-sse-cvt-int-to-fp reg/mem (mxcsr x86))))

       ((when flg1)
        (if (equal sp/dp #.*OP-DP*)
            (!!ms-fresh :dp-sse-cvt-int-to-fp flg1)
          (!!ms-fresh :sp-sse-cvt-int-to-fp flg1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size xmm-size xmm-index result x86))

       (x86 (!rip temp-rip x86)))
    x86)

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CVTSI2SS #x0F2A
                                      '(:misc
                                        (eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes)))
                                      'x86-cvtsi2s?-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTSI2SS #x0F2A
                                      '(:misc
                                        (eql #.*mandatory-f3h* (prefixes-slice
                                                                :group-1-prefix prefixes))
                                        (logbitp #.*w* rex-byte))
                                      'x86-cvtsi2s?-Op/En-RM)

    (add-to-implemented-opcodes-table 'CVTSI2SD #x0F2A
                                      '(:misc
                                        (eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes)))
                                      'x86-cvtsi2s?-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTSI2SD #x0F2A
                                      '(:misc
                                        (eql #.*mandatory-f2h* (prefixes-slice
                                                                :group-1-prefix prefixes))
                                        (logbitp #.*w* rex-byte))
                                      'x86-cvtsi2s?-Op/En-RM)))

(def-inst x86-cvts?2s?-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Convert scalar single/double precision FP value to scalar
  double/single FP value"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  F3 0F 5A: CVTSS2SD xmm1, xmm2/m32<br/>
  F2 0F 5A: CVTSD2SS xmm1, xmm2/m64<br/>"

  :dp-to-sp t

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-cvts?2s?-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (integer 4 8) xmm-size)
        (if (equal dp-to-sp #.*DP-TO-SP*) 4 8))

       ((the (integer 4 8) xmm/mem-size)
        (if (equal dp-to-sp #.*DP-TO-SP*) 8 4))

       ((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       (inst-ac? ;; Exceptions Type 3
        t)
       ((mv flg0 xmm/mem (the (integer 0 4) increment-RIP-by) (the (signed-byte 64) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*xmm-access* xmm/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))

       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg1 result (the (unsigned-byte 32) mxcsr))
        (if (equal dp-to-sp #.*DP-TO-SP*)
            (sse-cvt-dp-to-sp xmm/mem (mxcsr x86))
          (sse-cvt-sp-to-dp xmm/mem (mxcsr x86))))

       ((when flg1)
        (if (equal dp-to-sp #.*DP-TO-SP*)
            (!!ms-fresh :sse-cvt-dp-to-sp flg1)
          (!!ms-fresh :sse-cvt-sp-to-dp flg1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size xmm-size xmm-index result x86))

       (x86 (!rip temp-rip x86)))
    x86)

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CVTSS2SD #x0F5A
                                      '(:misc
                                        (eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes)))
                                      'x86-cvts?2s?-Op/En-RM)
    (add-to-implemented-opcodes-table 'CVTSD2SS #x0F5A
                                      '(:misc
                                        (eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes)))
                                      'x86-cvts?2s?-Op/En-RM)))

(def-inst x86-cvtps2pd-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Convert packed single-precision FP values to packed double-precision
  FP values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  0F 5A: CVTPS2PD xmm1, xmm2/m64<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-cvtps2pd-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       ;; [Shilpi]: The Intel manual doesn't mention that a lock
       ;; prefix causes an exception for this opcode. Should the
       ;; following be removed then?
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       (inst-ac? ;; Note that VEX.256 version follows Exception Type 3
        ;; without #AC. We haven't implemented VEX.256 yet.
        t)
       ((mv flg0
            (the (unsigned-byte 64) xmm/mem)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*xmm-access* 8 inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))

       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 31)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF xmm/mem))))

       (xmm/mem1 (mbe :logic (part-select xmm/mem :low 32 :high 63)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -32)))))

       (mxcsr (the (unsigned-byte 32) (mxcsr x86)))

       ((mv flg1
            (the (unsigned-byte 64) result0)
            (the (unsigned-byte 32) mxcsr0))
        (sse-cvt-sp-to-dp xmm/mem0 mxcsr))

       ((when flg1)
        (!!ms-fresh :sse-cvt-sp-to-dp flg1))

       ((mv flg2
            (the (unsigned-byte 64) result1)
            (the (unsigned-byte 32) mxcsr1))
        (sse-cvt-sp-to-dp xmm/mem1 mxcsr))

       ((when flg2)
        (!!ms-fresh :sse-cvt-sp-to-dp flg2))

       (result (merge-2-u64s result1 result0))

       (mxcsr (the (unsigned-byte 32)
                (logior mxcsr0 mxcsr1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (!rip temp-rip x86)))
    x86)
  :implemented
  (add-to-implemented-opcodes-table 'CVTPS2PD #x0F5A
                                    '(:nil nil)
                                    'x86-cvtps2pd-Op/En-RM))

(def-inst x86-cvtpd2ps-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Convert packed double-precision FP values to packed single-precision
  FP values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  66 0F 5A: CVTPD2PS xmm1, xmm2/m128<br/>"

  :guard-hints (("Goal" :in-theory (enable merge-2-u32s)))

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-cvtpd2ps-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       (inst-ac?
        ;; Exceptions Type 2
        nil)
       ((mv flg0
            (the (unsigned-byte 128) xmm/mem)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*xmm-access* 16 inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))

       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Raise an error if v-addr is not 16-byte aligned.
       ;; In case the second operand is an XMM register, v-addr = 0.
       ((when (not (eql (mod v-addr 16) 0)))
        (!!ms-fresh :memory-address-is-not-16-byte-aligned v-addr))

       (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 63)
                      :exec  (the (unsigned-byte 64)
                               (logand #uxFFFF_FFFF_FFFF_FFFF xmm/mem))))

       (xmm/mem1 (mbe :logic (part-select xmm/mem :low 64 :high 127)
                      :exec  (the (unsigned-byte 64)
                               (logand #uxFFFF_FFFF_FFFF_FFFF (ash xmm/mem -64)))))

       (mxcsr (the (unsigned-byte 32) (mxcsr x86)))

       ((mv flg1
            (the (unsigned-byte 32) result0)
            (the (unsigned-byte 32) mxcsr0))
        (sse-cvt-dp-to-sp xmm/mem0 mxcsr))

       ((when flg1)
        (!!ms-fresh :sse-cvt-dp-to-sp flg1))

       ((mv flg2
            (the (unsigned-byte 32) result1)
            (the (unsigned-byte 32) mxcsr1))
        (sse-cvt-dp-to-sp xmm/mem1 mxcsr))

       ((when flg2)
        (!!ms-fresh :sse-cvt-dp-to-sp flg2))

       (result (merge-2-u32s result1 result0))

       (mxcsr (the (unsigned-byte 32)
                (logior mxcsr0 mxcsr1)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       ;; Bits[127:64] of the destination XMM register are zeroed.
       ;; Hence, we write 8-byte result into 16-byte destination XMM register.
       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (!rip temp-rip x86)))
    x86)
  :implemented
  (add-to-implemented-opcodes-table 'CVTPD2PS #x0F5A
                                    '(:misc
                                      (eql #.*mandatory-66h*
                                           (prefixes-slice :group-3-prefix prefixes)))
                                    'x86-cvtpd2ps-Op/En-RM))

;; ======================================================================
