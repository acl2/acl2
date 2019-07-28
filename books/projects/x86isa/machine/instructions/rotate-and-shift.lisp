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
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "shifts-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "rotates-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR
;; ======================================================================

(local
 (defrule add-to-*ip-integerp-type
   (implies (and (integerp *ip)
                 (integerp delta))
            (integerp (mv-nth 1 (add-to-*ip proc-mode *ip delta x86))))
   :in-theory (e/d (add-to-*ip) ())
   :rule-classes (:rewrite :type-prescription)))

(def-inst x86-sal/sar/shl/shr/rcl/rcr/rol/ror

  :guard (not (equal (modr/m->reg modr/m) 6))

  :guard-hints (("Goal"
                 :in-theory (e/d ()
                                 (unsigned-byte-p
                                  not force (force)))))

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86)
                :hints (("Goal" :in-theory
                         (e/d ()
                              (trunc
                               select-operand-size
                               mv-nth-0-of-add-to-*ip-when-64-bit-modep
                               mv-nth-1-of-add-to-*ip-when-64-bit-modep
                               signed-byte-p
                               unsigned-byte-p
                               not force (force))))))

  :long
  "<p>
  Op/En: MI<br/>
  C0/0: ROL r/m8, imm8<br/>
  C0/1: ROR r/m8, imm8<br/>
  C0/2: RCL r/m8, imm8<br/>
  C0/3: RCR r/m8, imm8<br/>
  C0/4: SAL/SHL r/m8, imm8<br/>
  C0/5: SHR r/m8, imm8<br/>
  C0/7: SAR r/m8, imm8<br/>
  C1/0: ROL r/m16/32/64, imm8<br/>
  C1/1: ROR r/m16/32/64, imm8<br/>
  C1/2: RCL r/m16/32/64, imm8<br/>
  C1/3: RCR r/m16/32/64, imm8<br/>
  C1/4: SAL/SHL r/m16/32/64, imm8<br/>
  C1/5: SHR r/m16/32/64, imm8<br/>
  C1/7: SAR r/m16/32/64. imm8<br/>
  </p>

  <p>
  Op/En: M1<br/>
  D0/0: ROL r/m8, 1<br/>
  D0/1: ROR r/m8, 1<br/>
  D0/2: RCL r/m8, 1<br/>
  D0/3: RCR r/m8, 1<br/>
  D0/4: SAL/SHL r/m8, 1<br/>
  D0/5: SHR r/m8, 1<br/>
  D0/7: SAR r/m8, 1<br/>
  D1/0: ROL r/m16/32/64, 1<br/>
  D1/1: ROR r/m16/32/64, 1<br/>
  D1/2: RCL r/m16/32/64, 1<br/>
  D1/3: RCR r/m16/32/64, 1<br/>
  D1/4: SAL/SHL r/m16/32/64, 1<br/>
  D1/5: SHR r/m16/32/64, 1<br/>
  D1/7: SAR r/m16/32/64, 1<br/>
  </p>

  <p>
  Op/En: MC<br/>
  D2/0: ROL r/m8, CL<br/>
  D2/1: ROR r/m8, CL<br/>
  D2/2: RCL r/m8, CL<br/>
  D2/3: RCR r/m8, CL<br/>
  D2/4: SAL/SHL r/m8, CL<br/>
  D2/5: SHR r/m8, CL<br/>
  D2/7: SAR r/m8, CL<br/>
  D3/0: ROL r/m16/32/64, CL<br/>
  D3/1: ROR r/m16/32/64, CL<br/>
  D3/2: RCL r/m16/32/64, CL<br/>
  D3/3: RCR r/m16/32/64, CL<br/>
  D3/4: SAL/SHL r/m16/32/64, CL<br/>
  D3/5: SHR r/m16/32/64, CL<br/>
  D3/7: SAR r/m16/32/64, CL<br/>
  </p>"

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       (byte-operand? (or (equal opcode #xC0)
                          (equal opcode #xD0)
                          (equal opcode #xD2)))
       ((the (integer 0 8) ?reg/mem-size)
        (select-operand-size
         proc-mode byte-operand? rex-byte nil prefixes nil nil nil x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0 ?reg/mem (the (unsigned-byte 3) increment-RIP-by) addr x86)
        (x86-operand-from-modr/m-and-sib-bytes
         proc-mode #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         seg-reg p4? temp-rip rex-byte r/m mod sib
         ;; Bytes of immediate data (only relevant when RIP-relative
         ;; addressing is done to get ?reg/mem operand)
         (if (or (equal opcode #xC0)
                 (equal opcode #xC1))
             1
           0)
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ((mv flg1 shift/rotate-by x86)
        (case opcode
          ((#xD0 #xD1)
           (mv nil 1 x86))
          ((#xD2 #xD3)
           (mv nil (rr08 *rcx* rex-byte x86) x86))
          ((#xC0 #xC1)
           (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86))
          (otherwise ;; will not be reached
           (mv nil 0 x86))))
       ((when flg1)
        (!!ms-fresh :rme-size-error flg1))

       (countMask (if (logbitp #.*w* rex-byte)
                      #x3F
                    #x1F))
       (shift/rotate-by (logand countMask shift/rotate-by))

       ((mv flg (the (signed-byte #.*max-linear-address-size+1*) temp-rip))
        (if (or (equal opcode #xC0)
                (equal opcode #xC1))
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Computing the flags and the result:
       (input-rflags (the (unsigned-byte 32) (rflags x86)))

       ((mv result
            (the (unsigned-byte 32) output-rflags)
            (the (unsigned-byte 32) undefined-flags))
        (case reg
          (0
           ;; ROL
           (rol-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (1
           ;; ROR
           (ror-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (2
           ;; RCL
           (rcl-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (3
           ;; RCR
           (rcr-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (4
           ;; SAL/SHL
           (sal/shl-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (5
           ;; SHR
           (shr-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (7
           ;; SAR
           (sar-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          ;; The guard for this function will ensure that we don't
          ;; reach here.
          (otherwise
           (mv 0 0 0))))

       ;; Update the x86 state:

       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ((mv flg2 x86)
        (x86-operand-to-reg/mem proc-mode reg/mem-size
                                 inst-ac?
                                 nil ;; Not a memory pointer operand
                                 ;; TO-DO@Shilpi: Remove this trunc.
                                 (trunc reg/mem-size result)
                                 seg-reg
                                 addr
                                 rex-byte
                                 r/m
                                 mod
                                 x86))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
        (!!ms-fresh :x86-operand-to-reg/mem flg2))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: SHLD/SHRD
;; ======================================================================

(def-inst x86-shld/shrd

  :returns (x86 x86p :hyp (x86p x86))

  :parents (one-byte-opcodes)

  :short "Double-precision shift left or right."

  :long
  "<p>
   Op/En: MRI<br/>
   0F A4: SHLD r/m16, r16, imm8<br/>
   0F A4: SHLD r/m32, r32, imm8<br/>
   0F A4: SHLD r/m64, r64, imm8<br/>
   </p>

   <p>
   Op/En: MRC<br/>
   0F A5: SHLD r/m16, r16, CL<br/>
   0F A5: SHLD r/m32, r32, CL<br/>
   0F A5: SHLD r/m64, r64, CL<br/>
   </p>

   <p>
   Op/En: MRI<br/>
   0F AC: SHRD r/m16, r16, imm8<br/>
   0F AC: SHRD r/m32, r32, imm8<br/>
   0F AC: SHRD r/m64, r64, imm8<br/>
   </p>

   <p>
   Op/En: MRC<br/>
   0F AD: SHRD r/m16, r16, CL<br/>
   0F AD: SHRD r/m32, r32, CL<br/>
   0F AD: SHRD r/m64, r64, CL<br/>
   </p>"

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       ((the (integer 2 8) operand-size)
        (select-operand-size proc-mode
                             nil ; not a byte operand
                             rex-byte
                             nil ; not an immediate operand
                             prefixes
                             nil ; no 64-bit default in 64-bit mode
                             nil ; don't ignore REX in 64-bit mode
                             nil ; don't ignore P3 in 64-bit mode
                             x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; read destination operand:

       (inst-ac? t)
       ((mv flg dst-value increment-rip-by dst-addr x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               #.*gpr-access*
                                               operand-size
                                               inst-ac?
                                               nil ; not memory pointer operand
                                               seg-reg
                                               p4?
                                               temp-rip
                                               rex-byte
                                               r/m
                                               mod sib
                                               1 ; imm8
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; read source operand:

       (src-value (rgfi-size operand-size
                             (reg-index reg rex-byte #.*r*)
                             rex-byte
                             x86))

       ;; read count operand:

       ((mv flg count x86)
        (case opcode
          ((#xA4 #xAC) (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86))
          ((#xA5 #xAD) (mv nil (rr08 *rcx* rex-byte x86) x86))
          (otherwise (mv nil 0 x86)))) ; unreachable
       ((when flg) (!!ms-fresh :rme-size-error flg))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (case opcode
          ((#xA4 #xAC) (add-to-*ip proc-mode temp-rip 1 x86))
          ((#xA5 #xAD) (mv nil temp-rip))
          (otherwise (mv nil 0)))) ; unreachable
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; check instruction length now that we have read all of it:

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; mask count according to pseudocode (the text only mentions masking
       ;; when CL is used, but the pseudocode masks also if imm8 is used):

       (count-mask (if (logbitp #.*w* rex-byte)
                       #x3f
                     #x1f))
       (count (logand count-mask count))

       ;; compute result and flags:

       (input-rflags (the (unsigned-byte 32) (rflags x86)))

       ((mv result
            result-undefined?
            (the (unsigned-byte 32) output-rflags)
            (the (unsigned-byte 32) undefined-flags))
        (case opcode
          ((#xA4 #xA5) (shld-spec
                        operand-size dst-value src-value count input-rflags))
          ((#xAC #xAD) (shrd-spec
                        operand-size dst-value src-value count input-rflags))
          (otherwise (mv 0 nil 0 0)))) ; unreachable

       ((mv result x86)
        (if result-undefined?
            (undef-read x86)
          (mv result x86)))

       ;; update the state:

       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ((mv flg x86)
        (x86-operand-to-reg/mem proc-mode
                                operand-size
                                inst-ac?
                                nil ;; not memory pointer operand
                                (trunc operand-size result) ; TODO: remove trunc
                                seg-reg
                                dst-addr
                                rex-byte
                                r/m
                                mod
                                x86))
       ((when flg) (!!ms-fresh :x86-operand-to-reg/mem flg))

       (x86 (write-*ip proc-mode temp-rip x86)))

    x86))

;; ======================================================================
