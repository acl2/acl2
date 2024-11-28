; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2024, Yahya Sohail
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
; Yahya Sohail        <yahya@yahyasohail.com>

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (disable unsigned-byte-p)))

(define pshuf-body-gen (n el-width src order)
  :mode :program
  (if (equal n 0)
    0
    `(logapp ,el-width (logtail (* ,el-width (loghead 2 ,order)) ,src)
             ,(pshuf-body-gen (1- n) el-width src `(logtail 2 ,order)))))

(defmacro pshuf-gen (suffix el-width)
  (b* ((fn-name (acl2::packn (list 'pshuf suffix))))
      `(define ,fn-name ((src :type (unsigned-byte ,(* 4 el-width)))
                         (order :type (unsigned-byte 8)))
         :returns (result (unsigned-byte-p ,(* 4 el-width) result))
         (b* ((src (n128 src))
              (order (mbe :logic (loghead 8 order)
                          :exec order)))
             ,(pshuf-body-gen 4 el-width 'src 'order)))))

(pshuf-gen d 32)
(pshuf-gen w 16)

(def-inst x86-pshufd
  :parents (two-byte-opcodes)
  :long
  "<code>
  PSHUFD xmm1, xmm2/m128, imm8
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))
  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08)))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 128 bits, i.e. 16 bytes.
       (operand-size 16)

       ((the (unsigned-byte 4) dst-index)
        (reg-index reg rex-byte #.*r*))

       ;; The source operand (Operand 2 in the Intel manual) is the XMM
       ;; register, or memory operand, specified in Mod and R/M.
       (inst-ac? t)
       ((mv flg
            (the (unsigned-byte 128) src)
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
                                               1 ;; One-byte immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ((mv flg (the (unsigned-byte 8) imm) x86)
        (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg)
        (!!ms-fresh :imm-rme-size-error flg))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result.
       (result (pshufd src imm))

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

(def-inst x86-pshuflw
  :parents (two-byte-opcodes)
  :long
  "<code>
  PSHUFLW xmm1, xmm2/m128, imm8
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))
  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08)))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 128 bits, i.e. 16 bytes.
       (operand-size 16)

       ((the (unsigned-byte 4) dst-index)
        (reg-index reg rex-byte #.*r*))

       ;; The source operand (Operand 2 in the Intel manual) is the XMM
       ;; register, or memory operand, specified in Mod and R/M.
       (inst-ac? t)
       ((mv flg
            (the (unsigned-byte 128) src)
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
                                               1 ;; One-byte immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ((mv flg (the (unsigned-byte 8) imm) x86)
        (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg)
        (!!ms-fresh :imm-rme-size-error flg))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result.
       (result (logapp 64 (pshufw (loghead 64 src) imm)
                       (logtail 64 src)))

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

(def-inst x86-pshufhw
  :parents (two-byte-opcodes)
  :long
  "<code>
  PSHUFHW xmm1, xmm2/m128, imm8
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))
  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08)))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 128 bits, i.e. 16 bytes.
       (operand-size 16)

       ((the (unsigned-byte 4) dst-index)
        (reg-index reg rex-byte #.*r*))

       ;; The source operand (Operand 2 in the Intel manual) is the XMM
       ;; register, or memory operand, specified in Mod and R/M.
       (inst-ac? t)
       ((mv flg
            (the (unsigned-byte 128) src)
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
                                               1 ;; One-byte immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ((mv flg (the (unsigned-byte 8) imm) x86)
        (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg)
        (!!ms-fresh :imm-rme-size-error flg))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result.
       (result (logapp 64 (loghead 64 src)
                       (pshufw (logtail 64 src) imm)))

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))
