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
              :ttags (:undef-flg))
(include-book "base"
              :ttags (:undef-flg))
(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; =============================================================================
; INSTRUCTION: SSE2 64-Bit SIMD Integer Instructions
; =============================================================================

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

(define packuswb ((src1 :type (unsigned-byte 128))
                  (src2 :type (unsigned-byte 128)))
  :returns (result (unsigned-byte-p 128 result))
  :prepwork
  ((defmacro packuswb-helper (n src)
     (if (equal n 8)
       0
       `(logapp 8 (max 0 (min 255 (logext 16 (logtail ,(* n 16) ,src))))
                (packuswb-helper ,(1+ n) ,src)))))
  (b* ((src1 (n128 src1))
       (src2 (n128 src2)))
      (logapp 64 (packuswb-helper 0 src1)
              (packuswb-helper 0 src2))))

(def-inst x86-packuswb-sse
  :parents (two-byte-opcodes)
  :long
  "<code>
  PACKUSWB xmm1, xmm2/m128
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))
  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))

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
       (result (packuswb src1 src2))

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size src1/dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

;; Used to define `psll`, `psrl`, and `psra`
;; Operator specifies how to compute the shift for a single element given the
;; element and count
;; width-opcode-alist is an alist mapping the el-width to the opcode for the
;; xmm version of the instruction
(defmacro def-packed-shift-sse-inst (name
                                     operator
                                     width-opcode-alist)
  (b* ((xmm-inst-name (acl2::packn (list 'x86- name '-xmm-sse)))
       (imm-inst-name (acl2::packn (list 'x86- name '-imm-sse))))
      `(progn
         (define ,name ((result-width natp)
                        (el-width posp)
                        (a natp)
                        (cnt natp))
           :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
           :guard (equal (mod result-width el-width) 0)
           :returns (result (unsigned-byte-p result-width result)
                            :hyp (and (natp result-width)
                                      (<= (pos-fix el-width) result-width)
                                      (equal (mod result-width (pos-fix el-width)) 0))
                            :hints (("Goal" :in-theory (disable unsigned-byte-p))))
           :measure (nfix result-width)
           (b* ((result-width (nfix result-width))
                (el-width (pos-fix el-width))
                (a (nfix a))
                (cnt (nfix cnt))
                ((when (zp result-width)) 0))
               (logapp el-width (,operator (loghead el-width a)
                                           cnt)
                       (,name (- result-width el-width) el-width
                              (logtail el-width a) cnt))))


     (def-inst ,xmm-inst-name
       :parents (two-byte-opcodes)
       :long
       ,(xdoc::topstring
          (xdoc::code
            (symbol-name name) "W xmm1, xmm2/m128" (string #\Newline)
            (symbol-name name) "D xmm1, xmm2/m128" (string #\Newline)
            ;; Since PSRA has no 64-bit variant
            (if (assoc 64 width-opcode-alist)
              (xdoc::&& (symbol-name name) "Q xmm1, xmm2/m128" (string #\Newline))
              "")))

       :modr/m t

       :returns (x86 x86p :hyp (x86p x86))
       :guard (member opcode ',(strip-cdrs width-opcode-alist))
       :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))

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
            ;; Intel's SDM states that if we're reading from memory,
            ;; while we read the whole 128 bits, we ignore the upper 64
            ;; bits
            (src2 (if (not (equal mod #b11))
                    (loghead 64 src2) ;; Memory operand
                    src2)) ;; Register operand

            (el-width (car (rassoc opcode ',width-opcode-alist)))
            ;; Clamp to el-width because src2 may be huge; it comes from an xmm
            ;; reg, so it may be up to 128-bits long. This may cause the host
            ;; lisp to throw an error
            (src2 (if (> src2 el-width)
                    el-width
                    src2))
            (result (,name (* 8 operand-size) el-width src1 src2))

            ;; Store the result into the destination register.
            (x86 (!xmmi-size operand-size src1/dst-index result x86))

            ;; Update the instruction pointer.
            (x86 (write-*ip proc-mode temp-rip x86)))
           x86))

     (def-inst ,imm-inst-name
       :parents (two-byte-opcodes)
       :long
       ,(xdoc::topstring
          (xdoc::code
            (symbol-name name) "W xmm1, imm8" (string #\Newline)
            (symbol-name name) "D xmm1, imm8" (string #\Newline)
            ;; Since PSRA has no 64-bit variant
            (if (assoc 64 width-opcode-alist)
              (xdoc::&& (symbol-name name) "Q xmm1, imm8" (string #\Newline))
              "")))

       :modr/m t

       :returns (x86 x86p :hyp (x86p x86))
       :guard (member opcode '(#x71 #x72 #x73))
       :guard-hints (("Goal" :in-theory (e/d (rme-size-of-1-to-rme08)
                                             (unsigned-byte-p))))

       :body

       (b* (;; The operand size is always 128 bits, i.e. 16 bytes.
            (operand-size 16)

            ;; The first source operand (Operand 1 in the Intel manual)
            ;; is the XMM register specified in Reg.
            ;; This is also the destination operand,
            ;; and thus we obtain the index for later use.
            ((the (unsigned-byte 4) src1/dst-index)
             (reg-index reg rex-byte #.*r*))
            ((the (unsigned-byte 128) src1)
             (xmmi-size operand-size src1/dst-index x86))

            ;; Read the immediate operand
            ((mv flg1 (the (unsigned-byte 8) imm) x86)
             (rme-size-opt proc-mode 1
                           (the (signed-byte #.*max-linear-address-size*) temp-rip)
                           #.*cs* :x nil x86 :mem-ptr? nil))
            ((when flg1)
             (!!ms-fresh :imm-rme-size-error flg1))

            ;; Increment the instruction pointer in the temp-rip variable.
            ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
             (add-to-*ip proc-mode temp-rip 1 x86))
            ((when flg) (!!ms-fresh :rip-increment-error flg))

            ;; Ensure the instruction is not too long.
            (badlength? (check-instruction-length start-rip temp-rip 0))
            ((when badlength?)
             (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

            ;; Calculate the result.
            ;; Note: these opcodes are always the same; the reg field specifies
            ;; which type of shift and that's handled at decode time
            (el-width (case opcode
                        (#x71 16)
                        (#x72 32)
                        (#x73 64)))
            (result (,name (* 8 operand-size) el-width src1 imm))

            ;; Store the result into the destination register.
            (x86 (!xmmi-size operand-size src1/dst-index result x86))

            ;; Update the instruction pointer.
            (x86 (write-*ip proc-mode temp-rip x86)))
           x86)))))

(def-packed-shift-sse-inst psll
  (lambda (a cnt) (ash a cnt))
  ((16 . #xF1)
   (32 . #xF2)
   (64 . #xF3)))

(def-packed-shift-sse-inst psrl
  (lambda (a cnt) (ash a (- cnt)))
  ((16 . #xD1)
   (32 . #xD2)
   (64 . #xD3)))

(def-packed-shift-sse-inst psra
  (lambda (a cnt) (ash (logext el-width a) (- cnt)))
  ((16 . #xE1)
   (32 . #xE2)))

;; ======================================================================
