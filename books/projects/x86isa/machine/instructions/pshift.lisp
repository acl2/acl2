; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2026, Kestrel Technology, LLC
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

; Authors:
;   Cuong Chau        <ckcuong@cs.utexas.edu>
;   Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils" :ttags ())

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Left logical, right logical, and right arithmetic shifts.

(defmacro shift-spec-gen (name operator)
  (declare (xargs :guard (member-eq name '(psll psrl psra))))
  ;; OPERATOR specifies how to compute the shift for a single element
  ;; given the element A and the count CNT.
  (b* ((fn (mk-name name '-spec)))
    `(define ,fn ((result-width natp)
                  (el-width posp)
                  (a natp)
                  (cnt natp))
       :guard (equal (mod result-width el-width) 0)
       :returns (result (unsigned-byte-p result-width result)
                        :hyp (and (natp result-width)
                                  (<= (pos-fix el-width) result-width)
                                  (equal (mod result-width (pos-fix el-width))
                                         0))
                        :hints (("Goal" :in-theory (disable unsigned-byte-p))))
       (b* ((result-width (nfix result-width))
            (el-width (pos-fix el-width))
            (a (nfix a))
            (cnt (nfix cnt))
            ((when (zp result-width)) 0))
         (logapp el-width (,operator (loghead el-width a)
                                     cnt)
                 (,fn (- result-width el-width)
                      el-width
                      (logtail el-width a)
                      cnt)))
       :measure (nfix result-width)
       :prepwork ((local (include-book "arithmetic-5/top" :dir :system))))))

(shift-spec-gen psll (lambda (a cnt) (ash a cnt)))

(shift-spec-gen psrl (lambda (a cnt) (ash a (- cnt))))

(shift-spec-gen psra (lambda (a cnt) (ash (logext el-width a) (- cnt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PSLLW/PSSLD/PSSLQ, PSRLW/PSRLD/PSRLQ, PSRAW/PSRAD (SSE variants)

;; Used to define `PSLL`, `PSRL`, and `PSRA`:
;; WIDTH-OPCODE-ALIST is an alist mapping the EL-WIDTH to
;; the opcode for the XMM version of the instruction.
(defmacro def-packed-shift-sse-inst (name width-opcode-alist)
  (b* ((xmm-inst-name (acl2::packn (list 'x86- name '-xmm-sse)))
       (imm-inst-name (acl2::packn (list 'x86- name '-imm-sse)))
       (spec-fn (mk-name name '-spec)))
    `(progn

       (def-inst ,xmm-inst-name

         :parents (two-byte-opcodes)

         :long
         ,(xdoc::topstring
           (xdoc::code
            (symbol-name name) "W xmm1, xmm2/m128" (string #\Newline)
            (symbol-name name) "D xmm1, xmm2/m128" (string #\Newline)
            ;; Since PSRA has no 64-bit variant
            (if (assoc 64 width-opcode-alist)
                (xdoc::&&
                 (symbol-name name) "Q xmm1, xmm2/m128" (string #\Newline))
              "")))

         :guard (member opcode ',(strip-cdrs width-opcode-alist))

         :modr/m t

         :returns (x86 x86p :hyp (x86p x86))

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
              (result (,spec-fn (* 8 operand-size) el-width src1 src2))

              ;; Store the result into the destination register.
              (x86 (!xmmi-size operand-size src1/dst-index result x86))

              ;; Update the instruction pointer.
              (x86 (write-*ip proc-mode temp-rip x86)))

           x86)

         :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

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

         :guard (member opcode '(#x71 #x72 #x73))

         :modr/m t

         :returns (x86 x86p :hyp (x86p x86))

         :body

         (b* (;; The operand size is always 128 bits, i.e. 16 bytes.
              (operand-size 16)

              ;; The first source operand (Operand 1 in the Intel manual)
              ;; is the XMM register specified in r/m.
              ;; This is also the destination operand,
              ;; and thus we obtain the index for later use.
              ((the (unsigned-byte 4) src1/dst-index)
               (reg-index r/m rex-byte #.*b*))
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
              (result (,spec-fn (* 8 operand-size) el-width src1 imm))

              ;; Store the result into the destination register.
              (x86 (!xmmi-size operand-size src1/dst-index result x86))

              ;; Update the instruction pointer.
              (x86 (write-*ip proc-mode temp-rip x86)))

           x86)

         :guard-hints (("Goal" :in-theory (e/d (rme-size-of-1-to-rme08)
                                               (unsigned-byte-p))))))))

(def-packed-shift-sse-inst psll
  ((16 . #xF1)
   (32 . #xF2)
   (64 . #xF3)))

(def-packed-shift-sse-inst psrl
  ((16 . #xD1)
   (32 . #xD2)
   (64 . #xD3)))

(def-packed-shift-sse-inst psra
  ((16 . #xE1)
   (32 . #xE2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PSLLDQ/PSRLDQ (SSE variants)

(def-inst x86-pslldq/psrldq

  :parents (two-byte-opcodes)

  :short "Shift double quadword left/right logical (SSE variant)."

  :long
  "<code>
   PSLLDQ xmm1, imm8
   PSRLDQ xmm1, imm8
   </code>"

  :modr/m t

  :guard (member-equal (modr/m->reg modr/m) '(7 3))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (;; The index of the XMM register
       ;; is in the R/M portion of the ModR/M byte.
       ;; It can be extended by one bit via the REX byte.
       (reg-index (reg-index r/m rex-byte #.*b*))

       ;; Read the 128-bit (i.e. 16-byte) operand from the XMM register.
       (operand (xmmi-size 16 reg-index x86))

       ;; Read the shift count, which is an 8-bit immediate operand.
       ((mv flg count x86)
        (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86))
       ((when flg) (!!ms-fresh :rme-size-error flg))

       ;; Increment the instruction pointer by 1, to account for the imm8.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; According to Intel Manual (Dec 2023) Volume 2 Section 3.1.1.3,
       ;; imm8 indicates an 8-bit signed immediate operand,
       ;; i.e. an integer between -128 and +127.
       ;; However, the Intel Manual describes PSRLDQ
       ;; as if the count were unsigned:
       ;; it says what happens if it is greater than 15,
       ;; but it does not say what happens if it is negative.
       ;; We interpret this as if the imm8 is actually signed in this case;
       ;; thus, a negative value (if signed) is treated as
       ;; an unsigned value larger than 15.
       ;; If the count is larger than 15, the result is just 0.
       ;; If instead the count is between 0 and 15,
       ;; the operand is shifted by that number of bytes to the left or right,
       ;; and in the case of a left shift we only keep the low 128 bits.
       ;; We automatically get 0 as result if the count is larger than 15.
       ;; The left (PSLLDQ) vs. right (PSRLDQ)
       ;; is determined by the Reg byte, which is an opcode extension.
       ((the (unsigned-byte 128) result)
        (case reg
          (7 (logand (1- (expt 2 128)) (ash operand (* 8 count))))
          (3 (ash operand (- (* 8 count))))
          (t (prog2$ (acl2::impossible) 0))))

       ;; Write the result into the register.
       (x86 (!xmmi-size 16 reg-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p natp)))

  :prepwork
  ((defrulel verify-guards-lemma
     (implies (and (unsigned-byte-p 128 a)
                   (natp b))
              (unsigned-byte-p 128 (ash a (- (* 8 b))))))))
