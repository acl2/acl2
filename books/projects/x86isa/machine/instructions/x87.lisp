; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail
; Copyright (C) May 2024 - August 2024, Intel Corporation

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
; Yahya Sohail        <yahya.sohail@intel.com>

(in-package "X86ISA")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../top-level-memory")
(include-book "fp/base")

(define write-mm-regs ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
                       (inst-ac? booleanp)
                       (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
                       (start-reg :type (unsigned-byte 3))
                       (start-addr :type (signed-byte 64))
                       (cnt :type (integer 0 16))
                       x86)
  :guard (and (signed-byte-p 64 (+ start-addr (* cnt 16)))
              (<= (+ cnt start-reg) 8))
  :measure (nfix (- 16 start-reg))
  :returns (mv (flg booleanp)
               (x86 x86p :hyp (x86p x86)))
  (if (mbt (unsigned-byte-p 3 start-reg))
    (b* ((ctx 'write-mm-regs)
         ((when (equal cnt 0)) (mv nil x86))
         ((mv flg x86) (wme128 proc-mode start-addr seg-reg (fp-datai start-reg x86) inst-ac? x86))
         ((when flg) (b* ((x86 (!!ms-fresh :wme128 proc-mode flg)))
                         (mv t x86)))
         (cnt-1 (1- cnt))
         ((when (equal cnt-1 0)) (mv nil x86)))
        (write-mm-regs proc-mode inst-ac? seg-reg (1+ start-reg) (+ start-addr 16) cnt-1 x86))
    (mv nil x86)))

(define write-xmm-regs ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
                        (inst-ac? booleanp)
                        (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
                        (start-reg :type (unsigned-byte 4))
                        (start-addr :type (signed-byte 64))
                        (cnt :type (integer 0 16))
                        x86)
  :guard (and (signed-byte-p 64 (+ start-addr (* cnt 16)))
              (<= (+ cnt start-reg) 16))
  :measure (nfix (- 16 start-reg))
  :returns (mv (flg booleanp)
               (x86 x86p :hyp (x86p x86)))
  (if (mbt (unsigned-byte-p 4 start-reg))
    (b* ((ctx 'write-xmm-regs)
        ((when (equal cnt 0)) (mv nil x86))
        ((mv flg x86) (wme128 proc-mode start-addr seg-reg (rx128 start-reg x86) inst-ac? x86))
        ((when flg) (b* ((x86 (!!ms-fresh :wme128 proc-mode flg)))
                        (mv t x86)))
        (cnt-1 (1- cnt))
        ((when (equal cnt-1 0)) (mv nil x86)))
       (write-xmm-regs proc-mode inst-ac? seg-reg (1+ start-reg) (+ start-addr 16) cnt-1 x86))
    (mv nil x86)))

(def-inst x86-fxsave/fxsave64

          ;; Op/En: M
          ;; 0F AE /0: fxsave
          ;; REX.W + 00F AE /0: fxsave64

          :parents (two-byte-opcodes)

          :returns (x86 x86p :hyp (x86p x86))

          :modr/m t

          :prepwork
          ((local (in-theory (disable unsigned-byte-p signed-byte-p
                                      same-page-offset-implies-same-logheads
                                      logand-identity-lemma-for-base-addr)))
           (local (defthm integerp-fp-tag
                          (integerp (xr :fp-tag i x86))
                          :hints (("Goal" :use (:instance elem-p-of-xr-fp-tag (i i) (x86$a x86))
                                   :in-theory (disable elem-p-of-xr-mxcsr)))))
           (local (defthm unsigned-byte-p-64-fp-last-inst
                          (unsigned-byte-p 64 (xr :fp-last-inst i x86))
                          :hints (("Goal" :use (:instance elem-p-of-xr-fp-last-inst (i i) (x86$a x86))
                                   :in-theory (disable elem-p-of-xr-fp-last-inst)))))
           (local (defthm unsigned-byte-p-64-fp-last-data
                          (unsigned-byte-p 64 (xr :fp-last-data i x86))
                          :hints (("Goal" :use (:instance elem-p-of-xr-fp-last-data (i i) (x86$a x86))
                                   :in-theory (disable elem-p-of-xr-fp-last-data)))))
           (local (defthm unsigned-byte-p-16-fp-opcode
                          (unsigned-byte-p 16 (xr :fp-opcode i x86))
                          :hints (("Goal" :use (:instance elem-p-of-xr-fp-opcode (i i) (x86$a x86))
                                   :in-theory (disable elem-p-of-xr-fp-opcode))))))

          :body

          (b* ((p2 (prefixes->seg prefixes))
               (p4? (equal #.*addr-size-override*
                           (prefixes->adr prefixes)))
               ((the (integer 1 8) operand-size)
                (select-operand-size proc-mode nil rex-byte nil prefixes nil nil nil x86))
               (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
               (inst-ac? t)
               ((mv flg & (the (unsigned-byte 3) increment-RIP-by) (the (signed-byte 64) dest-addr) x86)
                (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                       0
                                                       operand-size
                                                       inst-ac?
                                                       t ;; Memory ptr operand
                                                       seg-reg
                                                       p4?
                                                       temp-rip
                                                       rex-byte
                                                       r/m
                                                       mod
                                                       sib
                                                       0 ;; No immediate operand
                                                       x86))
               ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))
               ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
                (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
               ((when flg) (!!ms-fresh :rip-increment-error temp-rip))
               ((unless (signed-byte-p 64 (+ 512 dest-addr))) (!!ms-fresh :fxsave-address-overflow))

               ((mv flg x86) (wme16 proc-mode dest-addr seg-reg (fp-ctrl x86) inst-ac? x86))
               ((when flg) (!!ms-fresh :wme16 proc-mode flg))
               ((mv flg x86) (wme16 proc-mode (+ 2 dest-addr) seg-reg (fp-status x86) inst-ac? x86))
               ((when flg) (!!ms-fresh :wme16 proc-mode flg))

               ;; The fp-tag register has two bits for each register. FXSAVE
               ;; saves only one bit per register in the FTW field, 0 if the
               ;; corresponding fp-tag bits are 11 and 1 otherwise.
               (fp-tag (fp-tag x86))
               (odd-tag-bits (logand #xAAAA fp-tag))
               (ftw (logand (ash odd-tag-bits -1) fp-tag))
               ;; Now we have the ftw values, but theres a 0 bit between each
               ;; bit. Each `iteration` in the following takes pairs of
               ;; `gathered` subfields and pushes them together
               (ftw (logior (ash (logand ftw #x4444) -1)
                            (logand ftw #x1111)))
               (ftw (logior (ash (logand ftw #x3030) -2)
                            (logand ftw #x0303)))
               (ftw (logior (ash (logand ftw #x0F00) -4)
                            (logand ftw #x000F)))
               ;; ftw currently is 1 for each register that has a tag of 11 and
               ;; 0 otherwise, so we just flip it
               (ftw (loghead 8 (lognot ftw)))
               ((mv flg x86) (wme08 proc-mode (+ 4 dest-addr) seg-reg ftw x86))
               ((when flg) (!!ms-fresh :wme08 proc-mode flg))

               ((mv flg x86) (wme16 proc-mode (+ 6 dest-addr) seg-reg (fp-opcode x86) inst-ac? x86))
               ((when flg) (!!ms-fresh :wme16 proc-mode flg))

               ;; The manual breaks this field up into FCS and FIP when operand
               ;; size is not 64-bit, but all the cases are equivalent to the
               ;; following
               ((mv flg x86) (wme64 proc-mode (+ 8 dest-addr) seg-reg (fp-last-inst x86) inst-ac? x86))
               ((when flg) (!!ms-fresh :wme64 proc-mode flg))

               ((mv flg x86) (wme64 proc-mode (+ 16 dest-addr) seg-reg (fp-last-data x86) inst-ac? x86))
               ((when flg) (!!ms-fresh :wme64 proc-mode flg))

               ((mv flg x86) (wme32 proc-mode (+ 24 dest-addr) seg-reg (mxcsr x86) inst-ac? x86))
               ((when flg) (!!ms-fresh :wme32 proc-mode flg))
               ((mv flg x86) (wme32 proc-mode (+ 28 dest-addr) seg-reg #xFFFF inst-ac? x86))
               ((when flg) (!!ms-fresh :wme32 proc-mode flg))

               ((mv flg x86) (write-mm-regs proc-mode inst-ac? seg-reg 0 (+ 32 dest-addr) 8 x86))
               ;; write-mm-regs sets ms in the event of a fault
               ((when flg) x86)

               ((mv flg x86) (write-xmm-regs proc-mode inst-ac? seg-reg 0 (+ 160 dest-addr)
                                             (if (equal proc-mode *64-bit-mode*) 16 8) x86))
               ;; write-xmm-regs sets ms in the event of a fault
               ((when flg) x86))
              (write-*ip proc-mode temp-rip x86)))

(define read-mm-regs ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
                       (inst-ac? booleanp)
                       (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
                       (start-reg :type (unsigned-byte 3))
                       (start-addr :type (signed-byte 64))
                       (cnt natp)
                       x86)
  :guard (and (signed-byte-p 64 (+ start-addr (* (1- cnt) 16)))
              (<= cnt (- 8 start-reg)))
  :returns (mv (flg booleanp)
               (x86 x86p :hyp (x86p x86)))
  :measure (nfix (- 8 start-reg))
  (if (mbt (unsigned-byte-p 3 start-reg))
    (b* ((ctx 'read-mm-regs)
       ((when (equal cnt 0)) (mv nil x86))
       ((mv flg val x86) (rme80 proc-mode start-addr seg-reg :r inst-ac? x86))
       ((when flg) (b* ((x86 (!!ms-fresh :rme80 proc-mode flg)))
                       (mv t x86)))
       (x86 (!fp-datai start-reg val x86))
       (cnt-1 (1- cnt))
       ((when (equal cnt-1 0)) (mv nil x86)))
      (read-mm-regs proc-mode inst-ac? seg-reg (1+ start-reg) (+ start-addr 16) cnt-1 x86))
    (mv nil x86)))

(define read-xmm-regs ((proc-mode :type (integer 0 #.*num-proc-modes-1*))
                       (inst-ac? booleanp)
                       (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
                       (start-reg :type (unsigned-byte 4))
                       (start-addr :type (signed-byte 64))
                       (cnt natp)
                       x86)
  :guard (and (signed-byte-p 64 (+ start-addr (* (1- cnt) 16)))
              (<= cnt (- 16 start-reg)))
  :returns (mv (flg booleanp)
               (x86 x86p :hyp (x86p x86)))
  :measure (nfix (- 16 start-reg))
  (if (mbt (unsigned-byte-p 4 start-reg))
    (b* ((ctx 'read-xmm-regs)
       ((when (equal cnt 0)) (mv nil x86))
       ((mv flg val x86) (rme128 proc-mode start-addr seg-reg :r inst-ac? x86))
       ((when flg) (b* ((x86 (!!ms-fresh :rme128 proc-mode flg)))
                       (mv t x86)))
       (x86 (wx128 start-reg val x86))
       (cnt-1 (1- cnt))
       ((when (equal cnt-1 0)) (mv nil x86)))
      (read-xmm-regs proc-mode inst-ac? seg-reg (1+ start-reg) (+ start-addr 16) cnt-1 x86))
    (mv nil x86)))

(define set-fp-tag ((ftw :type (unsigned-byte 8))
                    x86
                    &optional
                    ((start-reg :type (integer 0 8)) '0)
                    ((fp-tag :type (unsigned-byte 16)) '0))
  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p
                                            bitops::part-install-width-low)))
  :measure (nfix (- 8 start-reg))
  :returns (x86 x86p :hyp (x86p x86))
  (b* (((unless (mbt (and (<= 0 (- 8 start-reg))
                          (natp start-reg)))) x86)
       ((when (equal start-reg 8)) (!fp-tag fp-tag x86))
       (empty? (equal (loghead 1 ftw) 0))
       ;; Empty value
       ((when empty?)
        (set-fp-tag (logtail 1 ftw) x86 (1+ start-reg)
                    (part-install #b11 fp-tag :low (* 2 start-reg) :width 2)))

       (val (fp-datai start-reg x86))
       ((mv kind & & & &) (fp-decode val 15 64))
       (tag-val (case kind
                  ('zero #x01)
                  ('normal #x00)
                  (otherwise #x10))))
      (set-fp-tag (logtail 1 ftw) x86 (1+ start-reg)
                  (part-install tag-val fp-tag :low (* 2 start-reg) :width 2))))

(def-inst x86-fxrstor/fxrstor64

          ;; Op/En: M
          ;; 0F AE /0: fxrstor
          ;; REX.W + 00F AE /0: fxrstor64

          :parents (two-byte-opcodes)

          :returns (x86 x86p :hyp (x86p x86))

          :modr/m t

          :prepwork
          ((local (in-theory (disable unsigned-byte-p signed-byte-p))))

          :body

          (b* ((p2 (prefixes->seg prefixes))
               (p4? (equal #.*addr-size-override*
                           (prefixes->adr prefixes)))
               ((the (integer 1 8) operand-size)
                (select-operand-size proc-mode nil rex-byte nil prefixes nil nil nil x86))
               (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
               (inst-ac? t)
               ((mv flg & (the (unsigned-byte 3) increment-RIP-by) (the (signed-byte 64) src-addr) x86)
                (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                       0
                                                       operand-size
                                                       inst-ac?
                                                       t ;; Memory ptr operand
                                                       seg-reg
                                                       p4?
                                                       temp-rip
                                                       rex-byte
                                                       r/m
                                                       mod
                                                       sib
                                                       0 ;; No immediate operand
                                                       x86))
               ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))
               ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
                (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
               ((when flg) (!!ms-fresh :rip-increment-error temp-rip))
               ((unless (signed-byte-p 64 (+ 512 src-addr -1))) (!!ms-fresh :fxrstor-address-overflow))

               ((mv flg fp-ctrl x86) (rme16 proc-mode src-addr seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme16 proc-mode flg))
               (x86 (!fp-ctrl fp-ctrl x86))
               ((mv flg fp-status x86) (rme16 proc-mode (+ 2 src-addr) seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme16 proc-mode flg))
               (x86 (!fp-status fp-status x86))

               ;; Restoring fp-tag is hard because the save area only tells us
               ;; if the value is valid. We need to determine the rest of the
               ;; tag for valid entries ourselves. We read the FTW in now, but
               ;; we defer populating state until after we've populated the mm
               ;; registers.
               ((mv flg ftw x86) (rme08 proc-mode (+ 4 src-addr) seg-reg :r x86))
               ((when flg) (!!ms-fresh :rme08 proc-mode flg))

               ;; The SDM and our model says the FOP register is 11 bits, so
               ;; what do we do if the upper bits are set? I just clear them
               ;; for now
               ((mv flg fp-opcode x86) (rme16 proc-mode (+ 6 src-addr) seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme16 proc-mode flg))
               (x86 (!fp-opcode (loghead 11 fp-opcode) x86))

               ;; The manual breaks this field up into FCS and FIP when operand
               ;; size is not 64-bit, but all the cases are equivalent to the
               ;; following
               ((mv flg fp-last-inst x86) (rme32 proc-mode (+ 8 src-addr) seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme32 proc-mode flg))
               (x86 (!fp-last-inst fp-last-inst x86))

               ((mv flg fp-last-data x86) (rme32 proc-mode (+ 16 src-addr) seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme32 proc-mode flg))
               (x86 (!fp-last-data fp-last-data x86))

               ((mv flg mxcsr x86) (rme32 proc-mode (+ 24 src-addr) seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme32 proc-mode flg))
               ((mv flg mxcsr-mask x86) (rme32 proc-mode (+ 28 src-addr) seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme32 proc-mode flg))
               (mxcsr-mask (if (equal mxcsr-mask 0)
                             #x0000FFBF
                             mxcsr-mask))
               (mxcsr (logand mxcsr mxcsr-mask))
               ((when (not (equal (logand mxcsr #xFFFF0000) 0)))
                (!!fault-fresh :gp 0 :mxcsr-error mxcsr))
               (x86 (!mxcsr mxcsr x86))

               ((mv flg x86) (read-mm-regs proc-mode inst-ac? seg-reg 0 (+ 32 src-addr) 8 x86))
               ;; read-mm-regs sets ms in the event of a fault
               ((when flg) x86)

               ;; Set the fp-tag field using the ftw value we read earlier and
               ;; the mm register values we just read
               (x86 (set-fp-tag ftw x86))

               ((mv flg x86) (read-xmm-regs proc-mode inst-ac? seg-reg 0 (+ 160 src-addr)
                                            (if (equal proc-mode *64-bit-mode*) 16 8) x86))
               ;; read-xmm-regs sets ms if there is a fault
               ((when flg) x86))
              (write-*ip proc-mode temp-rip x86)))
