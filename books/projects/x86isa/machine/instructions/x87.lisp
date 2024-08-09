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
          ((local (defthm integerp-mxcsr
                          (integerp (xr :mxcsr i x86))
                          :hints (("Goal" :use (:instance elem-p-of-xr-mxcsr (i i) (x86$a x86)) :in-theory (disable elem-p-of-xr-mxcsr)))))
           (local (defthm mxcsr-range
                          (and (<= 0 (xr :mxcsr i x86))
                               (< (xr :mxcsr i x86) (expt 2 32)))
                          :rule-classes :linear
                          :hints (("Goal" :use (:instance elem-p-of-xr-mxcsr (i i) (x86$a x86)) :in-theory (disable elem-p-of-xr-mxcsr))))))

          :body

          (b* ((p2 (prefixes->seg prefixes))
               (p4? (equal #.*addr-size-override*
                           (prefixes->adr prefixes)))
               ;; TODO this should always be a memory address size, right?
               ((the (integer 1 8) operand-size)
                (select-operand-size proc-mode nil rex-byte nil prefixes nil nil nil x86))
               (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
               (inst-ac? nil) ;; TODO check 16 byte alignment requirement
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

               ;; Most of the first 32 bytes of the output have to do with the x87 state,
               ;; which has not been implemented
               ;; The only thing we output for now in this region is mxcsr and mxcsr mask
               ;; TODO update this if more of the x87 is implemented
               ((mv flg x86) (wme32 proc-mode (+ 24 dest-addr) seg-reg (mxcsr x86) inst-ac? x86))
               ((when flg) (!!ms-fresh :wme32 proc-mode flg))
               ((mv flg x86) (wme32 proc-mode (+ 28 dest-addr) seg-reg #xFFFF inst-ac? x86))
               ((when flg) (!!ms-fresh :wme32 proc-mode flg))
               ;; We don't have MMX registers, so we don't save those
               ((mv flg x86) (write-xmm-regs proc-mode inst-ac? seg-reg 0 (+ 160 dest-addr) (if (equal proc-mode *64-bit-mode*) 16 8) x86))
               ;; write-xmm-regs sets ms in the event of a fault
               ((when flg) x86))
              (write-*ip proc-mode temp-rip x86)))

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

(def-inst x86-fxrstor/fxrstor64

          ;; Op/En: M
          ;; 0F AE /0: fxrstor
          ;; REX.W + 00F AE /0: fxrstor64

          :parents (two-byte-opcodes)

          :guard-hints (("Goal" :in-theory (e/d () ())))
          :guard-debug t

          :returns (x86 x86p :hyp (x86p x86))

          :modr/m t

          :body

          (b* ((p2 (prefixes->seg prefixes))
               (p4? (equal #.*addr-size-override*
                           (prefixes->adr prefixes)))
               ;; TODO this should always be a memory address size, right?
               ((the (integer 1 8) operand-size)
                (select-operand-size proc-mode nil rex-byte nil prefixes nil nil nil x86))
               (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
               (inst-ac? nil) ;; TODO check 16 byte alignment requirement
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

               ;; Most of the first 32 bytes of the output have to do with the x87 state,
               ;; which has not been implemented
               ;; The only thing we read for now in this region is mxcsr and mxcsr mask
               ;; TODO update this if more of the x87 is implemented
               ((mv flg mxcsr x86) (rme32 proc-mode (+ 24 src-addr) seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme32 proc-mode flg))
               ;; TODO check if we're supposed to read the mxcsr-mask or not
               ((mv flg mxcsr-mask x86) (rme32 proc-mode (+ 28 src-addr) seg-reg :r inst-ac? x86))
               ((when flg) (!!ms-fresh :rme32 proc-mode flg))
               (mxcsr (logand mxcsr mxcsr-mask))
               ((when (not (equal (logand mxcsr #xFFFF0000) 0)))
                (!!fault-fresh :gp 0 :mxcsr-error mxcsr))
               (x86 (!mxcsr mxcsr x86))

               ;; We don't have MMX registers, so we don't restore those
               ((mv flg x86) (read-xmm-regs proc-mode inst-ac? seg-reg 0 (+ 160 src-addr) (if (equal proc-mode *64-bit-mode*) 16 8) x86))
               ;; read-xmm-regs sets ms if there is a fault
               ((when flg) x86))
              (write-*ip proc-mode temp-rip x86)))
