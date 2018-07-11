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
(include-book "base"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; =============================================================================
; INSTRUCTION: MXCSR State Management Instructions
; =============================================================================

(def-inst x86-ldmxcsr/stmxcsr-Op/En-M

  :parents (two-byte-opcodes fp-opcodes)

  :short "Load/Store MXCSR register"

  :long
  "<h3>Op/En = M: \[OP M\]</h3>
  0F AE /2: LDMXCSR m32<br/>
  0F AE /3: STMXCSR m32<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-ldmxcsr/stmxcsr-Op/En-M)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))
       (inst-ac? ;; Exceptions Type 5
        t)

       ((mv flg0
            (the (unsigned-byte 32) mem)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) v-addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* 4 inst-ac?
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

       ((when (not (canonical-address-p v-addr)))
        (!!ms-fresh :v-addr-not-canonical v-addr))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (x86
        (case reg
          (2 ;; LDMXCSR
           (!mxcsr mem x86))
          (3 ;; STMXCSR
           (b* ((mxcsr (the (unsigned-byte 32) (mxcsr x86)))
                ((mv flg1 x86)
                 (x86-operand-to-reg/mem
                  4 inst-ac?
                  nil ;; Not a memory pointer operand
                  mxcsr v-addr rex-byte r/m mod x86))
                ;; Note: If flg1 is non-nil, we bail out without changing the
                ;; x86 state.
                ((when flg1)
                 (!!ms-fresh :x86-operand-to-reg/mem flg1)))
             x86))
          (otherwise ;; Should never be reached, unimplemented.
           x86)))

       (x86 (!rip temp-rip x86)))
    x86)

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'LDMXCSR #x0FAE
                                      '(:misc (eql (mrm-reg modr/m) 2))
                                      'x86-ldmxcsr/stmxcsr-Op/En-M)
    (add-to-implemented-opcodes-table 'STMXCSR #x0FAE
                                      '(:misc (eql (mrm-reg modr/m) 3))
                                      'x86-ldmxcsr/stmxcsr-Op/En-M)))

;; ======================================================================
