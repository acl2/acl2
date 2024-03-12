; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2024, Kestrel Technology, LLC
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
; Alessandro Coglio (www.alessandrocoglio.info)

(in-package "X86ISA")

;; ======================================================================

(include-book "../../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "base"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

; =============================================================================
; INSTRUCTION: AVX Non-Arithmetic Instructions
; =============================================================================

(def-inst x86-vzeroupper

  :parents (two-byte-opcodes fp-opcodes)

  :short "VZEROUPPER: Zero Upper Bits of YMM and ZMM Registers"

  :vex t

  :guard (vex-prefixes-byte0-p vex-prefixes)

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (;; This instruction requires VEX.L = 0,
       ;; throwing a #UD otherwise;
       ;; see Intel Manuals Volume 2 Section 3.1.12 (Dec 2023).
       ((unless (equal (vex->l vex-prefixes) 0))
        (!!fault-fresh :ud nil ; #UD
                       :vzeroupper 'vex.l 1))

       (2^128-1 (1- (expt 2 128)))

       ;; Always zero the bits 128 and higher of registers ZMM0-ZMM7.
       (zmm0 (zmmi-size 64 0 x86))
       (zmm1 (zmmi-size 64 1 x86))
       (zmm2 (zmmi-size 64 2 x86))
       (zmm3 (zmmi-size 64 3 x86))
       (zmm4 (zmmi-size 64 4 x86))
       (zmm5 (zmmi-size 64 5 x86))
       (zmm6 (zmmi-size 64 6 x86))
       (zmm7 (zmmi-size 64 7 x86))
       (x86 (!zmmi-size 64 0 (logand zmm0 2^128-1) x86))
       (x86 (!zmmi-size 64 1 (logand zmm1 2^128-1) x86))
       (x86 (!zmmi-size 64 2 (logand zmm2 2^128-1) x86))
       (x86 (!zmmi-size 64 3 (logand zmm3 2^128-1) x86))
       (x86 (!zmmi-size 64 4 (logand zmm4 2^128-1) x86))
       (x86 (!zmmi-size 64 5 (logand zmm5 2^128-1) x86))
       (x86 (!zmmi-size 64 6 (logand zmm6 2^128-1) x86))
       (x86 (!zmmi-size 64 7 (logand zmm7 2^128-1) x86))

       ;; If we are in 64-bit mode, also clear the bits 128 and higher of
       ;; registers ZMM8-ZMM15.
       (x86
        (if (equal proc-mode #.*64-bit-mode*)
            (b* ((zmm8 (zmmi-size 64 8 x86))
                 (zmm9 (zmmi-size 64 9 x86))
                 (zmm10 (zmmi-size 64 10 x86))
                 (zmm11 (zmmi-size 64 11 x86))
                 (zmm12 (zmmi-size 64 12 x86))
                 (zmm13 (zmmi-size 64 13 x86))
                 (zmm14 (zmmi-size 64 14 x86))
                 (zmm15 (zmmi-size 64 15 x86))
                 (x86 (!zmmi-size 64 8 (logand zmm8 2^128-1) x86))
                 (x86 (!zmmi-size 64 9 (logand zmm9 2^128-1) x86))
                 (x86 (!zmmi-size 64 10 (logand zmm10 2^128-1) x86))
                 (x86 (!zmmi-size 64 11 (logand zmm11 2^128-1) x86))
                 (x86 (!zmmi-size 64 12 (logand zmm12 2^128-1) x86))
                 (x86 (!zmmi-size 64 13 (logand zmm13 2^128-1) x86))
                 (x86 (!zmmi-size 64 14 (logand zmm14 2^128-1) x86))
                 (x86 (!zmmi-size 64 15 (logand zmm15 2^128-1) x86)))
              x86)
          x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  ;; TODO: Ensure that we cover all the "Type 8 Class Exception Conditions"
  ;; mentioned in the documentation of VZEROUPPER.

  ;; TODO: Should we check that VEX.pp = #b00, or does the auto-generated
  ;; dispatch code handle that?

)
