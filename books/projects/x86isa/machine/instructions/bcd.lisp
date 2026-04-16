; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

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

; Original Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils")

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Binary Code Decimal (BCD) adjustment instructions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-aaa

  :parents (one-byte-opcodes)

  :short "AAA: ASCII Adjust After Addition."

  :long
  (xdoc::topstring
   (xdoc::codeblock
    "37 AAA"))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (;; See pseudocode in Intel manual for AAA.
       ((the (unsigned-byte 16) ax) (rr16 #.*eax* x86))
       ((the (unsigned-byte 8) al) (part-select ax :low 0 :width 8))
       ((the (unsigned-byte 32) rflags) (rflags x86))
       ((the (unsigned-byte 1) af) (rflagsBits->af rflags))
       (adjustp (or (> (logand al #x0f) 9)
                    (= af 1)))
       ((mv (the (unsigned-byte 16) ax)
            (the (unsigned-byte 1) af)
            (the (unsigned-byte 1) cf))
        (if adjustp
            (mv (n16 (+ ax #x106)) 1 1)
          (mv ax 0 0)))
       (al (logand ax #x000f))
       (ax (part-install al ax :low 0 :width 8))
       (x86 (wr16 #.*eax* ax x86))
       (x86 (!flgi :af af x86))
       (x86 (!flgi :cf cf x86))
       (x86 (!flgi-undefined :of x86))
       (x86 (!flgi-undefined :sf x86))
       (x86 (!flgi-undefined :zf x86))
       (x86 (!flgi-undefined :pf x86)))
    x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-aas

  :parents (one-byte-opcodes)

  :short "AAA: ASCII Adjust After Subtraction."

  :long
  (xdoc::topstring
   (xdoc::codeblock
    "3F AAS"))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (;; See pseudocode in Intel manual for AAS.
       ((the (unsigned-byte 16) ax) (rr16 #.*eax* x86))
       ((the (unsigned-byte 8) al) (part-select ax :low 0 :width 8))
       ((the (unsigned-byte 32) rflags) (rflags x86))
       ((the (unsigned-byte 1) af) (rflagsBits->af rflags))
       (adjustp (or (> (logand al #x0f) 9)
                    (= af 1)))
       ((mv (the (unsigned-byte 16) ax)
            (the (unsigned-byte 1) af)
            (the (unsigned-byte 1) cf))
        (if adjustp
            (b* ((ax (n16 (- ax 6)))
                 (ah (part-select ax :low 8 :width 8))
                 (ah (n08 (- ah 1)))
                 (ax (part-install ah ax :low 8 :width 8)))
              (mv ax 1 1))
          (mv ax 0 0)))
       (al (logand ax #x000f))
       (ax (part-install al ax :low 0 :width 8))
       (x86 (wr16 #.*eax* ax x86))
       (x86 (!flgi :af af x86))
       (x86 (!flgi :cf cf x86))
       (x86 (!flgi-undefined :of x86))
       (x86 (!flgi-undefined :sf x86))
       (x86 (!flgi-undefined :zf x86))
       (x86 (!flgi-undefined :pf x86)))
    x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-aam

  :parents (one-byte-opcodes)

  :short "AAM: ASCII Adjust After Multiplication."

  :long
  (xdoc::topstring
   (xdoc::codeblock
    "D4 0A AAM"
    "D4 ib AAM imm8"))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (;; The D4 opcode is always followed by a one-byte immediate.
       ;; The manual shows two formats, with 0A and ib,
       ;; because, as noted in the text, AAM is assembled to D4 0A,
       ;; while other immediates must be hand-coded in machine-code.
       ;; But at the binary level, we always have an immediate byte,
       ;; which may be 0A or some other value.
       ((mv flg (the (unsigned-byte 8) imm) x86)
        (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg) (!!ms-fresh :imm-rme-size-error flg))

       ;; Increment the instruction pointer.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; There is no need to check the instruction length,
       ;; because it is always 2 bytes.

       ;; The immediate must not be 0.
       ((when (= imm 0))
        (!!fault-fresh :de nil :null-immediate-in-aam)) ; #DE

       ;; See pseudocode in Intel manual for AAM.
       ((the (unsigned-byte 16) ax) (rr16 #.*eax* x86))
       ((the (unsigned-byte 8) temp-al) (part-select ax :low 0 :width 8))
       ((the (unsigned-byte 8) ah) (floor temp-al imm))
       ((the (unsigned-byte 8) al) (mod temp-al imm))
       ((the (unsigned-byte 16) ax) (logapp 8 al ah))
       (x86 (wr16 #.*eax* ax x86))

       ;; Flags are affected based on AL (see Intel manual).
       (x86 (!flgi :sf (sf-spec8 al) x86))
       (x86 (!flgi :zf (zf-spec al) x86))
       (x86 (!flgi :pf (pf-spec8 al) x86))
       (x86 (!flgi-undefined :of x86))
       (x86 (!flgi-undefined :af x86))
       (x86 (!flgi-undefined :cf x86))

       ;; Update instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86)

  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-aad

  :parents (one-byte-opcodes)

  :short "AAD: ASCII Adjust Before Division."

  :long
  (xdoc::topstring
   (xdoc::codeblock
    "D5 0A AAD"
    "D5 ib AAD imm8"))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (;; The D5 opcode is always followed by a one-byte immediate.
       ;; The manual shows two formats, with 0A and ib,
       ;; because, as noted in the text, AAD is assembled to D5 0A,
       ;; while other immediates must be hand-coded in machine-code.
       ;; But at the binary level, we always have an immediate byte,
       ;; which may be 0A or some other value.
       ((mv flg (the (unsigned-byte 8) imm) x86)
        (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg) (!!ms-fresh :imm-rme-size-error flg))

       ;; Increment the instruction pointer.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; There is no need to check the instruction length,
       ;; because it is always 2 bytes.

       ;; See pseudocode in Intel manual for AAD.
       ((the (unsigned-byte 16) ax) (rr16 #.*eax* x86))
       ((the (unsigned-byte 8) temp-al) (part-select ax :low 0 :width 8))
       ((the (unsigned-byte 8) temp-ah) (part-select ax :low 8 :width 8))
       ((the (unsigned-byte 8) al) (n08 (+ temp-al (* temp-ah imm))))
       ((the (unsigned-byte 8) ah) 0)
       ((the (unsigned-byte 16) ax) (logapp 8 al ah))
       (x86 (wr16 #.*eax* ax x86))

       ;; Flags are affected based on AL (see Intel manual).
       (x86 (!flgi :sf (sf-spec8 al) x86))
       (x86 (!flgi :zf (zf-spec al) x86))
       (x86 (!flgi :pf (pf-spec8 al) x86))
       (x86 (!flgi-undefined :of x86))
       (x86 (!flgi-undefined :af x86))
       (x86 (!flgi-undefined :cf x86))

       ;; Update instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86)

  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08))))
