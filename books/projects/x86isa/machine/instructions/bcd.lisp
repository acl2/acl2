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
