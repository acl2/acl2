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

; Original Author(s):
; Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-endbr32/endbr64

  ;; Op/En: ZO
  ;; F3 0F 1E FB (ENDBR32)
  ;; F3 0F 1E FA (ENDBR64)

  :returns (x86 x86p :hyp (x86p x86))

  :parents (two-byte-opcodes)

  :short "Terminate indirect branch."

  :long

  "<p>For now we model ENDBR32 and ENDBR64 as no-ops,
   effectively assuming no CET support
   (see Intel manual Volume 1 Chapter 17 of Dec 2023).
   In the future, we will add proper support
   (conditional under CPU features).</p>

   <p>Table A-3 of Intel manual Volume 2 shows <tt>0F 1E</tt>
   as a reserved NOP, i.e. an opcode reserved for future instructions,
   executed as a NOP by processors that do not implement them.
   Like the NOP <tt>0F 1F /0</tt>, it takes a ModR/M byte:
   the bytes <tt>FB</tt> (for ENDBR32) and <tt>FA</tt> (for ENDBR64)
   in the encodings of these instructions are ModR/M bytes,
   with mod = 3, reg = 7, and r/m = 3 and 2 respectively.
   Accordingly, the opcode map marks <tt>0F 1E</tt> as having a ModR/M byte,
   and dispatches to this function only when
   the mandatory prefix is <tt>F3</tt>
   and the ModR/M byte is <tt>FB</tt> or <tt>FA</tt>;
   the other encodings of <tt>0F 1E</tt> are dispatched to
   @(tsee x86-two-byte-nop).
   Thus, when this function is called,
   the whole instruction has been decoded,
   and @('temp-rip') points just past the ModR/M byte.</p>"

  :body
  (b* ((badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))
