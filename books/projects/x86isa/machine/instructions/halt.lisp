; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2024, Kestrel Technology, LLC
; All rights reserved.

; Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

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
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio (www.alessandrocoglio.info)

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
              :ttags (:undef-flg))

;; ======================================================================
;; INSTRUCTION: HLT
;; ======================================================================

(def-inst x86-hlt

  ;; Op/En: NP
  ;; F4

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (;; Update the x86 state:
       ;; Intel Vol. 2A, HLT specification: Instruction pointer is saved.
       ;; "If an interrupt ... is used to resume execution after a HLT
       ;; instruction, the saved instruction pointer points to the instruction
       ;; following the HLT instruction."
       (x86 (write-*ip proc-mode temp-rip x86))

       ;; In sys-view, HLT is essentially a NOP. This isn't correct; we should
       ;; stop executing instructions until we get an interrupt. However, most
       ;; of the time HLT is called in a loop, so it works fine for most real
       ;; world programs. Fixing this would require adding a halt state to the
       ;; model state and making it so either we spin the timer until it
       ;; interrupts or skip enough timer steps to cause an interrupt. This
       ;; breaks the notion that our model's time is tied to the number of
       ;; instructions executed, but that isn't a big deal.

       ;; In app-view, we set ms to stop execution
       (x86 (if (app-view x86)
              (!!ms-fresh :legal-halt :hlt)
              x86)))
    x86))
