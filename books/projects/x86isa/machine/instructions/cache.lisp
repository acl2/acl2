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

;; ======================================================================

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(def-inst x86-invlpg

          ;; Op/En: M
          ;; 0F 01/7

          :parents (two-byte-opcodes)

          :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

          :returns (x86 x86p :hyp (x86p x86))

          :modr/m t

          :body

          (b* ((p4? (equal #.*addr-size-override*
                           (prefixes->adr prefixes)))

               ((mv flg0
                    (the (signed-byte 64) addr)
                    (the (unsigned-byte 3) increment-RIP-by)
                    x86)
                (if (equal mod #b11)
                  (mv nil 0 0 x86)
                  (x86-effective-addr proc-mode p4?
                                      temp-rip
                                      rex-byte
                                      r/m
                                      mod
                                      sib
                                      0 ;; No immediate operand
                                      x86)))
               ((when flg0)
                (!!ms-fresh :x86-effective-addr flg0))

               (tlb (tlb x86))
               (?tlb (fast-alist-free tlb))
               (x86 (!tlb :tlb x86))

               ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
                (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
               ((when flg) (!!ms-fresh :next-rip-invalid temp-rip))

               (badlength? (check-instruction-length start-rip temp-rip 0))
               ((when badlength?)
                (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

               ;; Update the x86 state:
               (x86 (write-*ip proc-mode temp-rip x86)))
              x86))
