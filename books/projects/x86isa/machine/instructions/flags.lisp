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
;; INSTRUCTION: CMC/CLC/STC/CLD/STD
;; ======================================================================

(def-inst x86-cmc/clc/stc/cld/std

  ;; Op/En: NP
  ;; F5: CMC (CF complemented, all other flags are unaffected)
  ;; F8: CLC (CF cleared, all other flags are unaffected)
  ;; F9: STC (CF set, all other flags are unaffected)
  ;; FC: CLD (DF cleared, all other flags are unaffected)
  ;; FD: STD (DF set, all other flags are unaffected)

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((x86 (case opcode
              (#xF5 ;; CMC
               (let* ((cf (the (unsigned-byte 1)
                            (flgi :cf x86)))
                      (not-cf (if (equal cf 1) 0 1)))
                 (!flgi :cf not-cf x86)))
              (#xF8 ;; CLC
               (!flgi :cf 0 x86))
              (#xF9 ;; STC
               (!flgi :cf 1 x86))
              (#xFC ;; CLD
               (!flgi :df 0 x86))
              (otherwise ;; #xFD STD
               (!flgi :df 1 x86))))

       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: SAHF
;; ======================================================================

(def-inst x86-sahf

  ;; Opcode: #x9E

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (((the (unsigned-byte 16) ax) (rr16 #.*rax* x86))
       ((the (unsigned-byte 8) ah) (ash ax -8))
       ((the (unsigned-byte 32) rflags) (rflags x86))
       ;; Bits 1, 3, and 5 of eflags are unaffected, with the values remaining
       ;; 1, 0, and 0, respectively.
       (cf (rflagsBits->cf ah))
       (pf (rflagsBits->pf ah))
       (af (rflagsBits->af ah))
       (zf (rflagsBits->zf ah))
       (sf (rflagsBits->sf ah))
       ((the (unsigned-byte 32) new-rflags)
        (!rflagsBits->cf
         cf
         (!rflagsBits->pf
          pf
          (!rflagsBits->af
           af
           (!rflagsBits->zf
            zf
            (!rflagsBits->sf
             sf
             rflags))))))
       ;; Update the x86 state:
       (x86 (!rflags new-rflags x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LAHF
;; ======================================================================

(def-inst x86-lahf

  ;; Opcode: #x9F

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables
                                          riml08 riml32)
                                         ((tau-system)))))

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork
  ((local
    (defthm unsigned-byte-p-8-of-rflagsBits-for-lahf
      (< (rflagsbits cf 1 pf 0 af 0 zf sf 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         256)
      :hints (("Goal" :in-theory (e/d* (rflagsbits
                                        bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs)
                                       ()))))))

  :body

  (b* (((the (unsigned-byte 32) rflags) (rflags x86))
       (cf (rflagsBits->cf rflags))
       (pf (rflagsBits->pf rflags))
       (af (rflagsBits->af rflags))
       (zf (rflagsBits->zf rflags))
       (sf (rflagsBits->sf rflags))

       ((the (unsigned-byte 8) new-ah)
        (!rflagsBits->cf
         cf
         (!rflagsBits->res1
          1
          (!rflagsBits->pf
           pf
           (!rflagsBits->res2
            0
            (!rflagsBits->af
             af
             (!rflagsBits->res3
              0
              (!rflagsBits->zf
               zf
               (!rflagsBits->sf
                sf
                0)))))))))

       ((the (unsigned-byte 16) ax) (rr16 #.*rax* x86))
       ((the (unsigned-byte 16) new-ax)
        (logior (logand #xFF ax) (ash new-ah 8)))
       ;; Update the x86 state:
       (x86 (wr16 #.*rax* new-ax x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))
