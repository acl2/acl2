; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
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
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "divide-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: DIV
;; ======================================================================

(local
 (defthm x86-div-guard-proof-helper-1
   (implies (n16p rr16-a)
            (equal (logand 18446462598732906495 rr16-a)
                   rr16-a))
   :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))))

(local
 (defthm x86-div-guard-proof-helper-2
   (implies (forced-and (n08p val08-1)
                        (n08p val08-2))
            (equal
             (logior (ash val08-2 8)
                     (logand 4294902015 val08-1))
             (logior val08-1 (ash val08-2 8))))
   :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-div

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d () (force (force))))))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'DIV #xF6 '(:reg 6)
                                      'x86-div)
    (add-to-implemented-opcodes-table 'DIV #xF7 '(:reg 6)
                                      'x86-div))

  :guard (equal (mrm-reg modr/m) 6)

  :long
  "<h4>Op/En: M</h4>

  <p>F6/6:<br/>
      DIV r/m8:  \(AX div r/m8\),      AH  := Remainder, AL  := Quotient<br/><br/>
     F7/6:<br/>
      DIV r/m16: \(DX:AX div r/m16\),  DX  := Remainder, AX  := Quotient<br/>
      DIV r/m32: \(EDX:EAX div r/m8\), EDX := Remainder, EAX := Quotient<br/>
      DIV r/m64: \(RDX:RAX div r/m8\), RDX := Remainder, RAX := Quotient<br/></p>"

  :body

  (b* ((ctx 'x86-div)

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes x86))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       (inst-ac? t)
       ((mv flg0
            reg/mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes$ #.*gpr-access*
                                                reg/mem-size
                                                inst-ac?
                                                nil ;; Not a memory pointer operand
                                                seg-reg
                                                p4?
                                                temp-rip
                                                rex-byte
                                                r/m
                                                mod
                                                sib
                                                0 ;; No immediate operand
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((when (equal reg/mem 0))
        (!!fault-fresh :de nil :DE-exception-source-operand-zero reg/mem)) ;; #DE

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment--error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))
       (rDX (if select-byte-operand
                0
              (rgfi-size reg/mem-size *rdx* rex-byte x86)))

       ;; Computing the result:
       (dividend (if select-byte-operand
                     rAX
                   (mbe :logic (part-install rDX rAX
                                             :low   (ash reg/mem-size 3)
                                             :width (ash reg/mem-size 4))
                        :exec (logior (ash rDX (ash reg/mem-size 3)) rAX))))
       ((mv overflow? quotient remainder)
        (div-spec reg/mem-size dividend reg/mem))

       ;; Updating the x86 state:

       ((when overflow?)
        (!!ms-fresh :unsigned-divide-error-overflow
                    (cons 'dividend  dividend)
                    (cons 'divisor   reg/mem)))

       (x86
        (case reg/mem-size

          (1 ;; (AX div r/m8), AH := Remainder, AL := Quotient
           (let* ((result
                   (mbe :logic (part-install remainder quotient
                                             :low 8 :width 8)
                        :exec (logior (ash (the (unsigned-byte 8)
                                             remainder) 8)
                                      (the (unsigned-byte 8) quotient))))
                  (x86 (!rgfi-size 2 *rax* result rex-byte x86)))
             x86))

          (otherwise
           ;; (DX:AX   div r/m16), DX := Remainder, AX := Quotient
           ;; (EDX:EAX div r/m8), EDX := Remainder, EAX := Quotient
           ;; (RDX:RAX div r/m8), RDX := Remainder, RAX := Quotient
           (let* ((x86 (!rgfi-size reg/mem-size *rax* quotient  rex-byte x86))
                  (x86 (!rgfi-size reg/mem-size *rdx* remainder rex-byte x86)))
             x86))))

       ;; All the flags are undefined.
       (x86 (!flgi-undefined #.*cf* x86))
       (x86 (!flgi-undefined #.*pf* x86))
       (x86 (!flgi-undefined #.*af* x86))
       (x86 (!flgi-undefined #.*zf* x86))
       (x86 (!flgi-undefined #.*sf* x86))
       (x86 (!flgi-undefined #.*of* x86))

       (x86 (write-*ip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: IDIV
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-idiv

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d () (force (force))))))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'IDIV #xF6 '(:reg 7)
                                      'x86-idiv)
    (add-to-implemented-opcodes-table 'IDIV #xF7 '(:reg 7)
                                      'x86-idiv))

  :guard (equal (mrm-reg modr/m) 7)

  :long
  "<h4>Op/En: M</h4>

  <p>F6/7:<br/>
     IDIV r/m8:  \(AX div r/m8\),      AH  := Remainder, AL  := Quotient<br/><br/>

     F7/7:<br/>
     IDIV r/m16: \(DX:AX div r/m16\),  DX  := Remainder, AX  := Quotient <br/>
     IDIV r/m32: \(EDX:EAX div r/m8\), EDX := Remainder, EAX := Quotient <br/>
     IDIV r/m64: \(RDX:RAX div r/m8\), RDX := Remainder, RAX := Quotient</p>"

  :body

  (b* ((ctx 'x86-idiv)

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes x86))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       (inst-ac? t)
       ((mv flg0
            reg/mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes$ #.*gpr-access*
                                                reg/mem-size
                                                inst-ac?
                                                nil ;; Not a memory pointer operand
                                                seg-reg
                                                p4?
                                                temp-rip
                                                rex-byte
                                                r/m
                                                mod
                                                sib
                                                0 ;; No immediate operand
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((when (equal reg/mem 0))
        (!!fault-fresh :de nil :DE-exception-source-operand-zero reg/mem)) ;; #DE

       ((mv flg (the (signed-byte #.*max-linear-address-size+1*) temp-rip))
        (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (rAX (rgfi-size
             (if (eql reg/mem-size 1) 2 reg/mem-size)
             *rax* rex-byte x86))
       (rDX (if select-byte-operand
                0
              (rgfi-size reg/mem-size *rdx* rex-byte x86)))

       (dividend (if select-byte-operand
                     rAX
                   (mbe :logic (part-install rDX rAX
                                             :low   (ash reg/mem-size 3)
                                             :width (ash reg/mem-size 4))
                        :exec (logior (ash rDX (ash reg/mem-size 3)) rAX))))

       ;; Compute the result
       ((mv overflow? quotient remainder)
        (idiv-spec reg/mem-size dividend reg/mem))

       ((when overflow?)
        (!!ms-fresh :unsigned-divide-error-overflow
                    (cons 'dividend  dividend)
                    (cons 'divisor   reg/mem)))

       (x86
        (case reg/mem-size

          (1 ;; (AX div r/m8), AH := Remainder, AL := Quotient
           (let* ((result
                   (mbe :logic (part-install remainder quotient
                                             :low 8 :width 8)
                        :exec (logior (ash (the (unsigned-byte 8)
                                             remainder) 8)
                                      (the (unsigned-byte 8) quotient))))
                  (x86 (!rgfi-size 2 *rax* result rex-byte x86)))
             x86))

          (otherwise
           ;; (DX:AX   idiv r/m16), DX := Remainder, AX := Quotient
           ;; (EDX:EAX idiv r/m8), EDX := Remainder, EAX := Quotient
           ;; (RDX:RAX idiv r/m8), RDX := Remainder, RAX := Quotient
           (let* ((x86 (!rgfi-size reg/mem-size *rax* quotient  rex-byte x86))
                  (x86 (!rgfi-size reg/mem-size *rdx* remainder rex-byte x86)))
             x86))))

       ;; All the flags are undefined.
       (x86 (!flgi-undefined #.*cf* x86))
       (x86 (!flgi-undefined #.*pf* x86))
       (x86 (!flgi-undefined #.*af* x86))
       (x86 (!flgi-undefined #.*zf* x86))
       (x86 (!flgi-undefined #.*sf* x86))
       (x86 (!flgi-undefined #.*of* x86))

       (x86 (write-*ip temp-rip x86)))
    x86))

;; ======================================================================
