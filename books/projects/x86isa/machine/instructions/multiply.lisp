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

(include-book "multiply-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: MUL
;; ======================================================================

(def-inst x86-mul

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86)
                :hints (("Goal" :in-theory (e/d () (force (force))))))

  ;; Note that the reg field serves as an opcode extension for this
  ;; instruction.  The reg field will always be 4 when this function
  ;; is called.

  :guard (equal (modr/m->reg modr/m) 4)

  :long
  "<h4>Op/En: M</h4>

   <p>F6/4: <br/>
      MUL r/m8: AX := AL \* r/m8<br/><br/>

      F7/4: <br/>
      MUL r/m16: DX:AX := AX \* r/m16<br/>
      MUL r/m32: EDX:EAX := EAX \* r/m32<br/>
      MUL r/m64: RDX:RAX := RAX \* r/m64<br/></p>"

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0
            reg/mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         proc-mode #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         seg-reg p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))

       ;; Computing the result:
       ((mv product-high product-low product)
        (mul-spec reg/mem-size rAX reg/mem))

       ;; Updating the x86 state:

       (x86
        (case reg/mem-size
          (1 ;; AX := AL * r/m8
           (let* ((x86 (!rgfi-size 2 *rax* product rex-byte x86)))
             x86))
          (otherwise
           (let* ((x86 ;; Write to rAX
                   (!rgfi-size reg/mem-size *rax* product-low
                               rex-byte x86))
                  (x86 ;; Write to rDX
                   (!rgfi-size reg/mem-size *rdx* product-high
                               rex-byte x86)))
             x86))))

       (x86
        (if (equal product-high 0)
            (let* ((x86 (!flgi :cf 0 x86))
                   (x86 (!flgi-undefined :pf x86))
                   (x86 (!flgi-undefined :af x86))
                   (x86 (!flgi-undefined :zf x86))
                   (x86 (!flgi-undefined :sf x86))
                   (x86 (!flgi :of 0 x86)))
              x86)
          (let* ((x86 (!flgi :cf 1 x86))
                 (x86 (!flgi-undefined :pf x86))
                 (x86 (!flgi-undefined :af x86))
                 (x86 (!flgi-undefined :zf x86))
                 (x86 (!flgi-undefined :sf x86))
                 (x86 (!flgi :of 1 x86)))
            x86)))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: IMUL
;; ======================================================================

(def-inst x86-imul-Op/En-M

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86)
                :hints (("Goal" :in-theory (e/d () (force (force))))))

  ;; Note that the reg field serves as an opcode extension for this
  ;; instruction.  The reg field will always be 5 when this function is
  ;; called.

  :guard (equal (modr/m->reg modr/m) 5)

  :long
  "<h4>Op/En: M</h4>

   <p>F6/5: <br/>
      IMUL r/m8: AX := AL \* r/m8<br/><br/>

      F7/5: <br/>
      IMUL r/m16: DX:AX := AX  \* r/m16<br/>
      IMUL r/m32: EDX:EAX := EAX \* r/m32<br/>
      IMUL r/m64: RDX:RAX := RAX \* r/m64<br/></p>"

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
        (select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0
            reg/mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         proc-mode #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         seg-reg p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))

       ;; Computing the result:
       ((mv product-high product-low product (the (unsigned-byte 1) cf-and-of))
        (imul-spec reg/mem-size rAX reg/mem))

       ;; Updating the x86 state:

       (x86
        (case reg/mem-size
          (1 ;; AX := AL * r/m8
           (let* ((x86 (!rgfi-size 2 *rax* product rex-byte x86)))
             x86))
          (otherwise
           (let* ((x86 ;; Write to rAX
                   (!rgfi-size reg/mem-size *rax* product-low
                               rex-byte x86))
                  (x86 ;; Write to rDX
                   (!rgfi-size reg/mem-size *rdx* product-high
                               rex-byte x86)))
             x86))))

       (x86
        (let* ((x86 (!flgi :cf cf-and-of x86))
               (x86 (!flgi-undefined :pf x86))
               (x86 (!flgi-undefined :af x86))
               (x86 (!flgi-undefined :zf x86))
               (x86 (!flgi-undefined :sf x86))
               (x86 (!flgi :of cf-and-of x86)))
          x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-imul-Op/En-RM

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86)
                :hints (("Goal" :in-theory (e/d () (force (force))))))


  :long
  "<h4>Op/En: RM</h4>

   <p>0F AF:<br/>
      IMUL r16, r/m16: r16 := r16 \* r/m16 <br/>
      IMUL r32, r/m32: r32 := r32 \* r/m32 <br/>
      IMUL r64, r/m64: r64 := r64 \* r/m64 <br/> </p>"

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes->adr prefixes)))

       ((the (integer 1 8) reg/mem-size)
        (select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0
            reg/mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         proc-mode #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         seg-reg p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (register (rgfi-size reg/mem-size
                            (reg-index reg rex-byte #.*r*)
                            rex-byte
                            x86))

       ;; Computing the result:
       ((mv ?product-high product-low ?product (the (unsigned-byte 1) cf-and-of))
        (imul-spec reg/mem-size reg/mem register))

       ;; Updating the x86 state:
       (x86
        (!rgfi-size reg/mem-size
                    (reg-index reg rex-byte #.*r*)
                    product-low
                    rex-byte
                    x86))

       (x86
        (let* ((x86 (!flgi :cf cf-and-of x86))
               (x86 (!flgi-undefined :pf x86))
               (x86 (!flgi-undefined :af x86))
               (x86 (!flgi-undefined :zf x86))
               (x86 (!flgi-undefined :sf x86))
               (x86 (!flgi :of cf-and-of x86)))
          x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-imul-Op/En-RMI

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86)
                :hints (("Goal" :in-theory (e/d () (force (force))))))

  :long
  "<h4>Op/En: RMI</h4>

   <p>6B ib:<br/>
      IMUL r16, r/m16, imm8<br/>
      IMUL r32, r/m32, imm8 <br/>
      IMUL r64, r/m64, imm8 <br/> <br/>

      69 iw:<br/>
      IMUL r16, r/m16, imm16 <br/>
      IMUL r32, r/m32, imm32 <br/>
      IMUL r64, r/m64, imm32 <br/> </p>"

  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08
                                           rme-size-of-2-to-rme16
                                           rme-size-of-4-to-rme32)))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       ((the (integer 1 8) reg/mem-size)
        (select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

       ((the (integer 1 4) imm-size)
        (if (equal opcode #x6B)
            1
          ;; opcode = #x69
          (if (equal reg/mem-size 2)
              2
            4)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0
            reg/mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         proc-mode #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         seg-reg p4? temp-rip rex-byte r/m mod sib
         imm-size ;; imm-size bytes of immediate data
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       ((mv flg1 (the (unsigned-byte 32) imm) x86)
        (rme-size-opt proc-mode imm-size temp-rip #.*cs* :x nil x86))
       ((when flg1)
        (!!ms-fresh :rme-size-error flg1))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip imm-size x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Computing the result:
       ((mv ?product-high product-low ?product (the (unsigned-byte 1) cf-and-of))
        (imul-spec reg/mem-size reg/mem imm))

       ;; Updating the x86 state:
       (x86
        (!rgfi-size reg/mem-size
                    (reg-index reg rex-byte #.*r*)
                    product-low
                    rex-byte
                    x86))

       (x86
        (let* ((x86 (!flgi :cf cf-and-of x86))
               (x86 (!flgi-undefined :pf x86))
               (x86 (!flgi-undefined :af x86))
               (x86 (!flgi-undefined :zf x86))
               (x86 (!flgi-undefined :sf x86))
               (x86 (!flgi :of cf-and-of x86)))
          x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
