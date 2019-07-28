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

(include-book "arith-and-logic-spec"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: XCHG
;; ======================================================================

(def-inst x86-xchg

  ;; Note that for XCHG, the Op/En RM and MR are essentially the same.
  ;; In our model, we arbitrarily choose the MR encoding to represent
  ;; both of them.

  ;; Op/En: RM
  ;; 86: XCHG r8, r/m8
  ;; 87: XCHG r16/r32/r64, r/m16/r/m32/r/m64

  ;; Op/En: MR
  ;; 86: XCHG r/m8, r8
  ;; 87: XCHG r/m16/r/m32/r/m64, r16/r32/r64

  ;; Op/En: O
  ;; 90 +rw: XCHG ax, r16
  ;; 90 +rd: XCHG eax/rax, r32/r64

  ;; Note that opcode #x90 with REX.B = 0 is XCHG rAX, rAX, i.e., NOP.

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d* () (not))))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override*
		 (prefixes->adr prefixes)))

       (select-byte-operand (equal opcode #x86))
       (reg/mem-size
	(select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ;; Fetch the first operand and put it in val1.
       ;; If the opcode is #x90+rw/rd, we let rax be the first operand.
       ;; For other opcodes, we let the operand specified by the r/m field to
       ;; be the first operand.
       ((mv flg0
	    val1
	    (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte 64) addr)
	    x86)
	(if (equal (ash opcode -4) 9) ;; #x90+rw/rd
	    (mv nil (rgfi-size reg/mem-size *rax* rex-byte x86) 0 0 x86)
	  (x86-operand-from-modr/m-and-sib-bytes
	   proc-mode #.*gpr-access* reg/mem-size inst-ac?
	   nil ;; Not a memory pointer operand
	   seg-reg p4? temp-rip rex-byte r/m mod sib
	   0 ;; No immediate operand
	   x86)))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Fetch the second operand and put it in val2.
       ;; If the opcode is #x90+rw/rd, we let the contents of the register
       ;; chosen by rw/rd be the second operand.
       ;; For other opcodes, we let the operand specified by the reg field to
       ;; be the second operand.
       (rw/rd (the (unsigned-byte 3) (logand #x7 opcode)))
       (val2
	(if (equal (ash opcode -4) 9) ;; #x90+rw/rd
	    ;; See Intel Table 3.1, p.3-3, Vol. 2-A
	    (rgfi-size reg/mem-size (reg-index rw/rd rex-byte #.*b*)
		       rex-byte x86)
	  (rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*)
		     rex-byte x86)))

       ;; Update the x86 state:

       ;; Put val2 in the place of val1.
       ((mv flg2 x86)
	(if (equal (ash opcode -4) 9)
	    (let ((x86 (!rgfi-size reg/mem-size *rax* val2 rex-byte x86)))
	      (mv nil x86))
	  (x86-operand-to-reg/mem proc-mode reg/mem-size
				   inst-ac?
				   nil ;; Not a memory pointer operand
				   val2
				   seg-reg
				   (the (signed-byte 64) addr)
				   rex-byte
				   r/m
				   mod
				   x86)))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
	(!!ms-fresh :x86-operand-to-reg/mem-error flg2))

       ;; Put val1 in the place of val2.
       (x86
	(if (equal (the (unsigned-byte 4) (ash opcode -4)) 9) ;; #x90+rw/rd
	    ;; See Intel Table 3.1, p.3-3, Vol. 2-A
	    (!rgfi-size reg/mem-size (reg-index rw/rd rex-byte #.*b*) val1
			rex-byte x86)
	  (!rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*) val1 rex-byte
		      x86)))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: CMPXCHG
;; ======================================================================

(def-inst x86-cmpxchg

  ;; Op/En: MR
  ;; 0F B0: CMPXCHG r/m8, r8
  ;; 0F B1: CMPXCHG r/m16/32/64, r16/32/64

  :parents (two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       (select-byte-operand (equal opcode #xB0))
       ((the (integer 1 8) reg/mem-size)
	(select-operand-size
         proc-mode select-byte-operand rex-byte nil prefixes nil nil nil x86))

       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ;; Fetch the first (destination) operand:
       ((mv flg0
	    reg/mem
	    (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte 64) addr)
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

       ;; Computing the flags and the result:
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv result
	    (the (unsigned-byte 32) output-rflags)
	    (the (unsigned-byte 32) undefined-flags))
	(gpr-arith/logic-spec reg/mem-size #.*OP-CMP* reg/mem rAX input-rflags))

       ;; Update the x86 state:
       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ((mv flg1 x86)
	(if (equal result 0) ;; rAX == reg/mem or ZF == 1
	    ;; Fetch the second operand and put it in the destination operand.
	    (let ((register (rgfi-size reg/mem-size
				       (reg-index reg rex-byte #.*r*) rex-byte
				       x86)))
	      (x86-operand-to-reg/mem proc-mode reg/mem-size
				       inst-ac?
				       nil ;; Not a memory pointer operand
				       register
				       seg-reg
				       (the (signed-byte 64) addr)
				       rex-byte
				       r/m
				       mod
				       x86))
	  ;; rAX != reg/mem or ZF == 0
	  ;; Put the destination operand into the accumulator.
	  (let ((x86 (!rgfi-size reg/mem-size *rax* reg/mem rex-byte x86)))
	    (mv nil x86))))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg1)
	(!!ms-fresh :x86-operand-to-reg/mem-error flg1))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: NOP
;; ======================================================================

(def-inst x86-two-byte-nop

  ;; Op/En: NP
  ;; 0F 1F/0

  ;; The Intel manual (Vol. 2B, NOP specification) has a note on the recommended
  ;; multi-byte NOP sequences, and the address-size override prefix is
  ;; absent from all of them.  However, since the operand for the
  ;; multi-byte NOP is an r/m operand, we account for the effect of that
  ;; prefix anyway.

  :parents (two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (;; [Shilpi] Though Intel Manuals (May 2018 edition) specifically mention
       ;; in two different places (the opcode maps and the instruction
       ;; description page for NOP) that reg = 0 for this instruction, I have
       ;; not observed an x86 machine to throw a UD if reg != 0.
       ;; ((when (not (equal reg 0)))
       ;;  (!!fault-fresh :ud nil :illegal-reg modr/m))

       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       ((mv flg0
	    (the (signed-byte 64) ?addr)
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :next-rip-invalid temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
