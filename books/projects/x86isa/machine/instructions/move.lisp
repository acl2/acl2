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

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: MOV
;; ======================================================================

(def-inst x86-mov-Op/En-MR

  ;; Op/En: MR
  ;; [OP R/M, REG]
  ;; 88: MOV r/m8,  r8
  ;; 89: MOV r/m16, r16
  ;; 89: MOV r/m32, r32
  ;; 89: MOV r/m64, r64

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32)
					())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (the (unsigned-byte 8) (prefixes->seg prefixes)))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       (byte-operand? (equal opcode #x88))
       ((the (integer 1 8) operand-size)
	(select-operand-size
         proc-mode byte-operand? rex-byte nil prefixes nil nil nil x86))

       (register (rgfi-size operand-size (reg-index reg rex-byte #.*r*)
			    rex-byte x86))

       ((mv flg0
	    (the (signed-byte 64) addr)
	    (the (unsigned-byte 3) increment-RIP-by)
	    x86)
	(if (equal mod #b11)
	    (mv nil 0 0 x86)
	  (x86-effective-addr proc-mode p4? temp-rip rex-byte r/m mod sib
			      0 ;; No immediate operand
			      x86)))
       ((when flg0)
	(!!ms-fresh :x86-effective-addr-error flg0))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((mv flg temp-rip) (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (inst-ac? t)
       ((mv flg2 x86)
	(x86-operand-to-reg/mem proc-mode operand-size
				 inst-ac?
				 nil ;; Not a memory pointer operand
				 register
				 seg-reg
				 addr
				 rex-byte
				 r/m
				 mod
				 x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
	(!!ms-fresh :x86-operand-to-reg/mem flg2))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-mov-Op/En-RM

  ;; Op/En: RM
  ;; [OP REG, R/M]
  ;; 8A: MOV r8,  r/m8
  ;; 8B: MOV r16, r/m16
  ;; 8B: MOV r32, r/m32
  ;; 8B: MOV r64, r/m64

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       (byte-operand? (equal opcode #x8A))
       ((the (integer 1 8) operand-size)
	(select-operand-size
         proc-mode byte-operand? rex-byte nil prefixes nil nil nil x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by) ?addr x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 proc-mode #.*gpr-access* operand-size inst-ac?
	 nil ;; Not a memory pointer operand
	 seg-reg p4? temp-rip rex-byte r/m mod sib
	 0 ;; No immediate operand
	 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg temp-rip) (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*r*)
			reg/mem rex-byte x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-mov-Op/En-FD

  ;; Op/En: FD
  ;; [OP rAX, Moffs]
  ;; A0: MOV AL,         moffs8
  ;; A1: MOV AX/EAX/RAX, moffs16/moffs32/moffs64

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (e/d (select-address-size
					 segment-base-and-bounds
					 ea-to-la
					 rme-size
					 rime-size)
					(unsigned-byte-p))))

  :body

  (b* (;; This instruction does not require a ModR/M byte.
       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       ;; The Intel manual says the following:

       ;; Under the MOV instruction description:

       ;; The moffs8, moffs16, moffs32 and moffs64 operands specify a
       ;; simple offset relative to the segment base, where 8, 16, 32
       ;; and 64 refer to the size of the data. The address-size
       ;; attribute of the instruction determines the size of the
       ;; offset, either 16, 32 or 64 bits.

       ;; Under the "Instruction Column in the Opcode Summary Table"
       ;; (Intel manual, Jan'19, Vol. 2, Sec. 3.1.1.3):

       ;; moffs8, moffs16, moffs32, moffs64   A simple memory variable
       ;; (memory offset) of type byte, word, or doubleword used by
       ;; some variants of the MOV instruction. The actual address is
       ;; given by a simple offset relative to the segment base. No
       ;; ModR/M byte is used in the instruction. The number shown
       ;; with moffs indicates its size, which is determined by the
       ;; address-size attribute of the instruction.

       ;; Under "Codes for Addressing Method"
       ;; (Intel manual, Jan'19, Vol. 2, App. A.2.1):

       ;; O The instruction has no ModR/M byte. The offset of the
       ;; operand is coded as a word or double word (depending on
       ;; address size attribute) in the instruction. No base
       ;; register, index register, or scaling factor can be applied
       ;; (for example, MOV (A0-A3)).

       (byte-operand? (eql opcode #xA0))
       ((the (integer 1 8) operand-size)
	(select-operand-size
         proc-mode byte-operand? rex-byte nil prefixes nil nil nil x86))

       ((the (integer 1 8) offset-size)
	(select-address-size proc-mode p4? x86))

       ;; Get the offset:
       ((mv flg offset x86)
	(rime-size-opt proc-mode offset-size temp-rip #.*cs* :x nil x86))
       ((when flg) (!!ms-fresh :rime-size-error flg))

       ;; Check if the above memory read caused any problems:
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip offset-size x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (seg-reg (select-segment-register proc-mode p2 p4? 0 0 sib x86))

       ;; Get data from offset in segment:
       (inst-ac? (alignment-checking-enabled-p x86))
       ((mv flg data x86)
	(rme-size-opt proc-mode operand-size offset seg-reg :r inst-ac? x86
		      :check-canonicity t))
       ((when flg) (!!ms-fresh :rme-size-error flg))

       ;; Write the data to rAX:
       (x86 (!rgfi-size operand-size *rax* data rex-byte x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-mov-Op/En-TD

  ;; Op/En: TD
  ;; [OP Moffs, rAX]
  ;; A2: MOV moffs8,                  AL
  ;; A3: MOV moffs16/moffs32/moffs64, AX/EAX/RAX

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (e/d (select-address-size
					 segment-base-and-bounds
					 ea-to-la
					 rme-size
					 rime-size)
					(unsigned-byte-p))))
  :body

  (b* (;; This instruction does not require a ModR/M byte.
       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       ;; The Intel manual says the following:

       ;; Under the MOV instruction description:

       ;; The moffs8, moffs16, moffs32 and moffs64 operands specify a
       ;; simple offset relative to the segment base, where 8, 16, 32
       ;; and 64 refer to the size of the data. The address-size
       ;; attribute of the instruction determines the size of the
       ;; offset, either 16, 32 or 64 bits.

       ;; Under the "Instruction Column in the Opcode Summary Table"
       ;; (Intel manual, Jan'19, Vol. 2, Sec. 3.1.1.3):

       ;; moffs8, moffs16, moffs32, moffs64   A simple memory variable
       ;; (memory offset) of type byte, word, or doubleword used by
       ;; some variants of the MOV instruction. The actual address is
       ;; given by a simple offset relative to the segment base. No
       ;; ModR/M byte is used in the instruction. The number shown
       ;; with moffs indicates its size, which is determined by the
       ;; address-size attribute of the instruction.

       ;; Under "Codes for Addressing Method"
       ;; (Intel manual, Jan'19, Vol. 2, App. A.2.1):

       ;; O The instruction has no ModR/M byte. The offset of the
       ;; operand is coded as a word or double word (depending on
       ;; address size attribute) in the instruction. No base
       ;; register, index register, or scaling factor can be applied
       ;; (for example, MOV (A0-A3)).

       (byte-operand? (eql opcode #xA2))
       ((the (integer 1 8) operand-size)
	(select-operand-size
         proc-mode byte-operand? rex-byte nil prefixes nil nil nil x86))

       ((the (integer 1 8) offset-size)
	(select-address-size proc-mode p4? x86))

       ;; Get the offset:
       ((mv flg offset x86)
	(rime-size-opt proc-mode offset-size temp-rip #.*cs* :x nil x86))
       ((when flg) (!!ms-fresh :rime-size-error flg))

       ;; Check if the above memory read caused any problems:
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip offset-size x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (seg-reg (select-segment-register proc-mode p2 p4? 0 0 sib x86))

       ;; Get data from rAX:
       (data (rgfi-size operand-size *rax* rex-byte x86))

       ;; Write the data to offset in segment:
       (inst-ac? t)
       ((mv flg x86)
        (x86-operand-to-reg/mem proc-mode
                                operand-size
                                inst-ac?
                                nil ;; Not a memory pointer operand
                                data
                                seg-reg
                                offset
                                rex-byte
                                0
                                0
                                x86))
       ((when flg) (!!ms-fresh :x86-operand-to-reg/mem flg))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-mov-Op/En-OI

  ;; Op/En: OI
  ;; [OP REG, IMM]
  ;; B0 + rb: MOV r8,  imm8
  ;; B8 + rw: MOV r16, imm16
  ;; B8 + rd: MOV r32, imm32
  ;; B8 + rd: MOV r64, imm64

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (rme-size riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((byte-operand? (and (<= #xB0 opcode) ;; B0+rb
			   (<= opcode #xB7)))
       ((the (integer 1 8) operand-size)
	(select-operand-size
         proc-mode byte-operand? rex-byte nil prefixes nil nil nil x86))

       ;; We don't do any alignment check below when fetching the
       ;; immediate operand; reading the immediate operand is done
       ;; during code fetching, where alignment checks aren't supposed
       ;; to be done (see Intel Manuals, Volume 3, Section 6.15,
       ;; Exception and Interrupt Reference, Interrupt 17 Alignment
       ;; Check Exception (#AC) for details).
       ((mv flg0 imm x86)
	(rme-size-opt proc-mode operand-size temp-rip #.*cs* :x nil x86 :mem-ptr? nil))
       ((when flg0)
	(!!ms-fresh :imm-rme-size-error flg0))

       ((mv flg temp-rip) (add-to-*ip proc-mode temp-rip operand-size x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (reg (the (unsigned-byte 3) (logand 7 opcode)))
       ;; Update the x86 state:
       ;; See Intel Table 3.1, p.3-3, Vol. 2-A
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*b*)
			imm rex-byte x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

(def-inst x86-mov-Op/En-MI

  ;; Op/En: MI
  ;; [OP R/M, IMM]
  ;; C6/0: MOV r/m8, imm8
  ;; C7/0: MOV r/m16, imm16
  ;; C7/0: MOV r/m32, imm32
  ;; C7/0: MOV r/m64, imm32

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08
					 riml32
					 rme-size) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       (byte-operand? (eql opcode #xC6))
       ((the (integer 1 8) imm-size)
	(select-operand-size
         proc-mode byte-operand? rex-byte t prefixes nil nil nil x86))

       ((the (integer 1 8) reg/mem-size)
	(if (and (equal opcode #xC7)
		 (logbitp #.*w* rex-byte))
	    8
	  imm-size))

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
			      imm-size ;; bytes of immediate data
			      x86)))
       ((when flg0)
	(!!ms-fresh :x86-effective-addr-error flg0))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       ((mv flg2 imm x86)
	(rme-size-opt proc-mode imm-size temp-rip #.*cs* :x nil x86
		      :check-canonicity nil))
       ((when flg2)
	(!!ms-fresh :imm-rme-size-error flg2))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip imm-size x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (imm (if (equal reg/mem-size 8)
		;; Sign-extended
		(n64 (n32-to-i32 imm))
	      imm))

       ;; Update the x86 state:
       (inst-ac? t)
       ((mv flg3 x86)
	(x86-operand-to-reg/mem proc-mode reg/mem-size
				 inst-ac?
				 nil ;; Not a memory pointer operand
				 imm
				 seg-reg
				 addr
				 rex-byte
				 r/m
				 mod
				 x86))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg3)
	(!!ms-fresh :x86-operand-to-reg/mem flg3))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LEA
;; ======================================================================

(def-inst x86-lea

  ;; Op/En: RM
  ;; opcode = #x8D/r
  ;; LEA r16, m
  ;; LEA r32, m
  ;; LEA r64, m

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       ;; this is the operand size
       ;; in Intel manual, Mar'17, Vol 2, Tables 3-53 and 3-54:
       ((the (integer 2 8) register-size)
	(select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

       ((mv ?flg0
	    (the (signed-byte 64) M)
	    (the (unsigned-byte 3) increment-RIP-by)
	    x86)
	(x86-effective-addr proc-mode p4?
			    temp-rip
			    rex-byte
			    r/m
			    mod
			    sib
			    0 ;; No immediate operand
			    x86))
       ((when flg0) (!!ms-fresh :x86-effective-addr-error flg0))

       ((mv flg temp-rip) (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (M (trunc register-size M))
       ;; Update the x86 state:
       (x86 (!rgfi-size
	     register-size (reg-index reg rex-byte #.*r*) M rex-byte x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: MOVSX/MOVSXD
;; ======================================================================

; AT&T mnemonic: MOVSLQ

(def-inst x86-movsx

  ;; Op/En: RM
  ;; [OP REG, R/M]
  ;; #x63: MOVSXD r16, r/m16 (Move word to word)
  ;;       MOVSXD r32, r/m32 (Move doubleword to doubleword)
  ;;       MOVSXD r64, r/m32 (Move doubleword to quadword with sign-extension)

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))

       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       ((the (integer 1 8) reg/mem-size)
	(select-operand-size
         proc-mode nil rex-byte t prefixes nil nil nil x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0
	    reg/mem
	    (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte 64) ?addr)
	    x86)
	(x86-operand-from-modr/m-and-sib-bytes proc-mode
						#.*gpr-access*
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (register-size (if (logbitp #.*w* rex-byte)
			  8
			reg/mem-size))
       (reg/mem (if (equal register-size 8)
		    (n64 (n32-to-i32 reg/mem)) ;; sign-extended
		  reg/mem))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*) reg/mem
			rex-byte x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-movsxd

  ;; Op/En: RM
  ;; [OP REG, R/M]

  ;; #x0F BE: MOVSX r16/32/64, r/m8
  ;; (Move byte to word/doubleword/quadword with sign-extension)

  ;; #x0F BF: MOVSX r16/32/64, r/m16
  ;; (Move word to word/doubleword/quadword with sign-extension)

  ;; Note that Intel manual, May'18, Volume 2 excludes the operand-size variant
  ;; MOVSX r16 r/m16, in the sense that it does not list it explicitly.
  ;; AMD manual, Dec'17, Volume 3 also omits this operand-size variant.
  ;; However, experiments with real processors show that at least some
  ;; processors support that operand-size variant. This suggests that it may be
  ;; just an omission from the manuals, and therefore our model supports it.

  :parents (two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32
					       n08-to-i08
					       n16-to-i16
					       n32-to-i32
					       n64-to-i64)
					())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (reg/mem-size (if (equal opcode #xBE) 1 2))

       (inst-ac? t)
       ((mv flg0
	    reg/mem
	    (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte 64) ?addr)
	    x86)
	(x86-operand-from-modr/m-and-sib-bytes proc-mode
						#.*gpr-access*
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (register-size (select-operand-size
                       proc-mode nil rex-byte nil prefixes nil nil nil x86))

       (reg/mem (case reg/mem-size
		  (1
		   (mbe :logic (part-select (n08-to-i08 reg/mem)
					    :low 0 :width (ash register-size 3))
			:exec (logand (1- (ash 1 (the (integer 8 64)
						   (ash register-size 3))))
				      (n08-to-i08 reg/mem))))
		  (2 (case register-size
		       (2 reg/mem)
		       (otherwise
			(mbe :logic (part-select (n16-to-i16 reg/mem)
						 :low 0 :width (ash register-size 3))
			     :exec (logand (1- (ash 1 (the (integer 8 64)
							(ash register-size 3))))
					   (n16-to-i16 reg/mem))))))))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*) reg/mem
			rex-byte x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: MOVZX
;; ======================================================================

(def-inst x86-movzx

  ;; Op/En: RM
  ;; [OP REG, R/M]

  ;; #x0F B6: MOVZX r16/32/64, r/m8
  ;; (Move byte to word/doubleword/quadword with zero-extension)

  ;; #x0F B7: MOVZX r16/32/64, r/m16
  ;; (Move word to word/doubleword/quadword with zero-extension)

  ;; Note that Intel manual, May'18, Volume 2 excludes the operand-size variant
  ;; MOVZX r16 r/m16, in the sense that it does not list it explicitly.
  ;; AMD manual, Dec'17, Volume 3 also omits this operand-size variant.
  ;; However, experiments with real processors show that at least some
  ;; processors support that operand-size variant. This suggests that it may be
  ;; just an omission from the manuals, and therefore our model supports it.

  :parents (two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (reg/mem-size (if (equal opcode #xB6) 1 2))

       (inst-ac? t)
       ((mv flg0
	    reg/mem
	    (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte 64) ?addr)
	    x86)
	(x86-operand-from-modr/m-and-sib-bytes proc-mode #.*gpr-access*
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((the (integer 1 8) register-size)
	(select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*) reg/mem
			rex-byte x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: MOV to/from Control Registers
;; ======================================================================

(def-inst x86-mov-control-regs-Op/En-MR

  ;; Move control register to GPR

  ;; Op/En: MR
  ;; [OP R/M, REG]
  ;; 0F 20/r:         MOV r32, CR0-CR7
  ;; 0F 20/r:         MOV r64, CR0-CR7
  ;; REX.R + 0F 20/0: MOV r64, CR8

  ;; From Intel Manuals, Vol 2A, "MOV Move to/from Control
  ;; Register":

  ;; At the opcode level, the reg field within the ModR/M byte
  ;; specifies which of the control registers is loaded or read. The 2
  ;; bits in the mod field are ignored. The r/m field specifies the
  ;; general-purpose register loaded or read. Attempts to reference
  ;; CR1, CR5, CR6, CR7, and CR9-CR15 result in undefined opcode (#UD)
  ;; exceptions.

  ;; In 64-bit mode, the instruction's default operation size
  ;; is 64 bits. The REX.R prefix must be used to access
  ;; CR8. Use of REX.B permits access to additional registers
  ;; (R8-R15). Use of the REX.W prefix or 66H prefix is
  ;; ignored. Use of the REX.R prefix to specify a register
  ;; other than CR8 causes an invalid-opcode exception. See the
  ;; summary chart at the beginning of this section for encoding
  ;; data and limits.

  :parents (two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (;; The r/m field specifies the GPR (destination).
       ;; MOD field is ignored.
       ;; The reg field specifies the control register (source).

       ;; *operand-size-override* and REX.W are ignored.

       ;; Get value from the control register
       (ctr-index
	;; Note that there is a #UD Exception if an attempt is made to access
	;; CR1, CR5, CR6, or CR7 or if the REX.R prefix is used to specify a
	;; register other than CR8.  This is checked during dispatch --- see
	;; opcode-maps for details.
	(if (and (logbitp #.*r* rex-byte)
		 (equal reg 0))
	    #.*cr8*
	  reg))

       (operand-size (if (equal proc-mode #.*64-bit-mode*) 8 4))

       (ctr-val (the (unsigned-byte 64) (ctri ctr-index x86)))
       (ctr-val (if (eql operand-size 4) (n32 ctr-val) ctr-val))

       ;; Update the x86 state:
       (x86
	(!rgfi-size operand-size
		    (reg-index r/m rex-byte #.*b*)
		    ctr-val
		    rex-byte
		    x86))
       ;; The OF, SF, ZF, AF, PF, and CF flags are undefined.
       (x86 (!flgi-undefined :cf x86))
       (x86 (!flgi-undefined :pf x86))
       (x86 (!flgi-undefined :af x86))
       (x86 (!flgi-undefined :zf x86))
       (x86 (!flgi-undefined :sf x86))
       (x86 (!flgi-undefined :of x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
