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
;; INSTRUCTION: Jcc/JrCXZ/CMOVcc/SETcc
;; ======================================================================

; From Intel Vol. 1, 6-11:

;; In 64-bit mode, the operand size for all near branches (CALL, RET, JCC,
;; JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions update the
;; 64-bit RIP without the need for a REX operand-size prefix.

;; The following aspects of near branches are controlled by the effective
;; operand size:
;;   Truncation of the size of the instruction pointer
;;   Size of a stack pop or push, due to a CALL or RET
;;   Size of a stack-pointer increment or decrement, due to a CALL or RET
;;   Indirect-branch operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits regardless of
;; operand size prefixes (operand size prefixes are silently ignored). However,
;; the displacement field for relative branches is still limited to 32 bits and
;; the address size for near branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they also
;; impact the address calculation for memory indirect branches. Such addresses
;; are 64 bits by default; but they can be overridden to 32 bits by an address
;; size prefix.

(define jcc/cmovcc/setcc-spec
  ((opcode :type (unsigned-byte 8))
   x86)

  ;; Jcc

  ;; Op    Instruction                                  Condition
  ;; 70    JO rel8                                      Jump if OF = 1
  ;; 71    JNO rel8                                     Jump if OF = 0
  ;; 72    JB/NAE/C rel8                                Jump if CF = 1
  ;; 73    JNB/AE/NC rel8                               Jump if CF = 0
  ;; 74    JZ/E rel8                                    Jump if ZF = 1
  ;; 75    JNZ/NE rel8                                  Jump if ZF = 0
  ;; 76    JBE/NA rel8                                  Jump if CF = 1 or ZF = 1
  ;; 77    JNBE/A rel8                                  Jump if CF = 0 and ZF = 0
  ;; 78    JS rel8                                      Jump if SF = 1
  ;; 79    JNS rel8                                     Jump if SF = 0
  ;; 7A    JP/PE rel8                                   Jump if PF = 1
  ;; 7B    JNP/PO rel8                                  Jump if PF = 0
  ;; 7C    JL/NGE rel8                                  Jump if SF != OF
  ;; 7D    JNL/GE rel8                                  Jump if SF = OF
  ;; 7E    JLE/NG rel8                                  Jump if ZF = 1 or SF != OF
  ;; 7F    JNLE/G rel8                                  Jump if ZF = 0 and SF = OF

  ;; Op    Instruction                                  Condition
  ;; 0F 80 JO rel32                                     Jump if OF = 1
  ;; 0F 81 JNO rel32                                    Jump if OF = 0
  ;; 0F 82 JB/NAE/C rel32                               Jump if CF = 1
  ;; 0F 83 JNB/AE/NC rel32                              Jump if CF = 0
  ;; 0F 84 JZ/E rel32                                   Jump if ZF = 1
  ;; 0F 85 JNZ/JNE rel32                                Jump if ZF = 0
  ;; 0F 86 JBE/NA rel32                                 Jump if CF = 1 or ZF = 1
  ;; 0F 87 JNBE/A rel32                                 Jump if CF = 0 and ZF = 0
  ;; 0F 88 JS rel32                                     Jump if SF = 1
  ;; 0F 89 JNS rel32                                    Jump if SF = 0
  ;; 0F 8A JP/PE rel32                                  Jump if PF = 1
  ;; 0F 8B JNP/PO rel32                                 Jump if PF = 0
  ;; 0F 8C JL/NGE rel32                                 Jump if SF != OF
  ;; 0F 8D JNL/GE rel32                                 Jump if SF = OF
  ;; 0F 8E JLE/NG rel32                                 Jump if ZF = 1 or SF != OF
  ;; 0F 8F JNLE/G rel32                                 Jump if ZF = 0 and SF = OF

  ;; CMOVcc

  ;; 0F 40 CMOVO r16/32/64, r/m16/32/64                 Move if OF = 1
  ;; 0F 41 CMOVNO r16/32/64, r/m16/32/64                Move if OF = 0
  ;; 0F 42 CMOVB/CMOVC/CMOVNAE r16/32/64, r/m16/32/64   Move if CF = 1
  ;; 0F 43 CMOVAE/CMOVNB/CMOVNC r16/32/64, r/m16/32/64  Move if CF = 0
  ;; 0F 44 CMOVE/CMOVZ r16/32/64, r/m16/32/64           Move if ZF = 1
  ;; 0F 45 CMOVNE/CMOVNZ r16/32/64, r/m16/32/64         Move if ZF = 0
  ;; 0F 46 CMOVBE/CMOVNA r16/32/64, r/m16/32/64         Move if CF = 1 or ZF = 1
  ;; 0F 47 CMOVA/CMOVNBE  r16/32/64, r/m16/32/64        Move if CF = 0 and ZF = 0
  ;; 0F 48 CMOVS r16/32/64, r/m16/32/64                 Move if SF = 1
  ;; 0F 49 CMOVNS r16/32/64, r/m16/32/64                Move if SF = 0
  ;; 0F 4A CMOVP/CMOVPE r16/32/64, r/m16/32/64          Move if PF = 1
  ;; 0F 4B CMOVNP/CMOVPO r16/32/64, r/m16/32/64         Move if PF = 0
  ;; 0F 4C CMOVL/CMOVNGE r16/32/64, r/m16/32/64         Move if SF != OF
  ;; 0F 4D CMOVGE/CMOVNL r16/32/64, r/m16/32/64         Move if SF = OF
  ;; 0F 4E CMOVLE/CMOVNG r16/32/64, r/m16/32/64         Move if ZF = 1 or SF != OF
  ;; 0F 4F CMOVG/CMOVNLE r16/32/64, r/m16/32/64         Move if ZF = 0 and SF = OF

  (let ((low-nibble (the (unsigned-byte 4) (logand opcode #xf))))
    (case low-nibble
      (#x0 (equal 1 (the (unsigned-byte 1) (flgi :of x86))))
      (#x1 (equal 0 (the (unsigned-byte 1) (flgi :of x86))))
      (#x2 (equal 1 (the (unsigned-byte 1) (flgi :cf x86))))
      (#x3 (equal 0 (the (unsigned-byte 1) (flgi :cf x86))))
      (#x4 (equal 1 (the (unsigned-byte 1) (flgi :zf x86))))
      (#x5 (equal 0 (the (unsigned-byte 1) (flgi :zf x86))))
      (#x6 (or (equal 1 (the (unsigned-byte 1) (flgi :cf x86)))
	       (equal 1 (the (unsigned-byte 1) (flgi :zf x86)))))
      (#x7 (and (equal 0 (the (unsigned-byte 1) (flgi :cf x86)))
		(equal 0 (the (unsigned-byte 1) (flgi :zf x86)))))
      (#x8 (equal 1 (the (unsigned-byte 1) (flgi :sf x86))))
      (#x9 (equal 0 (the (unsigned-byte 1) (flgi :sf x86))))
      (#xA (equal 1 (the (unsigned-byte 1) (flgi :pf x86))))
      (#xB (equal 0 (the (unsigned-byte 1) (flgi :pf x86))))
      (#xC (not (equal (the (unsigned-byte 1) (flgi :sf x86))
		       (the (unsigned-byte 1) (flgi :of x86)))))
      (#xD (equal (the (unsigned-byte 1) (flgi :sf x86))
		  (the (unsigned-byte 1) (flgi :of x86))))
      (#xE (or (equal 1 (the (unsigned-byte 1) (flgi :zf x86)))
	       (not (equal (the (unsigned-byte 1) (flgi :sf x86))
			   (the (unsigned-byte 1) (flgi :of x86))))))
      (#xF (and (equal 0 (the (unsigned-byte 1) (flgi :zf x86)))
		(equal (the (unsigned-byte 1) (flgi :sf x86))
		       (the (unsigned-byte 1) (flgi :of x86)))))
      (otherwise ;; will not be reached
       nil))))

(def-inst x86-one-byte-jcc

  ;; Jump (short) if condition is met

  ;; Intel manual, Mar'17, Vol. 2A, Jcc reference says:
  ;; "In 64-bit mode, operand size is fixed at 64 bits.
  ;; JMP Short is RIP + 8-bit offset sign extended to 64 bits."

  ;; Op/En: D
  ;; Jcc

  ;; Op    Instruction                                  Condition
  ;; 70    JO rel8                                      Jump if OF = 1
  ;; 71    JNO rel8                                     Jump if OF = 0
  ;; 72    JB/NAE/C rel8                                Jump if CF = 1
  ;; 73    JNB/AE/NC rel8                               Jump if CF = 0
  ;; 74    JZ/E rel8                                    Jump if ZF = 1
  ;; 75    JNZ/NE rel8                                  Jump if ZF = 0
  ;; 76    JBE/NA rel8                                  Jump if CF = 1 or ZF = 1
  ;; 77    JNBE/A rel8                                  Jump if CF = 0 and ZF = 0
  ;; 78    JS rel8                                      Jump if SF = 1
  ;; 79    JNS rel8                                     Jump if SF = 0
  ;; 7A    JP/PE rel8                                   Jump if PF = 1
  ;; 7B    JNP/PO rel8                                  Jump if PF = 0
  ;; 7C    JL/NGE rel8                                  Jump if SF != OF
  ;; 7D    JNL/GE rel8                                  Jump if SF = OF
  ;; 7E    JLE/NG rel8                                  Jump if ZF = 1 or SF != OF
  ;; 7F    JNLE/G rel8                                  Jump if ZF = 0 and SF = OF

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32 rime-size) ())))

  :returns (x86 x86p :hyp (x86p x86)
		:hints (("Goal" :in-theory (enable rime-size))))

  :body

  (b* (;; temp-rip right now points to the rel8 byte.  Add 1 to
       ;; temp-rip to account for rel8 when computing the length
       ;; of this instruction.
       (badlength? (check-instruction-length start-rip temp-rip 1))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (branch-cond (jcc/cmovcc/setcc-spec opcode x86)))

    (if branch-cond

	;; branch condition is true:
	(b* (;; read rel8 (a value between -128 and +127):
	     ((mv flg rel8 x86) (rime-size proc-mode 1 temp-rip #.*cs* :x nil x86))
	     ((when flg) (!!ms-fresh :rime-size-error flg))
	     ;; add rel8 to the address of the next instruction,
	     ;; which is one past temp-rip to take the rel8 byte into account:
	     ((mv flg next-rip) (add-to-*ip proc-mode temp-rip (1+ rel8) x86))
	     ((when flg) (!!ms-fresh :rip-increment-error flg))
	     ;; set instruction pointer to new value:
	     (x86 (write-*ip proc-mode next-rip x86)))
	  x86)

      ;; branch condition is false:
      (b* (;; go to the next instruction,
	   ;; which starts just after the rel8 byte:
	   ((mv flg next-rip) (add-to-*ip proc-mode temp-rip 1 x86))
	   ((when flg) (!!ms-fresh :rip-increment-error flg))
	   (x86 (write-*ip proc-mode next-rip x86)))
	x86))))

(def-inst x86-two-byte-jcc

  ;; Jump (near) if condition is met

  ;; Intel manual, Mar'17, Vol. 2A, Jcc reference says:
  ;; "In 64-bit mode, operand size is fixed at 64 bits.
  ;; JMP Short is RIP + 32-bit offset sign extended to 64 bits."

  ;; Two-byte Jcc: The operand-size is forced to a 64-bit operand size
  ;; when in 64-bit mode (prefixes that change operand size are ignored
  ;; for this instruction in 64-bit mode).  See Intel Manual, Vol. 2C,
  ;; Table A-1, row with 'f64'.

  ;; Op/En: D
  ;; Op    Instruction                                  Condition
  ;; 0F 80 JO rel32                                     Jump if OF = 1
  ;; 0F 81 JNO rel32                                    Jump if OF = 0
  ;; 0F 82 JB/NAE/C rel32                               Jump if CF = 1
  ;; 0F 83 JNB/AE/NC rel32                              Jump if CF = 0
  ;; 0F 84 JZ/E rel32                                   Jump if ZF = 1
  ;; 0F 85 JNZ/JNE rel32                                Jump if ZF = 0
  ;; 0F 86 JBE/NA rel32                                 Jump if CF = 1 or ZF = 1
  ;; 0F 87 JNBE/A rel32                                 Jump if CF = 0 and ZF = 0
  ;; 0F 88 JS rel32                                     Jump if SF = 1
  ;; 0F 89 JNS rel32                                    Jump if SF = 0
  ;; 0F 8A JP/PE rel32                                  Jump if PF = 1
  ;; 0F 8B JNP/PO rel32                                 Jump if PF = 0
  ;; 0F 8C JL/NGE rel32                                 Jump if SF != OF
  ;; 0F 8D JNL/GE rel32                                 Jump if SF = OF
  ;; 0F 8E JLE/NG rel32                                 Jump if ZF = 1 or SF != OF
  ;; 0F 8F JNLE/G rel32                                 Jump if ZF = 0 and SF = OF

  :parents (two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32 rime-size) ())))

  :returns (x86 x86p :hyp (x86p x86)
		:hints (("Goal" :in-theory (enable rime-size))))

  :body

  ;; Note: Here opcode is the second byte of the two byte opcode.

  (b* (((the (integer 0 4) offset-size)
        (select-operand-size proc-mode nil rex-byte nil prefixes nil t t x86))

       ;; temp-rip right now points to the rel16/rel32 byte.  Add 2 or 4 to
       ;; temp-rip to account for rel16/rel32 when computing the length
       ;; of this instruction.
       (badlength? (check-instruction-length start-rip temp-rip offset-size))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (branch-cond (jcc/cmovcc/setcc-spec opcode x86)))

    (if branch-cond

	;; branch condition is true:
	(b* (;; read rel16/rel32 (as a signed value):
	     ((mv flg offset x86)
	      (rime-size proc-mode offset-size temp-rip #.*cs* :x nil x86))
	     ((when flg) (!!ms-fresh :rime-size-error flg))
	     ;; add rel16/rel32 to the address of the next instruction,
	     ;; which is 2 or 4 past temp-rip to take the rel16/32 into
	     ;; account:
	     ((mv flg next-rip)
	      (add-to-*ip proc-mode temp-rip (+ offset-size offset) x86))
	     ((when flg) (!!ms-fresh :rip-increment-error flg))
	     ;; set instruction pointer to new value:
	     (x86 (write-*ip proc-mode next-rip x86)))
	  x86)

      ;; branch condition is false:
      (b* (;; fo to the next instruction,
	   ;; which starts just after the rel16/rel32:
	   ((mv flg next-rip) (add-to-*ip proc-mode temp-rip offset-size x86))
	   ((when flg) (!!ms-fresh :rip-increment-error flg))
	   (x86 (write-*ip proc-mode next-rip x86)))
	x86))))

(def-inst x86-jrcxz

  ;; Jump (short) if condition is met

  ;; E3 cb: JCXZ  rel8 Jump short if CX  is 0
  ;; E3 cb: JECXZ rel8 Jump short if ECX is 0
  ;; E3 cb: JRCXZ rel8 Jump short if RCX is 0

  ;; The register checked is determined by the address-size attribute.

  ;; Jump short: RIP = RIP + 8-bit offset sign-extended to 64-bits

  ;; Op/En: D

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08
					 riml32
					 rime-size
					 select-address-size)
					())))

  :returns (x86 x86p :hyp (x86p x86)
		:hints (("Goal" :in-theory (enable rime-size))))

  :body

  (b* (;; temp-rip right now points to the rel8 byte.  Add 1 to
       ;; temp-rip to account for rel8 when computing the length
       ;; of this instruction.
       (badlength? (check-instruction-length start-rip temp-rip 1))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))
       (register-size (select-address-size proc-mode p4? x86))

       (branch-cond
	(equal (rgfi-size register-size *rcx* rex-byte x86) 0)))

    (if branch-cond

	;; branch condition is true:
	(b* (;; read rel8 (a value between -128 and +127):
	     ((mv flg rel8 x86) (rime-size proc-mode 1 temp-rip #.*cs* :x nil x86))
	     ((when flg) (!!ms-fresh :rime-size-error flg))
	     ;; add rel8 to the address of the next instruction,
	     ;; which is one past temp-rip to take the rel8 byte into account:
	     ((mv flg next-rip) (add-to-*ip proc-mode temp-rip (1+ rel8) x86))
	     ((when flg) (!!ms-fresh :rip-increment-error flg))
	     ;; set instruction pointer to new value:
	     (x86 (write-*ip proc-mode next-rip x86)))
	  x86)

      ;; branch condition is false:
      (b* (;; go to the next instruction,
	   ;; which starts just after the rel8 byte:
	   ((mv flg next-rip) (add-to-*ip proc-mode temp-rip 1 x86))
	   ((when flg) (!!ms-fresh :rip-increment-error flg))
	   (x86 (write-*ip proc-mode next-rip x86)))
	x86))))

(def-inst x86-cmovcc

  ;; Op/En: RM
  ;; [OP REG, R/M]

  ;; CMOVcc

  ;; 0F 40 CMOVO r16/32/64, r/m16/32/64                 Move if OF = 1
  ;; 0F 41 CMOVNO r16/32/64, r/m16/32/64                Move if OF = 0
  ;; 0F 42 CMOVB/CMOVC/CMOVNAE r16/32/64, r/m16/32/64   Move if CF = 1
  ;; 0F 43 CMOVAE/CMOVNB/CMOVNC r16/32/64, r/m16/32/64  Move if CF = 0
  ;; 0F 44 CMOVE/CMOVZ r16/32/64, r/m16/32/64           Move if ZF = 1
  ;; 0F 45 CMOVNE/CMOVNZ r16/32/64, r/m16/32/64         Move if ZF = 0
  ;; 0F 46 CMOVBE/CMOVNA r16/32/64, r/m16/32/64         Move if CF = 1 or ZF = 1
  ;; 0F 47 CMOVA/CMOVNBE  r16/32/64, r/m16/32/64        Move if CF = 0 and ZF = 0
  ;; 0F 48 CMOVS r16/32/64, r/m16/32/64                 Move if SF = 1
  ;; 0F 49 CMOVNS r16/32/64, r/m16/32/64                Move if SF = 0
  ;; 0F 4A CMOVP/CMOVPE r16/32/64, r/m16/32/64          Move if PF = 1
  ;; 0F 4B CMOVNP/CMOVPO r16/32/64, r/m16/32/64         Move if PF = 0
  ;; 0F 4C CMOVL/CMOVNGE r16/32/64, r/m16/32/64         Move if SF != OF
  ;; 0F 4D CMOVGE/CMOVNL r16/32/64, r/m16/32/64         Move if SF = OF
  ;; 0F 4E CMOVLE/CMOVNG r16/32/64, r/m16/32/64         Move if ZF = 1 or SF != OF
  ;; 0F 4F CMOVG/CMOVNLE r16/32/64, r/m16/32/64         Move if ZF = 0 and SF = OF

  :parents (two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  ;; Note, opcode here denotes the second byte of the two-byte opcode.

  (b* ((p2 (prefixes->seg prefixes))

       ((the (integer 1 8) operand-size)
	(select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0
	    reg/mem
	    (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte 64) ?addr)
	    x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 proc-mode #.*gpr-access* operand-size inst-ac?
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

       (branch-cond (jcc/cmovcc/setcc-spec opcode x86))

       ;; Update the x86 state:
       (x86
	(if branch-cond
	    (!rgfi-size operand-size
			(reg-index reg rex-byte #.*r*)
			reg/mem
			rex-byte
			x86)
	  x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-setcc

  ;; Op/En: M

  ;; SETcc

  ;; 0F 90 SETO r/m8                                    Set if OF = 1
  ;; 0F 91 SETNO r/m8                                   Set if OF = 0
  ;; 0F 92 SETB/SETC/SETNAE r/m8                        Set if CF = 1
  ;; 0F 93 SETAE/SETNB/SETNC r/m8                       Set if CF = 0
  ;; 0F 94 SETE/SETZ r/m8                               Set if ZF = 1
  ;; 0F 95 SETNE/SETNZ r/m8                             Set if ZF = 0
  ;; 0F 96 SETBE/SETNA r/m8                             Set if CF = 1 or ZF = 1
  ;; 0F 97 SETA/SETNBE  r/m8                            Set if CF = 0 and ZF = 0
  ;; 0F 98 SETS r/m8                                    Set if SF = 1
  ;; 0F 99 SETNS r/m8                                   Set if SF = 0
  ;; 0F 9A SETP/SETPE r/m8                              Set if PF = 1
  ;; 0F 9B SETNP/SETPO r/m8                             Set if PF = 0
  ;; 0F 9C SETL/SETNGE r/m8                             Set if SF != OF
  ;; 0F 9D SETGE/SETNL r/m8                             Set if SF = OF
  ;; 0F 9E SETLE/SETNG r/m8                             Set if ZF = 1 or SF != OF
  ;; 0F 9F SETG/SETNLE r/m8                             Set if ZF = 0 and SF = OF

  :parents (two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  ;; Note, opcode here denotes the second byte of the two-byte opcode.

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
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
	(!!ms-fresh :x86-effective-addr-error flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (branch-cond (jcc/cmovcc/setcc-spec opcode x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; Update the x86 state:
       (inst-ac? t)
       (val (if branch-cond 1 0))
       ((mv flg2 x86)
	(x86-operand-to-reg/mem proc-mode 1
				 inst-ac?
				 nil ;; Not a memory pointer operand
				 val
				 seg-reg
				 (the (signed-byte 64) addr)
				 rex-byte
				 r/m
				 mod
				 x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
	(!!ms-fresh :x86-operand-to-reg/mem flg2))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
