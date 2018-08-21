; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

; Copyright (C) 2018, Centaur Technology, Inc.
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
; Shilpi Goel         <shilpi@centtech.com>

(in-package "X86ISA")

(include-book "std/util/define" :dir :system)

; Lisp representation of Intel's opcode maps (See Intel Manuals,
; Vol. 2, Appendix A)

(defsection opcode-maps
  :parents (instructions x86-decoder)
  :short "ACL2 representation of Intel's x86 Opcode Maps"
  :long "<p>The constants @('*one-byte-opcode-map-lst*'),
 @('*two-byte-opcode-map-lst*'), @('*0F-38-three-byte-opcode-map-lst*'),
 @('*0F-3A-three-byte-opcode-map-lst*'), and
 @('*opcode-extensions-by-group-number*') contain information presented in the
 opcode maps, as described in Intel Manual, Volume 2, Appendix A.</p>

 <p>The constants @('*vex-0F-opcodes*'), @('*vex-0F38-opcodes*'),
 @('*vex-0F3A-opcodes*'), @('*evex-0F-opcodes*'), @('*evex-0F38-opcodes*'), and
 @('*evex-0F3A-opcodes*') contain a listing of all the possible VEX- and
 EVEX-encoded instructions, gleaned from the Instruction Set Reference pages of
 Intel Manuals, Vol. 2, Chapters 3, 4, and 5.</p>

 <p>We annotate each opcode in these opcode maps with the instruction semantic
 function that specifies it (if one exists; @(see x86-step-unimplemented) is
 the 'default' semantic function).  See @(see implemented-opcodes) for
 details.</p>")

(local (xdoc::set-default-parents 'opcode-maps))

;; ----------------------------------------------------------------------

(defconst *opcode-map-superscripts*

  ;; Source: Intel Manuals, Volume 2, Appendix A.2.5.
  ;; Table A-1. Superscripts Utilized in Opcode Tables.

  (list

   ;; Bits 5, 4, and 3 of ModR/M byte used as an opcode extension
   ;; (refer to Section A.4, Opcode Extensions For One-Byte And
   ;; Two-byte Opcodes)
   :1a

   ;; Use the 0F0B opcode (UD2 instruction) or the 0FB9H opcode when
   ;; deliberately trying to generate an invalid opcode exception
   ;; (#UD).
   :1b

   ;; Some instructions use the same two-byte opcode. If the
   ;; instruction has variations, or the opcode represents different
   ;; instructions, the ModR/M byte will be used to differentiate the
   ;; instruction. For the value of the ModR/M byte needed to decode
   ;; the instruction, see Table A-6.
   :1c

   ;; The instruction is invalid or not encodable in 64-bit mode. 40
   ;; through 4F (single-byte INC and DEC) are REX prefix combinations
   ;; when in 64-bit mode (use FE/FF Grp 4 and 5 for INC and DEC).
   :i64

   ;; Instruction is only available when in 64-bit mode.
   :o64

   ;; When in 64-bit mode, instruction defaults to 64-bit operand size
   ;; and cannot encode 32-bit operand size.
   :d64

   ;; The operand size is forced to a 64-bit operand size when in
   ;; 64-bit mode (prefixes that change operand size are ignored for
   ;; this instruction in 64-bit mode).
   :f64

   ;; VEX form only exists. There is no legacy SSE form of the
   ;; instruction. For Integer GPR instructions it means VEX prefix
   ;; required.
   :v

   ;; VEX128 & SSE forms only exist (no VEX256), when can't be
   ;; inferred from the data size.
   :v1
   ))

;; ----------------------------------------------------------------------

;; Definitions related to exceptions:

;; TODO regarding exceptions:

;; --- Only exceptions for the protected, compatibility, and 64-bit mode have
;;     been specified.

;; --- VMX, SMM instructions' exceptions have not been listed yet.

;; --- What's the exception scenario for RESERVEDNOP (Group 16, #ux0F_18)?

(defconst *ud-Lock-used*
  `(eql #.*lock* (prefixes-slice :lck prefixes)))

(defconst *ud-Opr-used*
  `(eql #.*operand-size-override* (prefixes-slice :opr prefixes)))

(defconst *ud-Reps-used*
  `(or (eql #.*repe* (prefixes-slice :rep prefixes))
       (eql #.*repne* (prefixes-slice :rep prefixes))))

(defconst *ud-ModR/M.Mod-indicates-Register*
  `(eql (mrm-mod modr/m) #b11))

(defconst *ud-Lock-used-mod-indicates-register*
  ;; For now, we check this only for instructions that require a modr/m byte.
  ;; There are some instructions that do not take a modr/m byte but that throw
  ;; a #UD when lock occurs and the destination is a register operand (e.g.,
  ;; ADC opcodes 0x14 and 0x15).  For those cases, use *ud-Lock-used* instead.
  `(and
    ;; ModR/M.mod = #b11 means that the modr/m byte points to a register, and
    ;; not to a memory operand.  See Table 2-2 (32-bit Addressing Forms with
    ;; the ModR/M byte) in Intel Vol. 2.
    ,*ud-ModR/M.Mod-indicates-Register*
    (eql #.*lock* (prefixes-slice :lck prefixes))))

(defconst *ud-Lock-used-Dest-not-Memory-Op*
  *ud-Lock-used-mod-indicates-register*)

(defconst *ud-source-operand-is-a-register*
  *ud-ModR/M.Mod-indicates-Register*)

(defconst *ud-second-operand-is-a-register*
  *ud-ModR/M.Mod-indicates-Register*)

(defconst *ud-cpl-is-not-zero*
  `(not (eql (cpl x86) 0)))

;; ----------------------------------------------------------------------

;; A note about our annotations of the opcode maps:

;; We annotate each opcode in our representation of the opcode maps with the
;; instruction semantic function that implements that opcode.  We use these
;; annotations to generate code that dispatches control to the appropriate
;; instruction semantic function once the instruction has been "sufficiently"
;; decoded (see x86-fetch-decode-execute), and to generate coverage reports
;; (i.e., which opcodes, in which modes, have been implemented in x86isa,
;; etc.).

;; <annotation> should always be a true-listp.

;; 1. <annotation> can be 'nil, which means unimplemented.  Semantic function
;;    x86-step-unimplemented should be called here, and this byte should be
;;    marked as "todo" in x86isa.

;;    General format: 'nil

;; In the rest of the list below, <annotation> takes the form:
;; (:fn . <name>), where <name> should always be a true-listp.

;; 2. <name> can be (:no-instruction), which means that there is no Intel
;;    instruction corresponding to this opcode (e.g., 0x26 is a legacy prefix
;;    or 0xD6 is blank in the one-byte opcode map).  Semantic function
;;    x86-illegal-instruction should be called here, in case this byte has been
;;    filed away by the x86isa decoder as an opcode byte --- if this happens,
;;    it'll indicate an error in the x86isa decoder.  However, unlike the
;;    previous case when x86-step-unimplemented is called, this byte should be
;;    marked as "implemented" in x86isa.

;; 3. If <name> has one element, then it is the name of the instruction
;;    semantic function that deals with all the currently implemented modes of
;;    operation.

;;    General format: (:fn . (instruction-semantic-fn))

;; 4. If <name> has more than one element, then the first one is the name of
;;    the instruction semantic function, and the rest are pairs whose keys are
;;    the formals of the function and values are the explicit values they
;;    should be assigned when creating the opcode dispatch function.  E.g., for
;;    opcode #x00:

;;    (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
;;             (operation . #.*OP-ADD*)))

;;    General format: (:fn . (instruction-semantic-fn (formal-1 . value-1)
;;                                                     ...
;;                                                    (formal-n . value-n)))

;; Note that for opcode cells with :i64 and :o64:
;;     ((:i64 . foo) (:o64 . bar))
;; the following sort of code will be generated:
;;    (if (64-bit-modep x86)
;;        <appropriate call for bar>
;;        <appropriate call for foo>)

(defconst *one-byte-opcode-map-lst*
  ;; Source: Intel Volume 2, Table A-2.

  '(
    #|       -------------------------------        |#

    #| 00 |# (("ADD" 2 (E b)  (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADD*)))
	       (:ud . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("ADD" 2 (E v)  (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADD*)))
	       (:ud . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("ADD" 2 (G b)  (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADD*)))
	       (:ud . (*ud-Lock-used*)))
	      ("ADD" 2 (G v)  (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADD*)))
	       (:ud . (*ud-Lock-used*)))
	      ("ADD" 2 (:AL)  (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADD*)))
	       (:ud . (*ud-Lock-used*)))
	      ("ADD" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADD*)))
	       (:ud . (*ud-Lock-used*)))
	      ((:i64 . ("PUSH ES" 0
			(:fn . (x86-push-segment-register))
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH ES is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP ES"  0
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD"  0
			(:fn . (x86-illegal-instruction
				(message .
					 "POP ES is illegal in the 64-bit mode!"))))))
	      ("OR" 2 (E b)  (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-OR*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("OR" 2 (E v)  (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-OR*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("OR" 2 (G b)  (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-OR*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("OR" 2 (G v)  (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-OR*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("OR" 2 (:AL)  (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-OR*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("OR" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-OR*)))
	       (:ud  . (*ud-Lock-used*)))
	      ((:i64 . ("PUSH CS" 0
			(:fn . (x86-push-segment-register))
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH CS is illegal in the 64-bit mode!"))))))
	      (:2-byte-escape
	       (:fn . (two-byte-opcode-decode-and-execute
		       (escape-byte . opcode)))))

    #| 10 |# (("ADC" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADC*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("ADC" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADC*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("ADC" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADC*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("ADC" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADC*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("ADC" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADC*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("ADC" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADC*)))
	       (:ud  . (*ud-Lock-used*)))
	      ((:i64 . ("PUSH SS" 0
			(:fn . (x86-push-segment-register))
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH SS is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP SS" 0
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "POP SS is illegal in the 64-bit mode!"))))))
	      ("SBB" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SBB*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("SBB" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SBB*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("SBB" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SBB*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("SBB" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SBB*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("SBB" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SBB*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("SBB" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SBB*)))
	       (:ud  . (*ud-Lock-used*)))
	      ((:i64 . ("PUSH DS" 0
			(:fn . (x86-push-segment-register))
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH DS is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP DS" 0
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "POP DS is illegal in the 64-bit mode!")))))))

    #| 20 |# (("AND" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-AND*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("AND" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-AND*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("AND" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-AND*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("AND" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-AND*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("AND" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-AND*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("AND" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-AND*)))
	       (:ud  . (*ud-Lock-used*)))
	      (:prefix-ES
	       (:fn . (:no-instruction)))
	      ((:i64 . ("DAA" 0
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "DAA is illegal in the 64-bit mode!"))))))
	      ("SUB" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SUB*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("SUB" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SUB*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("SUB" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SUB*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("SUB" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SUB*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("SUB" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SUB*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("SUB" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SUB*)))
	       (:ud  . (*ud-Lock-used*)))
	      (:prefix-CS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("DAS" 0
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "DAS is illegal in the 64-bit mode!")))))))

    #| 30 |# (("XOR" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-XOR*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("XOR" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-XOR*)))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("XOR" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-XOR*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("XOR" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-XOR*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("XOR" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-XOR*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("XOR" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-XOR*)))
	       (:ud  . (*ud-Lock-used*)))
	      (:prefix-SS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("AAA" 0
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "AAA is illegal in the 64-bit mode!"))))))
	      ("CMP" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-CMP*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMP" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-CMP*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMP" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-CMP*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMP" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-CMP*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMP" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-CMP*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMP" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-CMP*)))
	       (:ud  . (*ud-Lock-used*)))
	      (:prefix-DS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("AAS" 0
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "AAS is illegal in the 64-bit mode!")))))))

    #| 40 |# (((:o64  . (:rex (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eAX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-b (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eCX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-x (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eDX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-xb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eBX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-r (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eSP)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-rb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eBP)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-rx (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eSI)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-rxb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eDI)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-w (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eAX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-wb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eCX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-wx (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eDX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-wxb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eBX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-wr (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eSP)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-wrb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eBP)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-wrx (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eSI)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*)))))
	      ((:o64  . (:rex-wrxb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eDI)
			(:fn . (x86-inc/dec-4x))
			(:ud  . (*ud-Lock-used*))))))

    #| 50 |# (("PUSH" 1 (:rAX/r8)   :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSH" 1 (:rCX/r9)   :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSH" 1 (:rDX/r10)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSH" 1 (:rBX/r11)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSH" 1 (:rSP/r11)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSH" 1 (:rBP/r13)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSH" 1 (:rSI/r14)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSH" 1 (:rDI/r15)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"  1 (:rAX/r8)   :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"  1 (:rCX/r9)   :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"  1 (:rDX/r10)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"  1 (:rBX/r11)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"  1 (:rSP/r11)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"  1 (:rBP/r13)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"  1 (:rSI/r14)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"  1 (:rDI/r15)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . (*ud-Lock-used*))))

    #| 60 |# (((:i64 . ("PUSHA/PUSHAD" 0
			(:fn . (x86-pusha))
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSHA is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POPA/POPAD"   0
			(:fn . (x86-popa))
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "POPA is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("BOUND"  2 (G v) (M a)
			(:ud  . (*ud-Lock-used*
				 *ud-second-operand-is-a-register*))))
	       (:o64 . (:evex-byte0 (:fn . (:no-instruction)))
		     ;; ("#UD" 0
		     ;;  (:fn . (x86-illegal-instruction
		     ;;          (message .
		     ;;                   "BOUND is illegal in the 64-bit mode!"))))
		     ))
	      ((:o64 . ("MOVSXD" 2 (G v) (E v)
			(:fn . (x86-one-byte-movsxd))
			(:ud  . (*ud-Lock-used*))))
	       (:i64 . ("ARPL"   2 (E w) (G w)
			(:ud  . (*ud-Lock-used*)))))
	      (:prefix-FS
	       (:fn . (:no-instruction)))
	      (:prefix-GS
	       (:fn . (:no-instruction)))
	      (:prefix-OpSize
	       (:fn . (:no-instruction)))
	      (:prefix-AddrSize
	       (:fn . (:no-instruction)))
	      ("PUSH" 1 (I z) :d64
	       (:fn . (x86-push-I))
	       (:ud  . (*ud-Lock-used*)))
	      ("IMUL"  3 (G v) (E v) (I z)
	       (:fn . (x86-imul-Op/En-RMI))
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSH" 1 (I b) :d64
	       (:fn . (x86-push-I))
	       (:ud  . (*ud-Lock-used*)))
	      ("IMUL"  3 (G v) (E v) (I b)
	       (:fn . (x86-imul-Op/En-RMI))
	       (:ud  . (*ud-Lock-used*)))
	      ("INS/INSB" 2 (Y b) (:DX)
	       (:ud  . (*ud-Lock-used*)))
	      ("INS/INSW/INSD" 2 (Y z) (:DX)
	       (:ud  . (*ud-Lock-used*)))
	      ("OUTS/OUTSB" 2 (Y b) (:DX)
	       (:ud  . (*ud-Lock-used*)))
	      ("OUTS/OUTSW/OUTSD" 2 (Y z) (:DX)
	       (:ud  . (*ud-Lock-used*))))

    #| 70 |# (("JO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JNO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JB/NAE/C" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JNB/AE/NC" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JZ/E" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JNZ/NE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JBE/NA" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JNBE/A" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JS" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JNS" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JP/PE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JNP/PO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JL/NGE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JNL/GE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JLE/NG" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("JNLE/G" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . (*ud-Lock-used*))))

    #| 80 |#  ((:Group-1 2 (E b) (I b) :1a)
	       (:Group-1 2 (E v) (I z) :1a)
	       ((:i64 . (:Group-1 2 (E b) (I b) :1a))
		(:o64 . ("#UD" 0
			 (:fn . (x86-illegal-instruction
				 (message .
					  "Opcode 0x82 is illegal in the 64-bit mode!"))))))
	       (:Group-1 2 (E v) (I b) :1a)
	       ("TEST" 2 (E b) (G b)
		(:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
			(operation .  #.*OP-TEST*)))
		(:ud  . (*ud-Lock-used*)))
	       ("TEST" 2 (E v) (G v)
		(:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
			(operation .  #.*OP-TEST*)))
		(:ud  . (*ud-Lock-used*)))
	       ("XCHG" 2 (E b) (G b)
		(:fn . (x86-xchg))
		(:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	       ("XCHG" 2 (E v) (G v)
		(:fn . (x86-xchg))
		(:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	       ("MOV" 2 (E b) (G b)
		(:fn . (x86-mov-Op/En-MR))
		(:ud  . (*ud-Lock-used*)))
	       ("MOV" 2 (E v) (G v)
		(:fn . (x86-mov-Op/En-MR))
		(:ud  . (*ud-Lock-used*)))
	       ("MOV" 2 (G b) (E b)
		(:fn . (x86-mov-Op/En-RM))
		(:ud  . (*ud-Lock-used*)))
	       ("MOV" 2 (G v) (E v)
		(:fn . (x86-mov-Op/En-RM))
		(:ud  . (*ud-Lock-used*)))
	       ;; TODO: For (S w) operands, sensible modr/m.reg values are 0-5
	       ;; because there are 6 segment registers.  Will these
	       ;; instructions #UD when modr/m.reg = 6 or 7? E.g., when modr/m
	       ;; is #x30 or #x38.
	       ("MOV" 2 (E v) (S w)
		(:ud  . (*ud-Lock-used*)))
	       ("LEA" 2 (G v) (M)
		(:fn . (x86-lea))
		(:ud  . (*ud-source-operand-is-a-register*
			 *ud-Lock-used*)))
	       ("MOV" 2 (S w) (E w)
		(:ud  . (`(equal (mrm-reg modr/m) #.*cs*)
			 *ud-Lock-used*)))
	       ;; in Table A-6, Grp 1A only contains POP,
	       ;; so we leave the latter implicit here:
	       (:Group-1A 1 (E v) :1a :d64))

    #| 90 |# (("XCHG" 1 (:r8)
	       (:fn . (x86-xchg))
	       (:ud  . (*ud-Lock-used*)))
	      ("XCHG" 2 (:rCX/r9)  (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . (*ud-Lock-used*)))
	      ("XCHG" 2 (:rDX/r10) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . (*ud-Lock-used*)))
	      ("XCHG" 2 (:rBX/r11) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . (*ud-Lock-used*)))
	      ("XCHG" 2 (:rSP/r12) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . (*ud-Lock-used*)))
	      ("XCHG" 2 (:rBP/r13) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . (*ud-Lock-used*)))
	      ("XCHG" 2 (:rSI/r14) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . (*ud-Lock-used*)))
	      ("XCHG" 2 (:rDI/r15) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . (*ud-Lock-used*)))
	      ("CBW/CWDE/CDQE" 0
	       (:fn . (x86-cbw/cwd/cdqe))
	       (:ud  . (*ud-Lock-used*)))
	      ("CWD/CDQ/CQO" 0
	       (:fn . (x86-cwd/cdq/cqo))
	       (:ud  . (*ud-Lock-used*)))
	      ((:i64 . ("CALL" 1 (A p)
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "far CALL is illegal in the 64-bit mode!"))))))
	      ("FWAIT/WAIT" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("PUSHF/D/Q"  1 (F v) :d64
	       (:fn . (x86-pushf))
	       (:ud  . (*ud-Lock-used*)))
	      ("POPF/D/Q"   1 (F v) :d64
	       (:fn . (x86-popf))
	       (:ud  . (*ud-Lock-used*)))
	      ("SAHF" 0
	       (:fn . (x86-sahf))
	       (:ud  . (*ud-Lock-used*
			(:o64 .
			      (`(equal
				 ;; CPUID.80000001H.ECX[0]
				 (cpuid-flag
				  :value #ux_8000_0001
				  :ecx t
				  :bit 0)
				 0))))))
	      ("LAHF" 0
	       (:fn . (x86-lahf))
	       (:ud  . (*ud-Lock-used*
			(:o64 .
			      (`(equal
				 ;; CPUID.80000001H:ECX.LAHF-SAHF[bit 0]
				 (cpuid-flag
				  :value #ux_8000_0001
				  :ecx t
				  :bit 0)
				 0)))))))

    #| a0 |# (("MOV" 2 (:AL) (O b)
	       (:fn . (x86-mov-Op/En-FD))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2 (:rAX) (O v)
	       (:fn . (x86-mov-Op/En-FD))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2 (O b) (:AL)
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2 (O v) (:rAX)
	       (:ud  . (*ud-Lock-used*)))
	      ("MOVS/B" 2 (Y b) (X b)
	       (:fn . (x86-movs))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOVS/W/D/Q" 2 (Y v) (X v)
	       (:fn . (x86-movs))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMPS/B"   2 (X b) (Y b)
	       (:fn . (x86-cmps)))
	      ("CMPS/W/D" 2 (X v) (Y v)
	       (:fn . (x86-cmps))
	       (:ud  . (*ud-Lock-used*)))
	      ("TEST" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-TEST*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("TEST" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-TEST*)))
	       (:ud  . (*ud-Lock-used*)))
	      ("STOS/B" 2 (Y b) (:AL)
	       (:fn . (x86-stos))
	       (:ud  . (*ud-Lock-used*)))
	      ("STOS/W/D/Q" 2 (Y v) (:rAX)
	       (:fn . (x86-stos))
	       (:ud  . (*ud-Lock-used*)))
	      ("LODS/B" 2 (:AL) (X b)
	       (:ud  . (*ud-Lock-used*)))
	      ("LODS/W/D/Q" 2 (:rAX) (X v)
	       (:ud  . (*ud-Lock-used*)))
	      ("SCAS/B" 2 (:AL) (Y b)
	       (:ud  . (*ud-Lock-used*)))
	      ("SCAS/W/D/Q" 2 (:rAX) (Y v)
	       (:ud  . (*ud-Lock-used*))))

    #| b0 |# (("MOV" 2  (:AL/r8L)  (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:CL/r9L)  (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:DL/r10L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:BL/r11L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:AH/r12L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:CH/r13L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:DH/r14L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:BH/r15L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:rAX/r8)  (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:rCX/r9)  (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:rDX/r10) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:rBX/r11) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:rSP/r12) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:rBP/r13) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:rSI/r14) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOV" 2  (:rDI/r15) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . (*ud-Lock-used*))))

    #| c0 |# ((:Group-2 2 (E b) (I b) :1a)
	      (:Group-2 2 (E v) (I b) :1a)
	      ("RET" 1 (I w) :f64
	       (:fn . (x86-ret))
	       ;; No UD Exception
	       )
	      ("RET" 0 :f64
	       (:fn . (x86-ret))
	       ;; No UD Exception
	       )
	      ;; C4 and C5 are first bytes of the vex prefixes, both
	      ;; in 32-bit and IA-32e modes.  However, in the 32-bit
	      ;; and compatibility modes, the second byte determines
	      ;; whether the instruction is LES/LDS or a VEX
	      ;; instruction.  We use :o64 here because we're sure
	      ;; that an "opcode" of C4 and C5 in the 64-bit mode will
	      ;; not have a modr/m corresponding to it --- basically,
	      ;; we shouldn't be looking up modr/m info. for these
	      ;; opcodes in the 64-bit mode.
	      ((:o64 . (:vex3-byte0 (:fn . (:no-instruction))))
	       (:i64 . ("LES" 2 (G z) (M p)
			(:ud  . (*ud-Lock-used*
				 *ud-source-operand-is-a-register*)))))
	      ((:o64 . (:vex2-byte0 (:fn . (:no-instruction))))
	       (:i64 . ("LDS" 2 (G z) (M p)
			(:ud  . (*ud-Lock-used*
				 *ud-source-operand-is-a-register*)))))
	      (:Group-11 2 (E b) (I b) :1a)
	      (:Group-11 2 (E v) (I z) :1a)
	      ("ENTER" 2 (I w) (I b)
	       (:ud  . (*ud-Lock-used*)))
	      ("LEAVE" 0 :d64
	       (:fn . (x86-leave))
	       (:ud  . (*ud-Lock-used*)))
	      ("RET" 1 (I w)
	       ;; No UD Exception
	       )
	      ("RET" 0
	       ;; No UD Exception
	       )
	      ("INT3" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("INT" 1 (I b)
	       (:ud  . (*ud-Lock-used*)))
	      ((:i64 . ("INTO" 0
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "INTO is illegal in the 64-bit mode!"))))))
	      ("IRET/D/Q" 0
	       (:ud  . (*ud-Lock-used*))))

    #| d0 |# ((:Group-2 2 (E b) (1) :1a)
	      (:Group-2 2 (E v) (1) :1a)
	      (:Group-2 2 (E b) (:CL) :1a)
	      (:Group-2 2 (E v) (:CL) :1a)
	      ((:i64 . ("AAM" 1 (I b)
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "AAM is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("AAD" 1 (I b)
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "AAD is illegal in the 64-bit mode!"))))))
	      (:none
	       (:fn . (:no-instruction)))
	      ("XLAT/XLATB" 0
	       (:ud  . (*ud-Lock-used*)))
	      (:esc) ;; Escape to co-processor instruction set
	      (:esc) ;; Escape to co-processor instruction set
	      (:esc) ;; Escape to co-processor instruction set
	      (:esc) ;; Escape to co-processor instruction set
	      (:esc) ;; Escape to co-processor instruction set
	      (:esc) ;; Escape to co-processor instruction set
	      (:esc) ;; Escape to co-processor instruction set
	      (:esc) ;; Escape to co-processor instruction set
	      )

    #| e0 |# (("LOOPNE/LOOPNZ" 1 (J b) :f64
	       (:fn . (x86-loop))
	       (:ud  . (*ud-Lock-used*)))
	      ("LOOPE/LOOPZ" 1 (J b) :f64
	       (:fn . (x86-loop))
	       (:ud  . (*ud-Lock-used*)))
	      ("LOOP" 1 (J b) :f64
	       (:fn . (x86-loop))
	       (:ud  . (*ud-Lock-used*)))
	      ("JrCXZ" 1 (J b) :f64
	       (:fn . (x86-jrcxz))
	       (:ud  . (*ud-Lock-used*)))
	      ("IN" 2 (:AL) (I b)
	       (:ud  . (*ud-Lock-used*)))
	      ("IN" 2 (:eAX) (I b)
	       (:ud  . (*ud-Lock-used*)))
	      ("OUT" 2 (I b) (:AL)
	       (:ud  . (*ud-Lock-used*)))
	      ("OUT" 2 (I b) (:eAX)
	       (:ud  . (*ud-Lock-used*)))
	      ("CALL" 1 (J z) :f64
	       (:fn . (x86-call-E8-Op/En-M))
	       (:ud  . (*ud-Lock-used*)))
	      ("JMP"  1 (J z) :f64
	       (:fn . (x86-near-jmp-Op/En-D))
	       (:ud  . (*ud-Lock-used*)))
	      ((:i64 . ("JMP"  1 (A p)
			(:ud  . (*ud-Lock-used*))))
	       (:o64 . ("#UD"  0
			(:fn . (x86-illegal-instruction
				(message .
					 "JMP is illegal in the 64-bit mode!"))))))
	      ("JMP"  1 (J b) :f64
	       (:fn . (x86-near-jmp-Op/En-D))
	       (:ud  . (*ud-Lock-used*)))
	      ("IN" 2  (:AL) (:DX)
	       (:ud  . (*ud-Lock-used*)))
	      ("IN" 2  (:eAX) (:DX)
	       (:ud  . (*ud-Lock-used*)))
	      ("OUT" 2 (:DX) (:AL)
	       (:ud  . (*ud-Lock-used*)))
	      ("OUT" 2 (:DX) (:eAX)
	       (:ud  . (*ud-Lock-used*))))

    #| f0 |# ((:prefix-Lock
	       (:fn . (:no-instruction)))
	      ("INT1" 0
	       (:ud  . (*ud-Lock-used*)))
	      (:prefix-REPNE
	       (:fn . (:no-instruction)))
	      (:prefix-REP/REPE
	       (:fn . (:no-instruction)))
	      ("HLT" 0
	       (:fn . (x86-hlt))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std))
	       (:ud  . (*ud-Lock-used*)))
	      (:Group-3 1 (E b) :1a)
	      (:Group-3 1 (E v) :1a)
	      ("CLC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std))
	       (:ud  . (*ud-Lock-used*)))
	      ("STC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std))
	       (:ud  . (*ud-Lock-used*)))
	      ("CLI" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("STI" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("CLD" 0
	       (:fn . (x86-cmc/clc/stc/cld/std)))
	      ("STD" 0
	       (:fn . (x86-cmc/clc/stc/cld/std))
	       (:ud  . (*ud-Lock-used*)))
	      (:Group-4 1 (E b) :1a)
	      (:Group-5 1 (E v) :1a))

    #|       -------------------------------        |#
    ))


(defconst *two-byte-opcode-map-lst*
  ;; First byte is 0x0F.
  ;; Source: Intel Volume 2, Table A-3.

  '(
    #|       -------------------------------        |#

    #| 00 |# ((:Group-6 0 :1a)
	      (:Group-7 0 :1a)
	      ("LAR" 2 (G v) (E w)
	       (:ud  . (*ud-Lock-used*)))
	      ("LSL" 2 (G v) (E w)
	       (:ud  . (*ud-Lock-used*)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:o64 . ("SYSCALL" 0
			(:fn . (x86-syscall-both-views))
			(:ud  . (*ud-Lock-used*
				 `(equal
				   (ia32_efer-slice
				    :ia32_efer-sce
				    (n12 (msri *ia32_efer-idx* x86)))
				   0)))))
	       (:i64 . (:none
			(:fn . (:no-instruction)))))
	      ("CLTS" 0
	       (:ud  . (*ud-Lock-used*)))
	      ((:o64 . ("SYSRET" 0
			(:fn . (x86-sysret))
			(:ud  . (*ud-Lock-used*
				 `(equal
				   (ia32_efer-slice
				    :ia32_efer-sce
				    (n12 (msri *ia32_efer-idx* x86)))
				   0)))))
	       (:i64 . (:none
			(:fn . (:no-instruction)))))
    #| 08 |#  ("INVD" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("WBINVD" 0
	       (:ud  . (*ud-Lock-used*)))
	      (:none
	       (:fn . (:no-instruction)))
	      ("UD2" 0 :1b
	       (:fn . (x86-illegal-instruction
		       (message . "UD2 encountered!")))
	       (:ud  . (t)))
	      (:none
	       (:fn . (:no-instruction)))
	      ("prefetchw(/1)" 1 (E v)
	       (:ud  . (*ud-Lock-used*)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 10 |# (((:no-prefix . ("VMOVUPS"    2 (V ps) (W ps)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-RM))))
	       (:66        . ("VMOVUPD"    2 (V pd) (W pd)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-RM))))
	       (:F3        . ("VMOVSS"     3 (V x)  (H x)  (W ss)
			      (:fn . (x86-movss/movsd-Op/En-RM
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VMOVSD"     3 (V x)  (H x)  (W sd)
			      (:fn . (x86-movss/movsd-Op/En-RM
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VMOVUPS"    2 (W ps) (V ps)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-MR))))
	       (:66        . ("VMOVUPD"    2 (W pd) (V pd)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-MR))))
	       (:F3        . ("VMOVSS"     3 (W ss) (H x)  (V ss)
			      (:fn . (x86-movss/movsd-Op/En-MR
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VMOVSD"     3 (W sd) (H x)  (V sd)
			      (:fn . (x86-movss/movsd-Op/En-MR
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . (:ALT
			      (("VMOVLPS"    3 (V q)  (H q)  (M q))
			       ("VMOVHLPS"   3 (V q)  (H q)  (U q)))
			      (:fn . (x86-movlps/movlpd-Op/En-RM))))
	       (:66        . ("VMOVLPD"    3 (V q)  (H q)  (M q)
			      (:fn . (x86-movlps/movlpd-Op/En-RM))))
	       (:F3        . ("VMOVSLDUP"  2 (V x)  (W x)
			      (:fn . (x86-movlps/movlpd-Op/En-RM))))
	       (:F2        . ("VMOVDDUP"   2 (V x)  (W x)
			      (:fn . (x86-movlps/movlpd-Op/En-RM)))))

	      ((:no-prefix . ("VMOVLPS"    2 (M q)  (V q)
			      (:fn . (x86-movlps/movlpd-Op/En-MR))))
	       (:66        . ("VMOVLPD"    2 (M q)  (V q)
			      (:fn . (x86-movlps/movlpd-Op/En-MR)))))

	      ((:no-prefix . ("VUNPCKLPS"  3 (V x)  (H x)  (W x)
			      (:fn . (x86-unpck?ps-Op/En-RM
				      (high/low . #.*LOW-PACK*)))))
	       (:66        . ("VUNPCKLPD"  3 (V x)  (H x)  (W x)
			      (:fn . (x86-unpck?pd-Op/En-RM
				      (high/low . #.*LOW-PACK*))))))

	      ((:no-prefix . ("VUNPCKHPS"  3 (V x)  (H x)  (W x)
			      (:fn . (x86-unpck?ps-Op/En-RM
				      (high/low . #.*HIGH-PACK*)))))
	       (:66        . ("VUNPCKHPD"  3 (V x)  (H x)  (W x)
			      (:fn . (x86-unpck?pd-Op/En-RM
				      (high/low . #.*HIGH-PACK*))))))

	      ((:no-prefix . (:ALT
			      (("VMOVHPS"    3 (V dq)  (H q)  (M q) :v1)
			       ("VMOVLHPS"   3 (V dq)  (H q)  (U q)))
			      (:fn . (x86-movhps/movhpd-Op/En-RM))))
	       (:66        . ("VMOVHPD"    3 (V dq)  (H q)  (M q) :v1
			      (:fn . (x86-movhps/movhpd-Op/En-RM))))
	       (:F3        . ("VMOVSHDUP"  2 (V x)   (W x))))

	      ((:no-prefix . ("VMOVHPS"    2 (M q)  (V q) :v1
			      (:fn . (x86-movhps/movhpd-Op/En-MR))))
	       (:66        . ("VMOVHPD"    2 (M q)  (V q) :v1
			      (:fn . (x86-movhps/movhpd-Op/En-MR)))))

    #| 18 |#  (:Group-16 0 :1a)

	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ("NOP" 1 (E v)
	       (:fn . (x86-two-byte-nop))
	       (:ud  . (*ud-Lock-used*))))

    #| 20 |# (("MOV" 2 (R d) (C d)
	       (:fn . (x86-mov-control-regs-Op/En-MR))
	       (:ud  . (*ud-Lock-used*
			`(let ((reg (mrm-reg modr/m)))
			   (if (and (equal proc-mode #.*64-bit-mode*)
				    (logbitp #.*r* rex-byte))
			       (not (equal reg 0))
			     (or (equal reg #.*cr1*)
				 (equal reg #.*cr5*)
				 (equal reg #.*cr6*)
				 (equal reg #.*cr7*)))))))
	      ("MOV" 2 (R d) (D d)
	       (:ud  . (*ud-Lock-used*
			`(and (equal (cr4-slice :cr4-de (ctri #.*cr4* x86)) 1)
			      (or (equal (mrm-reg modr/m) #.*dr4*)
				  (equal (mrm-reg modr/m) #.*dr5*))))))
	      ("MOV" 2 (C d) (R d)
	       (:ud  . (*ud-Lock-used*
			`(let ((reg (mrm-reg modr/m)))
			   (if (and (equal proc-mode #.*64-bit-mode*)
				    (logbitp #.*r* rex-byte))
			       (not (equal reg 0))
			     (or (equal reg #.*cr1*)
				 (equal reg #.*cr5*)
				 (equal reg #.*cr6*)
				 (equal reg #.*cr7*)))))))
	      ("MOV" 2 (D d) (R d)
	       (:ud  . (*ud-Lock-used*
			`(and (equal (cr4-slice :cr4-de (ctri #.*cr4* x86)) 1)
			      (or (equal (mrm-reg modr/m) #.*dr4*)
				  (equal (mrm-reg modr/m) #.*dr5*))))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))

    #| 28 |#  ((:no-prefix . ("VMOVAPS"    2 (V ps)  (W ps)
			      (:fn . (x86-movaps/movapd-Op/En-RM))))
	       (:66        . ("VMOVAPD"    2 (V pd)  (W pd)
			      (:fn . (x86-movaps/movapd-Op/En-RM)))))

	      ((:no-prefix . ("VMOVAPS"    2 (W ps)  (V ps)
			      (:fn . (x86-movaps/movapd-Op/En-MR))))
	       (:66        . ("VMOVAPD"    2 (W pd)  (V pd)
			      (:fn . (x86-movaps/movapd-Op/En-MR)))))

	      ((:no-prefix . ("CVTPI2PS"   2 (V ps)  (Q pi)))
	       (:66        . ("CVTPI2PD"   2 (V pd)  (Q pi)))
	       (:F3        . ("VCVTSI2SS"  3 (V ss)  (H ss)  (E y)
			      (:fn . (x86-cvtsi2s?-Op/En-RM
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VCVTSI2SD"  3 (V sd)  (H sd)  (E y)
			      (:fn . (x86-cvtsi2s?-Op/En-RM
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VMOVNTPS"   2 (M ps)  (V ps)))
	       (:66        . ("VMOVNTPD"   2 (M pd)  (V pd))))

	      ((:no-prefix . ("CVTTPS2PI"  2 (P pi)  (W ps)))
	       (:66        . ("CVTTPD2PI"  2 (P pi)  (W pd)))
	       (:F3        . ("VCVTTSS2SI" 2 (G y)   (W ss)
			      (:fn . (x86-cvts?2si/cvtts?2si-Op/En-RM
				      (sp/dp . #.*OP-SP*)
				      (trunc . t)))))
	       (:F2        . ("VCVTTSD2SI" 2 (G y)   (W sd)
			      (:fn . (x86-cvts?2si/cvtts?2si-Op/En-RM
				      (sp/dp . #.*OP-DP*)
				      (trunc . t))))))

	      ((:no-prefix . ("CVTPS2PI"   2 (P pi)  (W ps)))
	       (:66        . ("CVTPD2PI"   2 (Q pi)  (W pd)))
	       (:F3        . ("VCVTSS2SI"  2 (G y)   (W ss)
			      (:fn . (x86-cvts?2si/cvtts?2si-Op/En-RM
				      (sp/dp . #.*OP-SP*)
				      (trunc . nil)))))
	       (:F2        . ("VCVTSD2SI"  2 (G y)   (W sd)
			      (:fn . (x86-cvts?2si/cvtts?2si-Op/En-RM
				      (sp/dp . #.*OP-DP*)
				      (trunc . nil))))))

	      ((:no-prefix . ("VUCOMISS"   2 (V ss)  (W ss)
			      (:fn . (x86-comis?/ucomis?-Op/En-RM
				      (operation . #.*OP-UCOMI*)
				      (sp/dp . #.*OP-SP*)))))
	       (:66        . ("VUCOMISD"   2 (V sd)  (W sd)
			      (:fn . (x86-comis?/ucomis?-Op/En-RM
				      (operation . #.*OP-UCOMI*)
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VCOMISS"    2 (V ss)  (W ss)
			      (:fn . (x86-comis?/ucomis?-Op/En-RM
				      (operation . #.*OP-UCOMI*)
				      (sp/dp . #.*OP-SP*)))))
	       (:66        . ("VCOMISD"    2 (V sd)  (W sd)
			      (:fn . (x86-comis?/ucomis?-Op/En-RM
				      (operation . #.*OP-UCOMI*)
				      (sp/dp . #.*OP-DP*)))))))

    #| 30 |# (("WRMSR" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("RDTSC" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("RDMSR" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("RDPMC" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("SYSENTER" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("SYSEXIT" 0
	       (:ud  . (*ud-Lock-used*)))
	      (:none
	       (:fn . (:no-instruction)))
	      ("GETSEC" 0)
    #| 38 |#  (:3-byte-escape
	       (:fn . (three-byte-opcode-decode-and-execute
		       (second-escape-byte . opcode))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:3-byte-escape
	       (:fn . (three-byte-opcode-decode-and-execute
		       (second-escape-byte . opcode))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 40 |# (("CMOVO" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVNO" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVB/C/NAE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVAE/NB/NC" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVE/Z" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVNE/NZ" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVBE/NA" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVA/NBE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
    #| 48 |#  ("CMOVS" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVNS" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVP/PE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVNP/PO" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVL/NGE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVNL/GE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVLE/NG" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("CMOVNLE/G" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . (*ud-Lock-used*))))

    #| 50 |# (((:no-prefix . ("VMOVMSKPS"  2 (G y)  (U ps)))
	       (:66        . ("VMOVMSKPD"  2 (G y)  (U pd))))

	      ((:no-prefix . ("VSQRTPS"    2 (V ps)  (W ps)
			      (:fn . (x86-sqrtps-Op/En-RM))))
	       (:66        . ("VSQRTPD"    2 (V pd)  (W pd)
			      (:fn . (x86-sqrtpd-Op/En-RM))))
	       (:F3        . ("VSQRTSS"    3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-sqrts?-Op/En-RM
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VSQRTSD"    3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-sqrts?-Op/En-RM
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VRSQRTPS"   2 (V ps)  (W ps)))
	       (:F3        . ("VRSQRTSS"   3 (V ss)  (H ss)  (W ss))))

	      ((:no-prefix . ("VRCPPS"     2 (V ps)  (W ps)))
	       (:F3        . ("VRCPSS"     3 (V ss)  (H ss)  (W ss))))

	      ((:no-prefix . ("VANDPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-AND*)))))
	       (:66        . ("VANDPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-AND*))))))

	      ((:no-prefix . ("VANDNPS"    3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-ANDN*)))))
	       (:66        . ("VANDNPD"    3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-ANDN*))))))

	      ((:no-prefix . ("VORPS"      3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-OR*)))))
	       (:66        . ("VORPD"      3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-OR*))))))

	      ((:no-prefix . ("VXORPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-XOR*)))))
	       (:66        . ("VXORPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-XOR*))))))

   #| 58 |#   ((:no-prefix . ("VADDPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-ADD*)))))
	       (:66        . ("VADDPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-ADD*)))))
	       (:F3        . ("VADDSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-ADD*)
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VADDSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-ADD*)
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VMULPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-MUL*)))))
	       (:66        . ("VMULPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-MUL*)))))
	       (:F3        . ("VMULSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MUL*)
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VMULSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MUL*)
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VCVTPS2PD"  2 (V pd)  (W ps)
			      (:fn . (x86-cvtps2pd-Op/En-RM))))
	       (:66        . ("VCVTPD2PS"  2 (V ps)  (W pd)
			      (:fn . (x86-cvtpd2ps-Op/En-RM))))
	       (:F3        . ("VCVTSS2SD"  3 (V sd)  (H x)   (W ss)
			      (:fn . (x86-cvts?2s?-Op/En-RM
				      (dp-to-sp . #.*SP-TO-DP*)))))
	       (:F2        . ("VCVTSD2SS"  3 (V ss)  (H x)   (W sd)
			      (:fn . (x86-cvts?2s?-Op/En-RM
				      (dp-to-sp . #.*DP-TO-SP*))))))

	      ((:no-prefix . ("VCVTDQ2PS"  2 (V ps)  (W dq)))
	       (:66        . ("VCVTPS2DQ"  2 (V dq)  (W ps)))
	       (:F3        . ("VCVTTPS2DQ" 2 (V dq)  (W ps))))

	      ((:no-prefix . ("VSUBPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-SUB*)))))
	       (:66        . ("VSUBPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-SUB*)))))
	       (:F3        . ("VSUBSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-SUB*)
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VSUBSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-SUB*)
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VMINPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-MIN*)))))
	       (:66        . ("VMINPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-MIN*)))))
	       (:F3        . ("VMINSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MIN*)
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VMINSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MIN*)
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VDIVPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-DIV*)))))
	       (:66        . ("VDIVPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-DIV*)))))
	       (:F3        . ("VDIVSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-DIV*)
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VDIVSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-DIV*)
				      (sp/dp . #.*OP-DP*))))))

	      ((:no-prefix . ("VMAXPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-MAX*)))))
	       (:66        . ("VMAXPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-MAX*)))))
	       (:F3        . ("VMAXSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MAX*)
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VMAXSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MAX*)
				      (sp/dp . #.*OP-DP*)))))))

    #| 60 |# (((:no-prefix . ("PUNPCKLBW"  2 (P q)  (Q d)))
	       (:66        . ("VPUNPCKLBW" 3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PUNPCKLWD"  2 (P q)  (Q d)))
	       (:66        . ("VPUNPCKLWD" 3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PUNPCKLDQ"  2 (P q)  (Q d)))
	       (:66        . ("VPUNPCKLDQ" 3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PACKSSWB"   2 (P q)  (Q q)))
	       (:66        . ("VPACKSSWB"  3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PCMPGTB"    2 (P q)  (Q q)))
	       (:66        . ("VPCMPGTB"   3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PCMPGTW"    2 (P q)  (Q q)))
	       (:66        . ("VPCMPGTW"   3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PCMPGTD"    2 (P q)  (Q q)))
	       (:66        . ("VPCMPGTD"   3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PACKUSWB"   2 (P q)  (Q q)))
	       (:66        . ("VPACKUSWB"  3 (V x)  (H x)  (W x))))

    #| 68 |#  ((:no-prefix . ("PUNPCKHBW"  2 (P q)  (Q d)))
	       (:66        . ("VPUNPCKHBW" 3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PUNPCKHWD"  2 (P q)  (Q d)))
	       (:66        . ("VPUNPCKHWD" 3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PUNPCKHDQ"  2 (P q)  (Q d)))
	       (:66        . ("VPUNPCKHDQ" 3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("PACKSSDW"  2 (P q)  (Q d)))
	       (:66        . ("VPACKSSDW" 3 (V x)  (H x)  (W x))))

	      ((:66        . ("VPUNPCKLQDQ" 3 (V x)  (H x)  (W x))))

	      ((:66        . ("VPUNPCKHQDQ" 3 (V x)  (H x)  (W x))))

	      ((:no-prefix . ("MOVD/Q"      2 (P d)  (E y)))
	       (:66        . ("VMOVD/Q"     2 (V y)  (E y))))

	      ((:no-prefix . ("MOVQ"        2 (P q)  (Q q)))
	       (:66        . ("VMOVDQA"     2 (V x)  (W x)))
	       (:F3        . ("VMOVDQU"     2 (V x)  (W x)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-RM))))))

    #| 70 |# (((:no-prefix . ("PSHUFW"      3 (P q)   (Q q)   (I b)))
	       (:66        . ("VPSHUFD"     3 (V x)   (W x)   (I b)))
	       (:F3        . ("VPSHUFHW"    3 (V x)   (W x)   (I b)))
	       (:F2        . ("VPSHUFLW"    3 (V x)   (W x)   (I b))))

	      (:Group-12 0 :1a)

	      (:Group-13 0 :1a)

	      (:Group-14 0 :1a)

	      ((:no-prefix . ("PCMPEQB"     2 (P q)   (Q q)))
	       (:66        . ("VPCMPEQB"    3 (V x)   (H x)  (W x)
			      (:fn . (x86-pcmpeqb-Op/En-RM)))))

	      ((:no-prefix . ("PCMPEQW"     2 (P q)   (Q q)))
	       (:66        . ("VPCMPEQW"    3 (V x)   (H x)  (W x))))

	      ((:no-prefix . ("PCMPEQD"     2 (P q)   (Q q)))
	       (:66        . ("VPCMPEQD"    3 (V x)   (H x)  (W x))))

	      ((:no-prefix . ("EMMS"        0))
	       (:v         . ("VZEROUPPER/VZEROALL"  0)))

    #| 78 |#  ("VMREAD" 2  (E y)  (G y))

	      ("VMWRITE" 2  (E y)  (G y))

	      (:none
	       (:fn . (:no-instruction)))

	      (:none
	       (:fn . (:no-instruction)))

	      ((:66        . ("VHADDPD"     3 (V pd)   (H pd)  (W pd)))
	       (:F2        . ("VHADDPS"     3 (V ps)   (H ps)  (W ps))))

	      ((:66        . ("VHSUBPD"     3 (V pd)   (H pd)  (W pd)))
	       (:F2        . ("VHSUBPS"     3 (V ps)   (H ps)  (W ps))))

	      ((:no-prefix . ("MOVD/Q"      2 (E y)    (P d)))
	       (:66        . ("VMOVD/Q"     2 (E y)    (V y)))
	       (:F3        . ("VMOVQ"       2 (V q)    (W q))))

	      ((:no-prefix . ("MOVQ"        2 (Q q)    (P q)))
	       (:66        . ("VMOVDQA"     2 (W x)    (V x)))
	       (:F3        . ("VMOVQU"      2 (W x)    (V x)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-MR))))))

    #| 80 |#  (("JO" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JNO" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JB/NAE/C" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JNB/AE/NC" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JZ/E" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JNZ/NE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JBE/NA" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JNBE/A" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
    #| 88 |#   ("JS" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JNS" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JP/PE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JNP/PO" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JL/NGE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JNL/GE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JLE/NG" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*)))
	       ("JNLE/G" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . (*ud-Lock-used*))))

    #| 90 |# (("SETO" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETNO" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETB/NAE/C" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETNB/AE/NC" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETZ/E" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETNZ/NE" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETBE/NA" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETNBE/A" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
    #| 98 |#  ("SETS" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETNS" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETP/PE" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETNP/PO" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETL/NGE" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETNL/GE" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETLE/NG" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*)))
	      ("SETNLE/G" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . (*ud-Lock-used*))))

    #| a0 |# (("PUSH"  1 (:FS) :d64
	       (:fn . (x86-push-segment-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"   1 (:FS) :d64
	       (:ud  . (*ud-Lock-used*)))
	      ("CPUID" 0
	       (:ud  . (*ud-Lock-used*)))
	      ("BT" 2 (E v) (G v)
	       (:fn . (x86-bt-0f-a3))
	       (:ud  . (*ud-Lock-used*)))
	      ("SHLD" 3 (E v) (G v) (I b)
	       (:ud  . (*ud-Lock-used*)))
	      ("SHLD" 3 (E v) (G v) (:CL)
	       (:ud  . (*ud-Lock-used*)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| a8 |#  ("PUSH"  1 (:GS) :d64
	       (:fn . (x86-push-segment-register))
	       (:ud  . (*ud-Lock-used*)))
	      ("POP"   1 (:GS) :d64
	       (:ud  . (*ud-Lock-used*)))
	      ("RSM" 0)
	      ("BTS" 2 (E v) (G v)
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("SHRD" 3 (E v) (G v) (I b)
	       (:ud  . (*ud-Lock-used*)))
	      ("SHRD" 3 (E v) (G v) (:CL)
	       (:ud  . (*ud-Lock-used*)))
	      (:Group-15 0 :1a :1c)
	      ("IMUL" 2 (G v) (E v)
	       (:fn . (x86-imul-Op/En-RM))
	       (:ud  . (*ud-Lock-used*))))

    #| b0 |# (("CMPXCHG" 2 (E b) (G b)
	       (:fn . (x86-cmpxchg))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("CMPXCHG" 2 (E v) (G v)
	       (:fn . (x86-cmpxchg))
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("LSS" 2 (G v) (M p)
	       (:ud  . (*ud-Lock-used*
			*ud-source-operand-is-a-register*)))
	      ("BTR" 2 (E v) (G v)
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("LFS" 2 (G v) (M p)
	       (:ud  . (*ud-Lock-used*
			*ud-source-operand-is-a-register*)))
	      ("LGS" 2 (G v) (M p)
	       (:ud  . (*ud-Lock-used*
			*ud-source-operand-is-a-register*)))
	      ("MOVZX" 2 (G v) (E b)
	       (:fn . (x86-movzx))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOVZX" 2 (G v) (E w)
	       (:fn . (x86-movzx))
	       (:ud  . (*ud-Lock-used*)))
    #| b8 |#  ((:no-prefix . ("JMPE"   0
			      ;; Reserved for emulator on IPF (Itanium
			      ;; Processor Family).
			      ))
	       (:F3        . ("POPCNT" 2 (G v) (E v)
			      (:ud  . (*ud-Lock-used*
				       `(equal
					 ;; CPUID.01H:ECX.POPCNT [Bit 23]
					 (cpuid-flag
					  :value #ux_01
					  :ecx t
					  :bit 23)
					 0))))))
	      (:Group-10 0 :1a :1b)
	      (:Group-8 2 (E v) (I b) :1a)
	      ("BTC" 2 (E v) (G v)
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ((:no-prefix . ("BSF"   2 (G v) (E v)
			      (:fn . (x86-bsf-Op/En-RM))
			      (:ud  . (*ud-Lock-used*))))
	       (:F3        . ("TZCNT" 2 (G v) (E v))))
	      ((:no-prefix . ("BSR"   2 (G v) (E v)
			      (:ud  . (*ud-Lock-used*))))
	       (:F3        . ("LZCNT" 2 (G v) (E v)
			      (:ud  . (*ud-Lock-used*)))))
	      ("MOVSX" 2 (G v) (E b)
	       (:fn . (x86-two-byte-movsxd))
	       (:ud  . (*ud-Lock-used*)))
	      ("MOVSX" 2 (G v) (E w)
	       (:fn . (x86-two-byte-movsxd))
	       (:ud  . (*ud-Lock-used*))))

    #| c0 |# (("XADD"     2 (E b)  (G b)
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ("XADD"     2 (E v)  (G v)
	       (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*)))
	      ((:no-prefix . ("VCMPPS"     4 (V ps)  (H ps)  (W ps)  (I b)
			      (:fn . (x86-cmpps-Op/En-RMI))))
	       (:66        . ("VCMPPD"     4 (V pd)  (H pd)  (W pd)  (I b)
			      (:fn . (x86-cmppd-Op/En-RMI))))
	       (:F3        . ("VCMPSS"     4 (V ss)  (H ss)  (W ss)  (I b)
			      (:fn . (x86-cmpss/cmpsd-Op/En-RMI
				      (sp/dp . #.*OP-SP*)))))
	       (:F2        . ("VCMPSD"     4 (V sd)  (H sd)  (W sd)  (I b)
			      (:fn . (x86-cmpss/cmpsd-Op/En-RMI
				      (sp/dp . #.*OP-DP*))))))

	      ("MOVNTI"     2 (M y)   (G y)
	       (:ud  . (*ud-Lock-used*
			`(equal
			  ;; CPUID.01H:EDX.SSE2[bit 26]
			  (cpuid-flag
			   :value #ux_01
			   :edx t
			   :bit 26)
			  0))))

	      ((:no-prefix . ("PINSRW"     3 (P q)   (R y)  (I b)))
	       (:no-prefix . ("PINSRW"     3 (P q)   (M w)  (I b)))
	       (:66        . ("VPINSRW"    4 (V dq)  (H dq) (R y)  (I b)))
	       (:66        . ("VPINSRW"    4 (V dq)  (H dq) (M w)  (I b))))

	      ((:no-prefix . ("PEXTRW"     3 (G d)   (N q)  (I b)))
	       (:66        . ("VPEXTRW"    3 (G d)   (U dq) (I b))))

	      ((:no-prefix . ("VSHUFPS"    4 (V ps)  (H ps)  (W ps)  (I b)
			      (:fn . (x86-shufps-Op/En-RMI))))
	       (:66        . ("VSHUFPD"    4 (V pd)  (H pd)  (W pd)  (I b)
			      (:fn . (x86-shufpd-Op/En-RMI)))))

	      (:Group-9 0 :1a)

    #| c8 |#  ("BSWAP" 1 (:RAX/EAX/R8/R8D)
	       (:ud  . (*ud-Lock-used*)))
	      ("BSWAP" 1 (:RCX/ECX/R9/R9D)
	       (:ud  . (*ud-Lock-used*)))
	      ("BSWAP" 1 (:RDX/EDX/R10/R10D)
	       (:ud  . (*ud-Lock-used*)))
	      ("BSWAP" 1 (:RBX/EBX/R11/R11D)
	       (:ud  . (*ud-Lock-used*)))
	      ("BSWAP" 1 (:RSP/ESP/R12/R12D)
	       (:ud  . (*ud-Lock-used*)))
	      ("BSWAP" 1 (:RBP/EBP/R13/R13D)
	       (:ud  . (*ud-Lock-used*)))
	      ("BSWAP" 1 (:RSI/ESI/R14/R14D)
	       (:ud  . (*ud-Lock-used*)))
	      ("BSWAP" 1 (:RDI/EDI/R15/R15D)
	       (:ud  . (*ud-Lock-used*))))

  #| d0 |# (((:66        . ("VADDSUBPD"  3 (V pd)  (H pd)  (W pd)))
	     (:F2        . ("VADDSUBPS"  3 (V ps)  (H ps)  (W ps))))

	    ((:no-prefix . ("PSRLW"      2 (P q)   (Q q)))
	     (:66        . ("VPSRLW"     3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PSRLD"      2 (P q)   (Q q)))
	     (:66        . ("VPSRLD"     3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PSRLQ"      2 (P q)   (Q q)))
	     (:66        . ("VPSRLQ"     3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PADDQ"      2 (P q)   (Q q)))
	     (:66        . ("VADDQ"      3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PMULLW"     2 (P q)   (Q q)))
	     (:66        . ("VPMULLW"    3 (V x)   (H x)  (W x))))

	    ((:66        . ("VMOVQ"     2 (W q)   (V q)))
	     (:F3        . ("MOVQ2DQ"   2 (V dq)  (N q)))
	     (:F2        . ("MOVDQ2Q"   2 (P q)   (U q))))

	    ((:no-prefix . ("PMOVMSKB"  2 (G d)   (N q)))
	     (:66        . ("VPMOVMSKB" 2 (G d)   (U x)
			    (:fn . (x86-pmovmskb-Op/En-RM)))))

  #| d8 |#  ((:no-prefix . ("PSUBUSB"   2 (P q)   (Q q)))
	     (:66        . ("VPSUBUSB"  3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PSUBUSW"   2 (P q)   (Q q)))
	     (:66        . ("VPSUBUSW"  3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PMINUB"    2 (P q)   (Q q)))
	     (:66        . ("VPMINUB"   3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PAND"      2 (P q)   (Q q)))
	     (:66        . ("VPAND"     3 (V x)   (H x)  (W x)
			    (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				    (operation . #.*OP-AND*))))))

	    ((:no-prefix . ("PADDUSB"   2 (P q)   (Q q)))
	     (:66        . ("VPADDUSB"  3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PADDUSW"   2 (P q)   (Q q)))
	     (:66        . ("VPADDUSW"  3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PMAXUB"    2 (P q)   (Q q)))
	     (:66        . ("VPMAXUB"   3 (V x)   (H x)  (W x))))

	    ((:no-prefix . ("PANDN"     2 (P q)   (Q q)))
	     (:66        . ("VPANDN"    3 (V x)   (H x)  (W x)
			    (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				    (operation . #.*OP-ANDN*)))))))

  #| e0 |# (((:no-prefix . ("PAVGB"      2 (P q)   (Q q)))
	     (:66        . ("VPAVGB"     3 (V x)   (H x)   (W x))))

	    ((:no-prefix . ("PSRAW"      2 (P q)   (Q q)))
	     (:66        . ("VPSRAW"     3 (V x)   (H x)   (W x))))

	    ((:no-prefix . ("PSRAD"      2 (P q)   (Q q)))
	     (:66        . ("VPSRAD"     3 (V x)   (H x)   (W x))))

	    ((:no-prefix . ("PAVGW"      2 (P q)   (Q q)))
	     (:66        . ("VPAVGW"     3 (V x)   (H x)   (W x))))

	    ((:no-prefix . ("PMULHUW"    2 (P q)   (Q q)))
	     (:66        . ("VPMULHUW"   3 (V x)   (H x)   (W x))))

	    ((:no-prefix . ("PMULHW"    2 (P q)   (Q q)))
	     (:66        . ("VPMULHW"   3 (V x)   (H x)   (W x))))

	    ((:66        . ("VCVTTPD2DQ" 2 (V x)   (W pd)))
	     (:F3        . ("VCVTDQ2PD"  2 (V x)   (W pd)))
	     (:F2        . ("VCVTPD2DQ"  2 (V x)   (W pd))))

	    ((:no-prefix . ("MOVNTQ"    2 (M q)   (P q)))
	     (:66        . ("VMOVNTDQ"  2 (M x)   (V x))))

  #| e8 |#  ((:no-prefix . ("PSUBSB"  2 (P q)  (Q q)))
	     (:66        . ("VPSUBSB" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PSUBSW"  2 (P q)  (Q q)))
	     (:66        . ("VPSUBSW" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PMINSW"  2 (P q)  (Q q)))
	     (:66        . ("VPMINSW" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("POR"  2 (P q)  (Q q)))
	     (:66        . ("VPOR" 3 (V x)  (H x)  (W x)
			    (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-OR*))))))

	    ((:no-prefix . ("PADDSB"  2 (P q)  (Q q)))
	     (:66        . ("VPADDSB" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PADDSW"  2 (P q)  (Q q)))
	     (:66        . ("VPADDSW" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PMAXSW"  2 (P q)  (Q q)))
	     (:66        . ("VPMAXSW" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PXOR"  2 (P q)  (Q q)))
	     (:66        . ("VPXOR" 3 (V x)  (H x)  (W x)
			    (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				    (operation . #.*OP-XOR*)))))))

  #| f0 |# (((:F2         . ("VLDDQU" 2 (V x)  (M x))))

	    ((:no-prefix . ("PSLLW"  2 (P q)  (Q q)))
	     (:66        . ("VPSLLW" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PSLLD"  2 (P q)  (Q q)))
	     (:66        . ("VPSLLD" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PSLLQ"  2 (P q)  (Q q)))
	     (:66        . ("VPSLLQ" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PMULUDQ"  2 (P q)  (Q q)))
	     (:66        . ("VPMULUDQ" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PMADDWD"  2 (P q)  (Q q)))
	     (:66        . ("VPMADDWD" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PSADBW"  2 (P q)  (Q q)))
	     (:66        . ("VPSADBW" 3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("MASKMOVQ"    2 (P q)  (N q)))
	     (:66        . ("VMASKMOVDQU" 2 (V dq) (U dq))))

  #| f8 |#  ((:no-prefix . ("PSUBB"    2 (P q)  (Q q)))
	     (:66        . ("VPSUBB"   3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PSUBW"    2 (P q)  (Q q)))
	     (:66        . ("VPSUBW"   3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PSUBD"    2 (P q)  (Q q)))
	     (:66        . ("VPSUBD"   3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PSUBQ"    2 (P q)  (Q q)))
	     (:66        . ("VPSUBQ"   3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PADDB"    2 (P q)  (Q q)))
	     (:66        . ("VPADDB"   3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PADDW"    2 (P q)  (Q q)))
	     (:66        . ("VPADDW"   3 (V x)  (H x)  (W x))))

	    ((:no-prefix . ("PADDD"    2 (P q)  (Q q)))
	     (:66        . ("VPADDD"   3 (V x)  (H x)  (W x))))

	    (:none
	       (:fn . (:no-instruction))))

  #|       -------------------------------        |#
  ))


(defconst *0F-38-three-byte-opcode-map-lst*
  ;; First two bytes are 0x0F 0x38.
  ;; Source: Intel Volume 2, Table A-4.

  '(
    #|       -------------------------------        |#


    #| 00 |# (((:no-prefix . ("PSHUFB"          2 (P q) (Q q)))
	       (:66        . ("VPSHUFB"         3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PHADDW"          2 (P q) (Q q)))
	       (:66        . ("VPHADDW"         3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PHADDD"          2 (P q) (Q q)))
	       (:66        . ("VPHADDD"         3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PHADDSW"         2 (P q) (Q q)))
	       (:66        . ("VPHADDSW"        3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PMADDUBSW"       2 (P q) (Q q)))
	       (:66        . ("VPMADDUBSW"      3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PHSUBW"          2 (P q) (Q q)))
	       (:66        . ("VPHSUBW"         3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PHSUBD"          2 (P q) (Q q)))
	       (:66        . ("VPHSUBD"         3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PHSUBSW"         2 (P q) (Q q)))
	       (:66        . ("VPHSUBSW"        3 (V x) (H x) (W x))))
    #| 08 |#  ((:no-prefix . ("PSIGNB"          2 (P q) (Q q)))
	       (:66        . ("VPSIGNB"         3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PSIGNW"          2 (P q) (Q q)))
	       (:66        . ("VPSIGNW"         3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PSIGND"          2 (P q) (Q q)))
	       (:66        . ("VPSIGND"         3 (V x) (H x) (W x))))
	      ((:no-prefix . ("PMULHRSW"        2 (P q) (Q q)))
	       (:66        . ("VPMULHRSW"       3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66       . ("VPERMILPS"      3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPERMILPD"      3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VTESTPS"        2 (V x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VTESTPD"        2 (V x) (W x)))))

    #| 10 |# (((:66        . ("PBLENDVB"        2 (V dq) (W dq))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:v66       . ("VCVTPH2PS"       3 (V x)  (W x)  (I b))))
	      ((:66        . ("BLENDVPS"        2 (V dq) (W dq))))
	      ((:66        . ("BLENDVPD"        2 (V dq) (W dq))))
	      ((:v66       . ("VPERMPS"         3 (V qq) (H qq) (W qq))))
	      ((:66        . ("VPTEST"          2 (V x)  (W x))))
    #| 18 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBROADCASTSS"    2 (V x)  (W d))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBROADCASTSD"    2 (V qq) (W q))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBROADCASTF128"  2 (V qq) (M dq))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . ("PABSB"           2 (P q)  (Q q)))
	       (:66        . ("VPABSB"          2 (V x)  (W x))))
	      ((:no-prefix . ("PABSW"           2 (P q)  (Q q)))
	       (:66        . ("VPABSW"          2 (V x)  (W x))))
	      ((:no-prefix . ("PABSD"           2 (P q)  (Q q)))
	       (:66        . ("VPABSD"          2 (V x)  (W x))))
	      (:none
	       (:fn . (:no-instruction))))

    #| 20 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVSXBW" 2 (V x) (U x))
			       ("VPMOVSXBW" 2 (V x) (M q))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVSXBD" 2 (V x) (U x))
			       ("VPMOVSXBD" 2 (V x) (M d))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVSXBQ" 2 (V x) (U x))
			       ("VPMOVSXBQ" 2 (V x) (M w))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVSXWD" 2 (V x) (U x))
			       ("VPMOVSXWD" 2 (V x) (M q))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVSXWQ" 2 (V x) (U x))
			       ("VPMOVSXWQ" 2 (V x) (M d))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVSXDQ" 2 (V x) (U x))
			       ("VPMOVSXDQ" 2 (V x) (M q))))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| 28 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMULDQ"     3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPCMPEQQ"    3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VMOVNTDQA"   2 (V x) (M x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPACKUSDW"   3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VMASKMOVPS"  3 (V x) (H x) (M x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VMASKMOVPD"  3 (V x) (H x) (M x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VMASKMOVPS"  3 (M x) (H x) (V x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VMASKMOVPD"  3 (M x) (H x) (V x)))))

    #| 30 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVZXBW" 2 (V x)  (U x))
			       ("VPMOVZXBW" 2 (V x)  (M q))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVZXBD" 2 (V x)  (U x))
			       ("VPMOVZXBD" 2 (V x)  (M d))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVZXBQ" 2 (V x)  (U x))
			       ("VPMOVZXBQ" 2 (V x)  (M w))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVZXWD" 2 (V x)  (U x))
			       ("VPMOVZXWD" 2 (V x)  (M q))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVZXWQ" 2 (V x)  (U x))
			       ("VPMOVZXWQ" 2 (V x)  (M d))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPMOVZXDQ" 2 (V x)  (U x))
			       ("VPMOVZXDQ" 2 (V x)  (M q))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPERMD"     3 (V qq) (H qq) (W qq))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPCMPGTQ"   3 (V x) (Hx) (W x))))
    #| 38 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMINSB"    3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMINSD"    3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMINUW"    3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMINUD"    3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMAXSB"    3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMAXSD"    3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMAXUW"    3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMAXUD"    3 (V x) (H x) (W x)))))

    #| 40 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPMULLD"     3 (V x)  (H x)    (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPHMINPOSUW" 2 (V dq) (W dq))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPSRLVD/Q"   3  (V x) (H x)    (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPSRAVD"     3  (V x) (H x)    (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPSLLVD/Q"   3  (V x) (H x)    (W x))))
    #| 48 |#  (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 50 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| 58 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPBROADCASTD"   2  (V x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPBROADCASTQ"   2  (V x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBROADCASTI128" 2  (V qq) (M dq))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 60 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| 68 |#  (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 70 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| 78 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPBROADCASTB" 2 (V x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPBROADCASTW" 2 (V x) (W x))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 80 |#  (((:no-prefix . (:none
			       (:fn . (:no-instruction))))
		(:66        . ("INVEPT"  2 (G y) (M dq))))
	       ((:no-prefix . (:none
			       (:fn . (:no-instruction))))
		(:66        . ("INVVPID" 2 (G y) (M dq))))
	       ((:no-prefix . (:none
			       (:fn . (:no-instruction))))
		(:66        . ("INVPCID" 2 (G y) (M dq))))
	       (:none
	       (:fn . (:no-instruction)))
	       (:none
	       (:fn . (:no-instruction)))
	       (:none
	       (:fn . (:no-instruction)))
	       (:none
	       (:fn . (:no-instruction)))
	       (:none
	       (:fn . (:no-instruction)))
    #| 88 |#   (:none
	       (:fn . (:no-instruction)))
	       (:none
	       (:fn . (:no-instruction)))
	       (:none
	       (:fn . (:no-instruction)))
	       (:none
	       (:fn . (:no-instruction)))
	       ((:no-prefix . (:none
			       (:fn . (:no-instruction))))
		(:v66        . ("VPMASKMOVD/Q" 3 (V x) (H x) (M x))))
	       (:none
	       (:fn . (:no-instruction)))
	       ((:no-prefix . (:none
			       (:fn . (:no-instruction))))
		(:v66        . ("VPMASKMOVD/Q" 3 (M x) (V x) (H x))))
	       (:none
	       (:fn . (:no-instruction))))

    #| 90 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VGATHERDD/Q"      3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VGATHERQD/Q"      3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VGATHERDPS/D"     3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VGATHERQPS/D"     3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:none
	       (:fn . (:no-instruction)))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:none
	       (:fn . (:no-instruction)))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADDSUB132PS/D" 3 (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUBADD132PS/D" 3 (V x) (H x) (W x))))
    #| 98 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD132PS/D"    3  (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD132SS/D"    3  (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB132PS/D"    3  (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB132SS/D"    3  (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD132PS/D"   3  (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD132SS/D"   3  (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB132PS/D"   3  (V x) (H x) (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB132SS/D"   3  (V x) (H x) (W x)))))

    #| a0 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADDSUB213PS/D" 3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUBADD213PS/D" 3 (V x)  (H x)  (W x))))
    #| a8 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD213PS/D"    3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD213SS/D"    3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB213PS/D"    3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB213SS/D"    3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD213PS/D"   3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD213SS/D"   3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB213PS/D"   3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB213SS/D"   3 (V x)  (H x)  (W x)))))

    #| b0 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADDSUB231PS/D" 3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUBADD231PS/D" 3 (V x)  (H x)  (W x))))
    #| b8 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD231PS/D"    3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD231SS/D"    3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB231PS/D"    3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB231SS/D"    3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD231PS/D"   3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD231SS/D"   3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB231PS/D"   3 (V x)  (H x)  (W x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB231SS/D"   3 (V x)  (H x)  (W x)))))

    #| c0 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| c8 |#  ("SHA1NEXTE"   2 (V dq) (W dq))
	      ("SHA1MSG1"    2 (V dq) (W dq))
	      ("SHA1MSG2"    2 (V dq) (W dq))
	      ("SHA256RNDS2" 2 (V dq) (W dq))
	      ("SHA256MSG1"  2 (V dq) (W dq))
	      ("SHA256MSG2"  2 (V dq) (W dq))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

  #| d0 |# ((:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
  #| d8 |#  (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("VAESIMC"     2 (V dq) (W dq))))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("VAESENC"     3 (V dq) (H dq) (W dq))))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("VAESENCLAST" 3 (V dq) (H dq) (W dq))))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("VAESDEC"     3 (V dq) (H dq) (W dq))))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("VAESDECLAST" 3 (V dq) (H dq) (W dq)))))

  #| e0 |# ((:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
  #| e8 |#  (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction))))

	   ;; A note about the two mandatory prefixes listed for CRC (0F 38 F0)
	   ;; in the Intel Opcode Map: The first three-byte opcode map lists
	   ;; CRC under 66 & F2 separately, even though CRC is already listed
	   ;; under F2 and MOVBE under 66.  Essentially, 66 is just a modifier
	   ;; prefix for CRC in this case.  So we ignore that opcode row in our
	   ;; representation, because opcode dispatch, modr/m determination,
	   ;; opcode coverage, etc. (which is what these tables are used for)
	   ;; will still work as expected for CRC, irrespective of whether 66
	   ;; is present as a modifier or not.

  #| f0 |# (((:no-prefix    . ("MOVBE" 2 (G y)  (M y)))
	     (:66           . ("MOVBE" 2 (G w)  (M w)))
	     (:F3           . (:none
			       (:fn . (:no-instruction))))
	     (:F2           . ("CRC32" 2 (G d)  (E b)))
	     ;; ((:66 :F2)     . ("CRC32" 2 (G d)  (E b)))
	     )
	    ((:no-prefix    . ("MOVBE" 2 (M y)  (G y)))
	     (:66           . ("MOVBE" 2 (M w)  (G w)))
	     (:F3           . (:none
			       (:fn . (:no-instruction))))
	     (:F2           . ("CRC32" 2 (G d)  (E y)))
	     ;; ((:66 :F2)     . ("CRC32" 2 (G d)  (E w)))
	     )
	    ((:v            . ("ANDN"  3 (G y)  (B y)  (E y)))
	     (:66           . (:none
			       (:fn . (:no-instruction))))
	     (:F3           . (:none
			       (:fn . (:no-instruction))))
	     (:F2           . (:none
			       (:fn . (:no-instruction))))
	     ;; ((:66 :F2)     . (:none (:fn . (:no-instruction))))
	     )
	    (:Group-17 0 :1a)
	    ((:no-prefix    . (:none
			       (:fn . (:no-instruction))))
	     (:66           . (:none
			       (:fn . (:no-instruction))))
	     (:F3           . (:none
			       (:fn . (:no-instruction))))
	     (:F2           . (:none
			       (:fn . (:no-instruction))))
	     ;; ((:66 :F2)     . (:none (:fn . (:no-instruction))))
	     )
	    ((:v            . ("BZHI"  3 (G y)  (E y)  (B y)))
	     (:66           . (:none
			       (:fn . (:no-instruction))))
	     (:vF3           . ("PEXT"  3 (G y)  (B y)  (E y)))
	     (:vF2           . ("PDEP"  3 (G y)  (B y)  (E y)))
	     ;; ((:66 :F2)     . (:none (:fn . (:no-instruction))))
	     )
	    ((:no-prefix    . (:none
			       (:fn . (:no-instruction))))
	     (:66           . ("ADCX"  2 (G y)  (E y)))
	     (:F3           . ("ADOX"  2 (G y)  (E y)))
	     (:vF2           . ("MULX"  3 (B y)  (G y)  (:rDX)  (E y)))
	     ;; ((:66 :F2)     . (:none (:fn . (:no-instruction))))
	     )
	    ((:v             . ("BEXTR" 3 (G y)  (E y)  (B y)))
	     (:v66           . ("SHLX"  3 (G y)  (E y)  (B y)))
	     (:vF3           . ("SARX"  3 (G y)  (E y)  (B y)))
	     (:vF2           . ("SHRX"  3 (G y)  (E y)  (B y)))
	     ;; ((:66 :F2)     . (:none (:fn . (:no-instruction))))
	     )
  #| f8 |#  (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction)))
	    (:none
	       (:fn . (:no-instruction))))

  #|       -------------------------------        |#
  ))

(defconst *0F-3A-three-byte-opcode-map-lst*
  ;; First two bytes are 0x0F 0x3A.
  ;; Source: Intel Volume 2, Table A-5.

  '(
    #|       -------------------------------        |#


    #| 00 |# (((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66        . ("VPERMQ"     3 (V qq)  (W qq)  (I b))))
	      ((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66        . ("VPERMPD"    3 (V qq)  (W qq)  (I b))))
	      ((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66        . ("VPBLENDD"   4 (V x)   (H x)   (W x)  (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66        . ("VPERMILPS"  3 (V x)  (W x)  (I b))))
	      ((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66       . ("VPERMILPD"  3 (V x)  (W x)  (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPERM2F128" 4 (V qq) (H qq) (W qq) (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      #| 08 |#  ((:no-prefix . (:none
					(:fn . (:no-instruction))))
			 (:66        . ("VROUNDPS" 3 (V x)  (W x)  (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VROUNDPD" 3 (V x)  (W x)  (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VROUNDSS" 3 (V ss) (W ss) (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VROUNDSD" 3 (V sd) (W sd) (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VBLENDPS" 4 (V x)  (H x)  (W x) (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VBLENDPD" 4 (V x)  (H x)  (W x) (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPBLENDW" 4 (V x)  (H x)  (W x) (I b))))
	      ((:no-prefix . ("PALIGNR"  3 (P q)  (Q q)  (I b)))
	       (:66        . ("VPALIGNR" 4 (V x)  (H x)  (W x) (I b)))))

    #| 10 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPEXTRB"    3 (R d)  (V dq)  (I b))
			       ("VPEXTRB"    3 (M b)  (V dq)  (I b))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPEXTRW"    3 (R d)  (V dq)  (I b))
			       ("VPEXTRW"    3 (M w)  (V dq)  (I b))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPEXTRD/Q"   3 (E y)  (V dq)  (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VEXTRACTPS"  3 (E d)  (V dq)  (I b))))
	      #| 18 |#  ((:no-prefix . (:none
					(:fn . (:no-instruction))))
			 (:v66        . ("VINSERTF128"  4 (V qq) (H qq) (W qq) (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VEXTRACTF128" 3 (W dq) (V qq) (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VCVTPS2PH"    3 (W x)  (V x)  (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 20 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VPINSRB"   4 (V dq) (H dq) (R y)  (I b))
			       ("VPINSRB"   4 (V dq) (H dq) (M b) (I b))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:ALT
			      (("VINSERTPS" 4 (V dq) (H dq) (U dq) (I b))
			       ("VINSERTPS" 4 (V dq) (H dq) (M d) (I b))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPINSRD/Q"  4 (V dq) (H dq) (E y)  (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| 28 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 30 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| 38 |#  ((:no-prefix . (:none
					(:fn . (:no-instruction))))
			 (:v66        . ("VINSERTI128"  4 (V qq) (H qq) (W qq) (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VEXTRACTI128" 3 (W dq) (V qq) (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 40 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VDPPS"      4 (V x)  (H x)  (W x)  (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VDPPD"      4 (V dq) (H dq) (W dq) (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VMPSADBW"   4 (V x)  (H x)  (W x)  (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPCLMULQDQ" 4 (V dq) (H dq) (W dq) (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPERM2I128" 4 (V qq) (H qq) (W qq) (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      #| 48 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBLENDVPS"  4 (V x)  (H x)  (W x)  (L x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBLENDVPD"  4 (V x)  (H x)  (W x)  (L x))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPBLENDVB"  4 (V x)  (H x)  (W x)  (L x))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 50 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| 58 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 60 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPCMPESTRM" 3 (V dq)  (W dq)  (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPCMPESTRI" 3 (V dq)  (W dq)  (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPCMPISTRM" 3 (V dq)  (W dq)  (I b))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VPCMPISTRI" 3 (V dq)  (W dq)  (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| 68 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 70 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| 78 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 80 |#  ((:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       #| 88 |#   (:none
			   (:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction)))
	       (:none
		(:fn . (:no-instruction))))

    #| 90 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| 98 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| a0 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| a8 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| b0 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| b8 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| c0 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| c8 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ("SHA1RNDS4" 3 (V dq) (W dq) (I b))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| d0 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| d8 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("VAESKEYGEN" 3 (V dq)  (W dq)  (I b)))))

    #| e0 |# ((:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| e8 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| f0 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:vF2        . ("RORX" 3 (G y)  (E y)  (I b))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      #| f8 |#  (:none
			 (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #|       -------------------------------        |#
    ))

(defconst *opcode-extensions-by-group-number*
  ;; Source: Intel Volume 2, Table A-6.

  ;; Format:
  ;; (<group name keyword> .
  ;;         (((<opcode-1> <pfx-1> <mod-1> <reg-1> <r/m-1>) . <instruction-1>)
  ;;           ;; ...
  ;;          ((<opcode-n> <pfx-n> <mod-n> <reg-n> <r/m-n>) . <instruction-n>)))

  '((:Group-1 . ;; Covers opcodes 80-83
	      ((((:opcode . #x80)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x80)
		 (:reg    . #b001)) .
		 ("OR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x80)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x80)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x80)
		 (:reg    . #b100)) .
		 ("AND" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x80)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x80)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x80)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))

	       (((:opcode . #x81)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x81)
		 (:reg    . #b001)) .
		 ("OR" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x81)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x81)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x81)
		 (:reg    . #b100)) .
		 ("AND" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x81)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x81)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x81)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))
		  (:ud  . (*ud-Lock-used*))))

	       (((:opcode . #x82)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x82)
		 (:reg    . #b001)) .
		 ("OR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x82)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x82)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x82)
		 (:reg    . #b100)) .
		 ("AND" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x82)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x82)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x82)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))
		  (:ud  . (*ud-Lock-used*))))

	       (((:opcode . #x83)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x83)
		 (:reg    . #b001)) .
		 ("OR" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x83)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x83)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x83)
		 (:reg    . #b100)) .
		 ("AND" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x83)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x83)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #x83)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))
		  (:ud  . (*ud-Lock-used*))))))

    (:Group-1A . ;; Covers opcode 8F.
	       ((((:opcode . #x8F)
		  (:reg    . #b000)) .
		  ("POP" 1 (E v) :1a :d64
		   (:fn . (x86-pop-Ev))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #x8F)
		  (:reg    . #b001)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #x8F)
		  (:reg    . #b010)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #x8F)
		  (:reg    . #b011)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #x8F)
		  (:reg    . #b100)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #x8F)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #x8F)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #x8F)
		  (:reg    . #b111)) .
		  (:none
		   (:fn . (:no-instruction))))))

    (:Group-2  . ;; Covers opcodes
	       ;; (C0, C1 reg, imm),
	       ;; (D0, D1 reg, 1),
	       ;; and
	       ;; (D2, D3 reg, CL).
	       ((((:opcode . #xC0)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC0)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC0)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC0)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC0)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC0)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC0)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC0)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))

		(((:opcode . #xC1)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC1)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC1)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC1)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC1)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC1)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC1)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC1)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))

		(((:opcode . #xD0)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD0)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD0)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD0)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD0)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD0)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD0)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD0)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))

		(((:opcode . #xD1)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD1)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD1)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD1)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD1)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD1)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD1)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD1)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))

		(((:opcode . #xD2)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD2)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD2)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD2)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD2)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD2)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD2)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD2)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))

		(((:opcode . #xD3)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD3)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD3)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD3)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD3)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD3)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xD3)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD3)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . (*ud-Lock-used*))))))

    (:Group-3 . ;; Covers opcodes F6 and F7.
	      ((((:opcode . #xF6)
		 (:reg    . #b000)) .
		 ("TEST" 1 (E b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-TEST*)))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xF6)
		 (:reg    . #b001)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xF6)
		 (:reg    . #b010)) .
		 ("NOT" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #xF6)
		 (:reg    . #b011)) .
		 ("NEG" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #xF6)
		 (:reg    . #b100)) .
		 ("MUL" 1 (E b) :1a
		  (:fn . (x86-mul))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xF6)
		 (:reg    . #b101)) .
		 ("IMUL" 1 (E b) :1a
		  (:fn . (x86-imul-Op/En-M))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xF6)
		 (:reg    . #b110)) .
		 ("DIV" 1 (E b) :1a
		  (:fn . (x86-div))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xF6)
		 (:reg    . #b111)) .
		 ("IDIV" 1 (E b) :1a
		  (:fn . (x86-idiv))
		  (:ud  . (*ud-Lock-used*))))

	       (((:opcode . #xF7)
		 (:reg    . #b000)) .
		 ("TEST" 1 (E b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-TEST*)))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xF7)
		 (:reg    . #b001)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xF7)
		 (:reg    . #b010)) .
		 ("NOT" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #xF7)
		 (:reg    . #b011)) .
		 ("NEG" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #xF7)
		 (:reg    . #b100)) .
		 ("MUL" 1 (E b) :1a
		  (:fn . (x86-mul))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xF7)
		 (:reg    . #b101)) .
		 ("IMUL" 1 (E b) :1a
		  (:fn . (x86-imul-Op/En-M))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xF7)
		 (:reg    . #b110)) .
		 ("DIV" 1 (E b) :1a
		  (:fn . (x86-div))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xF7)
		 (:reg    . #b111)) .
		 ("IDIV" 1 (E b) :1a
		  (:fn . (x86-idiv))
		  (:ud  . (*ud-Lock-used*))))))

    (:Group-4 . ;; Covers opcode FE.
	      ((((:opcode . #xFE)
		 (:reg    . #b000)) .
		 ("INC" 1 (E b) :1a
		  (:fn . (x86-inc/dec-FE-FF))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #xFE)
		 (:reg    . #b001)) .
		 ("DEC" 1 (E b) :1a
		  (:fn . (x86-inc/dec-FE-FF))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #xFE)
		 (:reg    . #b010)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xFE)
		 (:reg    . #b011)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xFE)
		 (:reg    . #b100)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xFE)
		 (:reg    . #b101)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xFE)
		 (:reg    . #b110)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xFE)
		 (:reg    . #b111)) .
		 (:none
		  (:fn . (:no-instruction))))))

    (:Group-5 . ;; Covers opcode FF.
	      ((((:opcode . #xFF)
		 (:reg    . #b000)) .
		 ("INC" 1 (E v) :1a
		  (:fn . (x86-inc/dec-FE-FF))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #xFF)
		 (:reg    . #b001)) .
		 ("DEC" 1 (E v) :1a
		  (:fn . (x86-inc/dec-FE-FF))
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #xFF)
		 (:reg    . #b010)) .
		 ("near CALL"  1 (E v) :1a :f64
		  (:fn . (x86-call-FF/2-Op/En-M))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xFF)
		 (:reg    . #b011)) .
		 ("far CALL"  1 (E p) :1a
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xFF)
		 (:reg    . #b100)) .
		 ("near JMP"  1 (E v) :1a :f64
		  (:fn . (x86-near-jmp-Op/En-M))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xFF)
		 (:reg    . #b101)) .
		 ("far JMP"  1 (M p) :1a
		  (:fn . (x86-far-jmp-Op/En-D))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xFF)
		 (:reg    . #b110)) .
		 ("PUSH"  1 (E v) :1a :d64
		  (:fn . (x86-push-Ev))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #xFF)
		 (:reg    . #b111)) .
		 (:none
		  (:fn . (:no-instruction))))))

    (:Group-6 . ;; Covers opcode 0F 00.
	      ((((:opcode . #ux0F_00)
		 (:reg    . #b000)) .
		 (:ALT
		  (("SLDT" 1 (R v) :1a)
		   ("SLDT" 1 (M w) :1a))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b001)) .
		 (:ALT
		  (("STR" 1 (R v) :1a)
		   ("STR" 1 (M w) :1a))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b010)) .
		 ("LLDT" 1 (E w) :1a
		  (:fn . (x86-lldt))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b011)) .
		 ("LTR" 1 (E w) :1a
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b100)) .
		 ("VERR" 1 (E w) :1a
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b101)) .
		 ("VERW" 1 (E w) :1a
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b110)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b111)) .
		 (:none
		  (:fn . (:no-instruction))))))

    (:Group-7 . ;; Covers opcode 0F 01.
	      ((((:opcode . #ux0F_01)
		 (:mod    . :mem)
		 (:reg    . #b000)) .
		 ("SGDT" 1 (M s) :1a
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b000)
		 (:r/m    . #b001)) .
		 ("VMCALL" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b000)
		 (:r/m    . #b010)) .
		 ("VMLAUNCH" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b000)
		 (:r/m    . #b011)) .
		 ("VMRESUME" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b000)
		 (:r/m    . #b100)) .
		 ("VMXOFF" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . :mem)
		 (:reg    . #b001)) .
		 ("SIDT" 1 (M s) :1a
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b000)) .
		 ("MONITOR" 0 :1a
		  (:ud  . (*ud-cpl-is-not-zero*
			   `(equal
			     ;; CPUID.01H:ECX.MONITOR[bit 3]
			     (cpuid-flag
			      :value #ux_01
			      :ecx t
			      :bit 3)
			     0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b001)) .
		 ("MWAIT" 0 :1a
		  (:ud  . (*ud-cpl-is-not-zero*
			   `(equal
			     ;; CPUID.01H:ECX.MONITOR[bit 3]
			     (cpuid-flag
			      :value #ux_01
			      :ecx t
			      :bit 3)
			     0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b010)) .
		 ("CLAC" 0 :1a
		  (:ud  . (*ud-Lock-used*
			   *ud-cpl-is-not-zero*
			   `(equal
			     ;; CPUID.(EAX=07H, ECX=0H):EBX.SMAP[bit 20]
			     (cpuid-flag
			      :eax #ux_07
			      :ecx #ux_00
			      :ebx t
			      :bit 20)
			     0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b011)) .
		 ("STAC" 0 :1a
		  (:ud  . (*ud-Lock-used*
			   *ud-cpl-is-not-zero*
			   `(equal
			     ;; CPUID.(EAX=07H, ECX=0H):EBX.SMAP[bit 20]
			     (cpuid-flag
			      :eax #ux_07
			      :ecx #ux_00
			      :ebx t
			      :bit 20)
			     0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b111)) .
		 ("ENCLS" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . :mem)
		 (:reg    . #b010)) .
		 ("LGDT" 1 (M s) :1a
		  (:fn . (x86-lgdt))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_01)
		 (:mod    . :mem)
		 (:reg    . #b011)) .
		 ("LIDT" 1 (M s) :1a
		  (:fn . (x86-lidt))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b000)) .
		 ("XGETBV" 0 :1a
		  (:ud  . (*ud-Lock-used*
			   `(equal
			     ;; CR4.OSXSAVE[bit 18]
			     (cr4-slice :cr4-osxsave (ctri #.*cr4* x86))
			     0)
			   `(equal
			     ;; CPUID.01H:ECX.XSAVE[bit 26]
			     (cpuid-flag
			      :value #ux_01
			      :ecx t
			      :bit 26)
			     0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b001)) .
		 ("XSETBV" 0 :1a
		  (:ud  . (*ud-Lock-used*
			   `(equal
			     ;; CR4.OSXSAVE[bit 18]
			     (cr4-slice :cr4-osxsave (ctri #.*cr4* x86))
			     0)
			   `(equal
			     ;; CPUID.01H:ECX.XSAVE[bit 26]
			     (cpuid-flag
			      :value #ux_01
			      :ecx t
			      :bit 26)
			     0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b100)) .
		 ("VMFUNC" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b101)) .
		 ("XEND" 0 :1a
		  (:ud  . (*ud-Lock-used*
			   *ud-Opr-used*
			   *ud-Reps-used*
			   `(equal
			     ;; CPUID.(EAX=7, ECX=0):EBX.RTM[bit 11]
			     (cpuid-flag
			      :eax #ux_07
			      :eax #ux_00
			      :ebx t
			      :bit 11)
			     0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b110)) .
		 ("XTEST" 0 :1a
		  (:ud  . (*ud-Lock-used*
			   ;; CPUID.(EAX=7, ECX=0):EBX.HLE[bit 4] = 0 and
			   ;; CPUID.(EAX=7, ECX=0):EBX.RTM[bit 11] = 0.
			   `(and (equal (cpuid-flag
					 :eax #ux_07
					 :ecx #ux_00
					 :ebx t
					 :bit 7)
					0)
				 (equal (cpuid-flag
					 :eax #ux_07
					 :ecx #ux_00
					 :ebx t
					 :bit 11)
					0))))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b111)) .
		 ("ENCLU" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b100)) .
		 (:ALT
		  (("SMSW" 1 (M w) :1a)
		   ("SMSW" 1 (R v) :1a))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b100)
		 (:r/m    . #b11)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b101)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b110)) .
		 ("LMSW" 1 (E w) :1a
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b111)
		 (:mod    . :mem)) .
		 ("INVLPG" 1 (M b) :1a
		  (:ud  . (*ud-Lock-used*
			   *ud-ModR/M.Mod-indicates-Register*))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b111)
		 (:r/m    . #b000)
		 (:mode   . :o64)) .
		 ("SWAPGS" 0 :1a
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b111)
		 (:r/m    . #b001)) .
		 ("RDTSCP" 0 :1a
		  (:ud  . (*ud-Lock-used*
			   `(equal
			     ;; CPUID.80000001H:EDX.RDTSCP[bit 27]
			     (cpuid-flag
			      :value #ux8000_0001
			      :edx t
			      :bit 27)
			     0)))))))

    (:Group-8 . ;; Covers opcode 0F BA.
	      ((((:opcode . #ux0F_BA)
		 (:reg    . #b000)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b001)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b010)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b011)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b100)) .
		 ("BT" 2 (E v) (I b) :1a
		  (:fn . (x86-bt-0f-ba))
		  (:ud  . (*ud-Lock-used*))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b101)) .
		 ("BTS" 2 (E b) (I b) :1a
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b110)) .
		 ("BTR" 2 (E b) (I b) :1a
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b111)) .
		 ("BTC" 2 (E b) (I b) :1a
		  (:ud  . (*ud-Lock-used-Dest-not-Memory-Op*))))))

    (:Group-9 . ;; Covers opcode 0F C7.
	      ((((:opcode . #ux0F_C7)
		 (:reg    . #b000)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . nil)
		 (:mod    . :mem)
		 (:reg    . #b001)) .
		 (:ALT
		  (("CMPXCH8B" 1 (M q) :1a)
		   ("CMPXCHG16B" 1 (M dq) :1a))
		  (:ud  . (*ud-ModR/M.Mod-indicates-Register*))))
	       (((:opcode . #ux0F_C7)
		 (:mod    . #b11)
		 (:reg    . #b001)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_C7)
		 (:reg    . #b010)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_C7)
		 (:reg    . #b011)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_C7)
		 (:reg    . #b100)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_C7)
		 (:reg    . #b101)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . nil)
		 (:mod    . :mem)
		 (:reg    . #b110)) .
		 ("VMPTRLD" 1 (M q) :1a))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :66)
		 (:mod    . :mem)
		 (:reg    . #b110)) .
		 ("VMCLEAR" 1 (M q) :1a))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :F3)
		 (:mod    . :mem)
		 (:reg    . #b110)) .
		 ("VMXON" 1 (M q) :1a))
	       (((:opcode . #ux0F_C7)
		 (:prefix . nil)
		 (:mod    . #b11)
		 (:reg    . #b110)) .
		 ("RDRAND" 1 (R v) :1a
		  (:fn . (x86-rdrand))
		  (:ud  . (*ud-Lock-used*
			   *ud-Reps-used*
			   `(equal
			     ;; CPUID.01H:ECX.RDRAND[bit 30]
			     (cpuid-flag
			      :value #ux_01
			      :ecx t
			      :bit 30)
			     t)))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . nil)
		 (:reg    . #b111)) .
		 ("RDSEED" 1 (R v) :1a
		  (:ud  . (*ud-Lock-used*
			   *ud-Reps-used*
			   `(equal
			     ;; CPUID.(EAX=07H, ECX=0H):EBX.RDSEED[bit 18]
			     (cpuid-flag
			      :eax #ux_07
			      :ecx #ux_00
			      :ebx t
			      :bit 18)
			     0)))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :F3)
		 (:reg    . #b111)) .
		 (:ALT
		  (("RDPID" 1 (R d) :1a)
		   ("RDPID" 1 (R q) :1a))
		  (:ud  . (*ud-Lock-used*
			   `(equal
			     ;; CPUID.7H.0:ECX.RDPID[bit 22]
			     (cpuid-flag
			      :value #ux_07
			      :value2 #ux_0
			      :ecx t
			      :bit 22)
			     0)))))))

    (:Group-10 . ;; Covers opcode 0F B9.
	       ((((:opcode . #ux0F_B9)) .
		 ("UD1" 0 :1a
		  (:fn . (x86-illegal-instruction
			  (message . "UD1 encountered!")))
		  (:ud  . (t))))))

    (:Group-11 . ;; Covers opcodes C6 and C7.
	       ((((:opcode . #xC6)
		  (:reg    . #b000)) .
		  ("MOV" 2 (E b) (I b) :1a
		   (:fn . (x86-mov-Op/En-MI))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC6)
		  (:reg    . #b001)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC6)
		  (:reg    . #b010)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC6)
		  (:reg    . #b011)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC6)
		  (:reg    . #b100)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC6)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC6)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC6)
		  (:mod    . :mem)
		  (:reg    . #b111)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC6)
		  (:mod    . #b11)
		  (:reg    . #b111)
		  (:r/m    . #b000)) .
		  ("XABORT" 1 (I b) :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal
			      ;; CPUID.(EAX=7, ECX=0):EBX.RTM[bit 11]
			      (cpuid-flag
			       :eax 7
			       :ecx 0
			       :ebx t
			       :bit 11 ;; RTM
			       )
			      0)))))

		(((:opcode . #xC7)
		  (:reg    . #b000)) .
		  ("MOV" 2 (E v) (I z) :1a
		   (:fn . (x86-mov-Op/En-MI))
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #xC7)
		  (:reg    . #b001)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC7)
		  (:reg    . #b010)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC7)
		  (:reg    . #b011)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC7)
		  (:reg    . #b100)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC7)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC7)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC7)
		  (:mod    . :mem)
		  (:reg    . #b111)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC7)
		  (:mod    . #b11)
		  (:reg    . #b111)
		  (:r/m    . #b000)) .
		  ("XBEGIN" 1 (J z) :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal
			      ;; CPUID.(EAX=7, ECX=0):EBX.RTM[bit 11]
			      (cpuid-flag
			       :eax 7
			       :ecx 0
			       :ebx t
			       :bit 11 ;; RTM
			       )
			      0)))))))

    (:Group-12 . ;; Covers opcode 0F 71.
	       ((((:opcode . #ux0F_71)
		  (:reg    . #b000)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_71)
		  (:reg    . #b001)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_71)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLW" 2 (N q) (I b) :1a))
		(((:opcode . #ux0F_71)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("VPSRLW" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_71)
		  (:reg    . #b011)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_71)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b100)) .
		  ("PSRAW" 2 (N q) (I b) :1a))
		(((:opcode . #ux0F_71)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b100)) .
		  ("VPSRAW" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_71)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_71)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLW" 2 (N q) (I b) :1a))
		(((:opcode . #ux0F_71)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("VPSLLW" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_71)
		  (:reg    . #b111)) .
		  (:none
		   (:fn . (:no-instruction))))))

    (:Group-13 . ;; Covers opcode 0F 72.
	       ((((:opcode . #ux0F_72)
		  (:reg    . #b000)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_72)
		  (:reg    . #b001)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_72)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLD" 2 (N q) (I b) :1a))
		(((:opcode . #ux0F_72)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("VPSRLD" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_72)
		  (:reg    . #b011)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_72)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b100)) .
		  ("PSRAD" 2 (N q) (I b) :1a))
		(((:opcode . #ux0F_72)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b100)) .
		  ("VPSRAD" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_72)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_72)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLD" 2 (N q) (I b) :1a))
		(((:opcode . #ux0F_72)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("VPSLLD" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_72)
		  (:reg    . #b111)) .
		  (:none
		   (:fn . (:no-instruction))))))

    (:Group-14 . ;; Covers opcode 0F 73.
	       ((((:opcode . #ux0F_73)
		  (:reg    . #b000)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_73)
		  (:reg    . #b001)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_73)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLQ" 2 (N q) (I b) :1a))
		(((:opcode . #ux0F_73)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("VPSRLQ" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_73)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b011)) .
		  ("VPSRLDQ" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_73)
		  (:prefix . nil)
		  (:reg    . #b100)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_73)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_73)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLQ" 2 (N q) (I b) :1a))
		(((:opcode . #ux0F_73)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("VPSLLQ" 3 (H x) (U x) (I b) :1a))
		(((:opcode . #ux0F_73)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b111)) .
		  ("VPSLLDQ" 3 (H x) (U x) (I b) :1a))))

    (:Group-15 . ;; Covers opcode 0F AE.
	       ((((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b000)) .
		  ("FXSAVE" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal
			      ;; CPUID.01H:EDX.FXSR[bit 24]
			      (cpuid-flag
			       :value #ux_01
			       :edx t
			       :bit 24)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b000)
		  (:mode   . :o64)) .
		  ("RDFSBASE" 1 (R y) :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal (cr4-slice :cr4-fsgsbase (ctri #.*cr4* x86)) 0)
			    `(equal
			      ;; CPUID.07H.0H:EBX.FSGSBASE[bit 0]
			      (cpuid-flag
			       :value #ux_07
			       :value2 #ux_00
			       :ebx t
			       :bit 0)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b001)) .
		  ("FXRSTOR" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal
			      ;; CPUID.01H:EDX.FXSR[bit 24]
			      (cpuid-flag
			       :value #ux_01
			       :edx t
			       :bit 24)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b001)
		  (:mode   . :o64)) .
		  ("RDGSBASE" 1 (R y) :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal (cr4-slice :cr4-fsgsbase (ctri #.*cr4* x86)) 0)
			    `(equal
			      ;; CPUID.07H.0H:EBX.FSGSBASE[bit 0]
			      (cpuid-flag
			       :value #ux_07
			       :value2 #ux_00
			       :ebx t
			       :bit 0)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b010)) .
		  ("LDMXCSR" 0 :1a
		   (:fn . (x86-ldmxcsr/stmxcsr-Op/En-M))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b010)
		  (:mode   . :o64)) .
		  ("WRFSBASE" 1 (R y) :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal (cr4-slice :cr4-fsgsbase (ctri #.*cr4* x86)) 0)
			    `(equal
			      ;; CPUID.07H.0H:EBX.FSGSBASE[bit 0]
			      (cpuid-flag
			       :value #ux_07
			       :value2 #ux_00
			       :ebx t
			       :bit 0)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b011)) .
		  ("STMXCSR" 0 :1a
		   (:fn . (x86-ldmxcsr/stmxcsr-Op/En-M))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b011)
		  (:mode   . :o64)) .
		  ("WRGSBASE" 1 (R y) :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal (cr4-slice :cr4-fsgsbase (ctri #.*cr4* x86)) 0)
			    `(equal
			      ;; CPUID.07H.0H:EBX.FSGSBASE[bit 0]
			      (cpuid-flag
			       :value #ux_07
			       :value2 #ux_00
			       :ebx t
			       :bit 0)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b100)) .
		  ("XSAVE" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal (cr4-slice :cr4-osxsave (ctri #.*cr4* x86)) 0)
			    `(equal
			      ;; CPUID.01H:ECX.XSAVE[bit 26]
			      (cpuid-flag
			       :value #ux_01
			       :ecx t
			       :bit 26)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b101)) .
		  ("XRSTOR" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal (cr4-slice :cr4-osxsave (ctri #.*cr4* x86)) 0)
			    `(equal
			      ;; CPUID.01H:ECX.XSAVE[bit 26]
			      (cpuid-flag
			       :value #ux_01
			       :ecx t
			       :bit 26)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b101)) .
		  ("LFENCE" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal
			      ;; CPUID.01H:EDX.SSE2[bit 26]
			      (cpuid-flag
			       :value #ux_01
			       :edx t
			       :bit 26)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b110)) .
		  ("XSAVEOPT" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal (cr4-slice :cr4-osxsave (ctri #.*cr4* x86)) 0)
			    `(or
			      (equal
			       ;; CPUID.01H:ECX.XSAVE[bit 26]
			       (cpuid-flag
				:value #ux_01
				:ecx t
				:bit 26)
			       0)
			      (equal
			       ;; CPUID.(EAX=0DH,ECX=1):EAX.XSAVEOPT[bit 0]
			       (cpuid-flag
				:eax #ux_0D
				:ecx #ux_01
				:eax t
				:bit 0)
			       0))))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("MFENCE" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal
			      ;; CPUID.01H:EDX.SSE2[bit 26]
			      (cpuid-flag
			       :value #ux_01
			       :edx t
			       :bit 26)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b111)) .
		  ("CLFLUSH" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal
			      ;; CPUID.01H:EDX.CLFSH[bit 19]
			      (cpuid-flag
			       :value #ux_01
			       :edx t
			       :bit 19)
			      0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b111)) .
		  ("SFENCE" 0 :1a
		   (:ud  . (*ud-Lock-used*
			    `(equal
			      ;; CPUID.01H:EDX.SSE[bit 25]
			      (cpuid-flag
			       :value #ux_01
			       :edx t
			       :bit 25)
			      0)))))))

    (:Group-16 . ;; Covers opcode 0F 18.
	       ((((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b000)) .
		  ("PREFETCHNTA" 0 :1a
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b001)) .
		  ("PREFETCHT0" 0 :1a
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b010)) .
		  ("PREFETCHT1" 0 :1a
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b011)) .
		  ("PREFETCHT2" 0 :1a
		   (:ud  . (*ud-Lock-used*))))
		(((:opcode . #ux0F_18)
		  (:reg    . #b100)) .
		  ("RESERVEDNOP" 0))
		(((:opcode . #ux0F_18)
		  (:reg    . #b101)) .
		  ("RESERVEDNOP" 0))
		(((:opcode . #ux0F_18)
		  (:reg    . #b110)) .
		  ("RESERVEDNOP" 0))
		(((:opcode . #ux0F_18)
		  (:reg    . #b111)) .
		  ("RESERVEDNOP" 0))
		(((:opcode . #ux0F_18)
		  (:mod    . #b11)) .
		  ("RESERVEDNOP" 0))))

    (:Group-17 . ;; Covers opcode VEX 0F 38 F3.
	       ((((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b000)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b001)) .
		  ("BLSR" 2 (B y) (E y) :v))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b010)) .
		  ("BLSMSK" 2 (B y) (E y) :v))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b011)) .
		  ("BLSI" 2 (B y) (E y) :v))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b100)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b111)) .
		  (:none
		   (:fn . (:no-instruction))))))
    ))

;; ----------------------------------------------------------------------

;; VEX-encoded instructions:

;; The vex listings below have been cross-checked with Table 2-16 (#UD
;; Exception and VEX.W=1 Encoding) and the first column of Table 2-17 (#UD
;; Exception and VEX.L Field Encoding) of Intel Manuals, Vol. 2.

(defconst *vex-0F-opcodes*
  '((#x10 ((:v :0F :LIG :F2 :WIG)                  ("VMOVSD"               3 (V x)  (H x)  (W sd)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VMOVSD"               3 (V x)  (H x)  (W sd)))
	  ((:v :0F :LIG :F3 :WIG)                  ("VMOVSS"               3 (V x)  (H x)  (W ss)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VMOVSS"               3 (V x)  (H x)  (W ss)))
	  ((:v :0F :128 :66 :WIG)                  ("VMOVUPD"              2 (V pd) (W pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVUPD"              2 (V pd) (W pd)))
	  ((:v :0F :128 :WIG)                      ("VMOVUPS"              2 (V ps) (W ps)))
	  ((:v :0F :256 :WIG)                      ("VMOVUPS"              2 (V ps) (W ps))))
    (#x11 ((:v :0F :LIG :F2 :WIG)                  ("VMOVSD"               3 (V x)  (H x)  (W sd)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VMOVSD"               3 (V x)  (H x)  (W sd)))
	  ((:v :0F :LIG :F3 :WIG)                  ("VMOVSS"               3 (V x)  (H x)  (W ss)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VMOVSS"               3 (V x)  (H x)  (W ss)))
	  ((:v :0F :128 :66 :WIG)                  ("VMOVUPD"              2 (V pd) (W pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVUPD"              2 (V pd) (W pd)))
	  ((:v :0F :128 :WIG)                      ("VMOVUPS"              2 (V ps) (W ps)))
	  ((:v :0F :256 :WIG)                      ("VMOVUPS"              2 (V ps) (W ps))))
    (#x12 ((:v :0F :128 :F2 :WIG)                  ("VMOVDDUP"             2 (V x)  (W x)))
	  ((:v :0F :256 :F2 :WIG)                  ("VMOVDDUP"             2 (V x)  (W x)))
	  ((:v :0F :NDS :128 :WIG)                 ("VMOVHLPS"             3 (V q)  (H q)  (U q)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VMOVLPD"              3 (V q)  (H q)  (M q)))
	  ((:v :0F :NDS :128 :WIG)                 ("VMOVLPS"              3 (V q)  (H q)  (M q)))
	  ((:v :0F :128 :F3 :WIG)                  ("VMOVSLDUP"            2 (V x)  (W x)))
	  ((:v :0F :256 :F3 :WIG)                  ("VMOVSLDUP"            2 (V x)  (W x))))
    (#x13 ((:v :0F :128 :66 :WIG)                  ("VMOVLPD"              3 (V q)  (H q)  (M q)))
	  ((:v :0F :128 :WIG)                      ("VMOVLPS"              3 (V q)  (H q)  (M q))))
    (#x14 ((:v :0F :NDS :128 :66 :WIG)             ("VUNPCKLPD"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VUNPCKLPD"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :WIG)                 ("VUNPCKLPS"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :WIG)                 ("VUNPCKLPS"            3 (V x)  (H x)  (W x))))
    (#x15 ((:v :0F :NDS :128 :66 :WIG)             ("VUNPCKHPD"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VUNPCKHPD"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :WIG)                 ("VUNPCKHPS"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :WIG)                 ("VUNPCKHPS"            3 (V x)  (H x)  (W x))))
    (#x16 ((:v :0F :NDS :128 :66 :WIG)             ("VMOVHPD"              3 (V dq)  (H q)  (M q) :v1))
	  ((:v :0F :NDS :128 :WIG)                 ("VMOVHPS"              3 (V dq)  (H q)  (M q) :v1))
	  ((:v :0F :NDS :128 :WIG)                 ("VMOVLHPS"             3 (V dq)  (H q)  (U q)))
	  ((:v :0F :128 :F3 :WIG)                  ("VMOVSHDUP"            2 (V x)   (W x)))
	  ((:v :0F :256 :F3 :WIG)                  ("VMOVSHDUP"            2 (V x)   (W x))))
    (#x17 ((:v :0F :128 :66 :WIG)                  ("VMOVHPD"              3 (V dq)  (H q)  (M q) :v1))
	  ((:v :0F :128 :WIG)                      ("VMOVHPS"              3 (V dq)  (H q)  (M q) :v1)))
    (#x28 ((:v :0F :128 :66 :WIG)                  ("VMOVAPD"              2 (V pd)  (W pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVAPD"              2 (V pd)  (W pd)))
	  ((:v :0F :128 :WIG)                      ("VMOVAPS"              2 (V ps)  (W ps)))
	  ((:v :0F :256 :WIG)                      ("VMOVAPS"              2 (V ps)  (W ps))))
    (#x29 ((:v :0F :128 :66 :WIG)                  ("VMOVAPD"              2 (V pd)  (W pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVAPD"              2 (V pd)  (W pd)))
	  ((:v :0F :128 :WIG)                      ("VMOVAPS"              2 (V ps)  (W ps)))
	  ((:v :0F :256 :WIG)                      ("VMOVAPS"              2 (V ps)  (W ps))))
    (#x2A ((:v :0F :NDS :LIG :F2 :W0)              ("VCVTSI2SD"            3 (V sd)  (H sd)  (E y)))
	  ((:v :0F :NDS :LIG :F2 :W1)              ("VCVTSI2SD"            3 (V sd)  (H sd)  (E y)))
	  ((:v :0F :NDS :LIG :F3 :W0)              ("VCVTSI2SS"            3 (V ss)  (H ss)  (E y)))
	  ((:v :0F :NDS :LIG :F3 :W1)              ("VCVTSI2SS"            3 (V ss)  (H ss)  (E y))))
    (#x2B ((:v :0F :128 :66 :WIG)                  ("VMOVNTPD"             2 (M pd)  (V pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVNTPD"             2 (M pd)  (V pd)))
	  ((:v :0F :128 :WIG)                      ("VMOVNTPS"             2 (M ps)  (V ps)))
	  ((:v :0F :256 :WIG)                      ("VMOVNTPS"             2 (M ps)  (V ps))))
    ;; Software should ensure VCVTTSD2SI, VC(VTTSS2SI are encoded with
    ;; VEX.L-0. Encoding VCVTTSD2SI with VEX(.L-1 may encounter unpredictable
    ;; behavior across different processor g(enerations.
    (#x2C ((:v :0F :LIG :F2 :W0)                   ("VCVTTSD2SI"           2 (G y)   (W sd)))
	  ((:v :0F :LIG :F2 :W1)                   ("VCVTTSD2SI"           2 (G y)   (W sd)))
	  ((:v :0F :LIG :F3 :W0)                   ("VCVTTSS2SI"           2 (G y)   (W ss)))
	  ((:v :0F :LIG :F3 :W1)                   ("VCVTTSS2SI"           2 (G y)   (W ss))))
    ;; Software should ensure VCVTSD2SI, VCV(TSS2SI are encoded with
    ;; VEX.L-0. Encoding VCVTSD2SI with VEX.(L-1 may encounter unpredictable
    ;; behavior across different processor g(enerations.
    (#x2D ((:v :0F :LIG :F2 :W0)                   ("VCVTSD2SI"            2 (G y)   (W sd)))
	  ((:v :0F :LIG :F2 :W1)                   ("VCVTSD2SI"            2 (G y)   (W sd)))
	  ((:v :0F :LIG :F3 :W0)                   ("VCVTSS2SI"            2 (G y)   (W ss)))
	  ((:v :0F :LIG :F3 :W1)                   ("VCVTSS2SI"            2 (G y)   (W ss))))
    (#x2E ((:v :0F :LIG :66 :WIG)                  ("VUCOMISD"             2 (V sd)  (W sd)))
	  ((:v :0F :LIG :WIG)                      ("VUCOMISS"             2 (V ss)  (W ss))))
    (#x2F ((:v :0F :LIG :66 :WIG)                  ("VCOMISD"              2 (V sd)  (W sd)))
	  ((:v :0F :LIG :WIG)                      ("VCOMISS"              2 (V ss)  (W ss))))
    (#x41 ((:v :0F :L1 :66 :W0 (:mod . #b11))      ("KANDB"                3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:v :0F :L1 :66 :W1 (:mod . #b11))      ("KANDD"                3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:v :0F :L1 :W1 (:mod . #b11))          ("KANDQ"                3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:v :0F :NDS :L1 :W0 (:mod . #b11))     ("KANDW"                3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x42 ((:v :0F :L1 :66 :W0 (:mod . #b11))      ("KANDNB"               3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:v :0F :L1 :66 :W1 (:mod . #b11))      ("KANDND"               3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:v :0F :L1 :W1 (:mod . #b11))          ("KANDNQ"               3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:v :0F :NDS :L1 :W0 (:mod . #b11))     ("KANDNW"               3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x44 ((:v :0F :L0 :66 :W0 (:mod . #b11))      ("KNOTB"                2 (K-reg b) (K-r/m b)))
	  ((:v :0F :L0 :66 :W1 (:mod . #b11))      ("KNOTD"                2 (K-reg d) (K-r/m d)))
	  ((:v :0F :L0 :W1 (:mod . #b11))          ("KNOTQ"                2 (K-reg q) (K-r/m q)))
	  ((:v :0F :L0 :W0 (:mod . #b11))          ("KNOTW"                2 (K-reg w) (K-r/m w))))
    (#x45 ((:v :0F :L1 :66 :W0 (:mod . #b11))      ("KORB"                 3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:v :0F :L1 :66 :W1 (:mod . #b11))      ("KORD"                 3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:v :0F :L1 :W1 (:mod . #b11))          ("KORQ"                 3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:v :0F :NDS :L1 :W0 (:mod . #b11))     ("KORW"                 3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x46 ((:v :0F :L1 :66 :W0 (:mod . #b11))      ("KXNORB"               3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:v :0F :L1 :66 :W1 (:mod . #b11))      ("KXNORD"               3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:v :0F :L1 :W1 (:mod . #b11))          ("KXNORQ"               3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:v :0F :NDS :L1 :W0 (:mod . #b11))     ("KXNORW"               3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x47 ((:v :0F :L1 :66 :W0 (:mod . #b11))      ("KXORB"                3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:v :0F :L1 :66 :W1 (:mod . #b11))      ("KXORD"                3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:v :0F :L1 :W1 (:mod . #b11))          ("KXORQ"                3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:v :0F :NDS :L1 :W0 (:mod . #b11))     ("KXORW"                3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x4A ((:v :0F :L1 :66 :W0 (:mod . #b11))      ("KADDB"                3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:v :0F :L1 :66 :W1 (:mod . #b11))      ("KADDD"                3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:v :0F :L1 :W1 (:mod . #b11))          ("KADDQ"                3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:v :0F :L1 :W0 (:mod . #b11))          ("KADDW"                3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x4B ((:v :0F :NDS :L1 :66 :W0 (:mod . #b11)) ("KUNPCKBW"             3 (K-reg w) (K-vex w) (K-r/m w)))
	  ((:v :0F :NDS :L1 :W1 (:mod . #b11))     ("KUNPCKDQ"             3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:v :0F :NDS :L1 :W0 (:mod . #b11))     ("KUNPCKWD"             3 (K-reg d) (K-vex d) (K-r/m d))))
    (#x50 ((:v :0F :128 :66 :WIG)                  ("VMOVMSKPD"            2 (G y)  (U pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVMSKPD"            2 (G y)  (U pd)))
	  ((:v :0F :128 :WIG)                      ("VMOVMSKPS"            2 (G y)  (U ps)))
	  ((:v :0F :256 :WIG)                      ("VMOVMSKPS"            2 (G y)  (U ps))))
    (#x51 ((:v :0F :128 :66 :WIG)                  ("VSQRTPD"              2 (V pd)  (W pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VSQRTPD"              2 (V pd)  (W pd)))
	  ((:v :0F :128 :WIG)                      ("VSQRTPS"              2 (V ps)  (W ps)))
	  ((:v :0F :256 :WIG)                      ("VSQRTPS"              2 (V ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VSQRTSD"              3 (V sd)  (H sd)  (W sd)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VSQRTSS"              3 (V ss)  (H ss)  (W ss))))
    (#x52 ((:v :0F :128 :WIG)                      ("VRSQRTPS"             2 (V ps)  (W ps)))
	  ((:v :0F :256 :WIG)                      ("VRSQRTPS"             2 (V ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VRSQRTSS"             3 (V ss)  (H ss)  (W ss))))
    (#x53 ((:v :0F :128 :WIG)                      ("VRCPPS"               2 (V ps)  (W ps)))
	  ((:v :0F :256 :WIG)                      ("VRCPPS"               2 (V ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VRCPSS"               3 (V ss)  (H ss)  (W ss))))
    (#x54 ((:v :0F :NDS :128 :66)                  ("VANDPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66)                  ("VANDPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128)                      ("VANDPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256)                      ("VANDPS"               3 (V ps)  (H ps)  (W ps))))
    (#x55 ((:v :0F :NDS :128 :66)                  ("VANDNPD"              3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66)                  ("VANDNPD"              3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128)                      ("VANDNPS"              3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256)                      ("VANDNPS"              3 (V ps)  (H ps)  (W ps))))
    (#x56 ((:v :0F :NDS :128 :66)                  ("VORPD"                3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66)                  ("VORPD"                3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128)                      ("VORPS"                3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256)                      ("VORPS"                3 (V ps)  (H ps)  (W ps))))
    (#x57 ((:v :0F :NDS :128 :66 :WIG)             ("VXORPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VXORPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :WIG)                 ("VXORPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :WIG)                 ("VXORPS"               3 (V ps)  (H ps)  (W ps))))
    (#x58 ((:v :0F :NDS :128 :66 :WIG)             ("VADDPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VADDPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :WIG)                 ("VADDPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :WIG)                 ("VADDPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VADDSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VADDSS"               3 (V ss)  (H ss)  (W ss))))
    (#x59 ((:v :0F :NDS :128 :66 :WIG)             ("VMULPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VMULPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :WIG)                 ("VMULPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :WIG)                 ("VMULPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VMULSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VMULSS"               3 (V ss)  (H ss)  (W ss))))
    (#x5A ((:v :0F :128 :66 :WIG)                  ("VCVTPD2PS"            2 (V ps)  (W pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VCVTPD2PS"            2 (V ps)  (W pd)))
	  ((:v :0F :128 :WIG)                      ("VCVTPS2PD"            2 (V pd)  (W ps)))
	  ((:v :0F :256 :WIG)                      ("VCVTPS2PD"            2 (V pd)  (W ps)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VCVTSD2SS"            3 (V ss)  (H x)   (W sd)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VCVTSS2SD"            3 (V sd)  (H x)   (W ss))))
    (#x5B ((:v :0F :128 :WIG)                      ("VCVTDQ2PS"            2 (V ps)  (W dq)))
	  ((:v :0F :256 :WIG)                      ("VCVTDQ2PS"            2 (V ps)  (W dq)))
	  ((:v :0F :128 :66 :WIG)                  ("VCVTPS2DQ"            2 (V dq)  (W ps)))
	  ((:v :0F :256 :66 :WIG)                  ("VCVTPS2DQ"            2 (V dq)  (W ps)))
	  ((:v :0F :128 :F3 :WIG)                  ("VCVTTPS2DQ"           2 (V dq)  (W ps)))
	  ((:v :0F :256 :F3 :WIG)                  ("VCVTTPS2DQ"           2 (V dq)  (W ps))))
    (#x5C ((:v :0F :NDS :128 :66 :WIG)             ("VSUBPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VSUBPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :WIG)                 ("VSUBPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :WIG)                 ("VSUBPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VSUBSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VSUBSS"               3 (V ss)  (H ss)  (W ss))))
    (#x5D ((:v :0F :NDS :128 :66 :WIG)             ("VMINPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VMINPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :WIG)                 ("VMINPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :WIG)                 ("VMINPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VMINSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VMINSS"               3 (V ss)  (H ss)  (W ss))))
    (#x5E ((:v :0F :NDS :128 :66 :WIG)             ("VDIVPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VDIVPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :WIG)                 ("VDIVPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :WIG)                 ("VDIVPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VDIVSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VDIVSS"               3 (V ss)  (H ss)  (W ss))))
    (#x5F ((:v :0F :NDS :128 :66 :WIG)             ("VMAXPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VMAXPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :WIG)                 ("VMAXPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :WIG)                 ("VMAXPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VMAXSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VMAXSS"               3 (V ss)  (H ss)  (W ss))))
    (#x60 ((:v :0F :NDS :256 :66 :WIG)             ("VPUNPCKLBW"           3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPUNPCKLBW"           3 (V x)  (H x)  (W x))))
    (#x61 ((:v :0F :NDS :256 :66 :WIG)             ("VPUNPCKLWD"           3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPUNPCKLWD"           3 (V x)  (H x)  (W x))))
    (#x62 ((:v :0F :NDS :256 :66 :WIG)             ("VPUNPCKLDQ"           3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPUNPCKLDQ"           3 (V x)  (H x)  (W x))))
    (#x63 ((:v :0F :NDS :128 :66 :WIG)             ("VPACKSSWB"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPACKSSWB"            3 (V x)  (H x)  (W x))))
    (#x64 ((:v :0F :NDS :128 :66 :WIG)             ("VPCMPGTB"             3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPCMPGTB"             3 (V x)  (H x)  (W x))))
    (#x65 ((:v :0F :NDS :128 :66 :WIG)             ("VPCMPGTW"             3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPCMPGTW"             3 (V x)  (H x)  (W x))))
    (#x66 ((:v :0F :NDS :128 :66 :WIG)             ("VPCMPGTD"             3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPCMPGTD"             3 (V x)  (H x)  (W x))))
    (#x67 ((:v :0F :NDS :128 :66 :WIG)             ("VPACKUSWB"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPACKUSWB"            3 (V x)  (H x)  (W x))))
    (#x68 ((:v :0F :NDS :256 :66 :WIG)             ("VPUNPCKHBW"           3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPUNPCKHBW"           3 (V x)  (H x)  (W x))))
    (#x69 ((:v :0F :NDS :256 :66 :WIG)             ("VPUNPCKHWD"           3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPUNPCKHWD"           3 (V x)  (H x)  (W x))))
    (#x6A ((:v :0F :NDS :256 :66 :WIG)             ("VPUNPCKHDQ"           3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPUNPCKHDQ"           3 (V x)  (H x)  (W x))))
    (#x6B ((:v :0F :NDS :128 :66 :WIG)             ("VPACKSSDW"            3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPACKSSDW"            3 (V x)  (H x)  (W x))))
    (#x6C ((:v :0F :NDS :256 :66 :WIG)             ("VPUNPCKLQDQ"          3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPUNPCKLQDQ"          3 (V x)  (H x)  (W x))))
    (#x6D ((:v :0F :NDS :256 :66 :WIG)             ("VPUNPCKHQDQ"          3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPUNPCKHQDQ"          3 (V x)  (H x)  (W x))))
    (#x6E ((:v :0F :128 :66 :W1)                   ("VMOVQ"                2 (V q)    (W q)))
	  ((:v :0F :128 :66 :W0)                   ("VMOVD"                2 (V q)    (W q))))
    (#x6F ((:v :0F :128 :66 :WIG)                  ("VMOVDQA"              2 (V x)  (W x)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVDQA"              2 (V x)  (W x)))
	  ((:v :0F :128 :F3 :WIG)                  ("VMOVDQU"              2 (V x)  (W x)))
	  ((:v :0F :256 :F3 :WIG)                  ("VMOVDQU"              2 (V x)  (W x))))
    (#x70 ((:v :0F :128 :66 :WIG)                  ("VPSHUFD"              3 (V x)   (W x)   (I b))) ;; ib
	  ((:v :0F :256 :66 :WIG)                  ("VPSHUFD"              3 (V x)   (W x)   (I b))) ;; ib
	  ((:v :0F :128 :F3 :WIG)                  ("VPSHUFHW"             3 (V x)   (W x)   (I b))) ;; ib
	  ((:v :0F :256 :F3 :WIG)                  ("VPSHUFHW"             3 (V x)   (W x)   (I b))) ;; ib
	  ((:v :0F :128 :F2 :WIG)                  ("VPSHUFLW"             3 (V x)   (W x)   (I b))) ;; ib
	  ((:v :0F :256 :F2 :WIG)                  ("VPSHUFLW"             3 (V x)   (W x)   (I b)))) ;; ib
    (#x71 ((:v :0F :NDD :128 :66 :WIG)             ("VPSRLW"               3 (V x)   (H x)  (W x))) ;; /2 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSRLW"               3 (V x)   (H x)  (W x))) ;; /2 ib
	  ((:v :0F :NDD :128 :66 :WIG)             ("VPSRAW"               3 (V x)   (H x)   (W x))) ;; /4 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSRAW"               3 (V x)   (H x)   (W x))) ;; /4 ib
	  ((:v :0F :NDD :128 :66 :WIG)             ("VPSLLW"               3 (V x)  (H x)  (W x))) ;; /6 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSLLW"               3 (V x)  (H x)  (W x)))) ;; /6 ib
    (#x72 ((:v :0F :NDD :128 :66 :WIG)             ("VPSLLD"               3 (V x)  (H x)  (W x))) ;; /2 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSLLD"               3 (V x)  (H x)  (W x))) ;; /2 ib
	  ((:v :0F :NDD :128 :66 :WIG)             ("VPSRAW"               3 (V x)   (H x)   (W x))) ;; /4 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSRAW"               3 (V x)   (H x)   (W x))) ;; /4 ib
	  ((:v :0F :NDD :128 :66 :WIG)             ("VPSLLW"               3 (V x)  (H x)  (W x))) ;; /6 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSLLW"               3 (V x)  (H x)  (W x)))) ;; /6 ib
    (#x73 ((:v :0F :NDD :128 :66 :WIG)             ("VPSRLQ"               3 (V x)   (H x)  (W x))) ;; /2 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSRLQ"               3 (V x)   (H x)  (W x))) ;; /2 ib
	  ((:v :0F :NDD :128 :66 :WIG)             ("VPSRLDQ"              3 (H x) (U x) (I b) :1a)) ;; /3 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSRLDQ"              3 (H x) (U x) (I b) :1a)) ;; /3 ib
	  ((:v :0F :NDD :128 :66 :WIG)             ("VPSLLQ"               3 (V x)  (H x)  (W x))) ;; /6 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSLLQ"               3 (V x)  (H x)  (W x))) ;; /6 ib
	  ((:v :0F :NDD :128 :66 :WIG)             ("VPSLLDQ"              3 (H x) (U x) (I b) :1a)) ;; /7 ib
	  ((:v :0F :NDD :256 :66 :WIG)             ("VPSLLDQ"              3 (H x) (U x) (I b) :1a))) ;; /7 ib
    (#x74 ((:v :0F :NDS :128 :66 :WIG)             ("VPCMPEQB"             3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPCMPEQB"             3 (V x)   (H x)  (W x))))
    (#x75 ((:v :0F :NDS :128 :66 :WIG)             ("VPCMPEQW"             3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPCMPEQW"             3 (V x)   (H x)  (W x))))
    (#x76 ((:v :0F :NDS :128 :66 :WIG)             ("VPCMPEQD"             3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPCMPEQD"             3 (V x)   (H x)  (W x))))
    (#x77 ((:v :0F :256 :WIG)                      ("VZEROALL"             0))
	  ((:v :0F :128 :WIG)                      ("VZEROUPPER"           0)))
    (#x7C ((:v :0F :NDS :128 :66 :WIG)             ("VHADDPD"              3 (V pd)   (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VHADDPD"              3 (V pd)   (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :F2 :WIG)             ("VHADDPS"              3 (V ps)   (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :F2 :WIG)             ("VHADDPS"              3 (V ps)   (H ps)  (W ps))))
    (#x7D ((:v :0F :NDS :128 :66 :WIG)             ("VHSUBPD"              3 (V pd)   (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VHSUBPD"              3 (V pd)   (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :F2 :WIG)             ("VHSUBPS"              3 (V ps)   (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :F2 :WIG)             ("VHSUBPS"              3 (V ps)   (H ps)  (W ps))))
    (#x7E ((:v :0F :128 :66 :W0)                   ("VMOVD"                2 (E y)    (V y)))
	  ((:v :0F :128 :66 :W1)                   ("VMOVQ"                2 (V q)    (W q)))
	  ((:v :0F :128 :F3 :WIG)                  ("VMOVQ"                2 (V q)    (W q))))
    (#x7F ((:v :0F :128 :66 :WIG)                  ("VMOVDQA"              2 (V x)  (W x)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVDQA"              2 (V x)  (W x)))
	  ((:v :0F :128 :F3 :WIG)                  ("VMOVDQU"              2 (V x)  (W x)))
	  ((:v :0F :256 :F3 :WIG)                  ("VMOVDQU"              2 (V x)  (W x))))
    (#x90 ((:v :0F :L0 :66 :W0)                    ("KMOVB"                2 (K-reg b) (K-r/m b)))
	  ((:v :0F :L0 :66 :W1)                    ("KMOVD"                2 (K-reg d) (K-r/m d)))
	  ((:v :0F :L0 :W1)                        ("KMOVQ"                2 (K-reg q) (K-r/m q)))
	  ((:v :0F :L0 :W0)                        ("KMOVW"                2 (K-reg w) (K-r/m w))))
    (#x91 ((:v :0F :L0 :66 :W0 (:mod . :mem))      ("KMOVB"                2 (K-r/m b) (K-reg b)))
	  ((:v :0F :L0 :66 :W1 (:mod . :mem))      ("KMOVD"                2 (K-r/m d) (K-reg d)))
	  ((:v :0F :L0 :W1 (:mod . :mem))          ("KMOVQ"                2 (K-r/m q) (K-reg q)))
	  ((:v :0F :L0 :W0 (:mod . :mem))          ("KMOVW"                2 (K-r/m w) (K-reg w))))
    (#x92 ((:v :0F :L0 :66 :W0 (:mod . #b11))      ("KMOVB"                2 (K-reg b) (K-r/m b)))
	  ((:v :0F :L0 :F2 :W0 (:mod . #b11))      ("KMOVD"                2 (K-reg d) (K-r/m d)))
	  ((:v :0F :L0 :F2 :W1 (:mod . #b11))      ("KMOVQ"                2 (K-reg q) (K-r/m q)))
	  ((:v :0F :L0 :W0 (:mod . #b11))          ("KMOVW"                2 (K-reg w) (K-r/m w))))
    (#x93 ((:v :0F :L0 :66 :W0 (:mod . #b11))      ("KMOVB"                2 (K-reg b) (K-r/m b)))
	  ((:v :0F :L0 :F2 :W0 (:mod . #b11))      ("KMOVD"                2 (K-reg d) (K-r/m d)))
	  ((:v :0F :L0 :F2 :W1 (:mod . #b11))      ("KMOVQ"                2 (K-reg q) (K-r/m q)))
	  ((:v :0F :L0 :W0 (:mod . #b11))          ("KMOVW"                2 (K-reg w) (K-r/m w))))
    (#x98 ((:v :0F :L0 :66 :W0 (:mod . #b11))      ("KORTESTB"             2 (K-reg b) (K-r/m b)))
	  ((:v :0F :L0 :66 :W1 (:mod . #b11))      ("KORTESTD"             2 (K-reg d) (K-r/m d)))
	  ((:v :0F :L0 :W1 (:mod . #b11))          ("KORTESTQ"             2 (K-reg q) (K-r/m q)))
	  ((:v :0F :L0 :W0 (:mod . #b11))          ("KORTESTW"             2 (K-reg w) (K-r/m w))))
    (#x99 ((:v :0F :L0 :66 :W0 (:mod . #b11))      ("KTESTB"               2 (K-reg b) (K-r/m b)))
	  ((:v :0F :L0 :66 :W1 (:mod . #b11))      ("KTESTD"               2 (K-reg d) (K-r/m d)))
	  ((:v :0F :L0 :W1 (:mod . #b11))          ("KTESTQ"               2 (K-reg q) (K-r/m q)))
	  ((:v :0F :L0 :W0 (:mod . #b11))          ("KTESTW"               2 (K-reg w) (K-r/m w))))
    (#xAE ((:v :0F :LZ :WIG)                       ("VLDMXCSR"             0 :1a))
	  ((:v :0F :LZ :WIG)                       ("VSTMXCSR"             0 :1a)))
    (#xC2 ((:v :0F :NDS :128 :66 :WIG)             ("VCMPPD"               4 (V pd)  (H pd)  (W pd)  (I b))) ;; ib
	  ((:v :0F :NDS :256 :66 :WIG)             ("VCMPPD"               4 (V pd)  (H pd)  (W pd)  (I b))) ;; ib
	  ((:v :0F :NDS :128 :WIG)                 ("VCMPPS"               4 (V ps)  (H ps)  (W ps)  (I b))) ;; ib
	  ((:v :0F :NDS :256 :WIG)                 ("VCMPPS"               4 (V ps)  (H ps)  (W ps)  (I b))) ;; ib
	  ((:v :0F :NDS :LIG :F2 :WIG)             ("VCMPSD"               4 (V sd)  (H sd)  (W sd)  (I b))) ;; ib
	  ((:v :0F :NDS :LIG :F3 :WIG)             ("VCMPSS"               4 (V ss)  (H ss)  (W ss)  (I b)))) ;; ib
    (#xC4 ((:v :0F :NDS :128 :66 :W0)              ("VPINSRW"              4 (V dq)  (H dq) (R y)  (I b)))) ;; ib
    (#xC5 ((:v :0F :128 :66 :W0)                   ("VPEXTRW"              3 (G d)   (U dq) (I b)))) ;; ib
    (#xC6 ((:v :0F :NDS :128 :66 :WIG)             ("VSHUFPD"              4 (V pd)  (H pd)  (W pd)  (I b))) ;; ib
	  ((:v :0F :NDS :256 :66 :WIG)             ("VSHUFPD"              4 (V pd)  (H pd)  (W pd)  (I b))) ;; ib
	  ((:v :0F :NDS :128 :WIG)                 ("VSHUFPS"              4 (V ps)  (H ps)  (W ps)  (I b))) ;; ib
	  ((:v :0F :NDS :256 :WIG)                 ("VSHUFPS"              4 (V ps)  (H ps)  (W ps)  (I b)))) ;; ib
    (#xD0 ((:v :0F :NDS :128 :66 :WIG)             ("VADDSUBPD"            3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VADDSUBPD"            3 (V pd)  (H pd)  (W pd)))
	  ((:v :0F :NDS :128 :F2 :WIG)             ("VADDSUBPS"            3 (V ps)  (H ps)  (W ps)))
	  ((:v :0F :NDS :256 :F2 :WIG)             ("VADDSUBPS"            3 (V ps)  (H ps)  (W ps))))
    (#xD1 ((:v :0F :NDS :128 :66 :WIG)             ("VPSRLW"               3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSRLW"               3 (V x)   (H x)  (W x))))
    (#xD2 ((:v :0F :NDS :128 :66 :WIG)             ("VPSRLD"               3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSRLD"               3 (V x)   (H x)  (W x))))
    (#xD3 ((:v :0F :NDS :128 :66 :WIG)             ("VPSRLQ"               3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSRLQ"               3 (V x)   (H x)  (W x))))
    (#xD4 ((:v :0F :NDS :128 :66 :WIG)             ("VPADDQ"               3 (V x)   (H x)  (W x) ))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPADDQ"               3 (V x)   (H x)  (W x))))
    (#xD5 ((:v :0F :NDS :128 :66 :WIG)             ("VPMULLW"              3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPMULLW"              3 (V x)   (H x)  (W x))))
    (#xD6 ((:v :0F :128 :66 :WIG)                  ("VMOVQ"                2 (V q)    (W q))))
    (#xD7 ((:v :0F :128 :66 :WIG)                  ("VPMOVMSKB"            2 (G d)   (U x)))
	  ((:v :0F :256 :66 :WIG)                  ("VPMOVMSKB"            2 (G d)   (U x))))
    (#xD8 ((:v :0F :NDS :128 :66 :WIG)             ("VPSUBUSB"             3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSUBUSB"             3 (V x)   (H x)  (W x))))
    (#xD9 ((:v :0F :NDS :128 :66 :WIG)             ("VPSUBUSW"             3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSUBUSW"             3 (V x)   (H x)  (W x))))
    (#xDA ((:v :0F :NDS :128 :66)                  ("VPMINUB"              3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66)                  ("VPMINUB"              3 (V x)   (H x)  (W x))))
    (#xDB ((:v :0F :NDS :128 :66 :WIG)             ("VPAND"                3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPAND"                3 (V x)   (H x)  (W x))))
    (#xDC ((:v :0F :NDS :128 :66 :WIG)             ("VPADDUSB"             3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPADDUSB"             3 (V x)   (H x)  (W x))))
    (#xDD ((:v :0F :NDS :128 :66 :WIG)             ("VPADDUSW"             3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPADDUSW"             3 (V x)   (H x)  (W x))))
    (#xDE ((:v :0F :NDS :128 :66)                  ("VPMAXUB"              3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66)                  ("VPMAXUB"              3 (V x)   (H x)  (W x))))
    (#xDF ((:v :0F :NDS :128 :66 :WIG)             ("VPANDN"               3 (V x)   (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPANDN"               3 (V x)   (H x)  (W x))))
    (#xE0 ((:v :0F :NDS :128 :66 :WIG)             ("VPAVGB"               3 (V x)   (H x)   (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPAVGB"               3 (V x)   (H x)   (W x))))
    (#xE1 ((:v :0F :NDS :128 :66 :WIG)             ("VPSRAW"               3 (V x)   (H x)   (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSRAW"               3 (V x)   (H x)   (W x))))
    (#xE2 ((:v :0F :NDS :128 :66 :WIG)             ("VPSRAD"               3 (V x)   (H x)   (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSRAD"               3 (V x)   (H x)   (W x))))
    (#xE3 ((:v :0F :NDS :128 :66 :WIG)             ("VPAVGW"               3 (V x)   (H x)   (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPAVGW"               3 (V x)   (H x)   (W x))))
    (#xE4 ((:v :0F :NDS :128 :66 :WIG)             ("VPMULHUW"             3 (V x)   (H x)   (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPMULHUW"             3 (V x)   (H x)   (W x))))
    (#xE5 ((:v :0F :NDS :128 :66 :WIG)             ("VPMULHW"              3 (V x)   (H x)   (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPMULHW"              3 (V x)   (H x)   (W x))))
    (#xE6 ((:v :0F :128 :F3 :WIG)                  ("VCVTDQ2PD"            2 (V x)   (W pd)))
	  ((:v :0F :256 :F3 :WIG)                  ("VCVTDQ2PD"            2 (V x)   (W pd)))
	  ((:v :0F :128 :F2 :WIG)                  ("VCVTPD2DQ"            2 (V x)   (W pd)))
	  ((:v :0F :256 :F2 :WIG)                  ("VCVTPD2DQ"            2 (V x)   (W pd)))
	  ((:v :0F :128 :66 :WIG)                  ("VCVTTPD2DQ"           2 (V x)   (W pd)))
	  ((:v :0F :256 :66 :WIG)                  ("VCVTTPD2DQ"           2 (V x)   (W pd))))
    (#xE7 ((:v :0F :128 :66 :WIG)                  ("VMOVNTDQ"             2 (M x)   (V x)))
	  ((:v :0F :256 :66 :WIG)                  ("VMOVNTDQ"             2 (M x)   (V x))))
    (#xE8 ((:v :0F :NDS :128 :66 :WIG)             ("VPSUBSB"              3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSUBSB"              3 (V x)  (H x)  (W x))))
    (#xE9 ((:v :0F :NDS :128 :66 :WIG)             ("VPSUBSW"              3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSUBSW"              3 (V x)  (H x)  (W x))))
    (#xEA ((:v :0F :NDS :128 :66)                  ("VPMINSW"              3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66)                  ("VPMINSW"              3 (V x)  (H x)  (W x))))
    (#xEB ((:v :0F :NDS :128 :66 :WIG)             ("VPOR"                 3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPOR"                 3 (V x)  (H x)  (W x))))
    (#xEC ((:v :0F :NDS :128 :66 :WIG)             ("VPADDSB"              3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPADDSB"              3 (V x)  (H x)  (W x))))
    (#xED ((:v :0F :NDS :128 :66 :WIG)             ("VPADDSW"              3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPADDSW"              3 (V x)  (H x)  (W x))))
    (#xEE ((:v :0F :NDS :128 :66 :WIG)             ("VPMAXSW"              3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPMAXSW"              3 (V x)  (H x)  (W x))))
    (#xEF ((:v :0F :NDS :128 :66 :WIG)             ("VPXOR"                3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPXOR"                3 (V x)  (H x)  (W x))))
    (#xF0 ((:v :0F :128 :F2 :WIG)                  ("VLDDQU"               2 (V x)  (M x)))
	  ((:v :0F :256 :F2 :WIG)                  ("VLDDQU"               2 (V x)  (M x))))
    (#xF1 ((:v :0F :NDS :128 :66 :WIG)             ("VPSLLW"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSLLW"               3 (V x)  (H x)  (W x))))
    (#xF2 ((:v :0F :NDS :128 :66 :WIG)             ("VPSLLD"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSLLD"               3 (V x)  (H x)  (W x))))
    (#xF3 ((:v :0F :NDS :128 :66 :WIG)             ("VPSLLQ"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSLLQ"               3 (V x)  (H x)  (W x))))
    (#xF4 ((:v :0F :NDS :128 :66 :WIG)             ("VPMULUDQ"             3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPMULUDQ"             3 (V x)  (H x)  (W x))))
    (#xF5 ((:v :0F :NDS :128 :66 :WIG)             ("VPMADDWD"             3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPMADDWD"             3 (V x)  (H x)  (W x))))
    (#xF6 ((:v :0F :NDS :128 :66 :WIG)             ("VPSADBW"              3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSADBW"              3 (V x)  (H x)  (W x))))
    (#xF7 ((:v :0F :128 :66 :WIG)                  ("VMASKMOVDQU"          2 (V dq) (U dq))))
    (#xF8 ((:v :0F :NDS :128 :66 :WIG)             ("VPSUBB"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSUBB"               3 (V x)  (H x)  (W x))))
    (#xF9 ((:v :0F :NDS :128 :66 :WIG)             ("VPSUBW"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSUBW"               3 (V x)  (H x)  (W x))))
    (#xFA ((:v :0F :NDS :128 :66 :WIG)             ("VPSUBD"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPSUBD"               3 (V x)  (H x)  (W x))))
    (#xFB ((:v :0F :NDS :256 :66 :WIG)             ("VPSUBQ"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :128 :66 :WIG)             ("VPSUBQ"               3 (V x)  (H x)  (W x))))
    (#xFC ((:v :0F :NDS :128 :66 :WIG)             ("VPADDB"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPADDB"               3 (V x)  (H x)  (W x))))
    (#xFD ((:v :0F :NDS :128 :66 :WIG)             ("VPADDW"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPADDW"               3 (V x)  (H x)  (W x))))
    (#xFE ((:v :0F :NDS :128 :66 :WIG)             ("VPADDD"               3 (V x)  (H x)  (W x)))
	  ((:v :0F :NDS :256 :66 :WIG)             ("VPADDD"               3 (V x)  (H x)  (W x))))))

(defconst *vex-0F38-opcodes*
  '((#x0 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPSHUFB"              3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPSHUFB"              3 (V x) (H x) (W x)))) ;;  ib
    (#x1 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPHADDW"              3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPHADDW"              3 (V x) (H x) (W x)))) ;;  ib
    (#x2 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPHADDD"              3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPHADDD"              3 (V x) (H x) (W x)))) ;;  ib
    (#x3 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPHADDSW"             3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPHADDSW"             3 (V x) (H x) (W x)))) ;;  ib
    (#x4 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPMADDUBSW"           3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPMADDUBSW"           3 (V x) (H x) (W x)))) ;;  ib
    (#x5 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPHSUBW"              3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPHSUBW"              3 (V x) (H x) (W x)))) ;;  ib
    (#x6 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPHSUBD"              3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPHSUBD"              3 (V x) (H x) (W x)))) ;;  ib
    (#x7 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPHSUBSW"             3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPHSUBSW"             3 (V x) (H x) (W x)))) ;;  ib
    (#x8 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPSIGNB"              3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPSIGNB"              3 (V x) (H x) (W x)))) ;;  ib
    (#x9 ((:v :0F38 :NDS :128 :66 :WIG)            ("VPSIGNW"              3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPSIGNW"              3 (V x) (H x) (W x)))) ;;  ib
    (#xA ((:v :0F38 :NDS :128 :66 :WIG)            ("VPSIGND"              3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPSIGND"              3 (V x) (H x) (W x)))) ;;  ib
    (#xB ((:v :0F38 :NDS :128 :66 :WIG)            ("VPMULHRSW"            3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :WIG)            ("VPMULHRSW"            3 (V x) (H x) (W x)))) ;;  ib
    (#xC ((:v :0F38 :NDS :128 :66 :W0)             ("VPERMILPS"            3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :W0)             ("VPERMILPS"            3 (V x) (H x) (W x)))) ;;  ib
    (#xD ((:v :0F38 :NDS :128 :66 :W0)             ("VPERMILPD"            3 (V x) (H x) (W x))) ;;  ib
	 ((:v :0F38 :NDS :256 :66 :W0)             ("VPERMILPD"            3 (V x) (H x) (W x)))) ;;  ib
    (#xE ((:v :0F38 :128 :66 :W0)                  ("VTESTPS"              2 (V x) (W x))) ;;  ib
	 ((:v :0F38 :256 :66 :W0)                  ("VTESTPS"              2 (V x) (W x)))) ;;  ib
    (#xF ((:v :0F38 :128 :66 :W0)                  ("VTESTPD"              2 (V x) (W x))) ;;  ib
	 ((:v :0F38 :256 :66 :W0)                  ("VTESTPD"              2 (V x) (W x)))) ;;  ib
    (#x13 ((:v :0F38 :128 :66 :W0)                 ("VCVTPH2PS"            3 (V x)  (W x)  (I b))) ;;  ib
	  ((:v :0F38 :256 :66 :W0)                 ("VCVTPH2PS"            3 (V x)  (W x)  (I b)))) ;;  ib
    (#x16 ((:v :0F38 :256 :66 :W0)                 ("VPERMPS"              3 (V qq) (H qq) (W qq)))) ;;  ib
    (#x17 ((:v :0F38 :128 :66 :WIG)                ("VPTEST"               2 (V x)  (W x))) ;;  ib
	  ((:v :0F38 :256 :66 :WIG)                ("VPTEST"               2 (V x)  (W x))))
    (#x18 ((:v :0F38 :128 :66 :W0)                 ("VBROADCASTSS"         2 (V x)  (W d)))
	  ((:v :0F38 :256 :66 :W0)                 ("VBROADCASTSS"         2 (V x)  (W d)))
	  ((:v :0F38 :256 :66 :W0)                 ("VBROADCASTSS"         2 (V x)  (W d)))
	  ((:v :0F38 :128 :66 :W0)                 ("VBROADCASTSS"         2 (V x)  (W d))))
    (#x19 ((:v :0F38 :256 :66 :W0)                 ("VBROADCASTSD"         2 (V qq) (W q)))
	  ((:v :0F38 :256 :66 :W0)                 ("VBROADCASTSD"         2 (V qq) (W q))))
    (#x1A ((:v :0F38 :256 :66 :W0)                 ("VBROADCASTF128"       2 (V qq) (M dq))))
    (#x1C ((:v :0F38 :128 :66 :WIG)                ("VPABSB"               2 (V x)  (W x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPABSB"               2 (V x)  (W x))))
    (#x1D ((:v :0F38 :128 :66 :WIG)                ("VPABSW"               2 (V x)  (W x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPABSW"               2 (V x)  (W x))))
    (#x1E ((:v :0F38 :128 :66 :WIG)                ("VPABSD"               2 (V x)  (W x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPABSD"               2 (V x)  (W x))))
    (#x20 ((:v :0F38 :128 :66 :WIG)                ("VPMOVSXBW"            2 (V x) (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVSXBW"            2 (V x) (U x))))
    (#x21 ((:v :0F38 :128 :66 :WIG)                ("VPMOVSXBD"            2 (V x) (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVSXBD"            2 (V x) (U x))))
    (#x22 ((:v :0F38 :128 :66 :WIG)                ("VPMOVSXBQ"            2 (V x) (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVSXBQ"            2 (V x) (U x))))
    (#x23 ((:v :0F38 :128 :66 :WIG)                ("VPMOVSXWD"            2 (V x) (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVSXWD"            2 (V x) (U x))))
    (#x24 ((:v :0F38 :128 :66 :WIG)                ("VPMOVSXWQ"            2 (V x) (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVSXWQ"            2 (V x) (U x))))
    (#x25 ((:v :0F38 :128 :66 :WIG)                ("VPMOVSXDQ"            2 (V x) (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVSXDQ"            2 (V x) (U x))))
    (#x28 ((:v :0F38 :NDS :128 :66 :WIG)           ("VPMULDQ"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPMULDQ"              3 (V x) (H x) (W x))))
    (#x29 ((:v :0F38 :NDS :128 :66 :WIG)           ("VPCMPEQQ"             3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPCMPEQQ"             3 (V x) (H x) (W x))))
    (#x2A ((:v :0F38 :128 :66 :WIG)                ("VMOVNTDQA"            2 (V x) (M x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VMOVNTDQA"            2 (V x) (M x))))
    (#x2B ((:v :0F38 :NDS :128 :66)                ("VPACKUSDW"            3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66)                ("VPACKUSDW"            3 (V x) (H x) (W x))))
    (#x2C ((:v :0F38 :NDS :128 :66 :W0)            ("VMASKMOVPS"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VMASKMOVPS"           3 (V x) (H x) (M x))))
    (#x2D ((:v :0F38 :NDS :128 :66 :W0)            ("VMASKMOVPD"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VMASKMOVPD"           3 (V x) (H x) (M x))))
    (#x2E ((:v :0F38 :NDS :128 :66 :W0)            ("VMASKMOVPS"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VMASKMOVPS"           3 (V x) (H x) (M x))))
    (#x2F ((:v :0F38 :NDS :128 :66 :W0)            ("VMASKMOVPD"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VMASKMOVPD"           3 (V x) (H x) (M x))))
    (#x30 ((:v :0F38 :128 :66 :WIG)                ("VPMOVZXBW"            2 (V x)  (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVZXBW"            2 (V x)  (U x))))
    (#x31 ((:v :0F38 :128 :66 :WIG)                ("VPMOVZXBD"            2 (V x)  (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVZXBD"            2 (V x)  (U x))))
    (#x32 ((:v :0F38 :128 :66 :WIG)                ("VPMOVZXBQ"            2 (V x)  (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVZXBQ"            2 (V x)  (U x))))
    (#x33 ((:v :0F38 :128 :66 :WIG)                ("VPMOVZXWD"            2 (V x)  (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVZXWD"            2 (V x)  (U x))))
    (#x34 ((:v :0F38 :128 :66 :WIG)                ("VPMOVZXWQ"            2 (V x)  (U x)))
	  ((:v :0F38 :256 :66 :WIG)                ("VPMOVZXWQ"            2 (V x)  (U x))))
    (#x35 ((:v :0F38 :256 :66 :WIG)                ("VPMOVZXDQ"            2 (V x)  (U x))))
    (#x36 ((:v :0F38 :NDS :256 :66 :W0)            ("VPERMD"               3 (V qq) (H qq) (W qq))))
    (#x37 ((:v :0F38 :NDS :128 :66 :WIG)           ("VPCMPGTQ"             3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPCMPGTQ"             3 (V x) (H x) (W x))))
    (#x38 ((:v :0F38 :NDS :128 :66)                ("VPMINSB"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66)                ("VPMINSB"              3 (V x) (H x) (W x))))
    (#x39 ((:v :0F38 :NDS :128 :66 :WIG)           ("VPMINSD"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPMINSD"              3 (V x) (H x) (W x))))
    (#x3A ((:v :0F38 :NDS :128 :66)                ("VPMINUW"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66)                ("VPMINUW"              3 (V x) (H x) (W x))))
    (#x3B ((:v :0F38 :NDS :128 :66 :WIG)           ("VPMINUD"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPMINUD"              3 (V x) (H x) (W x))))
    (#x3C ((:v :0F38 :NDS :128 :66 :WIG)           ("VPMAXSB"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPMAXSB"              3 (V x) (H x) (W x))))
    (#x3D ((:v :0F38 :NDS :128 :66 :WIG)           ("VPMAXSD"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPMAXSD"              3 (V x) (H x) (W x))))
    (#x3E ((:v :0F38 :NDS :128 :66)                ("VPMAXUW"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66)                ("VPMAXUW"              3 (V x) (H x) (W x))))
    (#x3F ((:v :0F38 :NDS :128 :66 :WIG)           ("VPMAXUD"              3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPMAXUD"              3 (V x) (H x) (W x))))
    (#x40 ((:v :0F38 :NDS :128 :66 :WIG)           ("VPMULLD"              3 (V x)  (H x)    (W x)))
	  ((:v :0F38 :NDS :256 :66 :WIG)           ("VPMULLD"              3 (V x)  (H x)    (W x))))
    (#x41 ((:v :0F38 :128 :66 :WIG)                ("VPHMINPOSUW"          2 (V dq) (W dq))))
    (#x45 ((:v :0F38 :NDS :128 :66 :W0)            ("VPSRLVD"              3  (V x) (H x)    (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VPSRLVD"              3  (V x) (H x)    (W x)))
	  ((:v :0F38 :NDS :128 :66 :W1)            ("VPSRLVQ"              3  (V x) (H x)    (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VPSRLVQ"              3  (V x) (H x)    (W x))))
    (#x46 ((:v :0F38 :NDS :128 :66 :W0)            ("VPSRAVD"              3  (V x) (H x)    (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VPSRAVD"              3  (V x) (H x)    (W x))))
    (#x47 ((:v :0F38 :NDS :128 :66 :W0)            ("VPSLLVD"              3  (V x) (H x)    (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VPSLLVD"              3  (V x) (H x)    (W x)))
	  ((:v :0F38 :NDS :128 :66 :W1)            ("VPSLLVQ"              3  (V x) (H x)    (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VPSLLVQ"              3  (V x) (H x)    (W x))))
    (#x58 ((:v :0F38 :128 :66 :W0)                 ("VPBROADCASTD"         2  (V x)  (W x)))
	  ((:v :0F38 :256 :66 :W0)                 ("VPBROADCASTD"         2  (V x)  (W x))))
    (#x59 ((:v :0F38 :128 :66 :W0)                 ("VPBROADCASTQ"         2  (V x)  (W x)))
	  ((:v :0F38 :256 :66 :W0)                 ("VPBROADCASTQ"         2  (V x)  (W x))))
    (#x5A ((:v :0F38 :256 :66 :W0)                 ("VBROADCASTI128"       2  (V qq) (M dq))))
    (#x78 ((:v :0F38 :128 :66 :W0)                 ("VPBROADCASTB"         2 (V x) (W x)))
	  ((:v :0F38 :256 :66 :W0)                 ("VPBROADCASTB"         2 (V x) (W x))))
    (#x79 ((:v :0F38 :128 :66 :W0)                 ("VPBROADCASTW"         2 (V x) (W x)))
	  ((:v :0F38 :256 :66 :W0)                 ("VPBROADCASTW"         2 (V x) (W x))))
    (#x8C ((:v :0F38 :NDS :128 :66 :W0)            ("VPMASKMOVD"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VPMASKMOVD"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :128 :66 :W1)            ("VPMASKMOVQ"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VPMASKMOVQ"           3 (V x) (H x) (M x))))
    (#x8E ((:v :0F38 :NDS :128 :66 :W0)            ("VPMASKMOVD"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VPMASKMOVD"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :128 :66 :W1)            ("VPMASKMOVQ"           3 (V x) (H x) (M x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VPMASKMOVQ"           3 (V x) (H x) (M x))))
    (#x90 ((:v :0F38 :DDS :128 :66 :W0)            ("VPGATHERDD"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VPGATHERDD"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W1)            ("VPGATHERDQ"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VPGATHERDQ"           3 (V x) (H x) (W x))))
    (#x91 ((:v :0F38 :DDS :128 :66 :W0)            ("VPGATHERQD"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VPGATHERQD"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W1)            ("VPGATHERQQ"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VPGATHERQQ"           3 (V x) (H x) (W x))))
    (#x92 ((:v :0F38 :DDS :128 :66 :W1)            ("VGATHERDPD"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VGATHERDPD"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W0)            ("VGATHERDPS"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VGATHERDPS"           3 (V x) (H x) (W x))))
    (#x93 ((:v :0F38 :DDS :128 :66 :W1)            ("VGATHERQPD"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VGATHERQPD"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W0)            ("VGATHERQPS"           3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VGATHERQPS"           3 (V x) (H x) (W x))))
    (#x96 ((:v :0F38 :DDS :128 :66 :W1)            ("VFMADDSUB132PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VFMADDSUB132PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W0)            ("VFMADDSUB132PS"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VFMADDSUB132PS"       3 (V x) (H x) (W x))))
    (#x97 ((:v :0F38 :DDS :128 :66 :W1)            ("VFMSUBADD132PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VFMSUBADD132PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W0)            ("VFMSUBADD132PS"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VFMSUBADD132PS"       3 (V x) (H x) (W x))))
    (#x98 ((:v :0F38 :NDS :128 :66 :W1)            ("VFMADD132PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFMADD132PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFMADD132PS"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFMADD132PS"          3 (V x) (H x) (W x))))
    (#x99 ((:v :0F38 :DDS :LIG :66 :W1)            ("VFMADD132SD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFMADD132SS"          3 (V x) (H x) (W x))))
    (#x9A ((:v :0F38 :NDS :128 :66 :W1)            ("VFMSUB132PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFMSUB132PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFMSUB132PS"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFMSUB132PS"          3 (V x) (H x) (W x))))
    (#x9B ((:v :0F38 :DDS :LIG :66 :W1)            ("VFMSUB132SD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFMSUB132SS"          3 (V x) (H x) (W x))))
    (#x9C ((:v :0F38 :NDS :128 :66 :W1)            ("VFNMADD132PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFNMADD132PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFNMADD132PS"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFNMADD132PS"         3 (V x) (H x) (W x))))
    (#x9D ((:v :0F38 :DDS :LIG :66 :W1)            ("VFNMADD132SD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFNMADD132SS"         3 (V x) (H x) (W x))))
    (#x9E ((:v :0F38 :NDS :128 :66 :W1)            ("VFNMSUB132PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFNMSUB132PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFNMSUB132PS"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFNMSUB132PS"         3 (V x) (H x) (W x))))
    (#x9F ((:v :0F38 :DDS :LIG :66 :W1)            ("VFNMSUB132SD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFNMSUB132SS"         3 (V x) (H x) (W x))))
    (#xA6 ((:v :0F38 :DDS :128 :66 :W1)            ("VFMADDSUB213PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VFMADDSUB213PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W0)            ("VFMADDSUB213PS"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VFMADDSUB213PS"       3 (V x) (H x) (W x))))
    (#xA7 ((:v :0F38 :DDS :128 :66 :W1)            ("VFMSUBADD213PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VFMSUBADD213PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W0)            ("VFMSUBADD213PS"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VFMSUBADD213PS"       3 (V x) (H x) (W x))))
    (#xA8 ((:v :0F38 :NDS :128 :66 :W1)            ("VFMADD213PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFMADD213PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFMADD213PS"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFMADD213PS"          3 (V x) (H x) (W x))))
    (#xA9 ((:v :0F38 :DDS :LIG :66 :W1)            ("VFMADD213SD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFMADD213SS"          3 (V x) (H x) (W x))))
    (#xAA ((:v :0F38 :NDS :128 :66 :W1)            ("VFMSUB213PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFMSUB213PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFMSUB213PS"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFMSUB213PS"          3 (V x) (H x) (W x))))
    (#xAB ((:v :0F38 :DDS :LIG :66 :W1)            ("VFMSUB213SD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFMSUB213SS"          3 (V x) (H x) (W x))))
    (#xAC ((:v :0F38 :NDS :128 :66 :W1)            ("VFNMADD213PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFNMADD213PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFNMADD213PS"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFNMADD213PS"         3 (V x) (H x) (W x))))
    (#xAD ((:v :0F38 :DDS :LIG :66 :W1)            ("VFNMADD213SD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFNMADD213SS"         3 (V x) (H x) (W x))))
    (#xAE ((:v :0F38 :NDS :128 :66 :W1)            ("VFNMSUB213PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFNMSUB213PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFNMSUB213PS"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFNMSUB213PS"         3 (V x) (H x) (W x))))
    (#xAF ((:v :0F38 :DDS :LIG :66 :W1)            ("VFNMSUB213SD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFNMSUB213SS"         3 (V x) (H x) (W x))))
    (#xB6 ((:v :0F38 :DDS :128 :66 :W1)            ("VFMADDSUB231PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VFMADDSUB231PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W0)            ("VFMADDSUB231PS"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VFMADDSUB231PS"       3 (V x) (H x) (W x))))
    (#xB7 ((:v :0F38 :DDS :128 :66 :W1)            ("VFMSUBADD231PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W1)            ("VFMSUBADD231PD"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :128 :66 :W0)            ("VFMSUBADD231PS"       3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :256 :66 :W0)            ("VFMSUBADD231PS"       3 (V x) (H x) (W x))))
    (#xB8 ((:v :0F38 :NDS :128 :66 :W1)            ("VFMADD231PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFMADD231PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFMADD231PS"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFMADD231PS"          3 (V x) (H x) (W x))))
    (#xB9 ((:v :0F38 :DDS :LIG :66 :W1)            ("VFMADD231SD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFMADD231SS"          3 (V x) (H x) (W x))))
    (#xBA ((:v :0F38 :NDS :128 :66 :W1)            ("VFMSUB231PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFMSUB231PD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFMSUB231PS"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFMSUB231PS"          3 (V x) (H x) (W x))))
    (#xBB ((:v :0F38 :DDS :LIG :66 :W1)            ("VFMSUB231SD"          3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFMSUB231SS"          3 (V x) (H x) (W x))))
    (#xBC ((:v :0F38 :NDS :128 :66 :W1)            ("VFNMADD231PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFNMADD231PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFNMADD231PS"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFNMADD231PS"         3 (V x) (H x) (W x))))
    (#xBD ((:v :0F38 :DDS :LIG :66 :W1)            ("VFNMADD231SD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFNMADD231SS"         3 (V x) (H x) (W x))))
    (#xBE ((:v :0F38 :NDS :128 :66 :W1)            ("VFNMSUB231PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W1)            ("VFNMSUB231PD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :128 :66 :W0)            ("VFNMSUB231PS"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :NDS :256 :66 :W0)            ("VFNMSUB231PS"         3 (V x) (H x) (W x))))
    (#xBF ((:v :0F38 :DDS :LIG :66 :W1)            ("VFNMSUB231SD"         3 (V x) (H x) (W x)))
	  ((:v :0F38 :DDS :LIG :66 :W0)            ("VFNMSUB231SS"         3 (V x) (H x) (W x))))
    (#xDB ((:v :0F38 :128 :66 :WIG)                ("VAESIMC"              2 (V dq) (W dq))))
    (#xDC ((:v :0F38 :NDS :128 :66 :WIG)           ("VAESENC"              3 (V dq) (H dq) (W dq))))
    (#xDD ((:v :0F38 :NDS :128 :66 :WIG)           ("VAESENCLAST"          3 (V dq) (H dq) (W dq))))
    (#xDE ((:v :0F38 :NDS :128 :66 :WIG)           ("VAESDEC"              3 (V dq) (H dq) (W dq))))
    (#xDF ((:v :0F38 :NDS :128 :66 :WIG)           ("VAESDECLAST"          3 (V dq) (H dq) (W dq))))
    (#xF2 ((:v :0F38 :NDS :LZ :W0)                 ("ANDN"                 3 (G y)  (B y)  (E y)))
	  ((:v :0F38 :NDS :LZ :W1)                 ("ANDN"                 3 (G y)  (B y)  (E y))))
    (#xF3 ((:v :0F38 :NDD :LZ :W0 (:reg . 1))      ("BLSR"                 2 (B y) (E y) :v))
	  ((:v :0F38 :NDD :LZ :W1 (:reg . 1))      ("BLSR"                 2 (B y) (E y) :v))
	  ((:v :0F38 :NDD :LZ :W0 (:reg . 2))      ("BLSMSK"               2 (B y) (E y) :v))
	  ((:v :0F38 :NDD :LZ :W1 (:reg . 2))      ("BLSMSK"               2 (B y) (E y) :v))
	  ((:v :0F38 :NDD :LZ :W0 (:reg . 3))      ("BLSI"                 2 (B y) (E y) :v))
	  ((:v :0F38 :NDD :LZ :W1 (:reg . 3))      ("BLSI"                 2 (B y) (E y) :v)))
    (#xF5 ((:v :0F38 :NDS :LZ :W0)                 ("BZHI"                 3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :W1)                 ("BZHI"                 3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :F2 :W0)             ("PDEP"                 3 (G y)  (B y)  (E y)))
	  ((:v :0F38 :NDS :LZ :F2 :W1)             ("PDEP"                 3 (G y)  (B y)  (E y)))
	  ((:v :0F38 :NDS :LZ :F3 :W0)             ("PEXT"                 3 (G y)  (B y)  (E y)))
	  ((:v :0F38 :NDS :LZ :F3 :W1)             ("PEXT"                 3 (G y)  (B y)  (E y))))
    (#xF6 ((:v :0F38 :NDD :LZ :F2 :W0)             ("MULX"                 3 (B y)  (G y)  (:rDX)  (E y)))
	  ((:v :0F38 :NDD :LZ :F2 :W1)             ("MULX"                 3 (B y)  (G y)  (:rDX)  (E y))))
    (#xF7 ((:v :0F38 :NDS :LZ :W0)                 ("BEXTR"                3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :W1)                 ("BEXTR"                3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :F3 :W0)             ("SARX"                 3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :F3 :W1)             ("SARX"                 3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :66 :W0)             ("SHLX"                 3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :66 :W1)             ("SHLX"                 3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :F2 :W0)             ("SHRX"                 3 (G y)  (E y)  (B y)))
	  ((:v :0F38 :NDS :LZ :F2 :W1)             ("SHRX"                 3 (G y)  (E y)  (B y))))))

(defconst *vex-0F3A-opcodes*
  '((#x0 ((:v :0F3A :256 :66 :W1)                  ("VPERMQ"               3 (V qq)  (W qq)  (I b))))
    (#x1 ((:v :0F3A :256 :66 :W1)                  ("VPERMPD"              3 (V qq)  (W qq)  (I b))))
    (#x2 ((:v :0F3A :NDS :128 :66 :W0)             ("VPBLENDD"             4 (V x)   (H x)   (W x)  (I b)))
	 ((:v :0F3A :NDS :256 :66 :W0)             ("VPBLENDD"             4 (V x)   (H x)   (W x)  (I b))))
    (#x4 ((:v :0F3A :128 :66 :W0)                  ("VPERMILPS"            3 (V x) (H x) (W x)))
	 ((:v :0F3A :256 :66 :W0)                  ("VPERMILPS"            3 (V x) (H x) (W x))))
    (#x5 ((:v :0F3A :128 :66 :W0)                  ("VPERMILPD"            3 (V x) (H x) (W x)))
	 ((:v :0F3A :256 :66 :W0)                  ("VPERMILPD"            3 (V x) (H x) (W x))))
    (#x6 ((:v :0F3A :NDS :256 :66 :W0)             ("VPERM2F128"           4 (V qq) (H qq) (W qq) (I b))))
    (#x8 ((:v :0F3A :128 :66 :WIG)                 ("VROUNDPS"             3 (V x)  (W x)  (I b)))
	 ((:v :0F3A :256 :66 :WIG)                 ("VROUNDPS"             3 (V x)  (W x)  (I b))))
    (#x9 ((:v :0F3A :128 :66 :WIG)                 ("VROUNDPD"             3 (V x)  (W x)  (I b)))
	 ((:v :0F3A :256 :66 :WIG)                 ("VROUNDPD"             3 (V x)  (W x)  (I b))))
    (#xA ((:v :0F3A :NDS :LIG :66 :WIG)            ("VROUNDSS"             3 (V ss) (W ss) (I b))))
    (#xB ((:v :0F3A :NDS :LIG :66 :WIG)            ("VROUNDSD"             3 (V sd) (W sd) (I b))))
    (#xC ((:v :0F3A :NDS :128 :66 :WIG)            ("VBLENDPS"             4 (V x)  (H x)  (W x) (I b)))
	 ((:v :0F3A :NDS :256 :66 :WIG)            ("VBLENDPS"             4 (V x)  (H x)  (W x) (I b))))
    (#xD ((:v :0F3A :NDS :128 :66 :WIG)            ("VBLENDPD"             4 (V x)  (H x)  (W x) (I b)))
	 ((:v :0F3A :NDS :256 :66 :WIG)            ("VBLENDPD"             4 (V x)  (H x)  (W x) (I b))))
    (#xE ((:v :0F3A :NDS :128 :66 :WIG)            ("VPBLENDW"             4 (V x)  (H x)  (W x) (I b)))
	 ((:v :0F3A :NDS :256 :66 :WIG)            ("VPBLENDW"             4 (V x)  (H x)  (W x) (I b))))
    (#xF ((:v :0F3A :NDS :128 :66 :WIG)            ("VPALIGNR"             4 (V x)  (H x)  (W x) (I b)))
	 ((:v :0F3A :NDS :256 :66 :WIG)            ("VPALIGNR"             4 (V x)  (H x)  (W x) (I b))))
    (#x14 ((:v :0F3A :128 :66 :W0)                 ("VPEXTRB"              3 (R d)  (V dq)  (I b))))
    (#x15 ((:v :0F3A :128 :66 :W0)                 ("VPEXTRW"              3 (G d)   (U dq) (I b))))
    (#x16 ((:v :0F3A :128 :66 :W0)                 ("VPEXTRD"              3 (E y)  (V dq)  (I b)))
	  ((:v :0F3A :128 :66 :W1)                 ("VPEXTRQ"              3 (E y)  (V dq)  (I b))))
    (#x17 ((:v :0F3A :128 :66 :WIG)                ("VEXTRACTPS"           3 (E d)  (V dq)  (I b))))
    (#x18 ((:v :0F3A :NDS :256 :66 :W0)            ("VINSERTF128"          4 (V qq) (H qq) (W qq) (I b))))
    (#x19 ((:v :0F3A :256 :66 :W0)                 ("VEXTRACTF128"         3 (W dq) (V qq) (I b))))
    (#x1D ((:v :0F3A :128 :66 :W0)                 ("VCVTPS2PH"            3 (W x)  (V x)  (I b)))
	  ((:v :0F3A :256 :66 :W0)                 ("VCVTPS2PH"            3 (W x)  (V x)  (I b))))
    (#x20 ((:v :0F3A :NDS :128 :66 :W0)            ("VPINSRB"              4 (V dq) (H dq) (R y)  (I b))))
    (#x21 ((:v :0F3A :NDS :128 :66 :WIG)      (:ALT
					       (   ("VINSERTPS"        4   (V dq) (H dq) (U dq) (I b))
						   ("VINSERTPS"        4   (V dq) (H dq) (M d) (I b))))))
    (#x22 ((:v :0F3A :NDS :128 :66 :W0)            ("VPINSRD"              4 (V dq) (H dq) (E y)  (I b)))
	  ((:v :0F3A :NDS :128 :66 :W1)            ("VPINSRQ"              4 (V dq) (H dq) (E y)  (I b))))
    (#x30 ((:v :0F3A :L0 :66 :W0 (:mod . #b11))    ("KSHIFTRB"             3 (K-reg b) (K-r/m b) (I b)))
	  ((:v :0F3A :L0 :66 :W1 (:mod . #b11))    ("KSHIFTRW"             3 (K-reg w) (K-r/m w) (I b))))
    (#x31 ((:v :0F3A :L0 :66 :W0 (:mod . #b11))    ("KSHIFTRD"             3 (K-reg d) (K-r/m d) (I b)))
	  ((:v :0F3A :L0 :66 :W1 (:mod . #b11))    ("KSHIFTRQ"             3 (K-reg q) (K-r/m q) (I b))))
    (#x32 ((:v :0F3A :L0 :66 :W0 (:mod . #b11))    ("KSHIFTLB"             3 (K-reg b) (K-r/m b) (I b)))
	  ((:v :0F3A :L0 :66 :W1 (:mod . #b11))    ("KSHIFTLW"             3 (K-reg w) (K-r/m w) (I b))))
    (#x33 ((:v :0F3A :L0 :66 :W0 (:mod . #b11))    ("KSHIFTLD"             3 (K-reg d) (K-r/m d) (I b)))
	  ((:v :0F3A :L0 :66 :W1 (:mod . #b11))    ("KSHIFTLQ"             3 (K-reg q) (K-r/m q) (I b))))
    (#x38 ((:v :0F3A :NDS :256 :66 :W0)            ("VINSERTI128"          4 (V qq) (H qq) (W qq) (I b))))     ;;  ib
    (#x39 ((:v :0F3A :256 :66 :W0)                 ("VEXTRACTI128"         3 (W dq) (V qq) (I b))))    ;;  ib
    (#x40 ((:v :0F3A :NDS :128 :66 :WIG)           ("VDPPS"                4 (V x)  (H x)  (W x)  (I b)))             ;;  ib
	  ((:v :0F3A :NDS :256 :66 :WIG)           ("VDPPS"                4 (V x)  (H x)  (W x)  (I b))))            ;;  ib
    (#x41 ((:v :0F3A :NDS :128 :66 :WIG)           ("VDPPD"                4 (V dq) (H dq) (W dq) (I b))))            ;;  ib
    (#x42 ((:v :0F3A :NDS :128 :66 :WIG)           ("VMPSADBW"             4 (V x)  (H x)  (W x)  (I b)))          ;;  ib
	  ((:v :0F3A :NDS :256 :66 :WIG)           ("VMPSADBW"             4 (V x)  (H x)  (W x)  (I b))))         ;;  ib
    (#x44 ((:v :0F3A :NDS :128 :66 :WIG)           ("VPCLMULQDQ"           4 (V dq) (H dq) (W dq) (I b))))       ;;  ib
    (#x46 ((:v :0F3A :NDS :256 :66 :W0)            ("VPERM2I128"           4 (V qq) (H qq) (W qq) (I b))))      ;;  ib
    (#x4A ((:v :0F3A :NDS :128 :66 :W0)            ("VBLENDVPS"            4 (V x)  (H x)  (W x)  (L x)))         ;;  /is4
	  ((:v :0F3A :NDS :256 :66 :W0)            ("VBLENDVPS"            4 (V x)  (H x)  (W x)  (L x))))        ;;  /is4
    (#x4B ((:v :0F3A :NDS :128 :66 :W0)            ("VBLENDVPD"            4 (V x)  (H x)  (W x)  (L x)))         ;;  /is4
	  ((:v :0F3A :NDS :256 :66 :W0)            ("VBLENDVPD"            4 (V x)  (H x)  (W x)  (L x))))        ;;  /is4
    (#x4C ((:v :0F3A :NDS :128 :66 :W0)            ("VPBLENDVB"            4 (V x)  (H x)  (W x)  (L x)))         ;;  /is4
	  ((:v :0F3A :NDS :256 :66 :W0)            ("VPBLENDVB"            4 (V x)  (H x)  (W x)  (L x))))        ;;  /is4
    (#x60 ((:v :0F3A :128 :66)                     ("VPCMPESTRM"           3 (V dq)  (W dq)  (I b))))       ;;  ib
    (#x61 ((:v :0F3A :128 :66)                     ("VPCMPESTRI"           3 (V dq)  (W dq)  (I b))))       ;;  ib
    (#x62 ((:v :0F3A :128 :66 :WIG)                ("VPCMPISTRM"           3 (V dq)  (W dq)  (I b))))       ;;  ib
    (#x63 ((:v :0F3A :128 :66 :WIG)                ("VPCMPISTRI"           3 (V dq)  (W dq)  (I b))))       ;;  ib
    (#xDF ((:v :0F3A :128 :66 :WIG)                ("AESKEYGENASSIST"      3 (V dq)  (W dq)  (I b)))) ;;  ib
    (#xF0 ((:v :0F3A :LZ :F2 :W0)                  ("RORX"                 3 (G y)  (E y)  (I b)))             ;;  ib
	  ((:v :0F3A :LZ :F2 :W1)                  ("RORX"                 3 (G y)  (E y)  (I b))))))

;; ----------------------------------------------------------------------

;; EVEX-encoded instructions:

(defconst *evex-0F-opcodes*
  '((#x10 ((:ev :0F :LIG :F2 :W1)                 "VMOVSD")                 ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VMOVSD")                 ;;
	  ((:ev :0F :LIG :F3 :W0)                 "VMOVSS")                 ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VMOVSS")                 ;;
	  ((:ev :0F :128 :66 :W1)                 "VMOVUPD")                ;;
	  ((:ev :0F :256 :66 :W1)                 "VMOVUPD")                ;;
	  ((:ev :0F :512 :66 :W1)                 "VMOVUPD")                ;;
	  ((:ev :0F :128 :W0)                     "VMOVUPS")                ;;
	  ((:ev :0F :256 :W0)                     "VMOVUPS")                ;;
	  ((:ev :0F :512 :W0)                     "VMOVUPS"))               ;;
    (#x11 ((:ev :0F :LIG :F2 :W1)                 "VMOVSD")                 ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VMOVSD")                 ;;
	  ((:ev :0F :LIG :F3 :W0)                 "VMOVSS")                 ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VMOVSS")                 ;;
	  ((:ev :0F :128 :66 :W1)                 "VMOVUPD")                ;;
	  ((:ev :0F :256 :66 :W1)                 "VMOVUPD")                ;;
	  ((:ev :0F :512 :66 :W1)                 "VMOVUPD")                ;;
	  ((:ev :0F :128 :W0)                     "VMOVUPS")                ;;
	  ((:ev :0F :256 :W0)                     "VMOVUPS")                ;;
	  ((:ev :0F :512 :W0)                     "VMOVUPS"))               ;;
    (#x12 ((:ev :0F :128 :F2 :W1)                 "VMOVDDUP")               ;;
	  ((:ev :0F :256 :F2 :W1)                 "VMOVDDUP")               ;;
	  ((:ev :0F :512 :F2 :W1)                 "VMOVDDUP")               ;;
	  ((:ev :0F :NDS :128 :W0)                "VMOVHLPS")               ;;
	  ((:ev :0F :NDS :128 :66 :W1)            "VMOVLPD")                ;;
	  ((:ev :0F :NDS :128 :W0)                "VMOVLPS")                ;;
	  ((:ev :0F :128 :F3 :W0)                 "VMOVSLDUP")              ;;
	  ((:ev :0F :256 :F3 :W0)                 "VMOVSLDUP")              ;;
	  ((:ev :0F :512 :F3 :W0)                 "VMOVSLDUP"))             ;;
    (#x13 ((:ev :0F :128 :66 :W1)                 "VMOVLPD")                ;;
	  ((:ev :0F :128 :W0)                     "VMOVLPS"))               ;;
    (#x14 ((:ev :0F :NDS :128 :66 :W1)            "VUNPCKLPD")              ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VUNPCKLPD")              ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VUNPCKLPD")              ;;
	  ((:ev :0F :NDS :128 :W0)                "VUNPCKLPS")              ;;
	  ((:ev :0F :NDS :256 :W0)                "VUNPCKLPS")              ;;
	  ((:ev :0F :NDS :512 :W0)                "VUNPCKLPS"))             ;;
    (#x15 ((:ev :0F :NDS :128 :66 :W1)            "VUNPCKHPD")              ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VUNPCKHPD")              ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VUNPCKHPD")              ;;
	  ((:ev :0F :NDS :128 :W0)                "VUNPCKHPS")              ;;
	  ((:ev :0F :NDS :256 :W0)                "VUNPCKHPS")              ;;
	  ((:ev :0F :NDS :512 :W0)                "VUNPCKHPS"))             ;;
    (#x16 ((:ev :0F :NDS :128 :66 :W1)            "VMOVHPD")                ;;
	  ((:ev :0F :NDS :128 :W0)                "VMOVHPS")                ;;
	  ((:ev :0F :NDS :128 :W0)                "VMOVLHPS")               ;;
	  ((:ev :0F :128 :F3 :W0)                 "VMOVSHDUP")              ;;
	  ((:ev :0F :256 :F3 :W0)                 "VMOVSHDUP")              ;;
	  ((:ev :0F :512 :F3 :W0)                 "VMOVSHDUP"))             ;;
    (#x17 ((:ev :0F :128 :66 :W1)                 "VMOVHPD")                ;;
	  ((:ev :0F :128 :W0)                     "VMOVHPS"))               ;;
    (#x28 ((:ev :0F :128 :66 :W1)                 "VMOVAPD")                ;;
	  ((:ev :0F :256 :66 :W1)                 "VMOVAPD")                ;;
	  ((:ev :0F :512 :66 :W1)                 "VMOVAPD")                ;;
	  ((:ev :0F :128 :W0)                     "VMOVAPS")                ;;
	  ((:ev :0F :256 :W0)                     "VMOVAPS")                ;;
	  ((:ev :0F :512 :W0)                     "VMOVAPS"))               ;;
    (#x29 ((:ev :0F :128 :66 :W1)                 "VMOVAPD")                ;;
	  ((:ev :0F :256 :66 :W1)                 "VMOVAPD")                ;;
	  ((:ev :0F :512 :66 :W1)                 "VMOVAPD")                ;;
	  ((:ev :0F :128 :W0)                     "VMOVAPS")                ;;
	  ((:ev :0F :256 :W0)                     "VMOVAPS")                ;;
	  ((:ev :0F :512 :W0)                     "VMOVAPS"))               ;;
    (#x2A ((:ev :0F :NDS :LIG :F2 :W0)            "VCVTSI2SD")              ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VCVTSI2SD")              ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VCVTSI2SS")              ;;
	  ((:ev :0F :NDS :LIG :F3 :W1)            "VCVTSI2SS"))             ;;
    (#x2B ((:ev :0F :128 :66 :W1)                 "VMOVNTPD")               ;;
	  ((:ev :0F :256 :66 :W1)                 "VMOVNTPD")               ;;
	  ((:ev :0F :512 :66 :W1)                 "VMOVNTPD")               ;;
	  ((:ev :0F :128 :W0)                     "VMOVNTPS")               ;;
	  ((:ev :0F :256 :W0)                     "VMOVNTPS")               ;;
	  ((:ev :0F :512 :W0)                     "VMOVNTPS"))              ;;
    (#x2C ((:ev :0F :LIG :F2 :W0)                 "VCVTTSD2SI")             ;;
	  ((:ev :0F :LIG :F2 :W1)                 "VCVTTSD2SI")             ;;
	  ((:ev :0F :LIG :F3 :W0)                 "VCVTTSS2SI")             ;;
	  ((:ev :0F :LIG :F3 :W1)                 "VCVTTSS2SI"))            ;;
    (#x2D ((:ev :0F :LIG :F2 :W0)                 "VCVTSD2SI")              ;;
	  ((:ev :0F :LIG :F2 :W1)                 "VCVTSD2SI")              ;;
	  ((:ev :0F :LIG :F3 :W0)                 "VCVTSS2SI")              ;;
	  ((:ev :0F :LIG :F3 :W1)                 "VCVTSS2SI"))             ;;
    (#x2E ((:ev :0F :LIG :66 :W1)                 "VUCOMISD")               ;;
	  ((:ev :0F :LIG :W0)                     "VUCOMISS"))              ;;
    (#x2F ((:ev :0F :LIG :66 :W1)                 "VCOMISD")                ;;
	  ((:ev :0F :LIG :W0)                     "VCOMISS"))               ;;
    (#x51 ((:ev :0F :128 :66 :W1)                 "VSQRTPD")                ;;
	  ((:ev :0F :256 :66 :W1)                 "VSQRTPD")                ;;
	  ((:ev :0F :512 :66 :W1)                 "VSQRTPD")                ;;
	  ((:ev :0F :128 :W0)                     "VSQRTPS")                ;;
	  ((:ev :0F :256 :W0)                     "VSQRTPS")                ;;
	  ((:ev :0F :512 :W0)                     "VSQRTPS")                ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VSQRTSD")                ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VSQRTSS"))               ;;
    (#x54 ((:ev :0F :NDS :128 :66 :W1)            "VANDPD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VANDPD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VANDPD")                 ;;
	  ((:ev :0F :NDS :128 :W0)                "VANDPS")                 ;;
	  ((:ev :0F :NDS :256 :W0)                "VANDPS")                 ;;
	  ((:ev :0F :NDS :512 :W0)                "VANDPS"))                ;;
    (#x55 ((:ev :0F :NDS :128 :66 :W1)            "VANDNPD")                ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VANDNPD")                ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VANDNPD")                ;;
	  ((:ev :0F :NDS :128 :W0)                "VANDNPS")                ;;
	  ((:ev :0F :NDS :256 :W0)                "VANDNPS")                ;;
	  ((:ev :0F :NDS :512 :W0)                "VANDNPS"))               ;;
    (#x56 ((:ev :0F :NDS :128 :66 :W1)            "VORPD")                  ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VORPD")                  ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VORPD")                  ;;
	  ((:ev :0F :NDS :128 :W0)                "VORPS")                  ;;
	  ((:ev :0F :NDS :256 :W0)                "VORPS")                  ;;
	  ((:ev :0F :NDS :512 :W0)                "VORPS"))                 ;;
    (#x57 ((:ev :0F :NDS :128 :66 :W1)            "VXORPD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VXORPD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VXORPD")                 ;;
	  ((:ev :0F :NDS :128 :W0)                "VXORPS")                 ;;
	  ((:ev :0F :NDS :256 :W0)                "VXORPS")                 ;;
	  ((:ev :0F :NDS :512 :W0)                "VXORPS"))                ;;
    (#x58 ((:ev :0F :NDS :128 :66 :W1)            "VADDPD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VADDPD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VADDPD")                 ;;
	  ((:ev :0F :NDS :128 :W0)                "VADDPS")                 ;;
	  ((:ev :0F :NDS :256 :W0)                "VADDPS")                 ;;
	  ((:ev :0F :NDS :512 :W0)                "VADDPS")                 ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VADDSD")                 ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VADDSS"))                ;;
    (#x59 ((:ev :0F :NDS :128 :66 :W1)            "VMULPD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VMULPD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VMULPD")                 ;;
	  ((:ev :0F :NDS :128 :W0)                "VMULPS")                 ;;
	  ((:ev :0F :NDS :256 :W0)                "VMULPS")                 ;;
	  ((:ev :0F :NDS :512 :W0)                "VMULPS")                 ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VMULSD")                 ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VMULSS"))                ;;
    (#x5A ((:ev :0F :128 :66 :W1)                 "VCVTPD2PS")              ;;
	  ((:ev :0F :256 :66 :W1)                 "VCVTPD2PS")              ;;
	  ((:ev :0F :512 :66 :W1)                 "VCVTPD2PS")              ;;
	  ((:ev :0F :128 :W0)                     "VCVTPS2PD")              ;;
	  ((:ev :0F :256 :W0)                     "VCVTPS2PD")              ;;
	  ((:ev :0F :512 :W0)                     "VCVTPS2PD")              ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VCVTSD2SS")              ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VCVTSS2SD"))             ;;
    (#x5B ((:ev :0F :128 :W0)                     "VCVTDQ2PS")              ;;
	  ((:ev :0F :256 :W0)                     "VCVTDQ2PS")              ;;
	  ((:ev :0F :512 :W0)                     "VCVTDQ2PS")              ;;
	  ((:ev :0F :128 :66 :W0)                 "VCVTPS2DQ")              ;;
	  ((:ev :0F :256 :66 :W0)                 "VCVTPS2DQ")              ;;
	  ((:ev :0F :512 :66 :W0)                 "VCVTPS2DQ")              ;;
	  ((:ev :0F :128 :W1)                     "VCVTQQ2PS")              ;;
	  ((:ev :0F :256 :W1)                     "VCVTQQ2PS")              ;;
	  ((:ev :0F :512 :W1)                     "VCVTQQ2PS")              ;;
	  ((:ev :0F :128 :F3 :W0)                 "VCVTTPS2DQ")             ;;
	  ((:ev :0F :256 :F3 :W0)                 "VCVTTPS2DQ")             ;;
	  ((:ev :0F :512 :F3 :W0)                 "VCVTTPS2DQ"))            ;;
    (#x5C ((:ev :0F :NDS :128 :66 :W1)            "VSUBPD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VSUBPD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VSUBPD")                 ;;
	  ((:ev :0F :NDS :128 :W0)                "VSUBPS")                 ;;
	  ((:ev :0F :NDS :256 :W0)                "VSUBPS")                 ;;
	  ((:ev :0F :NDS :512 :W0)                "VSUBPS")                 ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VSUBSD")                 ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VSUBSS"))                ;;
    (#x5D ((:ev :0F :NDS :128 :66 :W1)            "VMINPD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VMINPD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VMINPD")                 ;;
	  ((:ev :0F :NDS :128 :W0)                "VMINPS")                 ;;
	  ((:ev :0F :NDS :256 :W0)                "VMINPS")                 ;;
	  ((:ev :0F :NDS :512 :W0)                "VMINPS")                 ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VMINSD")                 ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VMINSS"))                ;;
    (#x5E ((:ev :0F :NDS :128 :66 :W1)            "VDIVPD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VDIVPD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VDIVPD")                 ;;
	  ((:ev :0F :NDS :128 :W0)                "VDIVPS")                 ;;
	  ((:ev :0F :NDS :256 :W0)                "VDIVPS")                 ;;
	  ((:ev :0F :NDS :512 :W0)                "VDIVPS")                 ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VDIVSD")                 ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VDIVSS"))                ;;
    (#x5F ((:ev :0F :NDS :128 :66 :W1)            "VMAXPD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VMAXPD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VMAXPD")                 ;;
	  ((:ev :0F :NDS :128 :W0)                "VMAXPS")                 ;;
	  ((:ev :0F :NDS :256 :W0)                "VMAXPS")                 ;;
	  ((:ev :0F :NDS :512 :W0)                "VMAXPS")                 ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VMAXSD")                 ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VMAXSS"))                ;;
    (#x60 ((:ev :0F :NDS :128 :66 :WIG)           "VPUNPCKLBW")             ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPUNPCKLBW")             ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPUNPCKLBW"))            ;;
    (#x61 ((:ev :0F :NDS :128 :66 :WIG)           "VPUNPCKLWD")             ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPUNPCKLWD")             ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPUNPCKLWD"))            ;;
    (#x62 ((:ev :0F :NDS :128 :66 :W0)            "VPUNPCKLDQ")             ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPUNPCKLDQ")             ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPUNPCKLDQ"))            ;;
    (#x63 ((:ev :0F :NDS :128 :66 :WIG)           "VPACKSSWB")              ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPACKSSWB")              ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPACKSSWB"))             ;;
    (#x64 ((:ev :0F :NDS :128 :66 :WIG)           "VPCMPGTB")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPCMPGTB")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPCMPGTB"))              ;;
    (#x65 ((:ev :0F :NDS :128 :66 :WIG)           "VPCMPGTW")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPCMPGTW")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPCMPGTW"))              ;;
    (#x66 ((:ev :0F :NDS :128 :66 :W0)            "VPCMPGTD")               ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPCMPGTD")               ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPCMPGTD"))              ;;
    (#x67 ((:ev :0F :NDS :128 :66 :WIG)           "VPACKUSWB")              ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPACKUSWB")              ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPACKUSWB"))             ;;
    (#x68 ((:ev :0F :NDS :128 :66 :WIG)           "VPUNPCKHBW")             ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPUNPCKHBW")             ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPUNPCKHBW"))            ;;
    (#x69 ((:ev :0F :NDS :128 :66 :WIG)           "VPUNPCKHWD")             ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPUNPCKHWD")             ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPUNPCKHWD"))            ;;
    (#x6A ((:ev :0F :NDS :128 :66 :W0)            "VPUNPCKHDQ")             ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPUNPCKHDQ")             ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPUNPCKHDQ"))            ;;
    (#x6B ((:ev :0F :NDS :128 :66 :W0)            "VPACKSSDW")              ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPACKSSDW")              ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPACKSSDW"))             ;;
    (#x6C ((:ev :0F :NDS :128 :66 :W1)            "VPUNPCKLQDQ")            ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPUNPCKLQDQ")            ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPUNPCKLQDQ"))           ;;
    (#x6D ((:ev :0F :NDS :128 :66 :W1)            "VPUNPCKHQDQ")            ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPUNPCKHQDQ")            ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPUNPCKHQDQ"))           ;;
    (#x6E ((:ev :0F :128 :66 :W0)                 "VMOVD")                  ;;
	  ((:ev :0F :128 :66 :W1)                 "VMOVQ"))                 ;;
    (#x6F ((:ev :0F :128 :66 :W0)                 "VMOVDQA32")              ;;
	  ((:ev :0F :256 :66 :W0)                 "VMOVDQA32")              ;;
	  ((:ev :0F :512 :66 :W0)                 "VMOVDQA32")              ;;
	  ((:ev :0F :128 :66 :W1)                 "VMOVDQA64")              ;;
	  ((:ev :0F :256 :66 :W1)                 "VMOVDQA64")              ;;
	  ((:ev :0F :512 :66 :W1)                 "VMOVDQA64")              ;;
	  ((:ev :0F :128 :F2 :W1)                 "VMOVDQU16")              ;;
	  ((:ev :0F :256 :F2 :W1)                 "VMOVDQU16")              ;;
	  ((:ev :0F :512 :F2 :W1)                 "VMOVDQU16")              ;;
	  ((:ev :0F :128 :F3 :W0)                 "VMOVDQU32")              ;;
	  ((:ev :0F :256 :F3 :W0)                 "VMOVDQU32")              ;;
	  ((:ev :0F :512 :F3 :W0)                 "VMOVDQU32")              ;;
	  ((:ev :0F :128 :F3 :W1)                 "VMOVDQU64")              ;;
	  ((:ev :0F :256 :F3 :W1)                 "VMOVDQU64")              ;;
	  ((:ev :0F :512 :F3 :W1)                 "VMOVDQU64")              ;;
	  ((:ev :0F :128 :F2 :W0)                 "VMOVDQU8")               ;;
	  ((:ev :0F :256 :F2 :W0)                 "VMOVDQU8")               ;;
	  ((:ev :0F :512 :F2 :W0)                 "VMOVDQU8"))              ;;
    (#x70 ((:ev :0F :128 :66 :W0)                 "VPSHUFD")                ;;  ib
	  ((:ev :0F :256 :66 :W0)                 "VPSHUFD")                ;;  ib
	  ((:ev :0F :512 :66 :W0)                 "VPSHUFD")                ;;  ib
	  ((:ev :0F :128 :F3 :WIG)                "VPSHUFHW")               ;;  ib
	  ((:ev :0F :256 :F3 :WIG)                "VPSHUFHW")               ;;  ib
	  ((:ev :0F :512 :F3 :WIG)                "VPSHUFHW")               ;;  ib
	  ((:ev :0F :128 :F2 :WIG)                "VPSHUFLW")               ;;  ib
	  ((:ev :0F :256 :F2 :WIG)                "VPSHUFLW")               ;;  ib
	  ((:ev :0F :512 :F2 :WIG)                "VPSHUFLW"))              ;;  ib
    (#x71 ((:ev :0F :NDD :128 :66 :WIG (:REG . 2)) "VPSRLW")                ;; /2 ib
	  ((:ev :0F :NDD :256 :66 :WIG (:REG . 2)) "VPSRLW")                ;;  /2 ib
	  ((:ev :0F :NDD :512 :66 :WIG (:REG . 2)) "VPSRLW")                ;;  /2 ib
	  ((:ev :0F :NDD :128 :66 :WIG (:REG . 4)) "VPSRAW")                ;;  /4 ib
	  ((:ev :0F :NDD :256 :66 :WIG (:REG . 4)) "VPSRAW")                ;;  /4 ib
	  ((:ev :0F :NDD :512 :66 :WIG (:REG . 4)) "VPSRAW")                ;;  /4 ib
	  ((:ev :0F :NDD :128 :66 :WIG (:REG . 6)) "VPSLLW")                ;;  /6 ib
	  ((:ev :0F :NDD :256 :66 :WIG (:REG . 6)) "VPSLLW")                ;;  /6 ib
	  ((:ev :0F :NDD :512 :66 :WIG (:REG . 6)) "VPSLLW"))               ;;  /6 ib
    (#x72 ((:ev :0F :NDD :128 :66 :W0 (:REG . 0)) "VPRORD")                 ;;  /0 ib
	  ((:ev :0F :NDD :128 :66 :W1 (:REG . 0)) "VPRORD")                 ;;  /0 ib
	  ((:ev :0F :NDD :256 :66 :W0 (:REG . 0)) "VPRORD")                 ;;  /0 ib
	  ((:ev :0F :NDD :256 :66 :W1 (:REG . 0)) "VPRORD")                 ;;  /0 ib
	  ((:ev :0F :NDD :512 :66 :W0 (:REG . 0)) "VPRORD")                 ;;  /0 ib
	  ((:ev :0F :NDD :512 :66 :W1 (:REG . 0)) "VPRORD")                 ;;  /0 ib
	  ((:ev :0F :NDD :128 :66 :W0 (:REG . 0)) "VPROLD")                 ;;  /1 ib
	  ((:ev :0F :NDD :128 :66 :W1 (:REG . 1)) "VPROLD")                 ;;  /1 ib
	  ((:ev :0F :NDD :256 :66 :W0 (:REG . 1)) "VPROLD")                 ;;  /1 ib
	  ((:ev :0F :NDD :256 :66 :W1 (:REG . 1)) "VPROLD")                 ;;  /1 ib
	  ((:ev :0F :NDD :512 :66 :W0 (:REG . 1)) "VPROLD")                 ;;  /1 ib
	  ((:ev :0F :NDD :512 :66 :W1 (:REG . 1)) "VPROLD")                 ;;  /1 ib
	  ((:ev :0F :NDD :128 :66 :W0 (:REG . 2)) "VPSRLD")                 ;;  /2 ib
	  ((:ev :0F :NDD :256 :66 :W0 (:REG . 2)) "VPSRLD")                 ;;  /2 ib
	  ((:ev :0F :NDD :512 :66 :W0 (:REG . 2)) "VPSRLD")                 ;;  /2 ib
	  ((:ev :0F :NDD :128 :66 :W0 (:REG . 4)) "VPSRAD")                 ;;  /4 ib
	  ((:ev :0F :NDD :128 :66 :W1 (:REG . 4)) "VPSRAD")                 ;;  /4 ib
	  ((:ev :0F :NDD :256 :66 :W0 (:REG . 4)) "VPSRAD")                 ;;  /4 ib
	  ((:ev :0F :NDD :256 :66 :W1 (:REG . 4)) "VPSRAD")                 ;;  /4 ib
	  ((:ev :0F :NDD :512 :66 :W0 (:REG . 4)) "VPSRAD")                 ;;  /4 ib
	  ((:ev :0F :NDD :512 :66 :W1 (:REG . 4)) "VPSRAD")                 ;;  /4 ib
	  ((:ev :0F :NDD :128 :66 :W0 (:REG . 6)) "VPSLLD")                 ;;  /6 ib
	  ((:ev :0F :NDD :256 :66 :W0 (:REG . 6)) "VPSLLD")                 ;;  /6 ib
	  ((:ev :0F :NDD :512 :66 :W0 (:REG . 6)) "VPSLLD"))                ;;  /6 ib
    (#x73 ((:ev :0F :NDD :128 :66 :W1 (:REG . 2)) "VPSRLQ")                 ;;  /2 ib
	  ((:ev :0F :NDD :256 :66 :W1 (:REG . 2)) "VPSRLQ")                 ;;  /2 ib
	  ((:ev :0F :NDD :512 :66 :W1 (:REG . 2)) "VPSRLQ")                 ;;  /2 ib
	  ((:ev :0F :NDD :128 :66 :WIG (:REG . 3)) "VPSRLDQ")               ;;  /3 ib
	  ((:ev :0F :NDD :256 :66 :WIG (:REG . 3)) "VPSRLDQ")               ;;  /3 ib
	  ((:ev :0F :NDD :512 :66 :WIG (:REG . 3)) "VPSRLDQ")               ;;  /3 ib
	  ((:ev :0F :NDD :128 :66 :W1 (:REG . 6)) "VPSLLQ")                 ;;  /6 ib
	  ((:ev :0F :NDD :256 :66 :W1 (:REG . 6)) "VPSLLQ")                 ;;  /6 ib
	  ((:ev :0F :NDD :512 :66 :W1 (:REG . 6)) "VPSLLQ")                 ;;  /6 ib
	  ((:ev :0F :NDD :128 :66 :WIG (:REG . 7)) "VPSLLDQ")               ;;  /7 ib
	  ((:ev :0F :NDD :256 :66 :WIG (:REG . 7)) "VPSLLDQ")               ;;  /7 ib
	  ((:ev :0F :NDD :512 :66 :WIG (:REG . 7)) "VPSLLDQ"))              ;;  /7 ib
    (#x74 ((:ev :0F :NDS :128 :66 :WIG)           "VPCMPEQB")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPCMPEQB")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPCMPEQB"))              ;;
    (#x75 ((:ev :0F :NDS :128 :66 :WIG)           "VPCMPEQW")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPCMPEQW")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPCMPEQW"))              ;;
    (#x76 ((:ev :0F :NDS :128 :66 :W0)            "VPCMPEQD")               ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPCMPEQD")               ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPCMPEQD"))              ;;
    (#x78 ((:ev :0F :256 :W1)                     "VCVTTPD2UDQ")            ;;  02
	  ((:ev :0F :128 :W1)                     "VCVTTPD2UDQ")            ;;
	  ((:ev :0F :512 :W1)                     "VCVTTPD2UDQ")            ;;
	  ((:ev :0F :128 :66 :W1)                 "VCVTTPD2UQQ")            ;;
	  ((:ev :0F :256 :66 :W1)                 "VCVTTPD2UQQ")            ;;
	  ((:ev :0F :512 :66 :W1)                 "VCVTTPD2UQQ")            ;;
	  ((:ev :0F :128 :W0)                     "VCVTTPS2UDQ")            ;;
	  ((:ev :0F :256 :W0)                     "VCVTTPS2UDQ")            ;;
	  ((:ev :0F :512 :W0)                     "VCVTTPS2UDQ")            ;;
	  ((:ev :0F :128 :66 :W0)                 "VCVTTPS2UQQ")            ;;
	  ((:ev :0F :256 :66 :W0)                 "VCVTTPS2UQQ")            ;;
	  ((:ev :0F :512 :66 :W0)                 "VCVTTPS2UQQ")            ;;
	  ((:ev :0F :LIG :F2 :W0)                 "VCVTTSD2USI")            ;;
	  ((:ev :0F :LIG :F2 :W1)                 "VCVTTSD2USI")            ;;
	  ((:ev :0F :LIG :F3 :W0)                 "VCVTTSS2USI")            ;;
	  ((:ev :0F :LIG :F3 :W1)                 "VCVTTSS2USI"))           ;;
    (#x79 ((:ev :0F :128 :W1)                     "VCVTPD2UDQ")             ;;
	  ((:ev :0F :256 :W1)                     "VCVTPD2UDQ")             ;;
	  ((:ev :0F :512 :W1)                     "VCVTPD2UDQ")             ;;
	  ((:ev :0F :128 :66 :W1)                 "VCVTPD2UQQ")             ;;
	  ((:ev :0F :256 :66 :W1)                 "VCVTPD2UQQ")             ;;
	  ((:ev :0F :512 :66 :W1)                 "VCVTPD2UQQ")             ;;
	  ((:ev :0F :128 :W0)                     "VCVTPS2UDQ")             ;;
	  ((:ev :0F :256 :W0)                     "VCVTPS2UDQ")             ;;
	  ((:ev :0F :512 :W0)                     "VCVTPS2UDQ")             ;;
	  ((:ev :0F :128 :66 :W0)                 "VCVTPS2UQQ")             ;;
	  ((:ev :0F :256 :66 :W0)                 "VCVTPS2UQQ")             ;;
	  ((:ev :0F :512 :66 :W0)                 "VCVTPS2UQQ")             ;;
	  ((:ev :0F :LIG :F2 :W0)                 "VCVTSD2USI")             ;;
	  ((:ev :0F :LIG :F2 :W1)                 "VCVTSD2USI")             ;;
	  ((:ev :0F :LIG :F3 :W0)                 "VCVTSS2USI")             ;;
	  ((:ev :0F :LIG :F3 :W1)                 "VCVTSS2USI"))            ;;
    (#x7A ((:ev :0F :128 :66 :W1)                 "VCVTTPD2QQ")             ;;
	  ((:ev :0F :256 :66 :W1)                 "VCVTTPD2QQ")             ;;
	  ((:ev :0F :512 :66 :W1)                 "VCVTTPD2QQ")             ;;
	  ((:ev :0F :128 :66 :W0)                 "VCVTTPS2QQ")             ;;
	  ((:ev :0F :256 :66 :W0)                 "VCVTTPS2QQ")             ;;
	  ((:ev :0F :512 :66 :W0)                 "VCVTTPS2QQ")             ;;
	  ((:ev :0F :128 :F3 :W0)                 "VCVTUDQ2PD")             ;;
	  ((:ev :0F :256 :F3 :W0)                 "VCVTUDQ2PD")             ;;
	  ((:ev :0F :512 :F3 :W0)                 "VCVTUDQ2PD")             ;;
	  ((:ev :0F :128 :F2 :W0)                 "VCVTUDQ2PS")             ;;
	  ((:ev :0F :256 :F2 :W0)                 "VCVTUDQ2PS")             ;;
	  ((:ev :0F :512 :F2 :W0)                 "VCVTUDQ2PS")             ;;
	  ((:ev :0F :128 :F3 :W1)                 "VCVTUQQ2PD")             ;;
	  ((:ev :0F :256 :F3 :W1)                 "VCVTUQQ2PD")             ;;
	  ((:ev :0F :512 :F3 :W1)                 "VCVTUQQ2PD")             ;;
	  ((:ev :0F :128 :F2 :W1)                 "VCVTUQQ2PS")             ;;
	  ((:ev :0F :256 :F2 :W1)                 "VCVTUQQ2PS")             ;;
	  ((:ev :0F :512 :F2 :W1)                 "VCVTUQQ2PS"))            ;;
    (#x7B ((:ev :0F :128 :66 :W1)                 "VCVTPD2QQ")              ;;
	  ((:ev :0F :256 :66 :W1)                 "VCVTPD2QQ")              ;;
	  ((:ev :0F :512 :66 :W1)                 "VCVTPD2QQ")              ;;
	  ((:ev :0F :128 :66 :W0)                 "VCVTPS2QQ")              ;;
	  ((:ev :0F :256 :66 :W0)                 "VCVTPS2QQ")              ;;
	  ((:ev :0F :512 :66 :W0)                 "VCVTPS2QQ")              ;;
	  ((:ev :0F :NDS :LIG :F2 :W0)            "VCVTUSI2SD")             ;;
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VCVTUSI2SD")             ;;
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VCVTUSI2SS")             ;;
	  ((:ev :0F :NDS :LIG :F3 :W1)            "VCVTUSI2SS"))            ;;
    (#x7E ((:ev :0F :128 :66 :W0)                 "VMOVD")                  ;;
	  ((:ev :0F :128 :66 :W1)                 "VMOVQ")                  ;;
	  ((:ev :0F :128 :F3 :W1)                 "VMOVQ"))                 ;;
    (#x7F ((:ev :0F :128 :66 :W0)                 "VMOVDQA32")              ;;
	  ((:ev :0F :256 :66 :W0)                 "VMOVDQA32")              ;;
	  ((:ev :0F :512 :66 :W0)                 "VMOVDQA32")              ;;
	  ((:ev :0F :128 :66 :W1)                 "VMOVDQA64")              ;;
	  ((:ev :0F :256 :66 :W1)                 "VMOVDQA64")              ;;
	  ((:ev :0F :512 :66 :W1)                 "VMOVDQA64")              ;;
	  ((:ev :0F :128 :F2 :W1)                 "VMOVDQU16")              ;;
	  ((:ev :0F :256 :F2 :W1)                 "VMOVDQU16")              ;;
	  ((:ev :0F :512 :F2 :W1)                 "VMOVDQU16")              ;;
	  ((:ev :0F :128 :F3 :W0)                 "VMOVDQU32")              ;;
	  ((:ev :0F :256 :F3 :W0)                 "VMOVDQU32")              ;;
	  ((:ev :0F :512 :F3 :W0)                 "VMOVDQU32")              ;;
	  ((:ev :0F :128 :F3 :W1)                 "VMOVDQU64")              ;;
	  ((:ev :0F :256 :F3 :W1)                 "VMOVDQU64")              ;;
	  ((:ev :0F :512 :F3 :W1)                 "VMOVDQU64")              ;;
	  ((:ev :0F :128 :F2 :W0)                 "VMOVDQU8")               ;;
	  ((:ev :0F :256 :F2 :W0)                 "VMOVDQU8")               ;;
	  ((:ev :0F :512 :F2 :W0)                 "VMOVDQU8"))              ;;
    (#xC2 ((:ev :0F :NDS :128 :66 :W1)            "VCMPPD")                 ;;  ib
	  ((:ev :0F :NDS :256 :66 :W1)            "VCMPPD")                 ;;  ib
	  ((:ev :0F :NDS :512 :66 :W1)            "VCMPPD")                 ;;  ib
	  ((:ev :0F :NDS :128 :W0)                "VCMPPS")                 ;;  ib
	  ((:ev :0F :NDS :256 :W0)                "VCMPPS")                 ;;  ib
	  ((:ev :0F :NDS :512 :W0)                "VCMPPS")                 ;;  ib
	  ((:ev :0F :NDS :LIG :F2 :W1)            "VCMPSD")                 ;;  ib
	  ((:ev :0F :NDS :LIG :F3 :W0)            "VCMPSS"))                ;;  ib
    (#xC4 ((:ev :0F :NDS :128 :66 :WIG)           "VPINSRW"))               ;;  ib
    (#xC5 ((:ev :0F :128 :66 :WIG)                "VPEXTRW"))               ;;  ib
    (#xC6 ((:ev :0F :NDS :128 :66 :W1)            "VSHUFPD")                ;;  ib
	  ((:ev :0F :NDS :256 :66 :W1)            "VSHUFPD")                ;;  ib
	  ((:ev :0F :NDS :512 :66 :W1)            "VSHUFPD")                ;;  ib
	  ((:ev :0F :NDS :128 :W0)                "VSHUFPS")                ;;  ib
	  ((:ev :0F :NDS :256 :W0)                "VSHUFPS")                ;;  ib
	  ((:ev :0F :NDS :512 :W0)                "VSHUFPS"))               ;;  ib
    (#xD1 ((:ev :0F :NDS :128 :66 :WIG)           "VPSRLW")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSRLW")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSRLW"))                ;;
    (#xD2 ((:ev :0F :NDS :128 :66 :W0)            "VPSRLD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPSRLD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPSRLD"))                ;;
    (#xD3 ((:ev :0F :NDS :128 :66 :W1)            "VPSRLQ")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPSRLQ")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPSRLQ"))                ;;
    (#xD4 ((:ev :0F :NDS :512 :66 :W1)            "VPADDQ")                 ;;
	  ((:ev :0F :NDS :128 :66 :W1)            "VPADDQ")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPADDQ"))                ;;
    (#xD5 ((:ev :0F :NDS :128 :66 :WIG)           "VPMULLW")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPMULLW")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPMULLW"))               ;;
    (#xD6 ((:ev :0F :128 :66 :W1)                 "VMOVQ"))                 ;;
    (#xD8 ((:ev :0F :NDS :128 :66 :WIG)           "VPSUBUSB")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSUBUSB")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSUBUSB"))              ;;
    (#xD9 ((:ev :0F :NDS :128 :66 :WIG)           "VPSUBUSW")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSUBUSW")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSUBUSW"))              ;;
    (#xDA ((:ev :0F :NDS :128 :66)                "VPMINUB")                ;;
	  ((:ev :0F :NDS :256 :66)                "VPMINUB")                ;;
	  ((:ev :0F :NDS :512 :66)                "VPMINUB"))               ;;
    (#xDB ((:ev :0F :NDS :512 :66 :W0)            "VPANDD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPANDQ")                 ;;
	  ((:ev :0F :NDS :128 :66 :W0)            "VPANDD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPANDD")                 ;;
	  ((:ev :0F :NDS :128 :66 :W1)            "VPANDQ")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPANDQ"))                ;;
    (#xDC ((:ev :0F :NDS :128 :66 :WIG)           "VPADDUSB")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPADDUSB")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPADDUSB"))              ;;
    (#xDD ((:ev :0F :NDS :128 :66 :WIG)           "VPADDUSW")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPADDUSW")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPADDUSW"))              ;;
    (#xDE ((:ev :0F :NDS :128 :66 :WIG)           "VPMAXUB")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPMAXUB")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPMAXUB"))               ;;
    (#xDF ((:ev :0F :NDS :128 :66 :W0)            "VPANDND")                ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPANDND")                ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPANDND")                ;;
	  ((:ev :0F :NDS :128 :66 :W1)            "VPANDNQ")                ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPANDNQ")                ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPANDNQ"))               ;;
    (#xE0 ((:ev :0F :NDS :128 :66 :WIG)           "VPAVGB")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPAVGB")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPAVGB"))                ;;
    (#xE1 ((:ev :0F :NDS :128 :66 :WIG)           "VPSRAW")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSRAW")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSRAW"))                ;;
    (#xE2 ((:ev :0F :NDS :128 :66 :W0)            "VPSRAD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPSRAD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPSRAD")                 ;;
	  ((:ev :0F :NDS :128 :66 :W1)            "VPSRAQ")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPSRAQ")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPSRAQ"))                ;;
    (#xE3 ((:ev :0F :NDS :128 :66 :WIG)           "VPAVGW")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPAVGW")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPAVGW"))                ;;
    (#xE4 ((:ev :0F :NDS :128 :66 :WIG)           "VPMULHUW")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPMULHUW")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPMULHUW"))              ;;
    (#xE5 ((:ev :0F :NDS :128 :66 :WIG)           "VPMULHW")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPMULHW")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPMULHW"))               ;;
    (#xE6 ((:ev :0F :128 :F3 :W0)                 "VCVTDQ2PD")              ;;
	  ((:ev :0F :256 :F3 :W0)                 "VCVTDQ2PD")              ;;
	  ((:ev :0F :512 :F3 :W0)                 "VCVTDQ2PD")              ;;
	  ((:ev :0F :128 :F2 :W1)                 "VCVTPD2DQ")              ;;
	  ((:ev :0F :256 :F2 :W1)                 "VCVTPD2DQ")              ;;
	  ((:ev :0F :512 :F2 :W1)                 "VCVTPD2DQ")              ;;
	  ((:ev :0F :128 :F3 :W1)                 "VCVTQQ2PD")              ;;
	  ((:ev :0F :256 :F3 :W1)                 "VCVTQQ2PD")              ;;
	  ((:ev :0F :512 :F3 :W1)                 "VCVTQQ2PD")              ;;
	  ((:ev :0F :128 :66 :W1)                 "VCVTTPD2DQ")             ;;
	  ((:ev :0F :256 :66 :W1)                 "VCVTTPD2DQ")             ;;
	  ((:ev :0F :512 :66 :W1)                 "VCVTTPD2DQ"))            ;;
    (#xE7 ((:ev :0F :128 :66 :W0)                 "VMOVNTDQ")               ;;
	  ((:ev :0F :256 :66 :W0)                 "VMOVNTDQ")               ;;
	  ((:ev :0F :512 :66 :W0)                 "VMOVNTDQ"))              ;;
    (#xE8 ((:ev :0F :NDS :128 :66 :WIG)           "VPSUBSB")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSUBSB")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSUBSB"))               ;;
    (#xE9 ((:ev :0F :NDS :128 :66 :WIG)           "VPSUBSW")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSUBSW")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSUBSW"))               ;;
    (#xEA ((:ev :0F :NDS :128 :66 :WIG)           "VPMINSW")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPMINSW")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPMINSW"))               ;;
    (#xEB ((:ev :0F :NDS :128 :66 :W0)            "VPORD")                  ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPORD")                  ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPORD")                  ;;
	  ((:ev :0F :NDS :128 :66 :W1)            "VPORQ")                  ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPORQ")                  ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPORQ"))                 ;;
    (#xEC ((:ev :0F :NDS :128 :66 :WIG)           "VPADDSB")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPADDSB")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPADDSB"))               ;;
    (#xED ((:ev :0F :NDS :128 :66 :WIG)           "VPADDSW")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPADDSW")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPADDSW"))               ;;
    (#xEE ((:ev :0F :NDS :128 :66 :WIG)           "VPMAXSW")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPMAXSW")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPMAXSW"))               ;;
    (#xEF ((:ev :0F :NDS :128 :66 :W0)            "VPXORD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPXORD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPXORD")                 ;;
	  ((:ev :0F :NDS :128 :66 :W1)            "VPXORQ")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPXORQ")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPXORQ"))                ;;
    (#xF1 ((:ev :0F :NDS :128 :66 :WIG)           "VPSLLW")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSLLW")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSLLW"))                ;;
    (#xF2 ((:ev :0F :NDS :128 :66 :W0)            "VPSLLD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPSLLD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPSLLD"))                ;;
    (#xF3 ((:ev :0F :NDS :128 :66 :W1)            "VPSLLQ")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPSLLQ")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPSLLQ"))                ;;
    (#xF4 ((:ev :0F :NDS :128 :66 :W1)            "VPMULUDQ")               ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPMULUDQ")               ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPMULUDQ"))              ;;
    (#xF5 ((:ev :0F :NDS :128 :66 :WIG)           "VPMADDWD")               ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPMADDWD")               ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPMADDWD"))              ;;
    (#xF6 ((:ev :0F :NDS :128 :66 :WIG)           "VPSADBW")                ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSADBW")                ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSADBW"))               ;;
    (#xF8 ((:ev :0F :NDS :128 :66 :WIG)           "VPSUBB")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSUBB")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSUBB"))                ;;
    (#xF9 ((:ev :0F :NDS :128 :66 :WIG)           "VPSUBW")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPSUBW")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPSUBW"))                ;;
    (#xFA ((:ev :0F :NDS :128 :66 :W0)            "VPSUBD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPSUBD")                 ;;
	  ((:ev :0F :NDS :512 :66 :W0)            "VPSUBD"))                ;;
    (#xFB ((:ev :0F :NDS :128 :66 :W1)            "VPSUBQ")                 ;;
	  ((:ev :0F :NDS :256 :66 :W1)            "VPSUBQ")                 ;;
	  ((:ev :0F :NDS :512 :66 :W1)            "VPSUBQ"))                ;;
    (#xFC ((:ev :0F :NDS :128 :66 :WIG)           "VPADDB")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPADDB")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPADDB"))                ;;
    (#xFD ((:ev :0F :NDS :128 :66 :WIG)           "VPADDW")                 ;;
	  ((:ev :0F :NDS :256 :66 :WIG)           "VPADDW")                 ;;
	  ((:ev :0F :NDS :512 :66 :WIG)           "VPADDW"))                ;;
    (#xFE ((:ev :0F :NDS :512 :66 :W0)            "VPADDD")                 ;;
	  ((:ev :0F :NDS :128 :66 :W0)            "VPADDD")                 ;;
	  ((:ev :0F :NDS :256 :66 :W0)            "VPADDD"))))              ;;

(defconst *evex-0F38-opcodes*
  '((#x0 ((:ev :0F38 :NDS :128 :66 :WIG)          "VPSHUFB")
	 ((:ev :0F38 :NDS :256 :66 :WIG)          "VPSHUFB")
	 ((:ev :0F38 :NDS :512 :66 :WIG)          "VPSHUFB"))
    (#x4 ((:ev :0F38 :NDS :128 :66 :WIG)          "VPMADDUBSW")
	 ((:ev :0F38 :NDS :256 :66 :WIG)          "VPMADDUBSW")
	 ((:ev :0F38 :NDS :512 :66 :WIG)          "VPMADDUBSW"))
    (#xB ((:ev :0F38 :NDS :128 :66 :WIG)          "VPMULHRSW")
	 ((:ev :0F38 :NDS :256 :66 :WIG)          "VPMULHRSW")
	 ((:ev :0F38 :NDS :512 :66 :WIG)          "VPMULHRSW"))
    (#xC ((:ev :0F38 :NDS :128 :66 :W0)           "VPERMILPS")
	 ((:ev :0F38 :NDS :256 :66 :W0)           "VPERMILPS")
	 ((:ev :0F38 :NDS :512 :66 :W0)           "VPERMILPS"))
    (#xD ((:ev :0F38 :NDS :128 :66 :W1)           "VPERMILPD")
	 ((:ev :0F38 :NDS :256 :66 :W1)           "VPERMILPD")
	 ((:ev :0F38 :NDS :512 :66 :W1)           "VPERMILPD"))
    (#x10 ((:ev :0F38 :128 :F3 :W0)               "VPMOVUSWB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVUSWB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVUSWB")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPSRLVW")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPSRLVW")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPSRLVW"))
    (#x11 ((:ev :0F38 :128 :F3 :W0)               "VPMOVUSDB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVUSDB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVUSDB")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPSRAVW")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPSRAVW")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPSRAVW"))
    (#x12 ((:ev :0F38 :128 :F3 :W0)               "VPMOVUSQB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVUSQB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVUSQB")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPSLLVW")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPSLLVW")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPSLLVW"))
    (#x13 ((:ev :0F38 :128 :F3 :W0)               "VPMOVUSDW")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVUSDW")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVUSDW")
	  ((:ev :0F38 :128 :66 :W0)               "VCVTPH2PS")
	  ((:ev :0F38 :256 :66 :W0)               "VCVTPH2PS")
	  ((:ev :0F38 :512 :66 :W0)               "VCVTPH2PS"))
    (#x14 ((:ev :0F38 :128 :F3 :W0)               "VPMOVUSQW")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVUSQW")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVUSQW")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VPRORVD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPRORVD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPRORVD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPRORVQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPRORVQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPRORVQ"))
    (#x15 ((:ev :0F38 :128 :F3 :W0)               "VPMOVUSQD")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVUSQD")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVUSQD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VPROLVD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPROLVD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPROLVD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPROLVQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPROLVQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPROLVQ"))
    (#x16 ((:ev :0F38 :NDS :256 :66 :W1)          "VPERMPD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPERMPD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPERMPS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPERMPS"))
    (#x18 ((:ev :0F38 :128 :66 :W0)               "VBROADCASTSS")
	  ((:ev :0F38 :256 :66 :W0)               "VBROADCASTSS")
	  ((:ev :0F38 :512 :66 :W0)               "VBROADCASTSS"))
    (#x19 ((:ev :0F38 :256 :66 :W0)               "VBROADCASTF32X2")
	  ((:ev :0F38 :512 :66 :W0)               "VBROADCASTF32X2")
	  ((:ev :0F38 :256 :66 :W1)               "VBROADCASTSD")
	  ((:ev :0F38 :512 :66 :W1)               "VBROADCASTSD"))
    (#x1A ((:ev :0F38 :256 :66 :W0)               "VBROADCASTF32X4")
	  ((:ev :0F38 :512 :66 :W0)               "VBROADCASTF32X4")
	  ((:ev :0F38 :256 :66 :W1)               "VBROADCASTF64X2")
	  ((:ev :0F38 :512 :66 :W1)               "VBROADCASTF64X2"))
    (#x1B ((:ev :0F38 :512 :66 :W0)               "VBROADCASTF32X8")
	  ((:ev :0F38 :512 :66 :W1)               "VBROADCASTF64X4"))
    (#x1C ((:ev :0F38 :128 :66 :WIG)              "VPABSB")
	  ((:ev :0F38 :256 :66 :WIG)              "VPABSB")
	  ((:ev :0F38 :512 :66 :WIG)              "VPABSB"))
    (#x1D ((:ev :0F38 :128 :66 :WIG)              "VPABSW")
	  ((:ev :0F38 :256 :66 :WIG)              "VPABSW")
	  ((:ev :0F38 :512 :66 :WIG)              "VPABSW"))
    (#x1E ((:ev :0F38 :128 :66 :W0)               "VPABSD")
	  ((:ev :0F38 :256 :66 :W0)               "VPABSD"))
    (#x1F ((:ev :0F38 :128 :66 :W1)               "VPABSQ")
	  ((:ev :0F38 :256 :66 :W1)               "VPABSQ")
	  ((:ev :0F38 :512 :66 :W1)               "VPABSQ"))
    (#x20 ((:ev :0F38 :128 :F3 :W0)               "VPMOVSWB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVSWB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVSWB")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVSXBW")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVSXBW")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVSXBW"))
    (#x21 ((:ev :0F38 :128 :F3 :W0)               "VPMOVSDB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVSDB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVSDB")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVSXBD")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVSXBD")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVSXBD"))
    (#x22 ((:ev :0F38 :128 :F3 :W0)               "VPMOVSQB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVSQB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVSQB")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVSXBQ")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVSXBQ")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVSXBQ"))
    (#x23 ((:ev :0F38 :128 :F3 :W0)               "VPMOVSDW")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVSDW")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVSDW")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVSXWD")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVSXWD")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVSXWD"))
    (#x24 ((:ev :0F38 :128 :F3 :W0)               "VPMOVSQW")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVSQW")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVSQW")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVSXWQ")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVSXWQ")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVSXWQ"))
    (#x25 ((:ev :0F38 :128 :F3 :W0)               "VPMOVSQD")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVSQD")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVSQD")
	  ((:ev :0F38 :128 :66 :W0)               "VPMOVSXDQ")
	  ((:ev :0F38 :256 :66 :W0)               "VPMOVSXDQ")
	  ((:ev :0F38 :512 :66 :W0)               "VPMOVSXDQ"))
    (#x26 ((:ev :0F38 :NDS :128 :66 :W0)          "VPTESTMB")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPTESTMB")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPTESTMB")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPTESTMW")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPTESTMW")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPTESTMW")
	  ((:ev :0F38 :NDS :128 :F3 :W0)          "VPTESTNMB")
	  ((:ev :0F38 :NDS :256 :F3 :W0)          "VPTESTNMB")
	  ((:ev :0F38 :NDS :512 :F3 :W0)          "VPTESTNMB")
	  ((:ev :0F38 :NDS :128 :F3 :W1)          "VPTESTNMW")
	  ((:ev :0F38 :NDS :256 :F3 :W1)          "VPTESTNMW")
	  ((:ev :0F38 :NDS :512 :F3 :W1)          "VPTESTNMW"))
    (#x27 ((:ev :0F38 :NDS :128 :66 :W0)          "VPTESTMD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPTESTMD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPTESTMD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPTESTMQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPTESTMQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPTESTMQ")
	  ((:ev :0F38 :NDS :128 :F3 :W0)          "VPTESTNMD")
	  ((:ev :0F38 :NDS :256 :F3 :W0)          "VPTESTNMD")
	  ((:ev :0F38 :NDS :512 :F3 :W0)          "VPTESTNMD")
	  ((:ev :0F38 :NDS :128 :F3 :W1)          "VPTESTNMQ")
	  ((:ev :0F38 :NDS :256 :F3 :W1)          "VPTESTNMQ")
	  ((:ev :0F38 :NDS :512 :F3 :W1)          "VPTESTNMQ"))
    (#x28 ((:ev :0F38 :128 :F3 :W0)               "VPMOVM2B")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVM2B")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVM2B")
	  ((:ev :0F38 :128 :F3 :W1)               "VPMOVM2W")
	  ((:ev :0F38 :256 :F3 :W1)               "VPMOVM2W")
	  ((:ev :0F38 :512 :F3 :W1)               "VPMOVM2W")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPMULDQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPMULDQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPMULDQ"))
    (#x29 ((:ev :0F38 :NDS :128 :66 :W1)          "VPCMPEQQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPCMPEQQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPCMPEQQ")
	  ((:ev :0F38 :128 :F3 :W0)               "VPMOVB2M")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVB2M")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVB2M")
	  ((:ev :0F38 :128 :F3 :W1)               "VPMOVW2M")
	  ((:ev :0F38 :256 :F3 :W1)               "VPMOVW2M")
	  ((:ev :0F38 :512 :F3 :W1)               "VPMOVW2M"))
    (#x2A ((:ev :0F38 :128 :66 :W0)               "VMOVNTDQA")
	  ((:ev :0F38 :256 :66 :W0)               "VMOVNTDQA")
	  ((:ev :0F38 :512 :66 :W0)               "VMOVNTDQA")
	  ((:ev :0F38 :128 :F3 :W1)               "VPBROADCASTMB2Q")
	  ((:ev :0F38 :256 :F3 :W1)               "VPBROADCASTMB2Q")
	  ((:ev :0F38 :512 :F3 :W1)               "VPBROADCASTMB2Q"))
    (#x2B ((:ev :0F38 :NDS :128 :66 :W0)          "VPACKUSDW")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPACKUSDW")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPACKUSDW"))
    (#x2C ((:ev :0F38 :NDS :128 :66 :W1)          "VSCALEFPD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VSCALEFPD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VSCALEFPD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VSCALEFPS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VSCALEFPS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VSCALEFPS"))
    (#x2D ((:ev :0F38 :NDS :LIG :66 :W1)          "VSCALEFSD")
	  ((:ev :0F38 :NDS :LIG :66 :W0)          "VSCALEFSS"))
    (#x30 ((:ev :0F38 :128 :F3 :W0)               "VPMOVWB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVWB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVWB")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVZXBW")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVZXBW")
	  ((:ev :0F38 :128 :66)                   "VPMOVZXBW"))
    (#x31 ((:ev :0F38 :128 :F3 :W0)               "VPMOVDB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVDB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVDB")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVZXBD")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVZXBD")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVZXBD"))
    (#x32 ((:ev :0F38 :128 :F3 :W0)               "VPMOVQB")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVQB")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVQB")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVZXBQ")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVZXBQ")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVZXBQ"))
    (#x33 ((:ev :0F38 :128 :F3 :W0)               "VPMOVDW")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVDW")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVDW")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVZXWD")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVZXWD")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVZXWD"))
    (#x34 ((:ev :0F38 :128 :F3 :W0)               "VPMOVQW")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVQW")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVQW")
	  ((:ev :0F38 :128 :66 :WIG)              "VPMOVZXWQ")
	  ((:ev :0F38 :256 :66 :WIG)              "VPMOVZXWQ")
	  ((:ev :0F38 :512 :66 :WIG)              "VPMOVZXWQ"))
    (#x35 ((:ev :0F38 :128 :F3 :W0)               "VPMOVQD")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVQD")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVQD")
	  ((:ev :0F38 :128 :66 :W0)               "VPMOVZXDQ")
	  ((:ev :0F38 :256 :66 :W0)               "VPMOVZXDQ")
	  ((:ev :0F38 :512 :66 :W0)               "VPMOVZXDQ"))
    (#x36 ((:ev :0F38 :NDS :256 :66 :W0)          "VPERMD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPERMD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPERMQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPERMQ"))
    (#x37 ((:ev :0F38 :NDS :128 :66 :W1)          "VPCMPGTQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPCMPGTQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPCMPGTQ"))
    (#x38 ((:ev :0F38 :NDS :128 :66 :WIG)         "VPMINSB")
	  ((:ev :0F38 :NDS :256 :66 :WIG)         "VPMINSB")
	  ((:ev :0F38 :NDS :512 :66 :WIG)         "VPMINSB")
	  ((:ev :0F38 :128 :F3 :W0)               "VPMOVM2D")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVM2D")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVM2D")
	  ((:ev :0F38 :128 :F3 :W1)               "VPMOVM2Q")
	  ((:ev :0F38 :256 :F3 :W1)               "VPMOVM2Q")
	  ((:ev :0F38 :512 :F3 :W1)               "VPMOVM2Q"))
    (#x39 ((:ev :0F38 :NDS :128 :66 :W0)          "VPMINSD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPMINSD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPMINSD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPMINSQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPMINSQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPMINSQ")
	  ((:ev :0F38 :128 :F3 :W0)               "VPMOVD2M")
	  ((:ev :0F38 :256 :F3 :W0)               "VPMOVD2M")
	  ((:ev :0F38 :512 :F3 :W0)               "VPMOVD2M")
	  ((:ev :0F38 :128 :F3 :W1)               "VPMOVQ2M")
	  ((:ev :0F38 :256 :F3 :W1)               "VPMOVQ2M")
	  ((:ev :0F38 :512 :F3 :W1)               "VPMOVQ2M"))
    (#x3A ((:ev :0F38 :128 :F3 :W0)               "VPBROADCASTMW2D")
	  ((:ev :0F38 :256 :F3 :W0)               "VPBROADCASTMW2D")
	  ((:ev :0F38 :512 :F3 :W0)               "VPBROADCASTMW2D")
	  ((:ev :0F38 :NDS :128 :66)              "VPMINUW")
	  ((:ev :0F38 :NDS :256 :66)              "VPMINUW")
	  ((:ev :0F38 :NDS :512 :66)              "VPMINUW"))
    (#x3B ((:ev :0F38 :NDS :128 :66 :W0)          "VPMINUD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPMINUD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPMINUD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPMINUQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPMINUQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPMINUQ"))
    (#x3C ((:ev :0F38 :NDS :128 :66 :WIG)         "VPMAXSB")
	  ((:ev :0F38 :NDS :256 :66 :WIG)         "VPMAXSB")
	  ((:ev :0F38 :NDS :512 :66 :WIG)         "VPMAXSB"))
    (#x3D ((:ev :0F38 :NDS :128 :66 :W0)          "VPMAXSD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPMAXSD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPMAXSD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPMAXSQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPMAXSQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPMAXSQ"))
    (#x3E ((:ev :0F38 :NDS :128 :66 :WIG)         "VPMAXUW")
	  ((:ev :0F38 :NDS :256 :66 :WIG)         "VPMAXUW")
	  ((:ev :0F38 :NDS :512 :66 :WIG)         "VPMAXUW"))
    (#x3F ((:ev :0F38 :NDS :128 :66 :W0)          "VPMAXUD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPMAXUD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPMAXUD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPMAXUQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPMAXUQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPMAXUQ"))
    (#x40 ((:ev :0F38 :NDS :128 :66 :W0)          "VPMULLD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPMULLD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPMULLD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPMULLQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPMULLQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPMULLQ"))
    (#x42 ((:ev :0F38 :128 :66 :W1)               "VGETEXPPD")
	  ((:ev :0F38 :256 :66 :W1)               "VGETEXPPD")
	  ((:ev :0F38 :512 :66 :W1)               "VGETEXPPD")
	  ((:ev :0F38 :128 :66 :W0)               "VGETEXPPS")
	  ((:ev :0F38 :256 :66 :W0)               "VGETEXPPS")
	  ((:ev :0F38 :512 :66 :W0)               "VGETEXPPS"))
    (#x43 ((:ev :0F38 :NDS :LIG :66 :W1)          "VGETEXPSD")
	  ((:ev :0F38 :NDS :LIG :66 :W0)          "VGETEXPSS"))
    (#x44 ((:ev :0F38 :128 :66 :W0)               "VPLZCNTD")
	  ((:ev :0F38 :256 :66 :W0)               "VPLZCNTD")
	  ((:ev :0F38 :512 :66 :W0)               "VPLZCNTD")
	  ((:ev :0F38 :128 :66 :W1)               "VPLZCNTQ")
	  ((:ev :0F38 :256 :66 :W1)               "VPLZCNTQ")
	  ((:ev :0F38 :512 :66 :W1)               "VPLZCNTQ"))
    (#x45 ((:ev :0F38 :NDS :128 :66 :W0)          "VPSRLVD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPSRLVD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPSRLVD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPSRLVQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPSRLVQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPSRLVQ"))
    (#x46 ((:ev :0F38 :NDS :128 :66 :W0)          "VPSRAVD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPSRAVD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPSRAVD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPSRAVQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPSRAVQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPSRAVQ"))
    (#x47 ((:ev :0F38 :NDS :128 :66 :W0)          "VPSLLVD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPSLLVD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPSLLVD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPSLLVQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPSLLVQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPSLLVQ"))
    (#x4C ((:ev :0F38 :128 :66 :W1)               "VRCP14PD")
	  ((:ev :0F38 :256 :66 :W1)               "VRCP14PD")
	  ((:ev :0F38 :512 :66 :W1)               "VRCP14PD")
	  ((:ev :0F38 :128 :66 :W0)               "VRCP14PS")
	  ((:ev :0F38 :256 :66 :W0)               "VRCP14PS")
	  ((:ev :0F38 :512 :66 :W0)               "VRCP14PS"))
    (#x4D ((:ev :0F38 :NDS :LIG :66 :W1)          "VRCP14SD")
	  ((:ev :0F38 :NDS :LIG :66 :W0)          "VRCP14SS"))
    (#x4E ((:ev :0F38 :128 :66 :W1)               "VRSQRT14PD")
	  ((:ev :0F38 :256 :66 :W1)               "VRSQRT14PD")
	  ((:ev :0F38 :512 :66 :W1)               "VRSQRT14PD")
	  ((:ev :0F38 :128 :66 :W0)               "VRSQRT14PS")
	  ((:ev :0F38 :256 :66 :W0)               "VRSQRT14PS")
	  ((:ev :0F38 :512 :66 :W0)               "VRSQRT14PS"))
    (#x4F ((:ev :0F38 :NDS :LIG :66 :W1)          "VRSQRT14SD")
	  ((:ev :0F38 :NDS :LIG :66 :W0)          "VRSQRT14SS"))
    (#x52 ((:ev :0F38 :DDS :512 :F2 :W0)          "VP4DPWSSD"))
    (#x53 ((:ev :0F38 :DDS :512 :F2 :W0)          "VP4DPWSSDS"))
    (#x58 ((:ev :0F38 :128 :66 :W0)               "VPBROADCASTD")
	  ((:ev :0F38 :256 :66 :W0)               "VPBROADCASTD")
	  ((:ev :0F38 :512 :66 :W0)               "VPBROADCASTD"))
    (#x59 ((:ev :0F38 :128 :66 :W0)               "VBROADCASTI32x2")
	  ((:ev :0F38 :256 :66 :W0)               "VBROADCASTI32x2")
	  ((:ev :0F38 :512 :66 :W0)               "VBROADCASTI32x2")
	  ((:ev :0F38 :128 :66 :W1)               "VPBROADCASTQ")
	  ((:ev :0F38 :256 :66 :W1)               "VPBROADCASTQ")
	  ((:ev :0F38 :512 :66 :W1)               "VPBROADCASTQ"))
    (#x5A ((:ev :0F38 :256 :66 :W0)               "VBROADCASTI32X4")
	  ((:ev :0F38 :512 :66 :W0)               "VBROADCASTI32X4")
	  ((:ev :0F38 :256 :66 :W1)               "VBROADCASTI64X2")
	  ((:ev :0F38 :512 :66 :W1)               "VBROADCASTI64X2"))
    (#x5B ((:ev :0F38 :512 :66 :W0)               "VBROADCASTI32X8")
	  ((:ev :0F38 :512 :66 :W1)               "VBROADCASTI64X4"))
    (#x64 ((:ev :0F38 :NDS :128 :66 :W0)          "VPBLENDMD")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPBLENDMD")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPBLENDMD")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPBLENDMQ")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPBLENDMQ")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPBLENDMQ"))
    (#x65 ((:ev :0F38 :NDS :128 :66 :W1)          "VBLENDMPD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VBLENDMPD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VBLENDMPD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VBLENDMPS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VBLENDMPS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VBLENDMPS"))
    (#x66 ((:ev :0F38 :NDS :128 :66 :W0)          "VPBLENDMB")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPBLENDMB")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPBLENDMB")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPBLENDMW")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPBLENDMW")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPBLENDMW"))
    (#x75 ((:ev :0F38 :DDS :128 :66 :W0)          "VPERMI2B")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VPERMI2B")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VPERMI2B")
	  ((:ev :0F38 :DDS :128 :66 :W1)          "VPERMI2W")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VPERMI2W")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VPERMI2W"))
    (#x76 ((:ev :0F38 :DDS :128 :66 :W0)          "VPERMI2D")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VPERMI2D")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VPERMI2D")
	  ((:ev :0F38 :DDS :128 :66 :W1)          "VPERMI2Q")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VPERMI2Q")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VPERMI2Q"))
    (#x77 ((:ev :0F38 :DDS :128 :66 :W1)          "VPERMI2PD")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VPERMI2PD")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VPERMI2PD")
	  ((:ev :0F38 :DDS :128 :66 :W0)          "VPERMI2PS")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VPERMI2PS")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VPERMI2PS"))
    (#x78 ((:ev :0F38 :128 :66 :W0)               "VPBROADCASTB")
	  ((:ev :0F38 :256 :66 :W0)               "VPBROADCASTB")
	  ((:ev :0F38 :512 :66 :W0)               "VPBROADCASTB"))
    (#x79 ((:ev :0F38 :128 :66 :W0)               "VPBROADCASTW")
	  ((:ev :0F38 :256 :66 :W0)               "VPBROADCASTW")
	  ((:ev :0F38 :512 :66 :W0)               "VPBROADCASTW"))
    (#x7A ((:ev :0F38 :128 :66 :W0)               "VPBROADCASTB")
	  ((:ev :0F38 :256 :66 :W0)               "VPBROADCASTB")
	  ((:ev :0F38 :512 :66 :W0)               "VPBROADCASTB"))
    (#x7B ((:ev :0F38 :128 :66 :W0)               "VPBROADCASTW")
	  ((:ev :0F38 :256 :66 :W0)               "VPBROADCASTW")
	  ((:ev :0F38 :512 :66 :W0)               "VPBROADCASTW"))
    (#x7C ((:ev :0F38 :128 :66 :W0)               "VPBROADCASTD")
	  ((:ev :0F38 :256 :66 :W0)               "VPBROADCASTD")
	  ((:ev :0F38 :512 :66 :W0)               "VPBROADCASTD")
	  ((:ev :0F38 :128 :66 :W1)               "VPBROADCASTQ")
	  ((:ev :0F38 :256 :66 :W1)               "VPBROADCASTQ")
	  ((:ev :0F38 :512 :66 :W1)               "VPBROADCASTQ"))
    (#x7D ((:ev :0F38 :DDS :128 :66 :W0)          "VPERMT2B")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPERMT2B")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPERMT2B")
	  ((:ev :0F38 :DDS :128 :66 :W1)          "VPERMT2W")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VPERMT2W")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VPERMT2W"))
    (#x7E ((:ev :0F38 :DDS :128 :66 :W0)          "VPERMT2D")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VPERMT2D")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VPERMT2D")
	  ((:ev :0F38 :DDS :128 :66 :W1)          "VPERMT2Q")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VPERMT2Q")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VPERMT2Q"))
    (#x7F ((:ev :0F38 :DDS :128 :66 :W1)          "VPERMT2PD")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VPERMT2PD")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VPERMT2PD")
	  ((:ev :0F38 :DDS :128 :66 :W0)          "VPERMT2PS")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VPERMT2PS")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VPERMT2PS"))
    (#x83 ((:ev :0F38 :NDS :128 :66 :W1)          "VPMULTISHIFTQB")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPMULTISHIFTQB")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPMULTISHIFTQB"))
    (#x88 ((:ev :0F38 :128 :66 :W1)               "VEXPANDPD")
	  ((:ev :0F38 :256 :66 :W1)               "VEXPANDPD")
	  ((:ev :0F38 :512 :66 :W1)               "VEXPANDPD")
	  ((:ev :0F38 :128 :66 :W0)               "VEXPANDPS")
	  ((:ev :0F38 :256 :66 :W0)               "VEXPANDPS")
	  ((:ev :0F38 :512 :66 :W0)               "VEXPANDPS"))
    (#x89 ((:ev :0F38 :128 :66 :W0)               "VPEXPANDD")
	  ((:ev :0F38 :256 :66 :W0)               "VPEXPANDD")
	  ((:ev :0F38 :512 :66 :W0)               "VPEXPANDD")
	  ((:ev :0F38 :128 :66 :W1)               "VPEXPANDQ")
	  ((:ev :0F38 :256 :66 :W1)               "VPEXPANDQ")
	  ((:ev :0F38 :512 :66 :W1)               "VPEXPANDQ"))
    (#x8A ((:ev :0F38 :128 :66 :W1)               "VCOMPRESSPD")
	  ((:ev :0F38 :256 :66 :W1)               "VCOMPRESSPD")
	  ((:ev :0F38 :512 :66 :W1)               "VCOMPRESSPD")
	  ((:ev :0F38 :128 :66 :W0)               "VCOMPRESSPS")
	  ((:ev :0F38 :256 :66 :W0)               "VCOMPRESSPS")
	  ((:ev :0F38 :512 :66 :W0)               "VCOMPRESSPS"))
    (#x8B ((:ev :0F38 :128 :66 :W0)               "VPCOMPRESSD")
	  ((:ev :0F38 :256 :66 :W0)               "VPCOMPRESSD")
	  ((:ev :0F38 :512 :66 :W0)               "VPCOMPRESSD")
	  ((:ev :0F38 :128 :66 :W1)               "VPCOMPRESSQ")
	  ((:ev :0F38 :256 :66 :W1)               "VPCOMPRESSQ")
	  ((:ev :0F38 :512 :66 :W1)               "VPCOMPRESSQ"))
    (#x8D ((:ev :0F38 :NDS :128 :66 :W0)          "VPERMB")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VPERMB")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VPERMB")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VPERMW")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VPERMW")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VPERMW"))
    (#x90 ((:ev :0F38 :128 :66 :W0)               "VPGATHERDD")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W0)               "VPGATHERDD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0)               "VPGATHERDD")  ;; /vsib
	  ((:ev :0F38 :128 :66 :W1)               "VPGATHERDQ")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W1)               "VPGATHERDQ")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1)               "VPGATHERDQ")) ;; /vsib
    (#x91 ((:ev :0F38 :128 :66 :W0)               "VPGATHERQD")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W0)               "VPGATHERQD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0)               "VPGATHERQD")  ;; /vsib
	  ((:ev :0F38 :128 :66 :W1)               "VPGATHERQQ")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W1)               "VPGATHERQQ")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1)               "VPGATHERQQ")) ;; /vsib
    (#x92 ((:ev :0F38 :128 :66 :W1)               "VGATHERDPD")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W1)               "VGATHERDPD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1)               "VGATHERDPD")  ;; /vsib
	  ((:ev :0F38 :128 :66 :W0)               "VGATHERDPS")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W0)               "VGATHERDPS")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0)               "VGATHERDPS")) ;; /vsib
    (#x93 ((:ev :0F38 :128 :66 :W1)               "VGATHERQPD")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W1)               "VGATHERQPD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1)               "VGATHERQPD")  ;; /vsib
	  ((:ev :0F38 :128 :66 :W0)               "VGATHERQPS")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W0)               "VGATHERQPS")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0)               "VGATHERQPS")) ;; /vsib
    (#x96 ((:ev :0F38 :DDS :128 :66 :W1)          "VFMADDSUB132PD")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VFMADDSUB132PD")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VFMADDSUB132PD")
	  ((:ev :0F38 :DDS :128 :66 :W0)          "VFMADDSUB132PS")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VFMADDSUB132PS")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VFMADDSUB132PS"))
    (#x97 ((:ev :0F38 :DDS :128 :66 :W1)          "VFMSUBADD132PD")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VFMSUBADD132PD")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VFMSUBADD132PD")
	  ((:ev :0F38 :DDS :128 :66 :W0)          "VFMSUBADD132PS")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VFMSUBADD132PS")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VFMSUBADD132PS"))
    (#x98 ((:ev :0F38 :NDS :128 :66 :W1)          "VFMADD132PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFMADD132PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFMADD132PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFMADD132PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFMADD132PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFMADD132PS"))
    (#x99 ((:ev :0F38 :DDS :LIG :66 :W1)          "VFMADD132SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFMADD132SS"))
    (#x9A ((:ev :0F38 :DDS :512 :F2 :W0)          "V4FMADDPS")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VFMSUB132PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFMSUB132PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFMSUB132PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFMSUB132PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFMSUB132PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFMSUB132PS"))
    (#x9B ((:ev :0F38 :DDS :LIG :F2 :W0)         "V4FMADDSS")
	  ((:ev :0F38 :DDS :LIG :66 :W1)          "VFMSUB132SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFMSUB132SS"))
    (#x9C ((:ev :0F38 :NDS :128 :66 :W1)          "VFNMADD132PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFNMADD132PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFNMADD132PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFNMADD132PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFNMADD132PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFNMADD132PS"))
    (#x9D ((:ev :0F38 :DDS :LIG :66 :W1)          "VFNMADD132SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFNMADD132SS"))
    (#x9E ((:ev :0F38 :NDS :128 :66 :W1)          "VFNMSUB132PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFNMSUB132PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFNMSUB132PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFNMSUB132PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFNMSUB132PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFNMSUB132PS"))
    (#x9F ((:ev :0F38 :DDS :LIG :66 :W1)          "VFNMSUB132SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFNMSUB132SS"))
    (#xA0 ((:ev :0F38 :128 :66 :W0)               "VPSCATTERDD")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W0)               "VPSCATTERDD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0)               "VPSCATTERDD")  ;; /vsib
	  ((:ev :0F38 :128 :66 :W1)               "VPSCATTERDQ")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W1)               "VPSCATTERDQ")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1)               "VPSCATTERDQ")) ;; /vsib
    (#xA1 ((:ev :0F38 :128 :66 :W0)               "VPSCATTERQD")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W0)               "VPSCATTERQD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0)               "VPSCATTERQD")  ;; /vsib
	  ((:ev :0F38 :128 :66 :W1)               "VPSCATTERQQ")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W1)               "VPSCATTERQQ")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1)               "VPSCATTERQQ")) ;; /vsib
    (#xA2 ((:ev :0F38 :128 :66 :W1)               "VSCATTERDPD")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W1)               "VSCATTERDPD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1)               "VSCATTERDPD")  ;; /vsib
	  ((:ev :0F38 :128 :66 :W0)               "VSCATTERDPS")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W0)               "VSCATTERDPS")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0)               "VSCATTERDPS")) ;; /vsib
    (#xA3 ((:ev :0F38 :128 :66 :W1)               "VSCATTERQPD")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W1)               "VSCATTERQPD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1)               "VSCATTERQPD")  ;; /vsib
	  ((:ev :0F38 :128 :66 :W0)               "VSCATTERQPS")  ;; /vsib
	  ((:ev :0F38 :256 :66 :W0)               "VSCATTERQPS")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0)               "VSCATTERQPS")) ;; /vsib
    (#xA6 ((:ev :0F38 :DDS :128 :66 :W1)          "VFMADDSUB213PD")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VFMADDSUB213PD")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VFMADDSUB213PD")
	  ((:ev :0F38 :DDS :128 :66 :W0)          "VFMADDSUB213PS")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VFMADDSUB213PS")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VFMADDSUB213PS"))
    (#xA7 ((:ev :0F38 :DDS :128 :66 :W1)          "VFMSUBADD213PD")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VFMSUBADD213PD")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VFMSUBADD213PD")
	  ((:ev :0F38 :DDS :128 :66 :W0)          "VFMSUBADD213PS")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VFMSUBADD213PS")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VFMSUBADD213PS"))
    (#xA8 ((:ev :0F38 :NDS :128 :66 :W1)          "VFMADD213PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFMADD213PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFMADD213PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFMADD213PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFMADD213PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFMADD213PS"))
    (#xA9 ((:ev :0F38 :DDS :LIG :66 :W1)          "VFMADD213SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFMADD213SS"))
    (#xAA ((:ev :0F38 :DDS :512 :F2 :W0)          "V4FNMADDPS")
	  ((:ev :0F38 :NDS :128 :66 :W1)          "VFMSUB213PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFMSUB213PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFMSUB213PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFMSUB213PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFMSUB213PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFMSUB213PS"))
    (#xAB ((:ev :0F38 :DDS :LIG :F2 :W0)         "V4FNMADDSS")
	  ((:ev :0F38 :DDS :LIG :66 :W1)          "VFMSUB213SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFMSUB213SS"))
    (#xAC ((:ev :0F38 :NDS :128 :66 :W1)          "VFNMADD213PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFNMADD213PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFNMADD213PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFNMADD213PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFNMADD213PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFNMADD213PS"))
    (#xAD ((:ev :0F38 :DDS :LIG :66 :W1)          "VFNMADD213SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFNMADD213SS"))
    (#xAE ((:ev :0F38 :NDS :128 :66 :W1)          "VFNMSUB213PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFNMSUB213PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFNMSUB213PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFNMSUB213PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFNMSUB213PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFNMSUB213PS"))
    (#xAF ((:ev :0F38 :DDS :LIG :66 :W1)          "VFNMSUB213SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFNMSUB213SS"))
    (#xB4 ((:ev :0F38 :DDS :128 :66 :W1)          "VPMADD52LUQ")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VPMADD52LUQ")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VPMADD52LUQ"))
    (#xB5 ((:ev :0F38 :DDS :128 :66 :W1)          "VPMADD52HUQ")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VPMADD52HUQ")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VPMADD52HUQ"))
    (#xB6 ((:ev :0F38 :DDS :128 :66 :W1)          "VFMADDSUB231PD")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VFMADDSUB231PD")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VFMADDSUB231PD")
	  ((:ev :0F38 :DDS :128 :66 :W0)          "VFMADDSUB231PS")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VFMADDSUB231PS")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VFMADDSUB231PS"))
    (#xB7 ((:ev :0F38 :DDS :128 :66 :W1)          "VFMSUBADD231PD")
	  ((:ev :0F38 :DDS :256 :66 :W1)          "VFMSUBADD231PD")
	  ((:ev :0F38 :DDS :512 :66 :W1)          "VFMSUBADD231PD")
	  ((:ev :0F38 :DDS :128 :66 :W0)          "VFMSUBADD231PS")
	  ((:ev :0F38 :DDS :256 :66 :W0)          "VFMSUBADD231PS")
	  ((:ev :0F38 :DDS :512 :66 :W0)          "VFMSUBADD231PS"))
    (#xB8 ((:ev :0F38 :NDS :128 :66 :W1)          "VFMADD231PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFMADD231PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFMADD231PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFMADD231PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFMADD231PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFMADD231PS"))
    (#xB9 ((:ev :0F38 :DDS :LIG :66 :W1)          "VFMADD231SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFMADD231SS"))
    (#xBA ((:ev :0F38 :NDS :128 :66 :W1)          "VFMSUB231PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFMSUB231PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFMSUB231PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFMSUB231PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFMSUB231PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFMSUB231PS"))
    (#xBB ((:ev :0F38 :DDS :LIG :66 :W1)          "VFMSUB231SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFMSUB231SS"))
    (#xBC ((:ev :0F38 :NDS :128 :66 :W1)          "VFNMADD231PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFNMADD231PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFNMADD231PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFNMADD231PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFNMADD231PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFNMADD231PS"))
    (#xBD ((:ev :0F38 :DDS :LIG :66 :W1)          "VFNMADD231SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFNMADD231SS"))
    (#xBE ((:ev :0F38 :NDS :128 :66 :W1)          "VFNMSUB231PD")
	  ((:ev :0F38 :NDS :256 :66 :W1)          "VFNMSUB231PD")
	  ((:ev :0F38 :NDS :512 :66 :W1)          "VFNMSUB231PD")
	  ((:ev :0F38 :NDS :128 :66 :W0)          "VFNMSUB231PS")
	  ((:ev :0F38 :NDS :256 :66 :W0)          "VFNMSUB231PS")
	  ((:ev :0F38 :NDS :512 :66 :W0)          "VFNMSUB231PS"))
    (#xBF ((:ev :0F38 :DDS :LIG :66 :W1)          "VFNMSUB231SD")
	  ((:ev :0F38 :DDS :LIG :66 :W0)          "VFNMSUB231SS"))
    (#xC4 ((:ev :0F38 :128 :66 :W0)               "VPCONFLICTD")
	  ((:ev :0F38 :256 :66 :W0)               "VPCONFLICTD")
	  ((:ev :0F38 :512 :66 :W0)               "VPCONFLICTD")
	  ((:ev :0F38 :128 :66 :W1)               "VPCONFLICTQ")
	  ((:ev :0F38 :256 :66 :W1)               "VPCONFLICTQ")
	  ((:ev :0F38 :512 :66 :W1)               "VPCONFLICTQ"))
    (#xC6 ((:ev :0F38 :512 :66 :W0 (:REG . 1))    "VGATHERPF0DPS")   ;; /vsib
	  ((:ev :0F38 :512 :66 :W1 (:REG . 1))    "VGATHERPF0DPD")   ;; /vsib
	  ((:ev :0F38 :512 :66 :W0 (:REG . 2))    "VGATHERPF1DPS")   ;; /vsib
	  ((:ev :0F38 :512 :66 :W1 (:REG . 2))    "VGATHERPF1DPD")   ;; /vsib
	  ((:ev :0F38 :512 :66 :W0 (:REG . 5))    "VSCATTERPF0DPS")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1 (:REG . 5))    "VSCATTERPF0DPD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0 (:REG . 6))    "VSCATTERPF1DPS")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1 (:REG . 6))    "VSCATTERPF1DPD")) ;; /vsib
    (#xC7 ((:ev :0F38 :512 :66 :W0 (:REG . 1))    "VGATHERPF0QPS")   ;; /vsib
	  ((:ev :0F38 :512 :66 :W1 (:REG . 1))    "VGATHERPF0QPD")   ;; /vsib
	  ((:ev :0F38 :512 :66 :W0 (:REG . 2))    "VGATHERPF1QPS")   ;; /vsib
	  ((:ev :0F38 :512 :66 :W1 (:REG . 2))    "VGATHERPF1QPD")   ;; /vsib
	  ((:ev :0F38 :512 :66 :W0 (:REG . 5))    "VSCATTERPF0QPS")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1 (:REG . 5))    "VSCATTERPF0QPD")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W0 (:REG . 6))    "VSCATTERPF1QPS")  ;; /vsib
	  ((:ev :0F38 :512 :66 :W1 (:REG . 6))    "VSCATTERPF1QPD")) ;; /vsib
    (#xC8 ((:ev :0F38 :512 :66 :W1)               "VEXP2PD")
	  ((:ev :0F38 :512 :66 :W0)               "VEXP2PS"))
    (#xCA ((:ev :0F38 :512 :66 :W1)               "VRCP28PD")
	  ((:ev :0F38 :512 :66 :W0)               "VRCP28PS"))
    (#xCB ((:ev :0F38 :NDS :LIG :66 :W1)          "VRCP28SD")
	  ((:ev :0F38 :NDS :LIG :66 :W0)          "VRCP28SS"))
    (#xCC ((:ev :0F38 :512 :66 :W1)               "VRSQRT28PD")
	  ((:ev :0F38 :512 :66 :W0)               "VRSQRT28PS"))
    (#xCD ((:ev :0F38 :NDS :LIG :66 :W1)          "VRSQRT28SD")
	  ((:ev :0F38 :NDS :LIG :66 :W0)          "VRSQRT28SS"))))

(defconst *evex-0F3A-opcodes*
  '((#x0 ((:ev :0F3A :256 :66 :W1)                "VPERMQ")         ;; ib
	 ((:ev :0F3A :512 :66 :W1)                "VPERMQ"))        ;; ib
    (#x1 ((:ev :0F3A :256 :66 :W1)                "VPERMPD")        ;; ib
	 ((:ev :0F3A :512 :66 :W1)                "VPERMPD"))       ;; ib
    (#x3 ((:ev :0F3A :NDS :128 :66 :W0)           "VALIGND")        ;; ib
	 ((:ev :0F3A :NDS :128 :66 :W1)           "VALIGNQ")        ;; ib
	 ((:ev :0F3A :NDS :256 :66 :W0)           "VALIGND")        ;; ib
	 ((:ev :0F3A :NDS :256 :66 :W1)           "VALIGNQ")        ;; ib
	 ((:ev :0F3A :NDS :512 :66 :W0)           "VALIGND")        ;; ib
	 ((:ev :0F3A :NDS :512 :66 :W1)           "VALIGNQ"))       ;; ib
    (#x4 ((:ev :0F3A :128 :66 :W0)                "VPERMILPS")      ;; ib
	 ((:ev :0F3A :256 :66 :W0)                "VPERMILPS")      ;; ib
	 ((:ev :0F3A :512 :66 :W0)                "VPERMILPS"))     ;; ib
    (#x5 ((:ev :0F3A :128 :66 :W1)                "VPERMILPD")      ;; ib
	 ((:ev :0F3A :256 :66 :W1)                "VPERMILPD")      ;; ib
	 ((:ev :0F3A :512 :66 :W1)                "VPERMILPD"))     ;; ib
    (#x8 ((:ev :0F3A :128 :66 :W0)                "VRNDSCALEPS")    ;; ib
	 ((:ev :0F3A :256 :66 :W0)                "VRNDSCALEPS")    ;; ib
	 ((:ev :0F3A :512 :66 :W0)                "VRNDSCALEPS"))   ;; ib
    (#x9 ((:ev :0F3A :128 :66 :W1)                "VRNDSCALEPD")    ;; ib
	 ((:ev :0F3A :256 :66 :W1)                "VRNDSCALEPD")    ;; ib
	 ((:ev :0F3A :512 :66 :W1)                "VRNDSCALEPD"))   ;; ib
    (#xA ((:ev :0F3A :NDS :LIG :66 :W0)           "VRNDSCALESS"))   ;; ib
    (#xB ((:ev :0F3A :NDS :LIG :66 :W1)           "VRNDSCALESD"))   ;; ib
    (#xF ((:ev :0F3A :NDS :128 :66 :WIG)          "VPALIGNR")       ;; ib
	 ((:ev :0F3A :NDS :256 :66 :WIG)          "VPALIGNR")       ;; ib
	 ((:ev :0F3A :NDS :512 :66 :WIG)          "VPALIGNR"))      ;; ib
    (#x14 ((:ev :0F3A :128 :66 :WIG)              "VPEXTRB"))       ;; ib
    (#x15 ((:ev :0F3A :128 :66 :WIG)              "VPEXTRW"))       ;; ib
    (#x16 ((:ev :0F3A :128 :66 :W0)               "VPEXTRD")        ;; ib
	  ((:ev :0F3A :128 :66 :W1)               "VPEXTRQ"))       ;; ib
    (#x17 ((:ev :0F3A :128 :66 :WIG)              "VEXTRACTPS"))    ;; ib
    (#x18 ((:ev :0F3A :NDS :256 :66 :W0)          "VINSERTF32X4")   ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VINSERTF64X2")   ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VINSERTF32X4")   ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VINSERTF64X2"))  ;; ib
    (#x19 ((:ev :0F3A :256 :66 :W0)               "VEXTRACTF32X4")  ;; ib
	  ((:ev :0F3A :256 :66 :W1)               "VEXTRACTF64X2")  ;; ib
	  ((:ev :0F3A :512 :66 :W0)               "VEXTRACTF32x4")  ;; ib
	  ((:ev :0F3A :512 :66 :W1)               "VEXTRACTF64X2")) ;; ib
    (#x1A ((:ev :0F3A :NDS :512 :66 :W0)          "VINSERTF32X4")   ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VINSERTF64X2"))  ;; ib
    (#x1B ((:ev :0F3A :512 :66 :W0)               "VEXTRACTF32x4")  ;; ib
	  ((:ev :0F3A :512 :66 :W1)               "VEXTRACTF64X2")) ;; ib
    (#x1D ((:ev :0F3A :128 :66 :W0)               "VCVTPS2PH")      ;; ib
	  ((:ev :0F3A :256 :66 :W0)               "VCVTPS2PH")      ;; ib
	  ((:ev :0F3A :512 :66 :W0)               "VCVTPS2PH"))     ;; ib
    (#x1E ((:ev :0F3A :NDS :128 :66 :W0)          "VPCMPD")         ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W0)          "VPCMPD")         ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VPCMPD")         ;; ib
	  ((:ev :0F3A :NDS :128 :66 :W1)          "VPCMPQ")         ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VPCMPQ")         ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VPCMPQ"))        ;; ib
    (#x1F ((:ev :0F3A :NDS :128 :66 :W0)          "VPCMPD")         ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W0)          "VPCMPD")         ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VPCMPD")         ;; ib
	  ((:ev :0F3A :NDS :128 :66 :W1)          "VPCMPQ")         ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VPCMPQ")         ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VPCMPQ"))        ;; ib
    (#x20 ((:ev :0F3A :NDS :128 :66 :WIG)         "VPINSRB"))       ;; ib
    (#x21 ((:ev :0F3A :NDS :128 :66 :W0)          "VINSERTPS"))     ;; ib
    (#x22 ((:ev :0F3A :NDS :128 :66 :W0)          "VPINSRD")        ;; ib
	  ((:ev :0F3A :NDS :128 :66 :W1)          "VPINSRQ"))       ;; ib
    (#x23 ((:ev :0F3A :NDS :256 :66 :W0)          "VSHUFF32X4")     ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VSHUFF64X2")     ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VSHUFF32x4")     ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VSHUFF64x2"))    ;; ib
    (#x25 ((:ev :0F3A :DDS :128 :66 :W0)          "VPTERNLOGD")     ;; ib
	  ((:ev :0F3A :DDS :128 :66 :W1)          "VPTERNLOGQ")     ;; ib
	  ((:ev :0F3A :DDS :256 :66 :W0)          "VPTERNLOGD")     ;; ib
	  ((:ev :0F3A :DDS :256 :66 :W1)          "VPTERNLOGQ")     ;; ib
	  ((:ev :0F3A :DDS :512 :66 :W0)          "VPTERNLOGD")     ;; ib
	  ((:ev :0F3A :DDS :512 :66 :W1)          "VPTERNLOGQ"))    ;; ib
    (#x26 ((:ev :0F3A :128 :66 :W1)               "VGETMANTPD")     ;; ib
	  ((:ev :0F3A :256 :66 :W1)               "VGETMANTPD")     ;; ib
	  ((:ev :0F3A :512 :66 :W1)               "VGETMANTPD")     ;; ib
	  ((:ev :0F3A :128 :66 :W0)               "VGETMANTPS")     ;; ib
	  ((:ev :0F3A :256 :66 :W0)               "VGETMANTPS")     ;; ib
	  ((:ev :0F3A :512 :66 :W0)               "VGETMANTPS"))    ;; ib
    (#x27 ((:ev :0F3A :NDS :LIG :66 :W1)          "VGETMANTSD")     ;; ib
	  ((:ev :0F3A :NDS :LIG :66 :W0)          "VGETMANTSS"))    ;; ib
    (#x38 ((:ev :0F3A :NDS :256 :66 :W0)          "VINSERTI32X4")   ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VINSERTI64X2")   ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VINSERTI32X4")   ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VINSERTI64X2"))  ;; ib
    (#x39 ((:ev :0F3A :256 :66 :W0)               "VEXTRACTI32X4")  ;; ib
	  ((:ev :0F3A :256 :66 :W1)               "VEXTRACTI64X2")  ;; ib
	  ((:ev :0F3A :512 :66 :W0)               "VEXTRACTI32x4")  ;; ib
	  ((:ev :0F3A :512 :66 :W1)               "VEXTRACTI64X2")) ;; ib
    (#x3A ((:ev :0F3A :NDS :512 :66 :W0)          "VINSERTI32X4")   ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VINSERTI64X2"))  ;; ib
    (#x3B ((:ev :0F3A :512 :66 :W0)               "VEXTRACTI32x4")  ;; ib
	  ((:ev :0F3A :512 :66 :W1)               "VEXTRACTI64X2")) ;; ib
    (#x3E ((:ev :0F3A :NDS :128 :66 :W0)          "VPCMPB")         ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W0)          "VPCMPB")         ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VPCMPB")         ;; ib
	  ((:ev :0F3A :NDS :128 :66 :W1)          "VPCMPW")         ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VPCMPW"))        ;; ib
    (#x3F ((:ev :0F3A :NDS :128 :66 :W0)          "VPCMPB")         ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W0)          "VPCMPB")         ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VPCMPB")         ;; ib
	  ((:ev :0F3A :NDS :128 :66 :W1)          "VPCMPW")         ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VPCMPW")         ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VPCMPW"))        ;; ib
    (#x42 ((:ev :0F3A :NDS :128 :66 :W0)          "VDBPSADBW")      ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W0)          "VDBPSADBW")      ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VDBPSADBW"))     ;; ib
    (#x43 ((:ev :0F3A :NDS :256 :66 :W0)          "VSHUFI32X4")     ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VSHUFI64X2")     ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VSHUFI32x4")     ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VSHUFI64x2"))    ;; ib
    (#x50 ((:ev :0F3A :NDS :128 :66 :W1)          "VRANGEPD")       ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VRANGEPD")       ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VRANGEPD")       ;; ib
	  ((:ev :0F3A :NDS :128 :66 :W0)          "VRANGEPS")       ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W0)          "VRANGEPS")       ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VRANGEPS"))      ;; ib
    (#x51 ((:ev :0F3A :NDS :LIG :66 :W1)          "VRANGESD")       ;;
	  ((:ev :0F3A :NDS :LIG :66 :W0)          "VRANGESS"))      ;;
    (#x54 ((:ev :0F3A :NDS :128 :66 :W1)          "VFIXUPIMMPD")    ;; ib
	  ((:ev :0F3A :NDS :256 :66 :W1)          "VFIXUPIMMPD")    ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W1)          "VFIXUPIMMPD")    ;; ib
	  ((:ev :0F3A :NDS :512 :66 :W0)          "VFIXUPIMMPS")    ;; ib
	  ((:ev :0F3A :NDS :128 :66 :W0)          "VFIXUPIMMPS")    ;;
	  ((:ev :0F3A :NDS :256 :66 :W0)          "VFIXUPIMMPS"))   ;;
    (#x55 ((:ev :0F3A :NDS :LIG :66 :W1)          "VFIXUPIMMSD")    ;; ib
	  ((:ev :0F3A :NDS :LIG :66 :W0)          "VFIXUPIMMSS"))   ;; ib
    (#x56 ((:ev :0F3A :128 :66 :W1)               "VREDUCEPD")      ;; ib
	  ((:ev :0F3A :256 :66 :W1)               "VREDUCEPD")      ;; ib
	  ((:ev :0F3A :512 :66 :W1)               "VREDUCEPD")      ;; ib
	  ((:ev :0F3A :128 :66 :W0)               "VREDUCEPS")      ;; ib
	  ((:ev :0F3A :256 :66 :W0)               "VREDUCEPS")      ;; ib
	  ((:ev :0F3A :512 :66 :W0)               "VREDUCEPS"))     ;; ib
    (#x57 ((:ev :0F3A :NDS :LIG :66 :W0)          "VREDUCESS")      ;; ib
	  ((:ev :0F3A :NDS :LIG :66 :W1)          "VREDUCESD"))     ;;
    (#x66 ((:ev :0F3A :128 :66 :W1)               "VFPCLASSPD")     ;; ib
	  ((:ev :0F3A :256 :66 :W1)               "VFPCLASSPD")     ;; ib
	  ((:ev :0F3A :512 :66 :W1)               "VFPCLASSPD")     ;; ib
	  ((:ev :0F3A :128 :66 :W0)               "VFPCLASSPS")     ;; ib
	  ((:ev :0F3A :256 :66 :W0)               "VFPCLASSPS")     ;; ib
	  ((:ev :0F3A :512 :66 :W0)               "VFPCLASSPS"))    ;; ib
    (#x67 ((:ev :0F3A :LIG :66 :W1)               "VFPCLASSSD")     ;; ib
	  ((:ev :0F3A :LIG :66 :W0)               "VFPCLASSSS"))))

;; ----------------------------------------------------------------------

;; Well-formedness of our representation of opcode maps:

;; Each cell in an opcode map (i.e., the box referring to one opcode
;; byte) must be a true-list. If this cell is NOT an alist, then we
;; call it a "SIMPLE CELL".  A simple cell's FIRST ELEMENT should be
;; any one of the following:
;; 1. A string which denotes the name of the instruction.
;; 2. A legal keyword in *simple-cells-legal-keywords*.

;; If this cell is an alistp, then we call it a "COMPOUND CELL".  The
;; following are the allowed KEYS: *compound-cells-legal-keys*
;; The VALUES of this alistp should be a simple cell.

;; Aside:
;; [[ One-byte opcode map legal keywords:
;;       :2-BYTE-ESCAPE, :NONE, :PREFIX-FS, :PREFIX-GS,
;;       :PREFIX-OPSIZE, :PREFIX-ADDRSIZE, :ESC, :PREFIX-LOCK, :ESC,
;;       :PREFIX-REPNE, :PREFIX-REP/REPE, and the following group
;;       numbers: 1, 1A, 2, 3, 4, 5, and 11.
;;   Two-byte opcode map legal keywords:
;;      :NONE, :3-BYTE-ESCAPE, and the following group numbers: 6, 7,
;;      8, 9, 10, 12, 13, 14, 15, and 16. ]]
;; [[ One-byte opcode map legal keys:
;;     all superscripts in *opcode-map-true-superscripts*.
;;   Two-byte opcode map legal keys:
;;     :NO-PREFIX, :66, :F3, :F2, and all superscripts except :i64 in
;;     *opcode-map-true-superscripts*. ]]

(defconst *group-numbers*
  (strip-cars *opcode-extensions-by-group-number*))

(local
 (defun remove-all (elems lst)
   (if (endp elems)
       lst
     (remove-all (cdr elems) (remove-equal (car elems) lst)))))

(defconst *opcode-map-true-superscripts*
  ;; All other superscripts in *opcode-map-superscripts* aren't
  ;; particularly useful --- we can infer information conveyed by
  ;; '(:1a :1b :1c :v :v1) by the addressing codes (see
  ;; *Z-addressing-method-info*) and '(:f64 :d64) have to be dealt
  ;; with in the instruction semantic functions.
  '(:i64 :o64))

(local
 (defthm true-superscripts-subset-of-superscripts
   (subsetp-equal *opcode-map-true-superscripts*
		  *opcode-map-superscripts*)))

(defconst *simple-cells-standalone-legal-keywords*
  ;; When a simple cell has one of these keywords as its first
  ;; element, then this should be the ONLY element of that cell --- no
  ;; addressing info. should follow.
  (list
   :NONE
   :ESC
   :2-BYTE-ESCAPE
   :3-BYTE-ESCAPE
   :PREFIX-ES
   :PREFIX-CS
   :PREFIX-SS
   :PREFIX-DS
   :PREFIX-FS
   :PREFIX-GS
   :PREFIX-OPSIZE
   :PREFIX-ADDRSIZE
   :PREFIX-LOCK
   :PREFIX-REPNE
   :PREFIX-REP/REPE
   :REX
   :REX-B
   :REX-X
   :REX-XB
   :REX-R
   :REX-RB
   :REX-RX
   :REX-RXB
   :REX-W
   :REX-WB
   :REX-WX
   :REX-WXB
   :REX-WR
   :REX-WRB
   :REX-WRX
   :REX-WRXB
   :VEX3-BYTE0
   :VEX2-BYTE0
   :EVEX-BYTE0))

(defconst *simple-cells-legal-keywords*
  (append
   ;; Semantics of :ALT:
   ;; Consider the following:
   ;; (:66 . (:ALT
   ;;         (("VPEXTRB"    3 (R d)  (V dq)  (I b))
   ;;          ("VPEXTRB"    3 (M b)  (V dq)  (I b)))))
   ;; This corresponds to the following cell in the Intel manuals:
   ;; vpextrb Rd/Mb, Vdq, Ib
   ;; What that means is that vpextrb can have a first operand that is
   ;; either an Rd or an Mb.  The opcode bytes (and prefixes,
   ;; extensions, etc.) are the same for both these cases, and the
   ;; ModR/M byte's mod and r/m fields are used to distinguish between
   ;; these two forms of the same instruction.
   (list :ALT)
   *group-numbers*
   *simple-cells-standalone-legal-keywords*))

(define simple-cells-legal-keyword-p (k)
  (member-equal k *simple-cells-legal-keywords*))

(define semantic-function-info-p (info)
  :short "Used to generate code that dispatches control to the appropriate
  instruction semantic function"
  (or
   ;; Either no info. is present...
   (equal info nil)
   ;; ... but if it is, it is well-formed.
   (and (consp info)
	(equal (car info) :FN)
	(true-listp (cdr info))
	(<= 1 (len (cdr info)))
	;; Name of instruction semantic function
	(symbolp (car (cdr info)))
	;; Alist binding formals to actuals
	(alistp (cdr (cdr info))))))

(define remove-semantic-function-info-p ((info true-listp))
  (if (endp info)
      nil
    (b* ((elem (car info))
	 (rest (cdr info)))
      (if (and (consp elem)
	       (equal (car elem) :FN))
	  rest
	(cons elem (remove-semantic-function-info-p rest)))))

  ///

  (defthm true-listp-remove-semantic-function-info-p
    (implies (true-listp info)
	     (true-listp (remove-semantic-function-info-p info)))))

(define get-semantic-function-info-p ((info true-listp))
  (if (endp info)
      nil
    (b* ((elem (car info))
	 (rest (cdr info)))
      (if (semantic-function-info-p elem)
	  elem
	(get-semantic-function-info-p rest))))
  ///

  (defthm semantic-function-info-p-of-get-semantic-function-info-p
    (implies (true-listp info)
	     (semantic-function-info-p (get-semantic-function-info-p info)))
    :hints (("Goal" :in-theory (e/d (semantic-function-info-p) ())))))

(define ud-info-p (info)
  :short "Information about #UD exception during decode"
  (or
   ;; Either no info. is present...
   (equal info nil)
   ;; ... but if it is, it is well-formed.
   (and (consp info)
	(equal (car info) :UD)
	(true-listp (cdr info)))))

(define remove-ud-info-p ((info true-listp))
  (if (endp info)
      nil
    (b* ((elem (car info))
	 (rest (cdr info)))
      (if (and (consp elem)
	       (equal (car elem) :UD))
	  rest
	(cons elem (remove-ud-info-p rest)))))

  ///

  (defthm true-listp-remove-ud-info-p
    (implies (true-listp info)
	     (true-listp (remove-ud-info-p info)))))

(define get-ud-info-p ((info true-listp))
  (if (endp info)
      nil
    (b* ((elem (car info))
	 (rest (cdr info)))
      (if (ud-info-p elem)
	  elem
	(get-ud-info-p rest))))
  ///

  (defthm ud-info-p-of-get-ud-info-p
    (implies (true-listp info)
	     (ud-info-p (get-ud-info-p info)))
    :hints (("Goal" :in-theory (e/d (ud-info-p) ())))))

(define simple-cell-addressing-info-p ((info true-listp))
  (and
   ;; Number of operands
   (natp (nth 0 info))
   ;; Number of operands <= Addressing info.
   ;; (this cannot be strengthened to = because, for example,
   ;; opcode FFh in the one-byte opcode map has :1A after (E
   ;; v)).
   (<= (nth 0 info) (len (nthcdr 1 info)))))

(define basic-simple-cell-p (cell)
  (b* (((unless (true-listp cell)) nil)
       (first (car cell))
       (rest (cdr cell))
       (new-rest (remove-semantic-function-info-p rest))
       (semantic-info (get-semantic-function-info-p rest)))
    (and
     (semantic-function-info-p semantic-info)
     (or
      (and (or (stringp first)
	       (member-equal first *group-numbers*))
	   (simple-cell-addressing-info-p new-rest))
      (and
       (member-equal first *simple-cells-standalone-legal-keywords*)
       (equal new-rest nil)))))
  ///
  (defthm basic-simple-cell-p-implies-true-listp
    (implies (basic-simple-cell-p cell)
	     (true-listp cell))
    :rule-classes :forward-chaining))

(define basic-simple-cells-p (cells)
  (if (atom cells)
      (equal cells nil)
    (and (basic-simple-cell-p (car cells))
	 (basic-simple-cells-p (cdr cells))))
  ///
  (defthm basic-simple-cells-p-implies-true-listp-and-true-list-listp
    (implies (basic-simple-cells-p cell)
	     (and (true-listp cell)
		  (true-list-listp cell)))
    :rule-classes :forward-chaining))

(define simple-cell-p (cell)
  (or (basic-simple-cell-p cell)
      (b* (((unless (true-listp cell)) nil)
	   (first (car cell))
	   (rest (cdr cell))
	   (ud-info (get-ud-info-p rest))
	   (semantic-info (get-semantic-function-info-p rest))
	   (new-rest (remove-ud-info-p rest))
	   (new-rest (remove-semantic-function-info-p new-rest)))
	(cond ((equal first :ALT)
	       (and
		(consp new-rest)
		;; (true-listp new-rest)
		(basic-simple-cells-p (car new-rest))
		(equal (cdr new-rest) nil)
		(semantic-function-info-p semantic-info)
		(ud-info-p ud-info)))
	      (t nil))))
  ///
  (defthm simple-cell-p-implies-true-listp
    (implies (simple-cell-p cell)
	     (true-listp cell))
    :rule-classes :forward-chaining))

(defconst *mandatory-prefixes*
  '(:66 :F3 :F2))

;; Reference: Section 3.1.1.2 (Opcode Column in the Instruction Summary Table
;; (Instructions with VEX prefix)), Intel Manual, Vol. 2A.

;; VEX.[NDS|NDD|DDS].[128|256|LIG|LZ].[66|F2|F3].[0F|0F38|0F3A].[W0|W1|WIG]
;; opcode
;; [ /r ]
;; [ /ib | /is4 ]

;; EVEX.[NDS|NDD|DDS].[128|256|512|LIG].[66|F2|F3].[0F|0F38|0F3A].[W0|W1|WIG]
;; opcode
;; [ /r ]
;; [ /ib ]

(defconst *vex-modifiers*
  '(:v :v66 :vF3 :vF2))

(defconst *evex-modifiers*
  '(:ev :ev66 :evF3 :evF2))

(defconst *compound-cells-legal-keys*
  (append
   (list :NO-PREFIX)
   *mandatory-prefixes*
   *vex-modifiers*
   *evex-modifiers*
   *opcode-map-true-superscripts*))

(define compound-cells-legal-key-p (k)
  (member-equal k *compound-cells-legal-keys*)
  ;; (if (true-listp k)
  ;;     ;; We can have more than one mandatory prefix: e.g.: in the
  ;;     ;; *0F-38-three-byte-opcode-map-lst*:
  ;;     ;; ((:66 :F2) . ("CRC32" 2 (G d) (E b)))
  ;;     (subsetp-equal k *mandatory-prefixes*)
  ;;   (member-equal k *compound-cells-legal-keys*))
  )

(define compound-cells-legal-keys-p (ks)
  (if (atom ks)
      (eq ks nil)
    (and (compound-cells-legal-key-p (car ks))
	 (compound-cells-legal-keys-p (cdr ks)))))

(define compound-cells-legal-values-p (vs)
  (if (atom vs)
      (eq vs nil)
    (and (true-listp (car vs))
	 (simple-cell-p (car vs))
	 (compound-cells-legal-values-p (cdr vs)))))

(define compound-cell-p (cell)
  ;; I haven't come across an opcode cell that looks like the
  ;; following:
  ;; (:66 . ((:i64 . ("foo" 0))
  ;;         (:o64 . ("bar" 0))))
  ;; That is, all compound cells in the opcode maps (one, two, and
  ;; three-byte) have simple cells corresponding to a key.  If Intel
  ;; does something wacky like this in the future, we'll have to
  ;; change the recognizer for a compound cell.
  (b* (((unless (alistp cell)) nil)
       (keys   (strip-cars cell))
       (values (strip-cdrs cell)))
    (and (compound-cells-legal-keys-p keys)
	 (compound-cells-legal-values-p values)))
  ///
  (defthm compound-cell-p-implies-alistp
    (implies (compound-cell-p cell)
	     (alistp cell))
    :rule-classes :forward-chaining))

(define opcode-cell-p (cell)
  (cond ((alistp cell) (compound-cell-p cell))
	((true-listp cell) (simple-cell-p cell))
	(t nil))
  ///
  (defthm opcode-cell-p-implies-true-listp
    (implies (opcode-cell-p cell)
	     (true-listp cell))
    :rule-classes :forward-chaining))

(define opcode-row-p (row)
  (if (atom row)
      (eq row nil)
    (and (opcode-cell-p (car row))
	 (opcode-row-p (cdr row))))
  ///

  (defthm opcode-row-p-implies-true-listp
    (implies (opcode-row-p row)
	     (true-listp row))
    :rule-classes :forward-chaining)

  (defthm opcode-row-p-implies-true-list-listp
    (implies (opcode-row-p row)
	     (true-list-listp row))
    :rule-classes :forward-chaining)

  (defthm opcode-row-p-implies-opcode-cell-p-of-car
    (implies
     (opcode-row-p row)
     (opcode-cell-p (car row))))

  (defthm opcode-row-p-implies-opcode-row-p-of-cdr
    (implies
     (opcode-row-p row)
     (opcode-row-p (cdr row)))))

(define opcode-map-p (map)
  (if (atom map)
      (eq map nil)
    (and (opcode-row-p (car map))
	 (opcode-map-p (cdr map))))
  ///
  (defthm opcode-map-p-implies-true-listp
    (implies (opcode-map-p map)
	     (true-listp map))
    :rule-classes :forward-chaining)

  (defthm opcode-map-p-implies-true-list-listp
    (implies (opcode-map-p map)
	     (true-list-listp map))
    :rule-classes :forward-chaining))

(define len-of-each-row-okay-p ((x true-list-listp))
  (if (endp x)
      t
    (and (equal (len (car x)) 16)
	 (len-of-each-row-okay-p (cdr x)))))

(defconst *opcode-descriptor-legal-keys*
  '(:opcode :reg :prefix :mod :r/m :vex :evex :mode))

(define opcode-descriptor-p (opcode-descriptor)
  (if (consp opcode-descriptor)
      (b* ((opcode-identifier (car opcode-descriptor))
	   ((unless (alistp opcode-identifier))
	    (cw "~%Opcode-identifier ~p0 not an alistp!~%" opcode-identifier))
	   (keys (strip-cars opcode-identifier))
	   ((unless (subsetp-equal
		     keys
		     *opcode-descriptor-legal-keys*))
	    (cw "~%Keys ~p0 ill-formed!~%" keys))
	   (opcode-cell (cdr opcode-descriptor))
	   ((unless (simple-cell-p opcode-cell))
	    (cw "~%Cell ~p0 ill-formed!~%" opcode-cell)))
	t)
    (cw "~%Opcode-descriptor ~p0 not a consp!~%"
	opcode-descriptor)))

(define opcode-descriptor-list-p (desc-list)
  (if (atom desc-list)
      (equal desc-list nil)
    (b* ((opcode-descriptor (car desc-list)))
      (and (opcode-descriptor-p opcode-descriptor)
	   (opcode-descriptor-list-p (cdr desc-list)))))
  ///
  (defthm cdr-of-opcode-descriptor-list-p
    (implies (opcode-descriptor-list-p x)
	     (opcode-descriptor-list-p (cdr x)))
    :hints (("Goal" :in-theory (e/d (opcode-descriptor-list-p) ())))))

(define opcode-extensions-map-p (map)
  (if (atom map)
      (equal map nil)
    (b* ((group (car map))
	 ((unless (consp group))
	  (cw "~%Group ~p0 not a consp!~%" group)
	  nil)
	 (group-name (car group))
	 ((unless (keywordp group-name))
	  (cw "~%Group-name ~p0 not a keywordp!~%" group-name)
	  nil)
	 (desc-list (cdr group))
	 ((unless (opcode-descriptor-list-p desc-list))
	  (cw "~%desc-list ~p0 ill-formed!~%" desc-list)
	  nil))
      (opcode-extensions-map-p (cdr map)))))

(defconst *vex-prefix-cases*
  ;; VEX:  [NDS|NDD|DDS].[128|256|LIG|LZ].[66|F2|F3].[0F|0F38|0F3A].[W0|W1|WIG]
  '(:v :unused-vvvv :NDS :NDD :DDS :128 :256 :L0 :L1 :LIG
       :LZ :66 :F2 :F3 :0F :0F38 :0F3A :W0 :W1 :WIG))

(defconst *evex-prefix-cases*
  ;; EVEX: [NDS|NDD|DDS].[128|256|512|LIG|LZ].[66|F2|F3].[0F|0F38|0F3A].[W0|W1|WIG]
  (append '(:ev :512) (remove :v *vex-prefix-cases*)))

(defconst *avx-extra-prefix-cases*
  ;; Note: Modify vex-keyword-case-gen in dispatch.lisp when more elements are
  ;; added here.
  '(:reg :mod))

(define kwd-or-key-consp ((e)
			  (vex? booleanp "@('t') if VEX; @('nil') if EVEX"))
  :enabled t
  (or (and (keywordp e)
	   (if vex? (member e *vex-prefix-cases*) (member e *evex-prefix-cases*)))
      (and (consp e)
	   (member (car e) *avx-extra-prefix-cases*))))

(define kwd-or-key-cons-listp ((lst)
			       (vex? booleanp "@('t') if VEX; @('nil') if EVEX"))
  :short "Recognizer for lists whose elements are either keywords or cons
  pairs whose @('car') is a keyword"
  :enabled t
  (if (atom lst)
      (equal lst nil)
    (and (kwd-or-key-consp (car lst) vex?)
	 (kwd-or-key-cons-listp (cdr lst) vex?))))

(define avx-cases-okp ((lst)
		       (vex? booleanp "@('t') if VEX; @('nil') if EVEX"))
  :enabled t
  (kwd-or-key-cons-listp lst vex?))

(define avx-opcode-cases-okp ((lst)
			      (vex? booleanp "@('t') if VEX; @('nil') if EVEX"))
  (if (atom lst)
      (equal lst nil)
    (b* ((first (car lst))
	 ((unless (consp first))
	  (cw "~% We expect ~p0 to be a cons pair! ~%" first)
	  nil)
	 (kwd-lst (car first))
	 ((unless (avx-cases-okp kwd-lst vex?))
	  (cw "~% ~p0 contains unrecognized prefix cases! ~%" kwd-lst)
	  nil))
      (avx-opcode-cases-okp (cdr lst) vex?))))

(define avx-maps-well-formed-p ((map)
				(vex? booleanp "@('t') if VEX; @('nil') if EVEX"))
  (if (atom map)
      (equal map nil)
    (b* ((first (car map))
	 ((unless (consp first))
	  (cw "~% We expect each opcode description to be a cons pair: ~p0 isn't! ~%"
	      first)
	  nil)
	 (opcode (car first))
	 ((unless (natp opcode))
	  (cw "~% We expect opcodes to be the keys of this alist, but ~p0 isn't!.~%"
	      opcode)
	  nil)
	 (variants (cdr first))
	 ((unless (avx-opcode-cases-okp variants vex?)) nil))
      (avx-maps-well-formed-p (cdr map) vex?))))

;; ----------------------------------------------------------------------

(local
 (defthm one-byte-map-is-well-formed
   (and (opcode-map-p *one-byte-opcode-map-lst*)
	(equal (len *one-byte-opcode-map-lst*) 16)
	(len-of-each-row-okay-p *one-byte-opcode-map-lst*))))

(local
 (defthm two-byte-map-is-well-formed
   (and (opcode-map-p *two-byte-opcode-map-lst*)
	(equal (len *two-byte-opcode-map-lst*) 16)
	(len-of-each-row-okay-p *two-byte-opcode-map-lst*))))

(local
 (defthm first-three-byte-map-is-well-formed
   (and (opcode-map-p *0F-38-three-byte-opcode-map-lst*)
	(equal (len *0F-38-three-byte-opcode-map-lst*) 16)
	(len-of-each-row-okay-p *0F-38-three-byte-opcode-map-lst*))))

(local
 (defthm second-three-byte-map-is-well-formed
   (and (opcode-map-p *0F-3A-three-byte-opcode-map-lst*)
	(equal (len *0F-3A-three-byte-opcode-map-lst*) 16)
	(len-of-each-row-okay-p *0F-3A-three-byte-opcode-map-lst*))))

(local
 (defthm opcode-extensions-map-is-well-formed
   (opcode-extensions-map-p *opcode-extensions-by-group-number*)))

(local
 (defthm vex-maps-are-well-formed
   (and (avx-maps-well-formed-p *vex-0F-opcodes* t)
	(avx-maps-well-formed-p *vex-0F38-opcodes* t)
	(avx-maps-well-formed-p *vex-0F3A-opcodes* t))))

(local
 (defthm evex-maps-are-well-formed
   (and (avx-maps-well-formed-p *evex-0F-opcodes* nil)
	(avx-maps-well-formed-p *evex-0F38-opcodes* nil)
	(avx-maps-well-formed-p *evex-0F3A-opcodes* nil))))

;; ----------------------------------------------------------------------

;; Some interesting resources related to x86 ISA instruction encoding:

;; -- http://www.sandpile.org/x86/opc_enc.htm

;; -- https://www.strchr.com/machine_code_redundancy

;; -- http://www.mlsite.net/blog/?p=76

;; -- http://www.mlsite.net/8086/#tbl_map1 --- this corresponds to
;;    Intel Manuals v24319102, which date back to 1999
;;    (http://datasheets.chipdb.org/Intel/x86/Intel%20Architecture/24319102.pdf).

;; ----------------------------------------------------------------------
