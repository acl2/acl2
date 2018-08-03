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
		       (operation . #.*OP-ADD*))))
	      ("ADD" 2 (E v)  (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADD*))))
	      ("ADD" 2 (G b)  (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADD*))))
	      ("ADD" 2 (G v)  (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADD*))))
	      ("ADD" 2 (:AL)  (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADD*))))
	      ("ADD" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADD*))))
	      ((:i64 . ("PUSH ES" 0
			(:fn . (x86-push-segment-register
				(vex-prefixes  . 0)
				(evex-prefixes . 0)))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH ES is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP ES"  0))
	       (:o64 . ("#UD"  0
			(:fn . (x86-illegal-instruction
				(message .
					 "POP ES is illegal in the 64-bit mode!"))))))
	      ("OR" 2 (E b)  (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-OR*))))
	      ("OR" 2 (E v)  (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-OR*))))
	      ("OR" 2 (G b)  (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-OR*))))
	      ("OR" 2 (G v)  (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-OR*))))
	      ("OR" 2 (:AL)  (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-OR*))))
	      ("OR" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-OR*))))
	      ((:i64 . ("PUSH CS" 0
			(:fn . (x86-push-segment-register
				(vex-prefixes  . 0)
				(evex-prefixes . 0)))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH CS is illegal in the 64-bit mode!"))))))
	      (:2-byte-escape
	       (:fn . (two-byte-opcode-decode-and-execute
		       ;; vex-prefixes is 0 here because we won't ever transfer
		       ;; to the two- or three-byte opcode maps from the
		       ;; one-byte opcode map in the presence of vex prefixes.
		       ;; See x86-fetch-decode-execute and
		       ;; vex-decode-and-execute for details.
		       (vex-prefixes . 0)
		       (evex-prefixes . 0)
		       (escape-byte . opcode)))))

    #| 10 |# (("ADC" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADC*))))
	      ("ADC" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADC*))))
	      ("ADC" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADC*))))
	      ("ADC" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADC*))))
	      ("ADC" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADC*))))
	      ("ADC" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADC*))))
	      ((:i64 . ("PUSH SS" 0
			(:fn . (x86-push-segment-register
				(vex-prefixes  . 0)
				(evex-prefixes . 0)))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH SS is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP SS" 0))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "POP SS is illegal in the 64-bit mode!"))))))
	      ("SBB" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SBB*))))
	      ("SBB" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SBB*))))
	      ("SBB" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SBB*))))
	      ("SBB" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SBB*))))
	      ("SBB" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SBB*))))
	      ("SBB" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SBB*))))
	      ((:i64 . ("PUSH DS" 0
			(:fn . (x86-push-segment-register
				(vex-prefixes  . 0)
				(evex-prefixes . 0)))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH DS is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP DS" 0))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "POP DS is illegal in the 64-bit mode!")))))))

    #| 20 |# (("AND" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-AND*))))
	      ("AND" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-AND*))))
	      ("AND" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-AND*))))
	      ("AND" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-AND*))))
	      ("AND" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-AND*))))
	      ("AND" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-AND*))))
	      (:prefix-ES
	       (:fn . (:no-instruction)))
	      ((:i64 . ("DAA" 0))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "DAA is illegal in the 64-bit mode!"))))))
	      ("SUB" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SUB*))))
	      ("SUB" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SUB*))))
	      ("SUB" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SUB*))))
	      ("SUB" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SUB*))))
	      ("SUB" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SUB*))))
	      ("SUB" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SUB*))))
	      (:prefix-CS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("DAS" 0))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "DAS is illegal in the 64-bit mode!")))))))

    #| 30 |# (("XOR" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-XOR*))))
	      ("XOR" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-XOR*))))
	      ("XOR" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-XOR*))))
	      ("XOR" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-XOR*))))
	      ("XOR" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-XOR*))))
	      ("XOR" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-XOR*))))
	      (:prefix-SS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("AAA" 0))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "AAA is illegal in the 64-bit mode!"))))))
	      ("CMP" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-CMP*))))
	      ("CMP" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-CMP*))))
	      ("CMP" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-CMP*))))
	      ("CMP" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-CMP*))))
	      ("CMP" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-CMP*))))
	      ("CMP" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-CMP*))))
	      (:prefix-DS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("AAS" 0))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "AAS is illegal in the 64-bit mode!")))))))

    #| 40 |# (((:o64  . (:rex (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eAX)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-b (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eCX)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-x (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eDX)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-xb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eBX)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-r (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eSP)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-rb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eBP)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-rx (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eSI)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-rxb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eDI)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-w (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eAX)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-wb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eCX)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-wx (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eDX)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-wxb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eBX)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-wr (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eSP)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-wrb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eBP)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-wrx (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eSI)
			(:fn . (x86-inc/dec-4x)))))
	      ((:o64  . (:rex-wrxb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eDI)
			(:fn . (x86-inc/dec-4x))))))

    #| 50 |# (("PUSH" 1 (:rAX/r8)   :d64
	       (:fn . (x86-push-general-register)))
	      ("PUSH" 1 (:rCX/r9)   :d64
	       (:fn . (x86-push-general-register)))
	      ("PUSH" 1 (:rDX/r10)  :d64
	       (:fn . (x86-push-general-register)))
	      ("PUSH" 1 (:rBX/r11)  :d64
	       (:fn . (x86-push-general-register)))
	      ("PUSH" 1 (:rSP/r11)  :d64
	       (:fn . (x86-push-general-register)))
	      ("PUSH" 1 (:rBP/r13)  :d64
	       (:fn . (x86-push-general-register)))
	      ("PUSH" 1 (:rSI/r14)  :d64
	       (:fn . (x86-push-general-register)))
	      ("PUSH" 1 (:rDI/r15)  :d64
	       (:fn . (x86-push-general-register)))
	      ("POP"  1 (:rAX/r8)   :d64
	       (:fn . (x86-pop-general-register)))
	      ("POP"  1 (:rCX/r9)   :d64
	       (:fn . (x86-pop-general-register)))
	      ("POP"  1 (:rDX/r10)  :d64
	       (:fn . (x86-pop-general-register)))
	      ("POP"  1 (:rBX/r11)  :d64
	       (:fn . (x86-pop-general-register)))
	      ("POP"  1 (:rSP/r11)  :d64
	       (:fn . (x86-pop-general-register)))
	      ("POP"  1 (:rBP/r13)  :d64
	       (:fn . (x86-pop-general-register)))
	      ("POP"  1 (:rSI/r14)  :d64
	       (:fn . (x86-pop-general-register)))
	      ("POP"  1 (:rDI/r15)  :d64
	       (:fn . (x86-pop-general-register))))

    #| 60 |# (((:i64 . ("PUSHA/PUSHAD" 0
			(:fn . (x86-pusha))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSHA is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POPA/POPAD"   0
			(:fn . (x86-popa))))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "POPA is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("BOUND"  2 (G v) (M a)))
	       (:o64 . (:evex-byte0 (:fn . (:no-instruction)))
		     ;; ("#UD" 0
		     ;;  (:fn . (x86-illegal-instruction
		     ;;          (message .
		     ;;                   "BOUND is illegal in the 64-bit mode!"))))
		     ))
	      ((:o64 . ("MOVSXD" 2 (G v) (E v)
			(:fn . (x86-one-byte-movsxd))))
	       (:i64 . ("ARPL"   2 (E w) (G w))))
	      (:prefix-FS
	       (:fn . (:no-instruction)))
	      (:prefix-GS
	       (:fn . (:no-instruction)))
	      (:prefix-OpSize
	       (:fn . (:no-instruction)))
	      (:prefix-AddrSize
	       (:fn . (:no-instruction)))
	      ("PUSH" 1 (I z) :d64
	       (:fn . (x86-push-I)))
	      ("IMUL"  3 (G v) (E v) (I z)
	       (:fn . (x86-imul-Op/En-RMI)))
	      ("PUSH" 1 (I b) :d64
	       (:fn . (x86-push-I)))
	      ("IMUL"  3 (G v) (E v) (I b)
	       (:fn . (x86-imul-Op/En-RMI)))
	      ("INS/INSB" 2 (Y b) (D x))
	      ("INS/INSW/INSD" 2 (Y z) (D x))
	      ("OUTS/OUTSB" 2 (Y b) (D x))
	      ("OUTS/OUTSW/OUTSD" 2 (Y z) (D x)))

    #| 70 |# (("JO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JNO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JB/NAE/C" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JNB/AE/NC" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JZ/E" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JNZ/NE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JBE/NA" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JNBE/A" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JS" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JNS" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JP/PE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JNP/PO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JL/NGE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JNL/GE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JLE/NG" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc)))
	      ("JNLE/G" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))))

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
			(operation .  #.*OP-TEST*))))
	       ("TEST" 2 (E v) (G v)
		(:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
			(operation .  #.*OP-TEST*))))
	       ("XCHG" 2 (E b) (G b)
		(:fn . (x86-xchg)))
	       ("XCHG" 2 (E v) (G v)
		(:fn . (x86-xchg)))
	       ("MOV" 2 (E b) (G b)
		(:fn . (x86-mov-Op/En-MR)))
	       ("MOV" 2 (E v) (G v)
		(:fn . (x86-mov-Op/En-MR)))
	       ("MOV" 2 (G b) (E b)
		(:fn . (x86-mov-Op/En-RM)))
	       ("MOV" 2 (G v) (E v)
		(:fn . (x86-mov-Op/En-RM)))
	       ("MOV" 2 (E v) (S w))
	       ("LEA" 2 (G v) (M)
		(:fn . (x86-lea)))
	       ("MOV" 2 (S w) (E w))
	       ;; in Table A-6, Grp 1A only contains POP,
	       ;; so we leave the latter implicit here:
	       (:Group-1A 1 (E v) :1a :d64))

    #| 90 |# (("XCHG" 1 (:r8)
	       (:fn . (x86-xchg)))
	      ("XCHG" 2 (:rCX/r9)  (:rAX)
	       (:fn . (x86-xchg)))
	      ("XCHG" 2 (:rDX/r10) (:rAX)
	       (:fn . (x86-xchg)))
	      ("XCHG" 2 (:rBX/r11) (:rAX)
	       (:fn . (x86-xchg)))
	      ("XCHG" 2 (:rSP/r12) (:rAX)
	       (:fn . (x86-xchg)))
	      ("XCHG" 2 (:rBP/r13) (:rAX)
	       (:fn . (x86-xchg)))
	      ("XCHG" 2 (:rSI/r14) (:rAX)
	       (:fn . (x86-xchg)))
	      ("XCHG" 2 (:rDI/r15) (:rAX)
	       (:fn . (x86-xchg)))
	      ("CBW/CWDE/CDQE" 0
	       (:fn . (x86-cbw/cwd/cdqe)))
	      ("CWD/CDQ/CQO" 0
	       (:fn . (x86-cwd/cdq/cqo)))
	      ((:i64 . ("CALL" 1 (A p)))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "far CALL is illegal in the 64-bit mode!"))))))
	      ("FWAIT/WAIT" 0)
	      ("PUSHF/D/Q"  1 (F v) :d64
	       (:fn . (x86-pushf)))
	      ("POPF/D/Q"   1 (F v) :d64
	       (:fn . (x86-popf)))
	      ("SAHF" 0
	       (:fn . (x86-sahf)))
	      ("LAHF" 0
	       (:fn . (x86-lahf))))

    #| a0 |# (("MOV" 2 (:AL) (O b)
	       (:fn . (x86-mov-Op/En-FD)))
	      ("MOV" 2 (:rAX) (O v)
	       (:fn . (x86-mov-Op/En-FD)))
	      ("MOV" 2 (O b) (:AL))
	      ("MOV" 2 (O v) (:rAX))
	      ("MOVS/B" 2 (Y b) (X b)
	       (:fn . (x86-movs)))
	      ("MOVS/W/D/Q" 2 (Y v) (X v)
	       (:fn . (x86-movs)))
	      ("CMPS/B"   2 (X b) (Y b)
	       (:fn . (x86-cmps)))
	      ("CMPS/W/D" 2 (X v) (Y v)
	       (:fn . (x86-cmps)))
	      ("TEST" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-TEST*))))
	      ("TEST" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-TEST*))))
	      ("STOS/B" 2 (Y b) (:AL)
	       (:fn . (x86-stos)))
	      ("STOS/W/D/Q" 2 (Y v) (:rAX)
	       (:fn . (x86-stos)))
	      ("LODS/B" 2 (:AL) (X b))
	      ("LODS/W/D/Q" 2 (:rAX) (X v))
	      ("SCAS/B" 2 (:AL) (Y b))
	      ("SCAS/W/D/Q" 2 (:rAX) (Y v)))

    #| b0 |# (("MOV" 2  (:AL/r8L)  (I b)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:CL/r9L)  (I b)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:DL/r10L) (I b)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:BL/r11L) (I b)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:AH/r12L) (I b)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:CH/r13L) (I b)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:DH/r14L) (I b)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:BH/r15L) (I b)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:rAX/r8)  (I v)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:rCX/r9)  (I v)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:rDX/r10) (I v)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:rBX/r11) (I v)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:rSP/r12) (I v)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:rBP/r13) (I v)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:rSI/r14) (I v)
	       (:fn . (x86-mov-Op/En-OI)))
	      ("MOV" 2  (:rDI/r15) (I v)
	       (:fn . (x86-mov-Op/En-OI))))

    #| c0 |# ((:Group-2 2 (E b) (I b) :1a)
	      (:Group-2 2 (E v) (I b) :1a)
	      ("RET" 1 (I w) :f64
	       (:fn . (x86-ret)))
	      ("RET" 0 :f64
	       (:fn . (x86-ret)))
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
	       (:i64 . ("LES" 2 (G z) (M p))))
	      ((:o64 . (:vex2-byte0 (:fn . (:no-instruction))))
	       (:i64 . ("LDS" 2 (G z) (M p))))
	      (:Group-11 2 (E b) (I b) :1a)
	      (:Group-11 2 (E v) (I z) :1a)
	      ("ENTER" 2 (I w) (I b))
	      ("LEAVE" 0 :d64
	       (:fn . (x86-leave)))
	      ("RET" 1 (I w))
	      ("RET" 0)
	      ("INT3" 0)
	      ("INT" 1 (I b))
	      ((:i64 . ("INTO" 0))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "INTO is illegal in the 64-bit mode!"))))))
	      ("IRET/D/Q" 0))

    #| d0 |# ((:Group-2 2 (E b) (1) :1a)
	      (:Group-2 2 (E v) (1) :1a)
	      (:Group-2 2 (E b) (:CL) :1a)
	      (:Group-2 2 (E v) (:CL) :1a)
	      ((:i64 . ("AAM" 1 (I b)))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "AAM is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("AAD" 1 (I b)))
	       (:o64 . ("#UD" 0
			(:fn . (x86-illegal-instruction
				(message .
					 "AAD is illegal in the 64-bit mode!"))))))
	      (:none
	       (:fn . (:no-instruction)))
	      ("XLAT/XLATB" 0)
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
	       (:fn . (x86-loop)))
	      ("LOOPE/LOOPZ" 1 (J b) :f64
	       (:fn . (x86-loop)))
	      ("LOOP" 1 (J b) :f64
	       (:fn . (x86-loop)))
	      ("JrCXZ" 1 (J b) :f64
	       (:fn . (x86-jrcxz)))
	      ("IN" 2 (:AL) (I b))
	      ("IN" 2 (:eAX) (I b))
	      ("OUT" 2 (I b) (:AL))
	      ("OUT" 2 (I b) (:eAX))
	      ("CALL" 1 (J z) :f64
	       (:fn . (x86-call-E8-Op/En-M)))
	      ("JMP"  1 (J z) :f64
	       (:fn . (x86-near-jmp-Op/En-D)))
	      ((:i64 . ("JMP"  1 (A p)))
	       (:o64 . ("#UD"  0
			(:fn . (x86-illegal-instruction
				(message .
					 "JMP is illegal in the 64-bit mode!"))))))
	      ("JMP"  1 (J b) :f64
	       (:fn . (x86-near-jmp-Op/En-D)))
	      ("IN" 2  (:AL) (:DX))
	      ("IN" 2  (:eAX) (:DX))
	      ("OUT" 2 (:DX) (:AL))
	      ("OUT" 2 (:DX) (:eAX)))

    #| f0 |# ((:prefix-Lock
	       (:fn . (:no-instruction)))
	      ("INT1" 0)
	      (:prefix-REPNE
	       (:fn . (:no-instruction)))
	      (:prefix-REP/REPE
	       (:fn . (:no-instruction)))
	      ("HLT" 0
	       (:fn . (x86-hlt)))
	      ("CMC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std)))
	      (:Group-3 1 (E b) :1a)
	      (:Group-3 1 (E v) :1a)
	      ("CLC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std)))
	      ("STC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std)))
	      ("CLI" 0)
	      ("STI" 0)
	      ("CLD" 0
	       (:fn . (x86-cmc/clc/stc/cld/std)))
	      ("STD" 0
	       (:fn . (x86-cmc/clc/stc/cld/std)))
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
	      ("LAR" 2 (G v) (E w))
	      ("LSL" 2 (G v) (E w))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:o64 . ("SYSCALL" 0
			(:fn . (x86-syscall-both-views))))
	       (:i64 . (:none
			(:fn . (:no-instruction)))))
	      ("CLTS" 0)
	      ((:o64 . ("SYSRET" 0
			(:fn . (x86-sysret))))
	       (:i64 . (:none
			(:fn . (:no-instruction)))))
    #| 08 |#  ("INVD" 0)
	      ("WBINVD" 0)
	      (:none
	       (:fn . (:no-instruction)))
	      ("UD2" 0 :1b)
	      (:none
	       (:fn . (:no-instruction)))
	      ("prefetchw(/1)" 1 (E v))
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
	       (:fn . (x86-two-byte-nop))))

    #| 20 |# (("MOV" 2 (R d) (C d)
	       (:fn . (x86-mov-control-regs-Op/En-MR)))
	      ("MOV" 2 (R d) (D d))
	      ("MOV" 2 (C d) (R d))
	      ("MOV" 2 (D d) (R d))
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

    #| 30 |# (("WRMSR" 0)
	      ("RDTSC" 0)
	      ("RDMSR" 0)
	      ("RDPMC" 0)
	      ("SYSENTER" 0)
	      ("SYSEXIT" 0)
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
	       (:fn . (x86-cmovcc)))
	      ("CMOVNO" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVB/C/NAE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVAE/NB/NC" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVE/Z" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVNE/NZ" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVBE/NA" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVA/NBE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
    #| 48 |#  ("CMOVS" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVNS" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVP/PE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVNP/PO" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVL/NGE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVNL/GE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVLE/NG" 2 (G v) (E v)
	       (:fn . (x86-cmovcc)))
	      ("CMOVNLE/G" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))))

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
		(:fn . (x86-two-byte-jcc)))
	       ("JNO" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JB/NAE/C" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JNB/AE/NC" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JZ/E" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JNZ/NE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JBE/NA" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JNBE/A" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
    #| 88 |#   ("JS" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JNS" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JP/PE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JNP/PO" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JL/NGE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JNL/GE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JLE/NG" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc)))
	       ("JNLE/G" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))))

    #| 90 |# (("SETO" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETNO" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETB/NAE/C" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETNB/AE/NC" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETZ/E" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETNZ/NE" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETBE/NA" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETNBE/A" 1 (E b)
	       (:fn . (x86-setcc)))
    #| 98 |#  ("SETS" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETNS" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETP/PE" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETNP/PO" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETL/NGE" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETNL/GE" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETLE/NG" 1 (E b)
	       (:fn . (x86-setcc)))
	      ("SETNLE/G" 1 (E b)
	       (:fn . (x86-setcc))))

    #| a0 |# (("PUSH"  1 (:FS) :d64
	       (:fn . (x86-push-segment-register)))
	      ("POP"   1 (:FS) :d64)
	      ("CPUID" 0)
	      ("BT" 2 (E v) (G v)
	       (:fn . (x86-bt-0f-a3)))
	      ("SHLD" 3 (E v) (G v) (I b))
	      ("SHLD" 3 (E v) (G v) (:CL))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| a8 |#  ("PUSH"  1 (:GS) :d64
	       (:fn . (x86-push-segment-register)))
	      ("POP"   1 (:GS) :d64)
	      ("RSM" 0)
	      ("BTS" 2 (E v) (G v))
	      ("SHRD" 3 (E v) (G v) (I b))
	      ("SHRD" 3 (E v) (G v) (:CL))
	      (:Group-15 0 :1a :1c)
	      ("IMUL" 2 (G v) (E v)
	       (:fn . (x86-imul-Op/En-RM))))

    #| b0 |# (("CMPXCHG" 2 (E b) (G b)
	       (:fn . (x86-cmpxchg)))
	      ("CMPXCHG" 2 (E v) (G v)
	       (:fn . (x86-cmpxchg)))
	      ("LSS" 2 (G v) (M p))
	      ("BTR" 2 (E v) (G v))
	      ("LFS" 2 (G v) (M p))
	      ("LGS" 2 (G v) (M p))
	      ("MOVZX" 2 (G v) (E b)
	       (:fn . (x86-movzx)))
	      ("MOVZX" 2 (G v) (E w)
	       (:fn . (x86-movzx)))
    #| b8 |#  ((:no-prefix . ("JMPE"   0))
	       (:F3        . ("POPCNT" 2 (G v) (E v))))

	      (:Group-10 0 :1a :1b)

	      (:Group-8 2 (E v) (I b) :1a)

	      ("BTC" 2 (E v) (G v))

	      ((:no-prefix . ("BSF"   2 (G v) (E v)
			      (:fn . (x86-bsf-Op/En-RM))))
	       (:F3        . ("TZCNT" 2 (G v) (E v))))

	      ((:no-prefix . ("BSR"   2 (G v) (E v)))
	       (:F3        . ("LZCNT" 2 (G v) (E v))))

	      ("MOVSX" 2 (G v) (E b)
	       (:fn . (x86-two-byte-movsxd)))
	      ("MOVSX" 2 (G v) (E w)
	       (:fn . (x86-two-byte-movsxd))))

    #| c0 |# (("XADD"     2 (E b)  (G b))

	      ("XADD"     2 (E v)  (G v))

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

	      ("MOVNTI"     2 (M y)   (G y))

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

    #| c8 |#  ("BSWAP" 1 (:RAX/EAX/R8/R8D))
	      ("BSWAP" 1 (:RCX/ECX/R9/R9D))
	      ("BSWAP" 1 (:RDX/EDX/R10/R10D))
	      ("BSWAP" 1 (:RBX/EBX/R11/R11D))
	      ("BSWAP" 1 (:RSP/ESP/R12/R12D))
	      ("BSWAP" 1 (:RBP/EBP/R13/R13D))
	      ("BSWAP" 1 (:RSI/ESI/R14/R14D))
	      ("BSWAP" 1 (:RDI/EDI/R15/R15D)))

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
			  (operation . #.*OP-ADD*)))))
	       (((:opcode . #x80)
		 (:reg    . #b001)) .
		 ("OR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))))
	       (((:opcode . #x80)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))))
	       (((:opcode . #x80)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))))
	       (((:opcode . #x80)
		 (:reg    . #b100)) .
		 ("AND" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))))
	       (((:opcode . #x80)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))))
	       (((:opcode . #x80)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))))
	       (((:opcode . #x80)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))))

	       (((:opcode . #x81)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))))
	       (((:opcode . #x81)
		 (:reg    . #b001)) .
		 ("OR" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))))
	       (((:opcode . #x81)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))))
	       (((:opcode . #x81)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))))
	       (((:opcode . #x81)
		 (:reg    . #b100)) .
		 ("AND" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))))
	       (((:opcode . #x81)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))))
	       (((:opcode . #x81)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))))
	       (((:opcode . #x81)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))))

	       (((:opcode . #x82)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))))
	       (((:opcode . #x82)
		 (:reg    . #b001)) .
		 ("OR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))))
	       (((:opcode . #x82)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))))
	       (((:opcode . #x82)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))))
	       (((:opcode . #x82)
		 (:reg    . #b100)) .
		 ("AND" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))))
	       (((:opcode . #x82)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))))
	       (((:opcode . #x82)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))))
	       (((:opcode . #x82)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))))

	       (((:opcode . #x83)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))))
	       (((:opcode . #x83)
		 (:reg    . #b001)) .
		 ("OR" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))))
	       (((:opcode . #x83)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))))
	       (((:opcode . #x83)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))))
	       (((:opcode . #x83)
		 (:reg    . #b100)) .
		 ("AND" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))))
	       (((:opcode . #x83)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))))
	       (((:opcode . #x83)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))))
	       (((:opcode . #x83)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))))))

    (:Group-1A . ;; Covers opcode 8F.
	       ((((:opcode . #x8F)
		  (:reg    . #b000)) .
		  ("POP" 1 (E v) :1a :d64
		   (:fn . (x86-pop-Ev))))
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
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC0)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC0)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC0)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC0)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC0)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC0)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC0)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))

		(((:opcode . #xC1)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC1)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC1)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC1)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC1)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC1)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xC1)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC1)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))

		(((:opcode . #xD0)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD0)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD0)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD0)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD0)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD0)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD0)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD0)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))

		(((:opcode . #xD1)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD1)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD1)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD1)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD1)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD1)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD1)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD1)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))

		(((:opcode . #xD2)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD2)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD2)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD2)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD2)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD2)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD2)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD2)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))

		(((:opcode . #xD3)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD3)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD3)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD3)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD3)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD3)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))
		(((:opcode . #xD3)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD3)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))))))

    (:Group-3 . ;; Covers opcodes F6 and F7.
	      ((((:opcode . #xF6)
		 (:reg    . #b000)) .
		 ("TEST" 1 (E b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-TEST*)))))
	       (((:opcode . #xF6)
		 (:reg    . #b001)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xF6)
		 (:reg    . #b010)) .
		 ("NOT" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))))
	       (((:opcode . #xF6)
		 (:reg    . #b011)) .
		 ("NEG" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))))
	       (((:opcode . #xF6)
		 (:reg    . #b100)) .
		 ("MUL" 1 (E b) :1a
		  (:fn . (x86-mul))))
	       (((:opcode . #xF6)
		 (:reg    . #b101)) .
		 ("IMUL" 1 (E b) :1a
		  (:fn . (x86-imul-Op/En-M))))
	       (((:opcode . #xF6)
		 (:reg    . #b110)) .
		 ("DIV" 1 (E b) :1a
		  (:fn . (x86-div))))
	       (((:opcode . #xF6)
		 (:reg    . #b111)) .
		 ("IDIV" 1 (E b) :1a
		  (:fn . (x86-idiv))))

	       (((:opcode . #xF7)
		 (:reg    . #b000)) .
		 ("TEST" 1 (E b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-TEST*)))))
	       (((:opcode . #xF7)
		 (:reg    . #b001)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xF7)
		 (:reg    . #b010)) .
		 ("NOT" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))))
	       (((:opcode . #xF7)
		 (:reg    . #b011)) .
		 ("NEG" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))))
	       (((:opcode . #xF7)
		 (:reg    . #b100)) .
		 ("MUL" 1 (E b) :1a
		  (:fn . (x86-mul))))
	       (((:opcode . #xF7)
		 (:reg    . #b101)) .
		 ("IMUL" 1 (E b) :1a
		  (:fn . (x86-imul-Op/En-M))))
	       (((:opcode . #xF7)
		 (:reg    . #b110)) .
		 ("DIV" 1 (E b) :1a
		  (:fn . (x86-div))))
	       (((:opcode . #xF7)
		 (:reg    . #b111)) .
		 ("IDIV" 1 (E b) :1a
		  (:fn . (x86-idiv))))))

    (:Group-4 . ;; Covers opcode FE.
	      ((((:opcode . #xFE)
		 (:reg    . #b000)) .
		 ("INC" 1 (E b) :1a
		  (:fn . (x86-inc/dec-FE-FF))))
	       (((:opcode . #xFE)
		 (:reg    . #b001)) .
		 ("DEC" 1 (E b) :1a
		  (:fn . (x86-inc/dec-FE-FF))))
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
		  (:fn . (x86-inc/dec-FE-FF))))
	       (((:opcode . #xFF)
		 (:reg    . #b001)) .
		 ("DEC" 1 (E v) :1a
		  (:fn . (x86-inc/dec-FE-FF))))
	       (((:opcode . #xFF)
		 (:reg    . #b010)) .
		 ("near CALL"  1 (E v) :1a :f64
		  (:fn . (x86-call-FF/2-Op/En-M))))
	       (((:opcode . #xFF)
		 (:reg    . #b011)) .
		 ("far CALL"  1 (E p) :1a))
	       (((:opcode . #xFF)
		 (:reg    . #b100)) .
		 ("near JMP"  1 (E v) :1a :f64
		  (:fn . (x86-near-jmp-Op/En-M))))
	       (((:opcode . #xFF)
		 (:reg    . #b101)) .
		 ("far JMP"  1 (M p) :1a
		  (:fn . (x86-far-jmp-Op/En-D))))
	       (((:opcode . #xFF)
		 (:reg    . #b110)) .
		 ("PUSH"  1 (E v) :1a :d64
		  (:fn . (x86-push-Ev))))
	       (((:opcode . #xFF)
		 (:reg    . #b111)) .
		 (:none
		  (:fn . (:no-instruction))))))


    (:Group-6 . ;; Covers opcode 0F 00.
	      ((((:opcode . #ux0F_00)
		 (:reg    . #b000)) .
		 (:ALT
		  (("SLDT" 1 (R v) :1a)
		   ("SLDT" 1 (M w) :1a))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b001)) .
		 (:ALT
		  (("STR" 1 (R v) :1a)
		   ("STR" 1 (M w) :1a))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b010)) .
		 ("LLDT" 1 (E w) :1a
		  (:fn . (x86-lldt))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b011)) .
		 ("LTR" 1 (E w) :1a))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b100)) .
		 ("VERR" 1 (E w) :1a))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b101)) .
		 ("VERW" 1 (E w) :1a))
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
		 ("SGDT" 1 (M s) :1a))
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
		 ("SIDT" 1 (M s) :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b000)) .
		 ("MONITOR" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b001)) .
		 ("MWAIT" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b010)) .
		 ("CLAC" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b011)) .
		 ("STAC" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b111)) .
		 ("ENCLS" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . :mem)
		 (:reg    . #b010)) .
		 ("LGDT" 1 (M s) :1a
		  (:fn . (x86-lgdt))))
	       (((:opcode . #ux0F_01)
		 (:mod    . :mem)
		 (:reg    . #b011)) .
		 ("LIDT" 1 (M s) :1a
		  (:fn . (x86-lidt))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b000)) .
		 ("XGETBV" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b001)) .
		 ("XSETBV" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b100)) .
		 ("VMFUNC" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b101)) .
		 ("XEND" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b110)) .
		 ("XTEST" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b111)) .
		 ("ENCLU" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b100)) .
		 (:ALT
		  (("SMSW" 1 (M w) :1a)
		   ("SMSW" 1 (R v) :1a))))
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
		 ("LMSW" 1 (E w) :1a))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b111)
		 (:r/m    . :mem)) .
		 ("INVLPG" 1 (M b) :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b111)
		 (:r/m    . #b000)) .
		 ("SWAPGS" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b111)
		 (:r/m    . #b001)) .
		 ("RDTSCP" 0 :1a))))

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
		  (:fn . (x86-bt-0f-ba))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b101)) .
		 ("BTS" 2 (E b) (I b) :1a))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b110)) .
		 ("BTR" 2 (E b) (I b) :1a))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b111)) .
		 ("BTC" 2 (E b) (I b) :1a))))

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
		   ("CMPXCHG16B" 1 (M dq) :1a))))
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
		  (:fn . (x86-rdrand))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . nil)
		 (:reg    . #b111)) .
		 ("RDSEED" 1 (R v) :1a))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :F3)
		 (:reg    . #b111)) .
		 (:ALT
		  (("RDPID" 1 (R d) :1a)
		   ("RDPID" 1 (R q) :1a))))))

    (:Group-10 . ;; Covers opcode 0F B9.
	       ((((:opcode . #ux0F_B9)) .
		 ("UD1" 0 :1a))))

    (:Group-11 . ;; Covers opcodes C6 and C7.
	       ((((:opcode . #xC6)
		  (:reg    . #b000)) .
		  ("MOV" 2 (E b) (I b) :1a
		   (:fn . (x86-mov-Op/En-MI))))
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
		  ("XABORT" 1 (I b) :1a))

		(((:opcode . #xC7)
		  (:reg    . #b000)) .
		  ("MOV" 2 (E v) (I z) :1a
		   (:fn . (x86-mov-Op/En-MI))))
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
		  ("XBEGIN" 1 (J z) :1a))))

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
		  ("FXSAVE" 0 :1a))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b000)) .
		  ("RDFSBASE" 1 (R y) :1a))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b001)) .
		  ("FXRSTOR" 0 :1a))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b001)) .
		  ("RDGSBASE" 1 (R y) :1a))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b010)) .
		  ("LDMXCSR" 0 :1a
		   (:fn . (x86-ldmxcsr/stmxcsr-Op/En-M))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("WRFSBASE" 1 (R y) :1a))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b011)) .
		  ("STMXCSR" 0 :1a
		   (:fn . (x86-ldmxcsr/stmxcsr-Op/En-M))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b011)) .
		  ("WRGSBASE" 1 (R y) :1a))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . :mem)
		  (:reg    . #b100)) .
		  ("XSAVE" 0 :1a))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b101)) .
		  (:ALT
		   (("XRSTOR" 0 :1a)
		    ("LFENCE" 0 :1a))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  (:ALT
		   (("XSAVEOPT" 0 :1a)
		    ("MFENCE" 0 :1a))))
		(((:opcode . #ux0F_AE)
		  (:prefix . nil)
		  (:mod    . #b11)
		  (:reg    . #b111)) .
		  (:ALT
		   (("CLFLUSH" 0 :1a)
		    ("SFENCE"  0 :1a))))))

    (:Group-16 . ;; Covers opcode 0F 18.
	       ((((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b000)) .
		  ("PREFETCHNTA" 0 :1a))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b001)) .
		  ("PREFETCHT0" 0 :1a))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b010)) .
		  ("PREFETCHT1" 0 :1a))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b011)) .
		  ("PREFETCHT2" 0 :1a))
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
	   (new-rest (remove-semantic-function-info-p rest))
	   (semantic-info (get-semantic-function-info-p rest)))
	(cond ((equal first :ALT)
	       (and
		(true-listp new-rest)
		(basic-simple-cells-p (car new-rest))
		(equal (cdr new-rest) nil)
		(semantic-function-info-p semantic-info)))
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
  '(:opcode :reg :prefix :mod :r/m :vex :evex))

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

;; ----------------------------------------------------------------------

;; Some interesting resources related to x86 ISA instruction encoding:

;; -- http://www.sandpile.org/x86/opc_enc.htm

;; -- https://www.strchr.com/machine_code_redundancy

;; -- http://www.mlsite.net/blog/?p=76

;; -- http://www.mlsite.net/8086/#tbl_map1 --- this corresponds to
;;    Intel Manuals v24319102, which date back to 1999
;;    (http://datasheets.chipdb.org/Intel/x86/Intel%20Architecture/24319102.pdf).

;; ----------------------------------------------------------------------
