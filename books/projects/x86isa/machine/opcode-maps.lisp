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
; Contributing Author(s):
; Rob Sumners         <rsumners@centtech.com>

(in-package "X86ISA")

(include-book "std/util/define" :dir :system)
(include-book "std/strings/hexify" :dir :system)
(local (include-book "std/strings/substrp" :dir :system))
(local (include-book "std/strings/isubstrp" :dir :system))

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

;; Annotations of the Opcode Maps:

;; TL;DR: See functions opcode-map-p and avx-maps-well-formed-p for information
;; about the layout, annotations, etc. of our representation of Intel's opcode
;; maps.

;; ------------------------------------------------------------
;; Annotations that list the instruction semantic functions
;; ------------------------------------------------------------

;; We annotate each opcode in our representation of the opcode maps with the
;; instruction semantic function that implements that opcode.  We use these
;; annotations to generate code that dispatches control to the appropriate
;; instruction semantic function once the instruction has been "sufficiently"
;; decoded (see x86-fetch-decode-execute), and to generate coverage reports
;; (i.e., which opcodes, in which modes, have been implemented in x86isa,
;; etc.).

;; <fn-annotation> should always be a true-listp.

;; 1. <fn-annotation> can be 'nil, which means that this opcode is unsupported by
;;    the x86isa books.  Semantic function x86-step-unimplemented should be
;;    called here, and this opcode should be marked as "unimplemented" in
;;    x86isa.

;;    General format: 'nil

;; In the rest of the list below, <fn-annotation> takes the form:
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

;; ------------------------------------------------------------
;; Annotations that list the decode-time exceptions
;; ------------------------------------------------------------
;;
;; --- Only exceptions for the protected, compatibility, and 64-bit mode have
;;     been specified.
;;
;; --- TODO: What's the exception scenario for RESERVEDNOP (Group 16,
;;     #ux0F_18)?

;; ----------------------------------------

(defconst *one-byte-opcode-map-lst*
  ;; Source: Intel Volume 2, Table A-2.

  '(
    #|       -------------------------------        |#

    #| 00 |# (("ADD" 2 (E b)  (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADD*)))
	       (:ud . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("ADD" 2 (E v)  (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADD*)))
	       (:ud . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("ADD" 2 (G b)  (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADD*)))
	       (:ud . ((ud-Lock-used))))
	      ("ADD" 2 (G v)  (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADD*)))
	       (:ud . ((ud-Lock-used))))
	      ("ADD" 2 (:AL)  (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADD*)))
	       (:ud . ((ud-Lock-used))))
	      ("ADD" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADD*)))
	       (:ud . ((ud-Lock-used))))
	      ((:i64 . ("PUSH ES" 0
			(:fn . (x86-push-segment-register))
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH ES is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP ES"  0
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD"  0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "POP ES is illegal in the 64-bit mode!"))))))
	      ("OR" 2 (E b)  (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-OR*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("OR" 2 (E v)  (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-OR*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("OR" 2 (G b)  (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-OR*)))
	       (:ud  . ((ud-Lock-used))))
	      ("OR" 2 (G v)  (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-OR*)))
	       (:ud  . ((ud-Lock-used))))
	      ("OR" 2 (:AL)  (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-OR*)))
	       (:ud  . ((ud-Lock-used))))
	      ("OR" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-OR*)))
	       (:ud  . ((ud-Lock-used))))
	      ((:i64 . ("PUSH CS" 0
			(:fn . (x86-push-segment-register))
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH CS is illegal in the 64-bit mode!"))))))
	      (:2-byte-escape
	       (:fn . (two-byte-opcode-decode-and-execute
		       (escape-byte . opcode)))))

    #| 10 |# (("ADC" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADC*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("ADC" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-ADC*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("ADC" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADC*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("ADC" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-ADC*)))
	       (:ud  . ((ud-Lock-used))))
	      ("ADC" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADC*)))
	       (:ud  . ((ud-Lock-used))))
	      ("ADC" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-ADC*)))
	       (:ud  . ((ud-Lock-used))))
	      ((:i64 . ("PUSH SS" 0
			(:fn . (x86-push-segment-register))
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH SS is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP SS" 0
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "POP SS is illegal in the 64-bit mode!"))))))
	      ("SBB" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SBB*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("SBB" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SBB*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("SBB" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SBB*)))
	       (:ud  . ((ud-Lock-used))))
	      ("SBB" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SBB*)))
	       (:ud  . ((ud-Lock-used))))
	      ("SBB" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SBB*)))
	       (:ud  . ((ud-Lock-used))))
	      ("SBB" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SBB*)))
	       (:ud  . ((ud-Lock-used))))
	      ((:i64 . ("PUSH DS" 0
			(:fn . (x86-push-segment-register))
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSH DS is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POP DS" 0
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "POP DS is illegal in the 64-bit mode!")))))))

    #| 20 |# (("AND" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-AND*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("AND" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-AND*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("AND" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-AND*)))
	       (:ud  . ((ud-Lock-used))))
	      ("AND" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-AND*)))
	       (:ud  . ((ud-Lock-used))))
	      ("AND" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-AND*)))
	       (:ud  . ((ud-Lock-used))))
	      ("AND" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-AND*)))
	       (:ud  . ((ud-Lock-used))))
	      (:prefix-ES
	       (:fn . (:no-instruction)))
	      ((:i64 . ("DAA" 0
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "DAA is illegal in the 64-bit mode!"))))))
	      ("SUB" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SUB*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("SUB" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-SUB*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("SUB" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SUB*)))
	       (:ud  . ((ud-Lock-used))))
	      ("SUB" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-SUB*)))
	       (:ud  . ((ud-Lock-used))))
	      ("SUB" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SUB*)))
	       (:ud  . ((ud-Lock-used))))
	      ("SUB" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-SUB*)))
	       (:ud  . ((ud-Lock-used))))
	      (:prefix-CS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("DAS" 0
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "DAS is illegal in the 64-bit mode!")))))))

    #| 30 |# (("XOR" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-XOR*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("XOR" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-XOR*)))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("XOR" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-XOR*)))
	       (:ud  . ((ud-Lock-used))))
	      ("XOR" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-XOR*)))
	       (:ud  . ((ud-Lock-used))))
	      ("XOR" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-XOR*)))
	       (:ud  . ((ud-Lock-used))))
	      ("XOR" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-XOR*)))
	       (:ud  . ((ud-Lock-used))))
	      (:prefix-SS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("AAA" 0
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "AAA is illegal in the 64-bit mode!"))))))
	      ("CMP" 2 (E b) (G b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-CMP*)))
	       (:ud  . ((ud-Lock-used))))
	      ("CMP" 2 (E v) (G v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
		       (operation . #.*OP-CMP*)))
	       (:ud  . ((ud-Lock-used))))
	      ("CMP" 2 (G b) (E b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-CMP*)))
	       (:ud  . ((ud-Lock-used))))
	      ("CMP" 2 (G v) (E v)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-G-E
		       (operation . #.*OP-CMP*)))
	       (:ud  . ((ud-Lock-used))))
	      ("CMP" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-CMP*)))
	       (:ud  . ((ud-Lock-used))))
	      ("CMP" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-CMP*)))
	       (:ud  . ((ud-Lock-used))))
	      (:prefix-DS
	       (:fn . (:no-instruction)))
	      ((:i64 . ("AAS" 0
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "AAS is illegal in the 64-bit mode!")))))))

    #| 40 |# (((:o64  . (:rex (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eAX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-b (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eCX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-x (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eDX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-xb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eBX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-r (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eSP)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-rb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eBP)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-rx (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eSI)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-rxb (:fn . (:no-instruction))))
	       (:i64 . ("INC"  1 (:eDI)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-w (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eAX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-wb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eCX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-wx (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eDX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-wxb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eBX)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-wr (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eSP)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-wrb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eBP)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-wrx (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eSI)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used))))))
	      ((:o64  . (:rex-wrxb (:fn . (:no-instruction))))
	       (:i64 . ("DEC"  1 (:eDI)
			(:fn . (x86-inc/dec-4x))
			(:ud  . ((ud-Lock-used)))))))

    #| 50 |# (("PUSH" 1 (:rAX/r8)   :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("PUSH" 1 (:rCX/r9)   :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("PUSH" 1 (:rDX/r10)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("PUSH" 1 (:rBX/r11)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("PUSH" 1 (:rSP/r11)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("PUSH" 1 (:rBP/r13)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("PUSH" 1 (:rSI/r14)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("PUSH" 1 (:rDI/r15)  :d64
	       (:fn . (x86-push-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"  1 (:rAX/r8)   :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"  1 (:rCX/r9)   :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"  1 (:rDX/r10)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"  1 (:rBX/r11)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"  1 (:rSP/r11)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"  1 (:rBP/r13)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"  1 (:rSI/r14)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"  1 (:rDI/r15)  :d64
	       (:fn . (x86-pop-general-register))
	       (:ud  . ((ud-Lock-used)))))

    #| 60 |# (((:i64 . ("PUSHA/PUSHAD" 0
			(:fn . (x86-pusha))
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "PUSHA is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("POPA/POPAD"   0
			(:fn . (x86-popa))
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "POPA is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("BOUND"  2 (G v) (M a)
			(:ud  . ((ud-Lock-used)
				 (ud-second-operand-is-a-register)))))
	       (:o64 . (:evex-byte0 (:fn . (:no-instruction)))
		     ;; TODO: Check CPUID feature flags for AVX support. If it
		     ;; doesn't exist, throw a #UD here.

		     ;; ("#UD" 0
		     ;;  (:fn . (x86-illegal-instruction
		     ;;          (message .
		     ;;                   "BOUND is illegal in the 64-bit mode!"))))
		     ))
	      ((:o64 . ("MOVSXD" 2 (G v) (E v)
			(:fn . (x86-movsx))
			(:ud  . ((ud-Lock-used)))))
	       (:i64 . ("ARPL"   2 (E w) (G w)
			(:ud  . ((ud-Lock-used))))))
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
	       (:ud  . ((ud-Lock-used))))
	      ("IMUL"  3 (G v) (E v) (I z)
	       (:fn . (x86-imul-Op/En-RMI))
	       (:ud  . ((ud-Lock-used))))
	      ("PUSH" 1 (I b) :d64
	       (:fn . (x86-push-I))
	       (:ud  . ((ud-Lock-used))))
	      ("IMUL"  3 (G v) (E v) (I b)
	       (:fn . (x86-imul-Op/En-RMI))
	       (:ud  . ((ud-Lock-used))))
	      ("INS/INSB" 2 (Y b) (:DX)
	       (:ud  . ((ud-Lock-used))))
	      ("INS/INSW/INSD" 2 (Y z) (:DX)
	       (:ud  . ((ud-Lock-used))))
	      ("OUTS/OUTSB" 2 (Y b) (:DX)
	       (:ud  . ((ud-Lock-used))))
	      ("OUTS/OUTSW/OUTSD" 2 (Y z) (:DX)
	       (:ud  . ((ud-Lock-used)))))

    #| 70 |# (("JO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JNO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JB/NAE/C" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JNB/AE/NC" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JZ/E" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JNZ/NE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JBE/NA" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JNBE/A" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JS" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JNS" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JP/PE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JNP/PO" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JL/NGE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JNL/GE" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JLE/NG" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used))))
	      ("JNLE/G" 1 (J b) :f64
	       (:fn . (x86-one-byte-jcc))
	       (:ud  . ((ud-Lock-used)))))

    #| 80 |#  ((:Group-1 :1a)
	       (:Group-1 :1a)
	       ((:i64 . (:Group-1 :1a))
		(:o64 . ("#UD" 0
			 (:ud  . (t))
			 (:fn .
			      (x86-illegal-instruction
			       (message .
					"Opcode 0x82 is illegal in the 64-bit mode!"))))))
	       (:Group-1 :1a)
	       ("TEST" 2 (E b) (G b)
		(:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
			(operation .  #.*OP-TEST*)))
		(:ud  . ((ud-Lock-used))))
	       ("TEST" 2 (E v) (G v)
		(:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
			(operation .  #.*OP-TEST*)))
		(:ud  . ((ud-Lock-used))))
	       ("XCHG" 2 (E b) (G b)
		(:fn . (x86-xchg))
		(:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	       ("XCHG" 2 (E v) (G v)
		(:fn . (x86-xchg))
		(:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	       ("MOV" 2 (E b) (G b)
		(:fn . (x86-mov-Op/En-MR))
		(:ud  . ((ud-Lock-used))))
	       ("MOV" 2 (E v) (G v)
		(:fn . (x86-mov-Op/En-MR))
		(:ud  . ((ud-Lock-used))))
	       ("MOV" 2 (G b) (E b)
		(:fn . (x86-mov-Op/En-RM))
		(:ud  . ((ud-Lock-used))))
	       ("MOV" 2 (G v) (E v)
		(:fn . (x86-mov-Op/En-RM))
		(:ud  . ((ud-Lock-used))))
	       ;; TODO: For (S w) operands, sensible modr/m.reg values are 0-5
	       ;; because there are 6 segment registers.  Will these
	       ;; instructions #UD when modr/m.reg = 6 or 7? E.g., when modr/m
	       ;; is #x30 or #x38.
	       ("MOV" 2 (E v) (S w)
		(:ud  . ((ud-Lock-used))))
	       ("LEA" 2 (G v) (M)
		(:fn . (x86-lea))
		(:ud  . ((ud-source-operand-is-a-register)
			 (ud-Lock-used))))
	       ("MOV" 2 (S w) (E w)
		(:ud  . ((equal (modr/m->reg modr/m) #.*cs*)
			 (ud-Lock-used))))
	       ;; in Table A-6, Grp 1A only contains POP,
	       ;; so we leave the latter implicit here:
	       (:Group-1A :1a :d64))

    #| 90 |# (("XCHG" 1 (:r8)
	       (:fn . (x86-xchg))
	       (:ud  . ((ud-Lock-used))))
	      ("XCHG" 2 (:rCX/r9)  (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . ((ud-Lock-used))))
	      ("XCHG" 2 (:rDX/r10) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . ((ud-Lock-used))))
	      ("XCHG" 2 (:rBX/r11) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . ((ud-Lock-used))))
	      ("XCHG" 2 (:rSP/r12) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . ((ud-Lock-used))))
	      ("XCHG" 2 (:rBP/r13) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . ((ud-Lock-used))))
	      ("XCHG" 2 (:rSI/r14) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . ((ud-Lock-used))))
	      ("XCHG" 2 (:rDI/r15) (:rAX)
	       (:fn . (x86-xchg))
	       (:ud  . ((ud-Lock-used))))
	      ("CBW/CWDE/CDQE" 0
	       (:fn . (x86-cbw/cwd/cdqe))
	       (:ud  . ((ud-Lock-used))))
	      ("CWD/CDQ/CQO" 0
	       (:fn . (x86-cwd/cdq/cqo))
	       (:ud  . ((ud-Lock-used))))
	      ((:i64 . ("CALL" 1 (A p)
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "far CALL is illegal in the 64-bit mode!"))))))
	      ("FWAIT/WAIT" 0
	       (:ud  . ((ud-Lock-used))))
	      ("PUSHF/D/Q"  1 (F v) :d64
	       (:fn . (x86-pushf))
	       (:ud  . ((ud-Lock-used))))
	      ("POPF/D/Q"   1 (F v) :d64
	       (:fn . (x86-popf))
	       (:ud  . ((ud-Lock-used))))
	      ("SAHF" 0
	       (:fn . (x86-sahf))
	       (:ud  . ((ud-Lock-used)
			(and (equal proc-mode #.*64-bit-mode*)
			     (equal
			      ;; CPUID.80000001H.ECX[0]
			      (cpuid-flag
			       #ux_8000_0001
			       :reg #.*ecx*
			       :bit 0)
			      0)))))
	      ("LAHF" 0
	       (:fn . (x86-lahf))
	       (:ud  . ((ud-Lock-used)
			(and (equal proc-mode #.*64-bit-mode*)
			     (equal
			      ;; CPUID.80000001H:ECX.LAHF-SAHF[bit 0]
			      (cpuid-flag
			       #ux_8000_0001
			       :reg #.*ecx*
			       :bit 0)
			      0))))))

    #| a0 |# (("MOV" 2 (:AL) (O b)
	       (:fn . (x86-mov-Op/En-FD))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2 (:rAX) (O v)
	       (:fn . (x86-mov-Op/En-FD))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2 (O b) (:AL)
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2 (O v) (:rAX)
	       (:ud  . ((ud-Lock-used))))
	      ("MOVS/B" 2 (Y b) (X b)
	       (:fn . (x86-movs))
	       (:ud  . ((ud-Lock-used))))
	      ("MOVS/W/D/Q" 2 (Y v) (X v)
	       (:fn . (x86-movs))
	       (:ud  . ((ud-Lock-used))))
	      ("CMPS/B"   2 (X b) (Y b)
	       (:fn . (x86-cmps)))
	      ("CMPS/W/D" 2 (X v) (Y v)
	       (:fn . (x86-cmps))
	       (:ud  . ((ud-Lock-used))))
	      ("TEST" 2 (:AL) (I b)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-TEST*)))
	       (:ud  . ((ud-Lock-used))))
	      ("TEST" 2 (:rAX) (I z)
	       (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
		       (operation . #.*OP-TEST*)))
	       (:ud  . ((ud-Lock-used))))
	      ("STOS/B" 2 (Y b) (:AL)
	       (:fn . (x86-stos))
	       (:ud  . ((ud-Lock-used))))
	      ("STOS/W/D/Q" 2 (Y v) (:rAX)
	       (:fn . (x86-stos))
	       (:ud  . ((ud-Lock-used))))
	      ("LODS/B" 2 (:AL) (X b)
	       (:ud  . ((ud-Lock-used))))
	      ("LODS/W/D/Q" 2 (:rAX) (X v)
	       (:ud  . ((ud-Lock-used))))
	      ("SCAS/B" 2 (:AL) (Y b)
	       (:ud  . ((ud-Lock-used))))
	      ("SCAS/W/D/Q" 2 (:rAX) (Y v)
	       (:ud  . ((ud-Lock-used)))))

    #| b0 |# (("MOV" 2  (:AL/r8L)  (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:CL/r9L)  (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:DL/r10L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:BL/r11L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:AH/r12L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:CH/r13L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:DH/r14L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:BH/r15L) (I b)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:rAX/r8)  (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:rCX/r9)  (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:rDX/r10) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:rBX/r11) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:rSP/r12) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:rBP/r13) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:rSI/r14) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used))))
	      ("MOV" 2  (:rDI/r15) (I v)
	       (:fn . (x86-mov-Op/En-OI))
	       (:ud  . ((ud-Lock-used)))))

    #| c0 |# ((:Group-2 :1a)
	      (:Group-2 :1a)
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
			(:ud  . ((ud-Lock-used)
				 (ud-source-operand-is-a-register))))))
	      ((:o64 . (:vex2-byte0 (:fn . (:no-instruction))))
	       (:i64 . ("LDS" 2 (G z) (M p)
			(:ud  . ((ud-Lock-used)
				 (ud-source-operand-is-a-register))))))
	      (:Group-11 :1a)
	      (:Group-11 :1a)
	      ("ENTER" 2 (I w) (I b)
	       (:ud  . ((ud-Lock-used))))
	      ("LEAVE" 0 :d64
	       (:fn . (x86-leave))
	       (:ud  . ((ud-Lock-used))))
	      ("RET" 1 (I w)
	       ;; No UD Exception
	       )
	      ("RET" 0
	       ;; No UD Exception
	       )
	      ("INT3" 0
	       (:ud  . ((ud-Lock-used))))
	      ("INT" 1 (I b)
	       (:ud  . ((ud-Lock-used))))
	      ((:i64 . ("INTO" 0
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "INTO is illegal in the 64-bit mode!"))))))
	      ("IRET/D/Q" 0
	       (:ud  . ((ud-Lock-used)))))

    #| d0 |# ((:Group-2 :1a)
	      (:Group-2 :1a)
	      (:Group-2 :1a)
	      (:Group-2 :1a)
	      ((:i64 . ("AAM" 1 (I b)
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "AAM is illegal in the 64-bit mode!"))))))
	      ((:i64 . ("AAD" 1 (I b)
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD" 0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "AAD is illegal in the 64-bit mode!"))))))
	      (:none
	       (:fn . (:no-instruction)))
	      ("XLAT/XLATB" 0
	       (:ud  . ((ud-Lock-used))))
	      (:esc ;; Escape to co-processor instruction set
	       (:nm  . ((nm-cr0-ts-is-1)
			(nm-cr0-em-is-1))))
	      (:esc ;; Escape to co-processor instruction set
	       (:nm  . ((nm-cr0-ts-is-1)
			(nm-cr0-em-is-1))))
	      (:esc ;; Escape to co-processor instruction set
	       (:nm  . ((nm-cr0-ts-is-1)
			(nm-cr0-em-is-1))))
	      (:esc ;; Escape to co-processor instruction set
	       (:nm  . ((nm-cr0-ts-is-1)
			(nm-cr0-em-is-1))))
	      (:esc ;; Escape to co-processor instruction set
	       (:nm  . ((nm-cr0-ts-is-1)
			(nm-cr0-em-is-1))))
	      (:esc ;; Escape to co-processor instruction set
	       (:nm  . ((nm-cr0-ts-is-1)
			(nm-cr0-em-is-1))))
	      (:esc ;; Escape to co-processor instruction set
	       (:nm  . ((nm-cr0-ts-is-1)
			(nm-cr0-em-is-1))))
	      (:esc ;; Escape to co-processor instruction set
	       (:nm  . ((nm-cr0-ts-is-1)
			(nm-cr0-em-is-1)))))

    #| e0 |# (("LOOPNE/LOOPNZ" 1 (J b) :f64
	       (:fn . (x86-loop))
	       (:ud  . ((ud-Lock-used))))
	      ("LOOPE/LOOPZ" 1 (J b) :f64
	       (:fn . (x86-loop))
	       (:ud  . ((ud-Lock-used))))
	      ("LOOP" 1 (J b) :f64
	       (:fn . (x86-loop))
	       (:ud  . ((ud-Lock-used))))
	      ("JrCXZ" 1 (J b) :f64
	       (:fn . (x86-jrcxz))
	       (:ud  . ((ud-Lock-used))))
	      ("IN" 2 (:AL) (I b)
	       (:ud  . ((ud-Lock-used))))
	      ("IN" 2 (:eAX) (I b)
	       (:ud  . ((ud-Lock-used))))
	      ("OUT" 2 (I b) (:AL)
	       (:ud  . ((ud-Lock-used))))
	      ("OUT" 2 (I b) (:eAX)
	       (:ud  . ((ud-Lock-used))))
	      ("CALL" 1 (J z) :f64
	       (:fn . (x86-call-E8-Op/En-M))
	       (:ud  . ((ud-Lock-used))))
	      ("JMP"  1 (J z) :f64
	       (:fn . (x86-near-jmp-Op/En-D))
	       (:ud  . ((ud-Lock-used))))
	      ((:i64 . ("JMP"  1 (A p)
			(:ud  . ((ud-Lock-used)))))
	       (:o64 . ("#UD"  0
			(:ud  . (t))
			(:fn . (x86-illegal-instruction
				(message .
					 "JMP is illegal in the 64-bit mode!"))))))
	      ("JMP"  1 (J b) :f64
	       (:fn . (x86-near-jmp-Op/En-D))
	       (:ud  . ((ud-Lock-used))))
	      ("IN" 2  (:AL) (:DX)
	       (:ud  . ((ud-Lock-used))))
	      ("IN" 2  (:eAX) (:DX)
	       (:ud  . ((ud-Lock-used))))
	      ("OUT" 2 (:DX) (:AL)
	       (:ud  . ((ud-Lock-used))))
	      ("OUT" 2 (:DX) (:eAX)
	       (:ud  . ((ud-Lock-used)))))

    #| f0 |# ((:prefix-Lock
	       (:fn . (:no-instruction)))
	      ("INT1" 0
	       (:ud  . ((ud-Lock-used))))
	      (:prefix-REPNE
	       (:fn . (:no-instruction)))
	      (:prefix-REP/REPE
	       (:fn . (:no-instruction)))
	      ("HLT" 0
	       (:fn . (x86-hlt))
	       (:ud  . ((ud-Lock-used))))
	      ("CMC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std))
	       (:ud  . ((ud-Lock-used))))
	      (:Group-3  :1a)
	      (:Group-3  :1a)
	      ("CLC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std))
	       (:ud  . ((ud-Lock-used))))
	      ("STC" 0
	       (:fn . (x86-cmc/clc/stc/cld/std))
	       (:ud  . ((ud-Lock-used))))
	      ("CLI" 0
	       (:ud  . ((ud-Lock-used))))
	      ("STI" 0
	       (:ud  . ((ud-Lock-used))))
	      ("CLD" 0
	       (:fn . (x86-cmc/clc/stc/cld/std)))
	      ("STD" 0
	       (:fn . (x86-cmc/clc/stc/cld/std))
	       (:ud  . ((ud-Lock-used))))
	      (:Group-4 :1a)
	      (:Group-5 :1a))

    #|       -------------------------------        |#
    ))


(defconst *two-byte-opcode-map-lst*
  ;; First byte is 0x0F.
  ;; Source: Intel Volume 2, Table A-3.

  '(
    #|       -------------------------------        |#

    #| 00 |# ((:Group-6 :1a)
	      (:Group-7 :1a)
	      ("LAR" 2 (G v) (E w)
	       (:ud  . ((ud-Lock-used))))
	      ("LSL" 2 (G v) (E w)
	       (:ud  . ((ud-Lock-used))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:o64 . ("SYSCALL" 0
			(:fn . (x86-syscall-both-views))
			(:ud  . ((ud-Lock-used)
				 (equal
				   (ia32_efer-slice
				    :ia32_efer-sce
				    (n12 (ia32_efer)))
				   0)))))
	       (:i64 . (:none
			(:fn . (:no-instruction)))))
	      ("CLTS" 0
	       (:ud  . ((ud-Lock-used)))
	       (:gp  . ((gp-cpl-not-0))))
	      ((:o64 . ("SYSRET" 0
			(:fn . (x86-sysret))
			(:ud  . ((ud-Lock-used)
				 (equal
				   (ia32_efer-slice
				    :ia32_efer-sce
				    (n12 (ia32_efer)))
				   0)))
			(:gp  . ((gp-cpl-not-0)))))
	       (:i64 . (:none
			(:fn . (:no-instruction)))))
    #| 08 |#  ("INVD" 0
	       (:ud  . ((ud-Lock-used))))
	      ("WBINVD" 0
	       (:ud  . ((ud-Lock-used))))
	      (:none
	       (:fn . (:no-instruction)))
	      ("UD2" 0 :1b
	       ;; (:ud  . (t))
	       (:fn . (x86-illegal-instruction
		       (message . "UD2 encountered!"))))
	      (:none
	       (:fn . (:no-instruction)))
	      ("prefetchw(/1)" 1 (E v)
	       (:ud  . ((ud-Lock-used))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 10 |# (((:no-prefix . ("MOVUPS"    2 (V ps) (W ps)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-RM))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("MOVUPD"    2 (V pd) (W pd)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-RM))
			      (:ex . ((chk-exc :type-4 (:sse2))))))
	       (:F3        . ("MOVSS"     3 (V x)  (H x)  (W ss)
			      (:fn . (x86-movss/movsd-Op/En-RM
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-5 (:sse))))))
	       (:F2        . ("MOVSD"     3 (V x)  (H x)  (W sd)
			      (:fn . (x86-movss/movsd-Op/En-RM
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-5 (:sse2)))))))

	      ((:no-prefix . ("MOVUPS"    2 (W ps) (V ps)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-MR))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("MOVUPD"    2 (W pd) (V pd)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-MR))
			      (:ex . ((chk-exc :type-4 (:sse2))))))
	       (:F3        . ("MOVSS"     3 (W ss) (H x)  (V ss)
			      (:fn . (x86-movss/movsd-Op/En-MR
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-5 (:sse))))))
	       (:F2        . ("MOVSD"     3 (W sd) (H x)  (V sd)
			      (:fn . (x86-movss/movsd-Op/En-MR
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-5 (:sse2)))))))

	      ((:no-prefix . (:EXT
			      (((:opcode . #ux0F_12)
				(:mod    . :mem)) .
				("MOVLPS"    3 (V q)  (H q)  (M q)
				 (:fn . (x86-movlps/movlpd-Op/En-RM))
				 (:ex . ((chk-exc :type-5 (:sse))))))
			      (((:opcode . #ux0F_12)
				(:mod    . #b11)) .
				("MOVHLPS"    3 (V q)  (H q)  (U q)
				 (:ex . ((chk-exc :type-7 (:sse))))))))

	       (:66        . ("MOVLPD"    3 (V q)  (H q)  (M q)
			      (:fn . (x86-movlps/movlpd-Op/En-RM))
			      (:ex . ((chk-exc :type-5 (:sse2))))
			      (:ud  . ((ud-ModR/M.Mod-indicates-Register)))))
	       (:F3        . ("MOVSLDUP"  2 (V x)  (W x)
			      (:fn . (x86-movlps/movlpd-Op/En-RM))
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:F2        . ("MOVDDUP"   2 (V x)  (W x)
			      (:fn . (x86-movlps/movlpd-Op/En-RM))
			      (:ex . ((chk-exc :type-5 (:sse3)))))))

	      ((:no-prefix . ("MOVLPS"    2 (M q)  (V q)
			      (:fn . (x86-movlps/movlpd-Op/En-MR))
			      (:ex . ((chk-exc :type-5 (:sse))))
			      (:ud  . ((ud-ModR/M.Mod-indicates-Register)))))
	       (:66        . ("MOVLPD"    2 (M q)  (V q)
			      (:fn . (x86-movlps/movlpd-Op/En-MR))
			      (:ex . ((chk-exc :type-5 (:sse2))))
			      (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))

	      ((:no-prefix . ("UNPCKLPS"  3 (V x)  (H x)  (W x)
			      (:fn . (x86-unpck?ps-Op/En-RM
				      (high/low . #.*LOW-PACK*)))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("UNPCKLPD"  3 (V x)  (H x)  (W x)
			      (:fn . (x86-unpck?pd-Op/En-RM
				      (high/low . #.*LOW-PACK*)))
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("UNPCKHPS"  3 (V x)  (H x)  (W x)
			      (:fn . (x86-unpck?ps-Op/En-RM
				      (high/low . #.*HIGH-PACK*)))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("UNPCKHPD"  3 (V x)  (H x)  (W x)
			      (:fn . (x86-unpck?pd-Op/En-RM
				      (high/low . #.*HIGH-PACK*)))
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . (:EXT
			      (((:opcode . #ux0F_16)
				(:mod    . :mem)) .
				("MOVHPS"    3 (V dq)  (H q)  (M q) :v1
				 (:fn . (x86-movhps/movhpd-Op/En-RM))
				 (:ex . ((chk-exc :type-5 (:sse))))))
			      (((:opcode . #ux0F_16)
				(:mod    . #b11)) .
				("MOVLHPS"   3 (V dq)  (H q)  (U q)
				 (:ex . ((chk-exc :type-7 (:sse))))))))
	       (:66        . ("MOVHPD"    3 (V dq)  (H q)  (M q) :v1
			      (:fn . (x86-movhps/movhpd-Op/En-RM))
			      (:ex . ((chk-exc :type-5 (:sse2))))
			      (:ud  . ((ud-source-operand-is-a-register)))))
	       (:F3        . ("MOVSHDUP"  2 (V x)   (W x)
			      (:ex . ((chk-exc :type-4 (:sse3)))))))

	      ((:no-prefix . ("MOVHPS"    2 (M q)  (V q) :v1
			      (:fn . (x86-movhps/movhpd-Op/En-MR))
			      (:ex . ((chk-exc :type-5 (:sse))))
			      (:ud  . ((ud-ModR/M.Mod-indicates-Register)))))
	       (:66        . ("MOVHPD"    2 (M q)  (V q) :v1
			      (:fn . (x86-movhps/movhpd-Op/En-MR))
			      (:ex . ((chk-exc :type-5 (:sse2))))
			      (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))

    #| 18 |#  (:Group-16 :1a)
	      ("RESERVEDNOP" 0)
	      (:Group-16 :1a)
	      (:Group-16 :1a)
	      ("RESERVEDNOP" 0)
	      ("RESERVEDNOP" 0)
	      ("RESERVEDNOP" 0)
	      ("NOP" 1 (E v)
	       (:fn . (x86-two-byte-nop))
	       (:ud  . ((ud-Lock-used)))))

    #| 20 |# (("MOV" 2 (R d) (C d)
	       (:fn . (x86-mov-control-regs-Op/En-MR))
	       (:ud  . ((ud-Lock-used)
			(let ((reg (modr/m->reg modr/m)))
			  (if (and (equal proc-mode #.*64-bit-mode*)
				   (logbitp #.*r* rex-byte))
			      (not (equal reg 0))
			    (or (equal reg #.*cr1*)
				(equal reg #.*cr5*)
				(equal reg #.*cr6*)
				(equal reg #.*cr7*))))))
	       (:gp  . ((gp-cpl-not-0))))
	      ("MOV" 2 (R d) (D d)
	       (:ud  . ((ud-Lock-used)
			(and (equal (cr4-slice :cr4-de (cr4)) 1)
			     (or (equal (modr/m->reg modr/m) #.*dr4*)
				 (equal (modr/m->reg modr/m) #.*dr5*)))))
	       (:gp  . ((gp-cpl-not-0))))
	      ("MOV" 2 (C d) (R d)
	       (:ud  . ((ud-Lock-used)
			(let ((reg (modr/m->reg modr/m)))
			  (if (and (equal proc-mode #.*64-bit-mode*)
				   (logbitp #.*r* rex-byte))
			      (not (equal reg 0))
			    (or (equal reg #.*cr1*)
				(equal reg #.*cr5*)
				(equal reg #.*cr6*)
				(equal reg #.*cr7*))))))
	       (:gp  . ((gp-cpl-not-0))))
	      ("MOV" 2 (D d) (R d)
	       (:ud  . ((ud-Lock-used)
			(and (equal (cr4-slice :cr4-de (cr4)) 1)
			     (or (equal (modr/m->reg modr/m) #.*dr4*)
				 (equal (modr/m->reg modr/m) #.*dr5*)))))
	       (:gp  . ((gp-cpl-not-0))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))

   #| 28 |#  ((:no-prefix . ("MOVAPS"    2 (V ps)  (W ps)
			     (:fn . (x86-movaps/movapd-Op/En-RM))
			     (:ex . ((chk-exc :type-1 (:sse))))))
	      (:66        . ("MOVAPD"    2 (V pd)  (W pd)
			     (:fn . (x86-movaps/movapd-Op/En-RM))
			     (:ex . ((chk-exc :type-1 (:sse2)))))))

	      ((:no-prefix . ("MOVAPS"    2 (W ps)  (V ps)
			      (:fn . (x86-movaps/movapd-Op/En-MR))
			      (:ex . ((chk-exc :type-1 (:sse))))))
	       (:66        . ("MOVAPD"    2 (W pd)  (V pd)
			      (:fn . (x86-movaps/movapd-Op/En-MR))
			      (:ex . ((chk-exc :type-1 (:sse2)))))))

	      ((:no-prefix . ("CVTPI2PS"   2 (V ps)  (Q pi)
			      (:ex . ((chk-exc :type-22-5 (:mmx))))))
	       (:66        . ("CVTPI2PD"   2 (V pd)  (Q pi)
			      (:ex . ((chk-exc :type-22-6 (:mmx))))))
	       (:F3        . ("CVTSI2SS"  3 (V ss)  (H ss)  (E y)
			      (:fn . (x86-cvtsi2s?-Op/En-RM
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("CVTSI2SD"  3 (V sd)  (H sd)  (E y)
			      (:fn . (x86-cvtsi2s?-Op/En-RM
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("MOVNTPS"   2 (M ps)  (V ps)
			      (:ex . ((chk-exc :type-1 (:sse))))
			      (:ud  . ((ud-ModR/M.Mod-indicates-Register)))))
	       (:66        . ("MOVNTPD"   2 (M pd)  (V pd)
			      (:ex . ((chk-exc :type-1 (:sse2))))
			      (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))

	      ((:no-prefix . ("CVTTPS2PI"  2 (P pi)  (W ps)
			      (:ex . ((chk-exc :type-22-5 (:mmx))))))
	       (:66        . ("CVTTPD2PI"  2 (P pi)  (W pd)
			      (:ex . ((chk-exc :type-22-4 (:mmx))))))
	       (:F3        . ("CVTTSS2SI" 2 (G y)   (W ss)
			      (:fn . (x86-cvts?2si/cvtts?2si-Op/En-RM
				      (sp/dp . #.*OP-SP*)
				      (trunc . t)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("CVTTSD2SI" 2 (G y)   (W sd)
			      (:fn . (x86-cvts?2si/cvtts?2si-Op/En-RM
				      (sp/dp . #.*OP-DP*)
				      (trunc . t)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("CVTPS2PI"   2 (P pi)  (W ps)
			      (:ex . ((chk-exc :type-22-5 (:mmx))))))
	       (:66        . ("CVTPD2PI"   2 (Q pi)  (W pd)
			      (:ex . ((chk-exc :type-22-4 (:mmx))))))
	       (:F3        . ("CVTSS2SI"  2 (G y)   (W ss)
			      (:fn . (x86-cvts?2si/cvtts?2si-Op/En-RM
				      (sp/dp . #.*OP-SP*)
				      (trunc . nil)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("CVTSD2SI"  2 (G y)   (W sd)
			      (:fn . (x86-cvts?2si/cvtts?2si-Op/En-RM
				      (sp/dp . #.*OP-DP*)
				      (trunc . nil)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("UCOMISS"   2 (V ss)  (W ss)
			      (:fn . (x86-comis?/ucomis?-Op/En-RM
				      (operation . #.*OP-UCOMI*)
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:66        . ("UCOMISD"   2 (V sd)  (W sd)
			      (:fn . (x86-comis?/ucomis?-Op/En-RM
				      (operation . #.*OP-UCOMI*)
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("COMISS"    2 (V ss)  (W ss)
			      (:fn . (x86-comis?/ucomis?-Op/En-RM
				      (operation . #.*OP-UCOMI*)
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:66        . ("COMISD"    2 (V sd)  (W sd)
			      (:fn . (x86-comis?/ucomis?-Op/En-RM
				      (operation . #.*OP-UCOMI*)
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2))))))))

    #| 30 |# (("WRMSR" 0
	       (:ud  . ((ud-Lock-used))))
	      ("RDTSC" 0
	       (:ud  . ((ud-Lock-used))))
	      ("RDMSR" 0
	       (:ud  . ((ud-Lock-used))))
	      ("RDPMC" 0
	       (:ud  . ((ud-Lock-used)))
	       (:gp  . ((and (gp-cpl-not-0) (gp-cr4-pce-is-0)))))
	      ("SYSENTER" 0
	       (:ud  . ((ud-Lock-used)))
	       (:gp  . ((gp-cr0-pe-is-0))))
	      ("SYSEXIT" 0
	       (:ud  . ((ud-Lock-used)))
	       (:gp  . ((gp-cpl-not-0)
			(gp-cr0-pe-is-0))))
	      (:none
	       (:fn . (:no-instruction)))
	      ("GETSEC" 0) ;; TODO: Lock Used?

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
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVNO" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVB/C/NAE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVAE/NB/NC" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVE/Z" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVNE/NZ" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVBE/NA" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVA/NBE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
    #| 48 |#  ("CMOVS" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVNS" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVP/PE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVNP/PO" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVL/NGE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVNL/GE" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVLE/NG" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used))))
	      ("CMOVNLE/G" 2 (G v) (E v)
	       (:fn . (x86-cmovcc))
	       (:ud  . ((ud-Lock-used)))))

    #| 50 |# (((:no-prefix . ("MOVMSKPS"  2 (G y)  (U ps)
			      (:ex . ((chk-exc :type-7 (:sse))))))
	       (:66        . ("MOVMSKPD"  2 (G y)  (U pd)
			      (:ex . ((chk-exc :type-7 (:sse2)))))))

	      ((:no-prefix . ("SQRTPS"    2 (V ps)  (W ps)
			      (:fn . (x86-sqrtps-Op/En-RM))
			      (:ex . ((chk-exc :type-2 (:sse))))))
	       (:66        . ("SQRTPD"    2 (V pd)  (W pd)
			      (:fn . (x86-sqrtpd-Op/En-RM))
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:F3        . ("SQRTSS"    3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-sqrts?-Op/En-RM
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("SQRTSD"    3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-sqrts?-Op/En-RM
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("RSQRTPS"   2 (V ps)  (W ps)
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:F3        . ("RSQRTSS"   3 (V ss)  (H ss)  (W ss)
			      (:ex . ((chk-exc :type-5 (:sse)))))))

	      ((:no-prefix . ("RCPPS"     2 (V ps)  (W ps)
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:F3        . ("RCPSS"     3 (V ss)  (H ss)  (W ss)
			      (:ex . ((chk-exc :type-5 (:sse)))))))

	      ((:no-prefix . ("ANDPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-AND*)))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("ANDPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-AND*)))
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("ANDNPS"    3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-ANDN*)))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("ANDNPD"    3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-ANDN*)))
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("ORPS"      3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-OR*)))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("ORPD"      3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-OR*)))
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("XORPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-XOR*)))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("XORPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-XOR*)))
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

   #| 58 |#   ((:no-prefix . ("ADDPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-ADD*)))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("ADDPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-ADD*)))
			      (:ex . ((chk-exc :type-4 (:sse2))))))
	       (:F3        . ("ADDSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-ADD*)
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("ADDSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-ADD*)
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("MULPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-MUL*)))
			      (:ex . ((chk-exc :type-2 (:sse))))))
	       (:66        . ("MULPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-MUL*)))
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:F3        . ("MULSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MUL*)
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("MULSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MUL*)
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("CVTPS2PD"  2 (V pd)  (W ps)
			      (:fn . (x86-cvtps2pd-Op/En-RM))
			      (:ex . ((chk-exc :type-3 (:sse2))))))
	       (:66        . ("CVTPD2PS"  2 (V ps)  (W pd)
			      (:fn . (x86-cvtpd2ps-Op/En-RM))
			      (:ex . ((chk-exc :type-3 (:sse2))))))
	       (:F3        . ("CVTSS2SD"  3 (V sd)  (H x)   (W ss)
			      (:fn . (x86-cvts?2s?-Op/En-RM
				      (dp-to-sp . #.*SP-TO-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2))))))
	       (:F2        . ("CVTSD2SS"  3 (V ss)  (H x)   (W sd)
			      (:fn . (x86-cvts?2s?-Op/En-RM
				      (dp-to-sp . #.*DP-TO-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("CVTDQ2PS"  2 (V ps)  (W dq)
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:66        . ("CVTPS2DQ"  2 (V dq)  (W ps)
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:F3        . ("CVTTPS2DQ" 2 (V dq)  (W ps)
			      (:ex . ((chk-exc :type-2 (:sse2)))))))

	      ((:no-prefix . ("SUBPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-SUB*)))
			      (:ex . ((chk-exc :type-2 (:sse))))))
	       (:66        . ("SUBPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-SUB*)))
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:F3        . ("SUBSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-SUB*)
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("SUBSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-SUB*)
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("MINPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-MIN*)))
			      (:ex . ((chk-exc :type-2 (:sse))))))
	       (:66        . ("MINPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-MIN*)))
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:F3        . ("MINSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MIN*)
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-2 (:sse))))))
	       (:F2        . ("MINSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MIN*)
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("DIVPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-DIV*)))
			      (:ex . ((chk-exc :type-2 (:sse))))))
	       (:66        . ("DIVPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-DIV*)))
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:F3        . ("DIVSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-DIV*)
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("DIVSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-DIV*)
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ((:no-prefix . ("MAXPS"     3 (V ps)  (H ps)  (W ps)
			      (:fn . (x86-addps/subps/mulps/divps/maxps/minps-Op/En-RM
				      (operation . #.*OP-MAX*)))
			      (:ex . ((chk-exc :type-2 (:sse))))))
	       (:66        . ("MAXPD"     3 (V pd)  (H pd)  (W pd)
			      (:fn . (x86-addpd/subpd/mulpd/divpd/maxpd/minpd-Op/En-RM
				      (operation . #.*OP-MAX*)))
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:F3        . ("MAXSS"     3 (V ss)  (H ss)  (W ss)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MAX*)
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("MAXSD"     3 (V sd)  (H sd)  (W sd)
			      (:fn . (x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
				      (operation . #.*OP-MAX*)
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2))))))))

    #| 60 |# (((:no-prefix . ("PUNPCKLBW"  2 (P q)  (Q d)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PUNPCKLBW" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PUNPCKLWD"  2 (P q)  (Q d)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PUNPCKLWD" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PUNPCKLDQ"  2 (P q)  (Q d)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PUNPCKLDQ" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PACKSSWB"   2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PACKSSWB"  3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PCMPGTB"    2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PCMPGTB"   3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PCMPGTW"    2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PCMPGTW"   3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PCMPGTD"    2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PCMPGTD"   3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PACKUSWB"   2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PACKUSWB"  3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

    #| 68 |#  ((:no-prefix . ("PUNPCKHBW"  2 (P q)  (Q d)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PUNPCKHBW" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PUNPCKHWD"  2 (P q)  (Q d)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PUNPCKHWD" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PUNPCKHDQ"  2 (P q)  (Q d)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PUNPCKHDQ" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PACKSSDW"  2 (P q)  (Q d)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PACKSSDW" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:66        . ("PUNPCKLQDQ" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:66        . ("PUNPCKHQDQ" 3 (V x)  (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("MOVD/Q"      2 (P d)  (E y)
			      (:ex . ((chk-exc :type-22-8 (:mmx))))))
	       (:66        . ("MOVD/Q"     2 (V y)  (E y)
			      (:ex . ((chk-exc :type-5 (:sse2)))))))

	      ((:no-prefix . ("MOVQ"        2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-22-8 (:mmx))))))
	       (:66        . ("MOVDQA"     2 (V x)  (W x)
			      (:ex . ((chk-exc :type-1 (:sse2))))))
	       (:F3        . ("MOVDQU"     2 (V x)  (W x)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-RM))
			      (:ex . ((chk-exc :type-4 (:sse2))))))))

    #| 70 |# (((:no-prefix . ("PSHUFW"      3 (P q)   (Q q)   (I b)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PSHUFD"     3 (V x)   (W x)   (I b)
			      (:ex . ((chk-exc :type-4 (:sse2))))))
	       (:F3        . ("PSHUFHW"    3 (V x)   (W x)   (I b)
			      (:ex . ((chk-exc :type-4 (:sse2))))))
	       (:F2        . ("PSHUFLW"    3 (V x)   (W x)   (I b)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))


	      (:Group-12  :1a)

	      (:Group-13  :1a)

	      (:Group-14  :1a)

	      ((:no-prefix . ("PCMPEQB"     2 (P q)   (Q q)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PCMPEQB"    3 (V x)   (H x)  (W x)
			      (:fn . (x86-pcmpeqb-Op/En-RM))
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PCMPEQW"     2 (P q)   (Q q)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PCMPEQW"    3 (V x)   (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("PCMPEQD"     2 (P q)   (Q q)
			      (:ex . ((chk-exc :type-22-7 (:mmx))))))
	       (:66        . ("PCMPEQD"    3 (V x)   (H x)  (W x)
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      ((:no-prefix . ("EMMS"        0
			      (:ud . ((ud-Lock-used)
				      (equal (cr0-slice :cr0-em (cr0)) 1)))))
	       (:v         . ("VZEROUPPER/VZEROALL"  0
			      (:ex . ((chk-exc :type-8 (:avx)))))))

    #| 78 |#  ("MREAD" 2  (E y)  (G y)
	       (:gp  . ((gp-cpl-not-0))))

	      ("MWRITE" 2  (E y)  (G y)
	       (:gp  . ((gp-cpl-not-0))))

	      (:none
	       (:fn . (:no-instruction)))

	      (:none
	       (:fn . (:no-instruction)))

	      ((:66        . ("HADDPD"     3 (V pd)   (H pd)  (W pd)
			      (:ex . ((chk-exc :type-2 (:sse3))))))
	       (:F2        . ("HADDPS"     3 (V ps)   (H ps)  (W ps)
			      (:ex . ((chk-exc :type-2 (:sse3)))))))

	      ((:66        . ("HSUBPD"     3 (V pd)   (H pd)  (W pd)
			      (:ex . ((chk-exc :type-2 (:sse3))))))
	       (:F2        . ("HSUBPS"     3 (V ps)   (H ps)  (W ps)
			      (:ex . ((chk-exc :type-2 (:sse3)))))))

	      ((:no-prefix . ("MOVD/Q"      2 (E y)    (P d)
			      (:ex . ((chk-exc :type-22-8 (:mmx))))))
	       (:66        . ("MOVD/Q"     2 (E y)    (V y)
			      (:ex . ((chk-exc :type-5 (:sse2))))))
	       (:F3        . ("MOVQ"       2 (V q)    (W q)
			      (:ex . ((chk-exc :type-5 (:sse2)))))))

	      ((:no-prefix . ("MOVQ"        2 (Q q)    (P q)
			      (:ex . ((chk-exc :type-22-8 (:mmx))))))
	       (:66        . ("MOVDQA"     2 (W x)    (V x)
			      (:ex . ((chk-exc :type-1 (:sse2))))))
	       (:F3        . ("MOVDQU"      2 (W x)    (V x)
			      (:fn . (x86-movups/movupd/movdqu-Op/En-MR))
			      (:ex . ((chk-exc :type-4 (:sse2))))))))

    #| 80 |#  (("JO" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JNO" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JB/NAE/C" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JNB/AE/NC" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JZ/E" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JNZ/NE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JBE/NA" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JNBE/A" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
    #| 88 |#   ("JS" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JNS" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JP/PE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JNP/PO" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JL/NGE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JNL/GE" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JLE/NG" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used))))
	       ("JNLE/G" 1 (J z) :f64
		(:fn . (x86-two-byte-jcc))
		(:ud  . ((ud-Lock-used)))))

    #| 90 |# (("SETO" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETNO" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETB/NAE/C" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETNB/AE/NC" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETZ/E" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETNZ/NE" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETBE/NA" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETNBE/A" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
    #| 98 |#  ("SETS" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETNS" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETP/PE" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETNP/PO" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETL/NGE" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETNL/GE" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETLE/NG" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used))))
	      ("SETNLE/G" 1 (E b)
	       (:fn . (x86-setcc))
	       (:ud  . ((ud-Lock-used)))))

    #| a0 |# (("PUSH"  1 (:FS) :d64
	       (:fn . (x86-push-segment-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"   1 (:FS) :d64
	       (:ud  . ((ud-Lock-used))))
	      ("CPUID" 0
	       (:ud  . ((ud-Lock-used))))
	      ("BT" 2 (E v) (G v)
	       (:fn . (x86-bt-0f-a3))
	       (:ud  . ((ud-Lock-used))))
	      ("SHLD" 3 (E v) (G v) (I b)
	       (:ud  . ((ud-Lock-used))))
	      ("SHLD" 3 (E v) (G v) (:CL)
	       (:ud  . ((ud-Lock-used))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| a8 |#  ("PUSH"  1 (:GS) :d64
	       (:fn . (x86-push-segment-register))
	       (:ud  . ((ud-Lock-used))))
	      ("POP"   1 (:GS) :d64
	       (:ud  . ((ud-Lock-used))))
	      ("RSM" 0)
	      ("BTS" 2 (E v) (G v)
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("SHRD" 3 (E v) (G v) (I b)
	       (:ud  . ((ud-Lock-used))))
	      ("SHRD" 3 (E v) (G v) (:CL)
	       (:ud  . ((ud-Lock-used))))
	      (:Group-15 :1a :1c)
	      ("IMUL" 2 (G v) (E v)
	       (:fn . (x86-imul-Op/En-RM))
	       (:ud  . ((ud-Lock-used)))))

    #| b0 |# (("CMPXCHG" 2 (E b) (G b)
	       (:fn . (x86-cmpxchg))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("CMPXCHG" 2 (E v) (G v)
	       (:fn . (x86-cmpxchg))
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("LSS" 2 (G v) (M p)
	       (:ud  . ((ud-Lock-used)
			(ud-source-operand-is-a-register))))
	      ("BTR" 2 (E v) (G v)
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("LFS" 2 (G v) (M p)
	       (:ud  . ((ud-Lock-used)
			(ud-source-operand-is-a-register))))
	      ("LGS" 2 (G v) (M p)
	       (:ud  . ((ud-Lock-used)
			(ud-source-operand-is-a-register))))
	      ("MOVZX" 2 (G v) (E b)
	       (:fn . (x86-movzx))
	       (:ud  . ((ud-Lock-used))))
	      ("MOVZX" 2 (G v) (E w)
	       (:fn . (x86-movzx))
	       (:ud  . ((ud-Lock-used))))
    #| b8 |#  ((:no-prefix . ("JMPE"   0
			      ;; Reserved for emulator on IPF (Itanium
			      ;; Processor Family).
			      ))
	       (:F3        . ("POPCNT" 2 (G v) (E v)
			      (:ud  . ((ud-Lock-used)
				       (equal
					 ;; CPUID.01H:ECX.POPCNT [Bit 23]
					 (cpuid-flag
					  #ux_01
					  :reg #.*ecx*
					  :bit 23)
					 0))))))
	      (:Group-10 :1a :1b)
	      (:Group-8  :1a)
	      ("BTC" 2 (E v) (G v)
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ((:no-prefix . ("BSF"   2 (G v) (E v)
			      (:fn . (x86-bsf-Op/En-RM))
			      (:ud  . ((ud-Lock-used)))))
	       (:F3        . ("TZCNT" 2 (G v) (E v))))
	      ((:no-prefix . ("BSR"   2 (G v) (E v)
			      (:ud  . ((ud-Lock-used)))))
	       (:F3        . ("LZCNT" 2 (G v) (E v)
			      (:ud  . ((ud-Lock-used))))))
	      ("MOVSX" 2 (G v) (E b)
	       (:fn . (x86-movsxd))
	       (:ud  . ((ud-Lock-used))))
	      ("MOVSX" 2 (G v) (E w)
	       (:fn . (x86-movsxd))
	       (:ud  . ((ud-Lock-used)))))

    #| c0 |# (("XADD"     2 (E b)  (G b)
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ("XADD"     2 (E v)  (G v)
	       (:ud  . ((ud-Lock-used-Dest-not-Memory-Op))))
	      ((:no-prefix . ("CMPPS"     4 (V ps)  (H ps)  (W ps)  (I b)
			      (:fn . (x86-cmpps-Op/En-RMI))
			      (:ex . ((chk-exc :type-2 (:sse))))))
	       (:66        . ("CMPPD"     4 (V pd)  (H pd)  (W pd)  (I b)
			      (:fn . (x86-cmppd-Op/En-RMI))
			      (:ex . ((chk-exc :type-2 (:sse2))))))
	       (:F3        . ("CMPSS"     4 (V ss)  (H ss)  (W ss)  (I b)
			      (:fn . (x86-cmpss/cmpsd-Op/En-RMI
				      (sp/dp . #.*OP-SP*)))
			      (:ex . ((chk-exc :type-3 (:sse))))))
	       (:F2        . ("CMPSD"     4 (V sd)  (H sd)  (W sd)  (I b)
			      (:fn . (x86-cmpss/cmpsd-Op/En-RMI
				      (sp/dp . #.*OP-DP*)))
			      (:ex . ((chk-exc :type-3 (:sse2)))))))

	      ("MOVNTI"     2 (M y)   (G y)
	       (:ud  . ((ud-Lock-used)
			(ud-ModR/M.Mod-indicates-Register)
			(equal
			  ;; CPUID.01H:EDX.SSE2[bit 26]
			  (cpuid-flag
			   #ux_01
			   :reg #.*edx*
			   :bit 26)
			  0))))

	      ((:no-prefix . (:EXT
			      (((:opcode . #ux0F_C4)
				(:mod    . #b11)) .
				("PINSRW"     3 (P q)   (R y)  (I b)
				 (:ex . ((chk-exc :type-5 (:sse))))))
			      (((:opcode . #ux0F_C4)
				(:mod    . :mem)) .
				("PINSRW"    3 (P q)   (M w)  (I b)
				 (:ex . ((chk-exc :type-5 (:sse))))))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_C4)
				(:prefix . :66)
				(:mod    . #b11)) .
				("PINSRW"    4 (V dq)  (H dq) (R y)  (I b)
				 (:ex . ((chk-exc :type-5 (:sse2))))))
			      (((:opcode . #ux0F_C4)
				(:prefix . :66)
				(:mod    . :mem)) .
				("PINSRW"    4 (V dq)  (H dq) (M w)  (I b)
				 (:ex . ((chk-exc :type-5 (:sse2)))))))))

	      ((:no-prefix . ("PEXTRW"     3 (G d)   (N q)  (I b)
			      (:ex . ((chk-exc :type-5 (:sse))))))
	       (:66        . ("PEXTRW"    3 (G d)   (U dq) (I b)
			      (:ex . ((chk-exc :type-5 (:sse2)))))))

	      ((:no-prefix . ("SHUFPS"    4 (V ps)  (H ps)  (W ps)  (I b)
			      (:fn . (x86-shufps-Op/En-RMI))
			      (:ex . ((chk-exc :type-4 (:sse))))))
	       (:66        . ("SHUFPD"    4 (V pd)  (H pd)  (W pd)  (I b)
			      (:fn . (x86-shufpd-Op/En-RMI))
			      (:ex . ((chk-exc :type-4 (:sse2)))))))

	      (:Group-9 :1a)

    #| c8 |#  ("BSWAP" 1 (:RAX/EAX/R8/R8D)
	       (:ud  . ((ud-Lock-used))))
	      ("BSWAP" 1 (:RCX/ECX/R9/R9D)
	       (:ud  . ((ud-Lock-used))))
	      ("BSWAP" 1 (:RDX/EDX/R10/R10D)
	       (:ud  . ((ud-Lock-used))))
	      ("BSWAP" 1 (:RBX/EBX/R11/R11D)
	       (:ud  . ((ud-Lock-used))))
	      ("BSWAP" 1 (:RSP/ESP/R12/R12D)
	       (:ud  . ((ud-Lock-used))))
	      ("BSWAP" 1 (:RBP/EBP/R13/R13D)
	       (:ud  . ((ud-Lock-used))))
	      ("BSWAP" 1 (:RSI/ESI/R14/R14D)
	       (:ud  . ((ud-Lock-used))))
	      ("BSWAP" 1 (:RDI/EDI/R15/R15D)
	       (:ud  . ((ud-Lock-used)))))

  #| d0 |# (((:66        . ("ADDSUBPD"  3 (V pd)  (H pd)  (W pd)
			    (:ex . ((chk-exc :type-4 (:sse3))))))
	     (:F2        . ("ADDSUBPS"  3 (V ps)  (H ps)  (W ps)
			    (:ex . ((chk-exc :type-4 (:sse3)))))))

	    ((:no-prefix . ("PSRLW"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSRLW"     3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSRLD"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSRLD"     3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSRLQ"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSRLQ"     3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PADDQ"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("ADDQ"      3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMULLW"     2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PMULLW"    3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:66        . ("MOVQ"     2 (W q)   (V q)
			    (:ex . ((chk-exc :type-4 (:sse2))))))
	     (:F3        . ("MOVQ2DQ"   2 (V dq)  (N q)
			    (:ud . ((equal (cr0-slice :cr0-ts (cr0)) 1)
				    (equal (cr0-slice :cr0-em (cr0)) 1)
				    (equal (cr4-slice :cr4-osfxsr (cr4)) 0)
				    (equal (feature-flag-macro :sse2) 0)
				    (ud-Lock-used)))))
	     (:F2        . ("MOVDQ2Q"   2 (P q)   (U q)
			    (:ud . ((equal (cr0-slice :cr0-ts (cr0)) 1)
				    (equal (cr0-slice :cr0-em (cr0)) 1)
				    (equal (cr4-slice :cr4-osfxsr (cr4)) 0)
				    (equal (feature-flag-macro :sse2) 0)
				    (ud-Lock-used))))))

	    ((:no-prefix . ("PMOVMSKB"  2 (G d)   (N q)
			    (:ex . ((chk-exc :type-7 (:sse))))))
	     (:66        . ("PMOVMSKB" 2 (G d)   (U x)
			    (:fn . (x86-pmovmskb-Op/En-RM))
			    (:ex . ((chk-exc :type-7 (:sse2)))))))

  #| d8 |#  ((:no-prefix . ("PSUBUSB"   2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSUBUSB"  3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSUBUSW"   2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSUBUSW"  3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMINUB"    2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:sse))))))
	     (:66        . ("PMINUB"   3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PAND"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PAND"     3 (V x)   (H x)  (W x)
			    (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				    (operation . #.*OP-AND*)))
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PADDUSB"   2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PADDUSB"  3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PADDUSW"   2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PADDUSW"  3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMAXUB"    2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:sse))))))
	     (:66        . ("PMAXUB"   3 (V x)   (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PANDN"     2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PANDN"    3 (V x)   (H x)  (W x)
			    (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				    (operation . #.*OP-ANDN*)))
			    (:ex . ((chk-exc :type-4 (:sse2))))))))

  #| e0 |# (((:no-prefix . ("PAVGB"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:sse))))))
	     (:66        . ("PAVGB"     3 (V x)   (H x)   (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSRAW"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSRAW"     3 (V x)   (H x)   (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSRAD"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSRAD"     3 (V x)   (H x)   (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PAVGW"      2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:sse))))))
	     (:66        . ("PAVGW"     3 (V x)   (H x)   (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMULHUW"    2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:sse))))))
	     (:66        . ("PMULHUW"   3 (V x)   (H x)   (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMULHW"    2 (P q)   (Q q)
			    (:ex . ((chk-exc :type-22-7 (:sse))))))
	     (:66        . ("PMULHW"   3 (V x)   (H x)   (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:66        . ("CVTTPD2DQ" 2 (V x)   (W pd)
			    (:ex . ((chk-exc :type-2 (:sse2))))))
	     (:F3        . ("CVTDQ2PD"  2 (V x)   (W pd)
			    (:ex . ((chk-exc :type-5 (:sse2))))))
	     (:F2        . ("CVTPD2DQ"  2 (V x)   (W pd)
			    (:ex . ((chk-exc :type-2 (:sse2)))))))

	    ((:no-prefix . ("MOVNTQ"    2 (M q)   (P q)
			    (:ex . ((chk-exc :type-22-8 (:mmx))))
			    (:ud  . ((ud-ModR/M.Mod-indicates-Register)))))
	     (:66        . ("MOVNTDQ"  2 (M x)   (V x)
			    (:ex . ((chk-exc :type-1 (:sse2))))
			    (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))

  #| e8 |#  ((:no-prefix . ("PSUBSB"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSUBSB" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSUBSW"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSUBSW" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMINSW"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-4 (:sse))))))
	     (:66        . ("PMINSW" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("POR"  2 (P q)  (Q q)
			    ;; Note: Table 22-7 does not list POR in the
			    ;; "Applicable Instructions" section, but it does
			    ;; list PXOR.  So this is a guess.
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("POR" 3 (V x)  (H x)  (W x)
			    (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				      (operation . #.*OP-OR*)))
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PADDSB"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PADDSB" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PADDSW"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PADDSW" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMAXSW"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:sse))))))
	     (:66        . ("PMAXSW" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PXOR"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PXOR" 3 (V x)  (H x)  (W x)
			    (:fn . (x86-andp?/andnp?/orp?/xorp?/pand/pandn/por/pxor-Op/En-RM
				    (operation . #.*OP-XOR*)))
			    (:ex . ((chk-exc :type-4 (:sse2))))))))

  #| f0 |# (((:F2        . ("LDDQU" 2 (V x)  (M x)
			    (:ex . ((chk-exc :type-4 (:sse3))))
			    (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))

	    ((:no-prefix . ("PSLLW"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSLLW" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSLLD"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSLLD" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSLLQ"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSLLQ" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMULUDQ"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PMULUDQ" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PMADDWD"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PMADDWD" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSADBW"  2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:sse))))))
	     (:66        . ("PSADBW" 3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("MASKMOVQ"    2 (P q)  (N q)
			    (:ex . ((chk-exc :type-22-8 (:mmx))))))
	     (:66        . ("MASKMOVDQU" 2 (V dq) (U dq)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

  #| f8 |#  ((:no-prefix . ("PSUBB"    2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSUBB"   3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSUBW"    2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSUBW"   3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSUBD"    2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSUBD"   3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PSUBQ"    2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PSUBQ"   3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PADDB"    2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PADDB"   3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PADDW"    2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PADDW"   3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    ((:no-prefix . ("PADDD"    2 (P q)  (Q q)
			    (:ex . ((chk-exc :type-22-7 (:mmx))))))
	     (:66        . ("PADDD"   3 (V x)  (H x)  (W x)
			    (:ex . ((chk-exc :type-4 (:sse2)))))))

	    (:none
	       (:fn . (:no-instruction))))

  #|       -------------------------------        |#
  ))


(defconst *0F-38-three-byte-opcode-map-lst*
  ;; First two bytes are 0x0F 0x38.
  ;; Source: Intel Volume 2, Table A-4.

  '(
    #|       -------------------------------        |#

;; BOZO Rob question -- should these be UD in 64-bit mode? or just ignored..
    #| 00 |# (((:no-prefix . ("PSHUFB"          2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PSHUFB"         3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PHADDW"          2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PHADDW"         3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PHADDD"          2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PHADDD"         3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PHADDSW"         2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PHADDSW"        3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PMADDUBSW"       2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PMADDUBSW"      3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PHSUBW"          2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PHSUBW"         3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PHSUBD"          2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PHSUBD"         3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PHSUBSW"         2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PHSUBSW"        3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:sse3)))))))
    #| 08 |#  ((:no-prefix . ("PSIGNB"          2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PSIGNB"         3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:sse3)))))))
	      ((:no-prefix . ("PSIGNW"          2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PSIGNW"         3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PSIGND"          2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PSIGND"         3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . ("PMULHRSW"        2 (P q) (Q q)
			      (:ex . ((chk-exc :type-4 (:sse3))))))
	       (:66        . ("PMULHRSW"       3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66       . ("VPERMILPS"      3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPERMILPD"      3 (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VTESTPS"        2 (V x) (W x)
			       (:ex . ((chk-exc :type-4 (:avx)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VTESTPD"        2 (V x) (W x)
			       (:ex . ((chk-exc :type-4 (:avx))))))))

    #| 10 |# (((:66        . ("PBLENDVB"        2 (V dq) (W dq)
			      (:ex . ((chk-exc :type-4 (:sse4.1)))))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:v66       . ("VCVTPH2PS"       3 (V x)  (W x)  (I b)
			      (:ex . ((chk-exc :type-11 (:avx)))))))
	      ((:66        . ("BLENDVPS"        2 (V dq) (W dq)
			      (:ex . ((chk-exc :type-4 (:sse4.1)))))))
	      ((:66        . ("BLENDVPD"        2 (V dq) (W dq)
			      (:ex . ((chk-exc :type-4 (:sse4.1)))))))
	      ((:v66       . ("VPERMPS"         3 (V qq) (H qq) (W qq)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:66        . ("PTEST"          2 (V x)  (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
    #| 18 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBROADCASTSS"    2 (V x)  (W d)
			       (:ex . ((chk-exc :type-6 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBROADCASTSD"    2 (V qq) (W q)
			       (:ex . ((chk-exc :type-6 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBROADCASTF128"  2 (V qq) (M dq)
			       (:ex . ((chk-exc :type-6 (:avx2))))
			       (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . ("PABSB"           2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-4 (:sse4.1))))))
	       (:66        . ("PABSB"          2 (V x)  (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . ("PABSW"           2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-4 (:sse4.1))))))
	       (:66        . ("PABSW"          2 (V x)  (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . ("PABSD"           2 (P q)  (Q q)
			      (:ex . ((chk-exc :type-4 (:sse4.1))))))
	       (:66        . ("PABSD"          2 (V x)  (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction))))

;; BOZO Rob -- do the following have UD?

    #| 20 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_20)
				(:prefix . :66)
				(:mod    . :mem)) .
				("PMOVSXBW" 2 (V x) (M q)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_20)
				(:prefix . :66)
				(:mod    . #b11)) .
				("PMOVSXBW" 2 (V x) (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_21)
				(:prefix . :66)
				(:mod    . :mem)) .
				("PMOVSXBD" 2 (V x) (M d)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_21)
				(:prefix . :66)
				(:mod    . #b11)) .
				("PMOVSXBD" 2 (V x) (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_22)
				(:prefix . :66)
				(:mod    . :mem)) .
				("PMOVSXBQ" 2 (V x) (M w)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_22)
				(:prefix . :66)
				(:mod    . #b11)) .
				("PMOVSXBQ" 2 (V x) (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_23)
				(:prefix . :66)
				(:mod    . :mem)) .
				("PMOVSXWD" 2 (V x) (M q)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_23)
				(:prefix . :66)
				(:mod    . #b11)) .
				("PMOVSXWD" 2 (V x) (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_23)
				(:prefix . :66)
				(:mod    . :mem)) .
				("PMOVSXWQ" 2 (V x) (M d)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_23)
				(:prefix . :66)
				(:mod    . #b11)) .
				("PMOVSXWQ" 2 (V x) (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_23)
				(:prefix . :66)
				(:mod    . :mem)) .
				("PMOVSXDQ" 2 (V x) (M q)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_23)
				(:prefix . :66)
				(:mod    . #b11)) .
				("PMOVSXDQ" 2 (V x) (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
    #| 28 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMULDQ"     3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PCMPEQQ"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("MOVNTDQA"   2 (V x) (M x)
			      (:ex . ((chk-exc :type-1 (:avx2))))
			      (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PACKUSDW"   3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VMASKMOVPS"  3 (V x) (H x) (M x)
			       (:ex . ((chk-exc :type-6 (:avx2))))
			       (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VMASKMOVPD"  3 (V x) (H x) (M x)
			       (:ex . ((chk-exc :type-6 (:avx2))))
			       (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VMASKMOVPS"  3 (M x) (H x) (V x)
			       (:ex . ((chk-exc :type-6 (:avx2))))
			       (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VMASKMOVPD"  3 (M x) (H x) (V x)
			       (:ex . ((chk-exc :type-6 (:avx2))))
			       (:ud  . ((ud-ModR/M.Mod-indicates-Register)))))))

    #| 30 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_30)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PMOVZXBW" 2 (V x)  (M q)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_30)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PMOVZXBW" 2 (V x)  (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_31)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PMOVZXBD" 2 (V x)  (M d)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_31)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PMOVZXBD" 2 (V x)  (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_32)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PMOVZXBQ" 2 (V x)  (M w)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_32)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PMOVZXBQ" 2 (V x)  (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_33)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PMOVZXWD" 2 (V x)  (M q)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_33)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PMOVZXWD" 2 (V x)  (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_34)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PMOVZXWQ" 2 (V x)  (M d)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_34)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PMOVZXWQ" 2 (V x)  (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_38_35)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PMOVZXDQ" 2 (V x)  (M q)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_38_35)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PMOVZXDQ" 2 (V x)  (U x)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPERMD"     3 (V qq) (H qq) (W qq)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PCMPGTQ"   3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))

    #| 38 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMINSB"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMINSD"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMINUW"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMINUD"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMAXSB"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMAXSD"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMAXUW"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMAXUD"    3 (V x) (H x) (W x)
			      (:ex . ((chk-exc :type-4 (:avx2))))))))

    #| 40 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PMULLD"     3 (V x)  (H x)    (W x)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PHMINPOSUW" 2 (V dq) (W dq)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPSRLVD/Q"   3  (V x) (H x)    (W x)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPSRAVD"     3  (V x) (H x)    (W x)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPSLLVD/Q"   3  (V x) (H x)    (W x)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
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
	       (:v66        . ("VPBROADCASTD"   2  (V x)  (W x)
			       (:ex . ((chk-exc :type-7 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPBROADCASTQ"   2  (V x)  (W x)
			       (:ex . ((chk-exc :type-7 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBROADCASTI128" 2  (V qq) (M dq)
			       (:ex . ((chk-exc :type-6 (:avx2))))
			       (:ud  . ((ud-ModR/M.Mod-indicates-Register))))))
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
	       (:v66        . ("VPBROADCASTB" 2 (V x) (W x)
			       (:ex . ((chk-exc :type-7 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPBROADCASTW" 2 (V x) (W x)
			       (:ex . ((chk-exc :type-7 (:avx2)))))))
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
		(:66        . ("INVEPT"  2 (G y) (M dq)
			       (:ud  . ((ud-not-in-prot-or-64-mode)
					(ud-not-in-vmx-operation)
					(ud-invept-not-supported)
					(ud-ModR/M.Mod-indicates-Register)))
			       (:gp  . ((gp-cpl-not-0))))))
	       ((:no-prefix . (:none
			       (:fn . (:no-instruction))))
		(:66        . ("INVVPID" 2 (G y) (M dq)
			       (:ud  . ((ud-not-in-prot-or-64-mode)
					(ud-not-in-vmx-operation)
					(ud-invvpid-not-supported)
					(ud-ModR/M.Mod-indicates-Register)))
			       (:gp  . ((gp-cpl-not-0))))))
	       ((:no-prefix . (:none
			       (:fn . (:no-instruction))))
		(:66        . ("INVPCID" 2 (G y) (M dq)
			       (:ud  . ((ud-Lock-used)
					(ud-invpcid-not-supported)
					(ud-ModR/M.Mod-indicates-Register)))
			       (:gp  . ((gp-cpl-not-0))))))
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
		(:v66        . ("VPMASKMOVD/Q" 3 (V x) (H x) (M x)
				(:ex . ((chk-exc :type-6 (:avx2))))
				(:ud  . ((ud-ModR/M.Mod-indicates-Register))))))
	       (:none
	       (:fn . (:no-instruction)))
	       ((:no-prefix . (:none
			       (:fn . (:no-instruction))))
		(:v66        . ("VPMASKMOVD/Q" 3 (M x) (V x) (H x)
				(:ex . ((chk-exc :type-6 (:avx2))))
				(:ud  . ((ud-ModR/M.Mod-indicates-Register))))))
	       (:none
	       (:fn . (:no-instruction))))

    #| 90 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VGATHERDD/Q"      3 (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-12 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VGATHERQD/Q"      3 (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-12 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VGATHERDPS/D"     3 (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-12 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VGATHERQPS/D"     3 (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-12 (:avx2)))))))
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
	       (:v66        . ("VFMADDSUB132PS/D" 3 (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUBADD132PS/D" 3 (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
    #| 98 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD132PS/D"    3  (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD132SS/D"    3  (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB132PS/D"    3  (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB132SS/D"    3  (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD132PS/D"   3  (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD132SS/D"   3  (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB132PS/D"   3  (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB132SS/D"   3  (V x) (H x) (W x)
			       (:ex . ((chk-exc :type-3 (:avx2))))))))

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
	       (:v66        . ("VFMADDSUB213PS/D" 3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUBADD213PS/D" 3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
    #| a8 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD213PS/D"    3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD213SS/D"    3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB213PS/D"    3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB213SS/D"    3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD213PS/D"   3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD213SS/D"   3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB213PS/D"   3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB213SS/D"   3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-3 (:avx2))))))))

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
	       (:v66        . ("VFMADDSUB231PS/D" 3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUBADD231PS/D" 3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
    #| b8 |#  ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD231PS/D"    3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMADD231SS/D"    3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB231PS/D"    3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFMSUB231SS/D"    3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD231PS/D"   3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMADD231SS/D"   3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB231PS/D"   3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VFNMSUB231SS/D"   3 (V x)  (H x)  (W x)
			       (:ex . ((chk-exc :type-3 (:avx2))))))))

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
    #| c8 |#  ("SHA1NEXTE"   2 (V dq) (W dq)
	       (:ex . ((chk-exc :type-4 (:avx2)))))
	      ("SHA1MSG1"    2 (V dq) (W dq)
	       (:ex . ((chk-exc :type-4 (:avx2)))))
	      ("SHA1MSG2"    2 (V dq) (W dq)
	       (:ex . ((chk-exc :type-4 (:avx2)))))
	      ("SHA256RNDS2" 2 (V dq) (W dq)
	       (:ex . ((chk-exc :type-4 (:avx2)))))
	      ("SHA256MSG1"  2 (V dq) (W dq)
	       (:ex . ((chk-exc :type-4 (:avx2)))))
	      ("SHA256MSG2"  2 (V dq) (W dq)
	       (:ex . ((chk-exc :type-4 (:avx2)))))
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
	     (:66        . ("AESIMC"     2 (V dq) (W dq)
			    (:ex . ((chk-exc :type-4 (:aes)))))))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("AESENC"     3 (V dq) (H dq) (W dq)
			    (:ex . ((chk-exc :type-4 (:aes)))))))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("AESENCLAST" 3 (V dq) (H dq) (W dq)
			    (:ex . ((chk-exc :type-4 (:aes)))))))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("AESDEC"     3 (V dq) (H dq) (W dq)
			    (:ex . ((chk-exc :type-4 (:aes)))))))
	    ((:no-prefix . (:none
			    (:fn . (:no-instruction))))
	     (:66        . ("AESDECLAST" 3 (V dq) (H dq) (W dq)
			    (:ex . ((chk-exc :type-4 (:aes))))))))

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

  #| f0 |# (((:no-prefix    . ("MOVBE" 2 (G y)  (M y)
			       (:ud . ((= (cpuid-flag #ux_01 :reg #.*ecx* :bit 22) 0)
				       (ud-Lock-used)
				       (ud-repne-f2-V86-cpuid-case)
				       (ud-rep-f3-used)
				       (ud-ModR/M.Mod-indicates-Register)))))
	     (:66           . ("MOVBE" 2 (G w)  (M w)
			       (:ud . ((= (cpuid-flag #ux_01 :reg #.*ecx* :bit 22) 0)
				       (ud-Lock-used)
				       (ud-repne-f2-V86-cpuid-case)
				       (ud-rep-f3-used)
				       (ud-ModR/M.Mod-indicates-Register)))))
	     (:F3           . (:none
			       (:fn . (:no-instruction))))
	     (:F2           . ("CRC32" 2 (G d)  (E b)
			       (:ud . ((= (cpuid-flag #ux_01 :reg #.*ecx* :bit 20) 0)
				       (ud-Lock-used)))))
	     ;; ((:66 :F2)     . ("CRC32" 2 (G d)  (E b)))
	     )
	    ((:no-prefix    . ("MOVBE" 2 (M y)  (G y)
			       (:ud . ((= (cpuid-flag #ux_01 :reg #.*ecx* :bit 22) 0)
				       (ud-Lock-used)
				       (ud-repne-f2-V86-cpuid-case)
				       (ud-rep-f3-used)
				       (ud-ModR/M.Mod-indicates-Register)))))
	     (:66           . ("MOVBE" 2 (M w)  (G w)
			       (:ud . ((= (cpuid-flag #ux_01 :reg #.*ecx* :bit 22) 0)
				       (ud-Lock-used)
				       (ud-repne-f2-V86-cpuid-case)
				       (ud-rep-f3-used)
				       (ud-ModR/M.Mod-indicates-Register)))))
	     (:F3           . (:none
			       (:fn . (:no-instruction))))
	     (:F2           . ("CRC32" 2 (G d)  (E y)
			       (:ud . ((= (cpuid-flag #ux_01 :reg #.*ecx* :bit 20) 0)
				       (ud-Lock-used)))))
	     ;; ((:66 :F2)     . ("CRC32" 2 (G d)  (E w)))
	     )
	    ((:v            . ("ANDN"  3 (G y)  (B y)  (E y)
			       (:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
	     (:66           . (:none
			       (:fn . (:no-instruction))))
	     (:F3           . (:none
			       (:fn . (:no-instruction))))
	     (:F2           . (:none
			       (:fn . (:no-instruction))))
	     ;; ((:66 :F2)     . (:none (:fn . (:no-instruction))))
	     )
	    (:Group-17
	     ;; [Shilpi] I commented out :1a here, because :Group-17 is
	     ;; vex-specific only.  For legacy instructions, no modr/m byte is
	     ;; expected here.
	     ;; :1a
	     :v)
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
	    ((:v            . ("BZHI"  3 (G y)  (E y)  (B y)
			       (:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
	     (:66           . (:none
			       (:fn . (:no-instruction))))
	     (:vF3           . ("PEXT"  3 (G y)  (B y)  (E y)
				(:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
	     (:vF2           . ("PDEP"  3 (G y)  (B y)  (E y)
				(:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
	     ;; ((:66 :F2)     . (:none (:fn . (:no-instruction))))
	     )
	    ((:no-prefix    . (:none
			       (:fn . (:no-instruction))))
	     (:66           . ("ADCX"  2 (G y)  (E y)
			       (:ud . ((eql (feature-flag-macro :adx) 0)
				       (ud-Lock-used)))))
	     (:F3           . ("ADOX"  2 (G y)  (E y)
			       (:ud . ((eql (feature-flag-macro :adx) 0)
				       (ud-Lock-used)))))
	     (:vF2           . ("MULX"  3 (B y)  (G y)  (:rDX)  (E y)
				(:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
	     ;; ((:66 :F2)     . (:none (:fn . (:no-instruction))))
	     )
	    ((:v             . ("BEXTR" 3 (G y)  (E y)  (B y)
				(:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
	     (:v66           . ("SHLX"  3 (G y)  (E y)  (B y)
				(:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
	     (:vF3           . ("SARX"  3 (G y)  (E y)  (B y)
				(:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
	     (:vF2           . ("SHRX"  3 (G y)  (E y)  (B y)
				(:ex . ((chk-exc :type-vex-gpr (:bmi1))))))
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
	       (:v66        . ("VPERMQ"     3 (V qq)  (W qq)  (I b)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66        . ("VPERMPD"    3 (V qq)  (W qq)  (I b)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66        . ("VPBLENDD"   4 (V x)   (H x)   (W x)  (I b)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66        . ("VPERMILPS"  3 (V x)  (W x)  (I b)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix  . (:none
			       (:fn . (:no-instruction))))
	       (:v66       . ("VPERMILPD"  3 (V x)  (W x)  (I b)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPERM2F128" 4 (V qq) (H qq) (W qq) (I b)
			       (:ex . ((chk-exc :type-6 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction)))
   #| 08 |#  ((:no-prefix . (:none
			     (:fn . (:no-instruction))))
	      (:66        . ("ROUNDPS" 3 (V x)  (W x)  (I b)
			     (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("ROUNDPD" 3 (V x)  (W x)  (I b)
			      (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("ROUNDSS" 3 (V ss) (W ss) (I b)
			      (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("ROUNDSD" 3 (V sd) (W sd) (I b)
			      (:ex . ((chk-exc :type-3 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("BLENDPS" 4 (V x)  (H x)  (W x) (I b)
			      (:ex . ((chk-exc :type-4 (:sse4.1)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("BLENDPD" 4 (V x)  (H x)  (W x) (I b)
			      (:ex . ((chk-exc :type-4 (:sse4.1)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PBLENDW" 4 (V x)  (H x)  (W x) (I b)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . ("PALIGNR"  3 (P q)  (Q q)  (I b)
			      (:ex . ((chk-exc :type-4 (:avx2))))))
	       (:66        . ("PALIGNR" 4 (V x)  (H x)  (W x) (I b)
			      (:ex . ((chk-exc :type-4 (:avx2))))))))

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
	       (:66        . (:EXT
			      (((:opcode . #ux0F_3A_14)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PEXTRB"    3 (M b)  (V dq)  (I b)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_3A_14)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PEXTRB"    3 (R d)  (V dq)  (I b)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_3A_15)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PEXTRW"    3 (M w)  (V dq)  (I b)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_3A_15)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PEXTRW"    3 (R d)  (V dq)  (I b)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PEXTRD/Q"   3 (E y)  (V dq)  (I b)
			      (:ex . ((chk-exc :type-5 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("EXTRACTPS"  3 (E d)  (V dq)  (I b)
			      (:ex . ((chk-exc :type-5 (:avx2)))))))
   #| 18 |#  ((:no-prefix . (:none
			     (:fn . (:no-instruction))))
	      (:v66        . ("VINSERTF128"  4 (V qq) (H qq) (W qq) (I b)
			      (:ex . ((chk-exc :type-6 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VEXTRACTF128" 3 (W dq) (V qq) (I b)
			       (:ex . ((chk-exc :type-6 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VCVTPS2PH"    3 (W x)  (V x)  (I b)
			       (:ex . ((chk-exc :type-11 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction))))

    #| 20 |# (((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_3A_21)
				(:mod    . :mem)
				(:prefix . :66)) .
				("PINSRB"   4 (V dq) (H dq) (M b) (I b)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_3A_21)
				(:mod    . #b11)
				(:prefix . :66)) .
				("PINSRB"   4 (V dq) (H dq) (R y)  (I b)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . (:EXT
			      (((:opcode . #ux0F_3A_22)
				(:mod    . :mem)
				(:prefix . :66)) .
				("INSERTPS" 4 (V dq) (H dq) (M d) (I b)
				 (:ex . ((chk-exc :type-5 (:avx2))))))
			      (((:opcode . #ux0F_3A_22)
				(:mod    . #b11)
				(:prefix . :66)) .
				("INSERTPS" 4 (V dq) (H dq) (U dq) (I b)
				 (:ex . ((chk-exc :type-5 (:avx2)))))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PINSRD/Q"  4 (V dq) (H dq) (E y)  (I b)
			      (:ex . ((chk-exc :type-5 (:avx2)))))))
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
	      (:v66        . ("VINSERTI128"  4 (V qq) (H qq) (W qq) (I b)
			      (:ex . ((chk-exc :type-6 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VEXTRACTI128" 3 (W dq) (V qq) (I b)
			       (:ex . ((chk-exc :type-6 (:avx2)))))))
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
	       (:66        . ("DPPS"      4 (V x)  (H x)  (W x)  (I b)
			      (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("DPPD"      4 (V dq) (H dq) (W dq) (I b)
			      (:ex . ((chk-exc :type-2 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("MPSADBW"   4 (V x)  (H x)  (W x)  (I b)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PCLMULQDQ" 4 (V dq) (H dq) (W dq) (I b)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPERM2I128" 4 (V qq) (H qq) (W qq) (I b)
			       (:ex . ((chk-exc :type-6 (:avx2)))))))
	      (:none
	       (:fn . (:no-instruction)))
    #| 48 |#  (:none
	       (:fn . (:no-instruction)))
	      (:none
	       (:fn . (:no-instruction)))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBLENDVPS"  4 (V x)  (H x)  (W x)  (L x)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VBLENDVPD"  4 (V x)  (H x)  (W x)  (L x)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:v66        . ("VPBLENDVB"  4 (V x)  (H x)  (W x)  (L x)
			       (:ex . ((chk-exc :type-4 (:avx2)))))))
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
	       (:66        . ("PCMPESTRM" 3 (V dq)  (W dq)  (I b)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PCMPESTRI" 3 (V dq)  (W dq)  (I b)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PCMPISTRM" 3 (V dq)  (W dq)  (I b)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
	      ((:no-prefix . (:none
			      (:fn . (:no-instruction))))
	       (:66        . ("PCMPISTRI" 3 (V dq)  (W dq)  (I b)
			      (:ex . ((chk-exc :type-4 (:avx2)))))))
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
   #| b8 |#   (:none
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
	      ("SHA1RNDS4" 3 (V dq) (W dq) (I b)
	       (:ex . ((chk-exc :type-4 (:avx2)))))
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
   #| d8 |#   (:none
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
	       (:66        . ("AESKEYGENASSIST" 3 (V dq)  (W dq)  (I b)
			      (:ex . ((chk-exc :type-4 (:aes))))))))

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
	       (:vF2        . ("RORX" 3 (G y)  (E y)  (I b)
			       (:ex . ((chk-exc :type-vex-gpr (:bmi1)))))))
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
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x80)
		 (:reg    . #b001)) .
		 ("OR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x80)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x80)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x80)
		 (:reg    . #b100)) .
		 ("AND" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x80)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x80)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x80)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))

	       (((:opcode . #x81)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x81)
		 (:reg    . #b001)) .
		 ("OR" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x81)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x81)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x81)
		 (:reg    . #b100)) .
		 ("AND" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x81)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x81)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x81)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E v) (I z) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))
		  (:ud  . ((ud-Lock-used)))))

	       (((:opcode . #x82)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x82)
		 (:reg    . #b001)) .
		 ("OR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x82)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x82)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x82)
		 (:reg    . #b100)) .
		 ("AND" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x82)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x82)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x82)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E b) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))
		  (:ud  . ((ud-Lock-used)))))

	       (((:opcode . #x83)
		 (:reg    . #b000)) .
		 ("ADD" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADD*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x83)
		 (:reg    . #b001)) .
		 ("OR" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-OR*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x83)
		 (:reg    . #b010)) .
		 ("ADC" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-ADC*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x83)
		 (:reg    . #b011)) .
		 ("SBB" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SBB*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x83)
		 (:reg    . #b100)) .
		 ("AND" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-AND*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x83)
		 (:reg    . #b101)) .
		 ("SUB" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-SUB*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x83)
		 (:reg    . #b110)) .
		 ("XOR" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-XOR*)))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #x83)
		 (:reg    . #b111)) .
		 ("CMP" 2 (E v) (I b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-CMP*)))
		  (:ud  . ((ud-Lock-used)))))))

    (:Group-1A . ;; Covers opcode 8F.
	       ((((:opcode . #x8F)
		  (:reg    . #b000)) .
		  ("POP" 1 (E v) :1a :d64
		   (:fn . (x86-pop-Ev))
		   (:ud  . ((ud-Lock-used)))))
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
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC0)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC0)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC0)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC0)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC0)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC0)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC0)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))

		(((:opcode . #xC1)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC1)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC1)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC1)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC1)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC1)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xC1)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xC1)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (I b) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))

		(((:opcode . #xD0)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD0)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD0)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD0)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD0)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD0)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD0)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD0)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))

		(((:opcode . #xD1)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD1)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD1)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD1)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD1)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD1)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD1)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD1)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (1) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))

		(((:opcode . #xD2)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD2)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD2)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD2)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD2)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD2)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD2)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD2)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E b) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))

		(((:opcode . #xD3)
		  (:reg    . #b000)) .
		  ("ROL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD3)
		  (:reg    . #b001)) .
		  ("ROR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD3)
		  (:reg    . #b010)) .
		  ("RCL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD3)
		  (:reg    . #b011)) .
		  ("RCR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD3)
		  (:reg    . #b100)) .
		  ("SHL/SAL" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD3)
		  (:reg    . #b101)) .
		  ("SHR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #xD3)
		  (:reg    . #b110)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #xD3)
		  (:reg    . #b111)) .
		  ("SAR" 2 (E v) (:CL) :1a
		   (:fn . (x86-sal/sar/shl/shr/rcl/rcr/rol/ror))
		   (:ud  . ((ud-Lock-used)))))))

    (:Group-3 . ;; Covers opcodes F6 and F7.
	      ((((:opcode . #xF6)
		 (:reg    . #b000)) .
		 ("TEST" 1 (E b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-TEST*)))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xF6)
		 (:reg    . #b001)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xF6)
		 (:reg    . #b010)) .
		 ("NOT" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #xF6)
		 (:reg    . #b011)) .
		 ("NEG" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #xF6)
		 (:reg    . #b100)) .
		 ("MUL" 1 (E b) :1a
		  (:fn . (x86-mul))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xF6)
		 (:reg    . #b101)) .
		 ("IMUL" 1 (E b) :1a
		  (:fn . (x86-imul-Op/En-M))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xF6)
		 (:reg    . #b110)) .
		 ("DIV" 1 (E b) :1a
		  (:fn . (x86-div))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xF6)
		 (:reg    . #b111)) .
		 ("IDIV" 1 (E b) :1a
		  (:fn . (x86-idiv))
		  (:ud  . ((ud-Lock-used)))))

	       (((:opcode . #xF7)
		 (:reg    . #b000)) .
		 ("TEST" 1 (E b) :1a
		  (:fn . (x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
			  (operation . #.*OP-TEST*)))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xF7)
		 (:reg    . #b001)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #xF7)
		 (:reg    . #b010)) .
		 ("NOT" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #xF7)
		 (:reg    . #b011)) .
		 ("NEG" 1 (E b) :1a
		  (:fn . (x86-not/neg-F6-F7))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #xF7)
		 (:reg    . #b100)) .
		 ("MUL" 1 (E b) :1a
		  (:fn . (x86-mul))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xF7)
		 (:reg    . #b101)) .
		 ("IMUL" 1 (E b) :1a
		  (:fn . (x86-imul-Op/En-M))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xF7)
		 (:reg    . #b110)) .
		 ("DIV" 1 (E b) :1a
		  (:fn . (x86-div))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xF7)
		 (:reg    . #b111)) .
		 ("IDIV" 1 (E b) :1a
		  (:fn . (x86-idiv))
		  (:ud  . ((ud-Lock-used)))))))

    (:Group-4 . ;; Covers opcode FE.
	      ((((:opcode . #xFE)
		 (:reg    . #b000)) .
		 ("INC" 1 (E b) :1a
		  (:fn . (x86-inc/dec-FE-FF))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #xFE)
		 (:reg    . #b001)) .
		 ("DEC" 1 (E b) :1a
		  (:fn . (x86-inc/dec-FE-FF))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
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
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #xFF)
		 (:reg    . #b001)) .
		 ("DEC" 1 (E v) :1a
		  (:fn . (x86-inc/dec-FE-FF))
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #xFF)
		 (:reg    . #b010)) .
		 ("near CALL"  1 (E v) :1a :f64
		  (:fn . (x86-call-FF/2-Op/En-M))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xFF)
		 (:reg    . #b011)) .
		 ("far CALL"  1 (E p) :1a
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xFF)
		 (:reg    . #b100)) .
		 ("near JMP"  1 (E v) :1a :f64
		  (:fn . (x86-near-jmp-Op/En-M))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xFF)
		 (:reg    . #b101)
		 (:mod    . :mem)) .
		 ("far JMP"  1 (M p) :1a
		  (:fn . (x86-far-jmp-Op/En-D))
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #xFF)
		 (:reg    . #b110)) .
		 ("PUSH"  1 (E v) :1a :d64
		  (:fn . (x86-push-Ev))
		  (:ud  . ((ud-Lock-used)))))
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
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((and (gp-cpl-not-0) (gp-cr4-umip-is-1))))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b001)) .
		 (:ALT
		  (("STR" 1 (R v) :1a)
		   ("STR" 1 (M w) :1a))
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((and (gp-cpl-not-0) (gp-cr4-umip-is-1))))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b010)) .
		 ("LLDT" 1 (E w) :1a
		  (:fn . (x86-lldt))
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b011)) .
		 ("LTR" 1 (E w) :1a
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b100)) .
		 ("VERR" 1 (E w) :1a
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #ux0F_00)
		 (:reg    . #b101)) .
		 ("VERW" 1 (E w) :1a
		  (:ud  . ((ud-Lock-used)))))
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
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((and (gp-cpl-not-0) (gp-cr4-umip-is-1))))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b000)
		 (:r/m    . #b001)) .
		 ("VMCALL" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b000)
		 (:r/m    . #b010)) .
		 ("VMLAUNCH" 0 :1a
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b000)
		 (:r/m    . #b011)) .
		 ("VMRESUME" 0 :1a))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b000)
		 (:r/m    . #b100)) .
		 ("VMXOFF" 0 :1a
		  ;; BOZO Rob -- following GP only if executed in VMX root operation!
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . :mem)
		 (:reg    . #b001)) .
		 ("SIDT" 1 (M s) :1a
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((and (gp-cpl-not-0) (gp-cr4-umip-is-1))))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b000)) .
		 ("MONITOR" 0 :1a
		  (:ud  . ((ud-cpl-is-not-zero)
			   (equal
			    ;; CPUID.01H:ECX.MONITOR[bit 3]
			    (cpuid-flag
			     #ux_01
			     :reg #.*ecx*
			     :bit 3)
			    0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b001)) .
		 ("MWAIT" 0 :1a
		  (:ud  . ((ud-cpl-is-not-zero)
			   (equal
			    ;; CPUID.01H:ECX.MONITOR[bit 3]
			    (cpuid-flag
			     #ux_01
			     :reg #.*ecx*
			     :bit 3)
			    0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b010)) .
		 ("CLAC" 0 :1a
		  (:ud  . ((ud-Lock-used)
			   (ud-cpl-is-not-zero)
			   (equal (feature-flag-macro :smap) 0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b001)
		 (:r/m    . #b011)) .
		 ("STAC" 0 :1a
		  (:ud  . ((ud-Lock-used)
			   (ud-cpl-is-not-zero)
			   (equal
			    ;; CPUID.(EAX=07H, ECX=0H):EBX.SMAP[bit 20]
			    (cpuid-flag
			     #ux_07
			     :ecx #ux_00
			     :reg #.*ebx*
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
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . :mem)
		 (:reg    . #b011)) .
		 ("LIDT" 1 (M s) :1a
		  (:fn . (x86-lidt))
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b000)) .
		 ("XGETBV" 0 :1a
		  (:ud  . ((ud-Lock-used)
			   (equal
			    ;; CR4.OSXSAVE[bit 18]
			    (cr4-slice :cr4-osxsave (cr4))
			    0)
			   (equal
			    ;; CPUID.01H:ECX.XSAVE[bit 26]
			    (cpuid-flag
			     #ux_01
			     :reg #.*ecx*
			     :bit 26)
			    0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b001)) .
		 ("XSETBV" 0 :1a
		  (:ud  . ((ud-Lock-used)
			   (equal
			    ;; CR4.OSXSAVE[bit 18]
			    (cr4-slice :cr4-osxsave (cr4))
			    0)
			   (equal
			    ;; CPUID.01H:ECX.XSAVE[bit 26]
			    (cpuid-flag
			     #ux_01
			     :reg #.*ecx*
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
		  (:ud  . ((ud-Lock-used)
			   (ud-Opr-used)
			   (ud-Reps-used)
			   (equal
			    ;; CPUID.(EAX=7, ECX=0):EBX.RTM[bit 11]
			    (cpuid-flag
			     #ux_07
			     :ecx #ux_00
			     :reg #.*ebx*
			     :bit 11)
			    0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b110)) .
		 ("XTEST" 0 :1a
		  (:ud  . ((ud-Lock-used)
			   ;; CPUID.(EAX=7, ECX=0):EBX.HLE[bit 4] = 0 and
			   ;; CPUID.(EAX=7, ECX=0):EBX.RTM[bit 11] = 0.
			   (and (equal (cpuid-flag
					#ux_07
					:ecx #ux_00
					:reg #.*ebx*
					:bit 7)
				       0)
				(equal (cpuid-flag
					#ux_07
					:ecx #ux_00
					:reg #.*ebx*
					:bit 11)
				       0))))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b011)
		 (:r/m    . #b111)) .
		 ("ENCLU" 0 :1a
		  (:nm . ((nm-cr0-ts-is-1)))))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b100)) .
		 (:ALT
		  (("SMSW" 1 (M w) :1a)
		   ("SMSW" 1 (R v) :1a))
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((and (gp-cpl-not-0) (gp-cr4-umip-is-1))))))
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
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_01)
		 (:reg    . #b111)
		 (:mod    . :mem)) .
		 ("INVLPG" 1 (M b) :1a
		  (:ud  . ((ud-Lock-used)
			   (ud-ModR/M.Mod-indicates-Register)))
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b111)
		 (:r/m    . #b000)
		 (:mode   . :o64)) .
		 ("SWAPGS" 0 :1a
		  (:ud  . ((ud-Lock-used)))
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_01)
		 (:mod    . #b11)
		 (:reg    . #b111)
		 (:r/m    . #b001)) .
		 ("RDTSCP" 0 :1a
		  (:ud  . ((ud-Lock-used)
			   (equal
			    ;; CPUID.80000001H:EDX.RDTSCP[bit 27]
			    (cpuid-flag
			     #ux8000_0001
			     :reg #.*edx*
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
		  (:ud  . ((ud-Lock-used)))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b101)) .
		 ("BTS" 2 (E b) (I b) :1a
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b110)) .
		 ("BTR" 2 (E b) (I b) :1a
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))
	       (((:opcode . #ux0F_BA)
		 (:reg    . #b111)) .
		 ("BTC" 2 (E b) (I b) :1a
		  (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)))))))

    (:Group-9 . ;; Covers opcode 0F C7.
	      ((((:opcode . #ux0F_C7)
		 (:reg    . #b000)) .
		 (:none
		  (:fn . (:no-instruction))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :no-prefix)
		 (:mod    . :mem)
		 (:reg    . #b001)) .
		 (:ALT
		  (("CMPXCH8B" 1 (M q) :1a)
		   ("CMPXCHG16B" 1 (M dq) :1a))
		  (:ud  . ((ud-ModR/M.Mod-indicates-Register)))))
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
		 (:prefix . :no-prefix)
		 (:mod    . :mem)
		 (:reg    . #b110)) .
		 ("VMPTRLD" 1 (M q) :1a
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :66)
		 (:mod    . :mem)
		 (:reg    . #b110)) .
		 ("VMCLEAR" 1 (M q) :1a
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :F3)
		 (:mod    . :mem)
		 (:reg    . #b110)) .
		 ("VMXON" 1 (M q) :1a
		  ;; BOZO Rob -- following GP only if executed outside VMX operation!
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :no-prefix)
		 (:mod    . :mem)
		 (:reg    . #b111)) .
		 ("VMPTRLD" 1 (M q) :1a
		  (:gp  . ((gp-cpl-not-0)))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :no-prefix)
		 (:mod    . #b11)
		 (:reg    . #b110)) .
		 ("RDRAND" 1 (R v) :1a
		  (:fn . (x86-rdrand))
		  (:ud  . ((ud-Lock-used)
			   (ud-Reps-used)
			   (equal
			    ;; CPUID.01H:ECX.RDRAND[bit 30]
			    (cpuid-flag
			     #ux_01
			     :reg #.*ecx*
			     :bit 30)
			    t)))))
	       ;; [Shilpi] RDRAND, with #x66 prefix, isn't listed in the Intel
	       ;; manuals (May 2018 edition).  This is because all opcodes in
	       ;; this table other than RDRAND throw an error if they're used
	       ;; with a SIMD prefix that's not listed as an allowed mandatory
	       ;; prefix for that opcode.  RDRAND can be used with :no-prefix
	       ;; and :66, but not :F2 or :F3 (see (ud-Reps-used) in :ud
	       ;; listing).
	       (((:opcode . #ux0F_C7)
		 (:prefix . :66)
		 (:mod    . #b11)
		 (:reg    . #b110)) .
		 ("RDRAND" 1 (R w) :1a
		  (:fn . (x86-rdrand))
		  (:ud  . ((ud-Lock-used)
			   (ud-Reps-used)
			   (equal
			    ;; CPUID.01H:ECX.RDRAND[bit 30]
			    (cpuid-flag
			     #ux_01
			     :reg #.*ecx*
			     :bit 30)
			    t)))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :no-prefix)
		 (:reg    . #b111)) .
		 ("RDSEED" 1 (R v) :1a
		  (:ud  . ((ud-Lock-used)
			   (ud-Reps-used)
			   (equal
			    ;; CPUID.(EAX=07H, ECX=0H):EBX.RDSEED[bit 18]
			    (cpuid-flag
			     #ux_07
			     :ecx #ux_00
			     :reg #.*ebx*
			     :bit 18)
			    0)))))
	       (((:opcode . #ux0F_C7)
		 (:prefix . :F3)
		 (:reg    . #b111)) .
		 (:ALT
		  (("RDPID" 1 (R d) :1a)
		   ("RDPID" 1 (R q) :1a))
		  (:ud  . ((ud-Lock-used)
			   (equal
			    ;; CPUID.7H.0:ECX.RDPID[bit 22]
			    (cpuid-flag
			     #ux_07
			     :ecx #ux_0
			     :reg #.*ecx*
			     :bit 22)
			    0)))))))

    (:Group-10 . ;; Covers opcode 0F B9.
	       ((((:opcode . #ux0F_B9)) .
		 ("UD1" 0 :1a
		  ;; (:ud  . (t))
		  (:fn . (x86-illegal-instruction
			  (message . "UD1 encountered!")))))))

    (:Group-11 . ;; Covers opcodes C6 and C7.
	       ((((:opcode . #xC6)
		  (:reg    . #b000)) .
		  ("MOV" 2 (E b) (I b) :1a
		   (:fn . (x86-mov-Op/En-MI))
		   (:ud  . ((ud-Lock-used)))))
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
		   (:ud  . ((ud-Lock-used)
			    (equal
			     ;; CPUID.(EAX=7, ECX=0):EBX.RTM[bit 11]
			     (cpuid-flag
			      #ux_07
			      :ecx #ux_00
			      :reg #.*ebx*
			      :bit 11 ;; RTM
			      )
			     0)))))

		(((:opcode . #xC7)
		  (:reg    . #b000)) .
		  ("MOV" 2 (E v) (I z) :1a
		   (:fn . (x86-mov-Op/En-MI))
		   (:ud  . ((ud-Lock-used)))))
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
		   (:ud  . ((ud-Lock-used)
			    (equal
			     ;; CPUID.(EAX=7, ECX=0):EBX.RTM[bit 11]
			     (cpuid-flag
			      #ux_07
			      :ecx #ux_00
			      :reg #.*ebx*
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
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLW" 2 (N q) (I b) :1a
		   (:ex . ((chk-exc :type-22-7 (:mmx))))))
		(((:opcode . #ux0F_71)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLW" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
		(((:opcode . #ux0F_71)
		  (:reg    . #b011)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_71)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b100)) .
		  ("PSRAW" 2 (N q) (I b) :1a
		   (:ex . ((chk-exc :type-22-7 (:mmx))))))
		(((:opcode . #ux0F_71)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b100)) .
		  ("PSRAW" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
		(((:opcode . #ux0F_71)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_71)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLW" 2 (N q) (I b) :1a
		   (:ex . ((chk-exc :type-22-7 (:mmx))))))
		(((:opcode . #ux0F_71)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLW" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
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
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLD" 2 (N q) (I b) :1a
		   (:ex . ((chk-exc :type-22-7 (:mmx))))))
		(((:opcode . #ux0F_72)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLD" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
		(((:opcode . #ux0F_72)
		  (:reg    . #b011)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_72)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b100)) .
		  ("PSRAD" 2 (N q) (I b) :1a
		   (:ex . ((chk-exc :type-22-7 (:mmx))))))
		(((:opcode . #ux0F_72)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b100)) .
		  ("PSRAD" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
		(((:opcode . #ux0F_72)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_72)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLD" 2 (N q) (I b) :1a
		   (:ex . ((chk-exc :type-22-7 (:mmx))))))
		(((:opcode . #ux0F_72)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLD" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
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
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLQ" 2 (N q) (I b) :1a
		   (:ex . ((chk-exc :type-22-7 (:mmx))))))
		(((:opcode . #ux0F_73)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b010)) .
		  ("PSRLQ" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
		(((:opcode . #ux0F_73)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b011)) .
		  ("PSRLDQ" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
		(((:opcode . #ux0F_73)
		  (:prefix . :no-prefix)
		  (:reg    . #b100)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_73)
		  (:reg    . #b101)) .
		  (:none
		   (:fn . (:no-instruction))))
		(((:opcode . #ux0F_73)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLQ" 2 (N q) (I b) :1a
		   (:ex . ((chk-exc :type-22-7 (:mmx))))))
		(((:opcode . #ux0F_73)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("PSLLQ" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))
		(((:opcode . #ux0F_73)
		  (:prefix . :66)
		  (:mod    . #b11)
		  (:reg    . #b111)) .
		  ("PSLLDQ" 3 (H x) (U x) (I b) :1a
		   (:ex . ((chk-exc :type-7 (:sse2))))))))

    (:Group-15 . ;; Covers opcode 0F AE.
	       ((((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . :mem)
		  (:reg    . #b000)) .
		  ("FXSAVE" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal
			     ;; CPUID.01H:EDX.FXSR[bit 24]
			     (cpuid-flag
			      #ux_01
			      :reg #.*edx*
			      :bit 24)
			     0)))
		   (:nm  . ((nm-cr0-ts-is-1)
			    (nm-cr0-em-is-1)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b000)
		  (:mode   . :o64)) .
		  ("RDFSBASE" 1 (R y) :1a
		   (:ud  . ((ud-Lock-used)
			    (equal (cr4-slice :cr4-fsgsbase (cr4)) 0)
			    (equal
			     ;; CPUID.07H.0H:EBX.FSGSBASE[bit 0]
			     (cpuid-flag
			      #ux_07
			      :ecx #ux_00
			      :reg #.*ebx*
			      :bit 0)
			     0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . :mem)
		  (:reg    . #b001)) .
		  ("FXRSTOR" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal
			     ;; CPUID.01H:EDX.FXSR[bit 24]
			     (cpuid-flag
			      #ux_01
			      :reg #.*edx*
			      :bit 24)
			     0)))
		   (:nm  . ((nm-cr0-ts-is-1)
			    (nm-cr0-em-is-1)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :F3)
		  (:mod    . #b11)
		  (:reg    . #b001)
		  (:mode   . :o64)) .
		  ("RDGSBASE" 1 (R y) :1a
		   (:ud  . ((ud-Lock-used)
			    (equal (cr4-slice :cr4-fsgsbase (cr4)) 0)
			    (equal
			     ;; CPUID.07H.0H:EBX.FSGSBASE[bit 0]
			     (cpuid-flag
			      #ux_07
			      :ecx #ux_00
			      :reg #.*ebx*
			      :bit 0)
			     0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
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
		   (:ud  . ((ud-Lock-used)
			    (equal (cr4-slice :cr4-fsgsbase (cr4)) 0)
			    (equal
			     ;; CPUID.07H.0H:EBX.FSGSBASE[bit 0]
			     (cpuid-flag
			      #ux_07
			      :ecx #ux_00
			      :reg #.*ebx*
			      :bit 0)
			     0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
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
		   (:ud  . ((ud-Lock-used)
			    (equal (cr4-slice :cr4-fsgsbase (cr4)) 0)
			    (equal
			     ;; CPUID.07H.0H:EBX.FSGSBASE[bit 0]
			     (cpuid-flag
			      #ux_07
			      :ecx #ux_00
			      :reg #.*ebx*
			      :bit 0)
			     0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . :mem)
		  (:reg    . #b100)) .
		  ("XSAVE" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal (cr4-slice :cr4-osxsave (cr4)) 0)
			    (equal
			     ;; CPUID.01H:ECX.XSAVE[bit 26]
			     (cpuid-flag
			      #ux_01
			      :reg #.*ecx*
			      :bit 26)
			     0)))
		   (:gp  . ((gp-cpl-not-0)))
		   (:nm  . ((nm-cr0-ts-is-1)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . :mem)
		  (:reg    . #b101)) .
		  ("XRSTOR" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal (cr4-slice :cr4-osxsave (cr4)) 0)
			    (equal
			     ;; CPUID.01H:ECX.XSAVE[bit 26]
			     (cpuid-flag
			      #ux_01
			      :reg #.*ecx*
			      :bit 26)
			     0)))
		   (:gp  . ((gp-cpl-not-0)))
		   (:nm  . ((nm-cr0-ts-is-1)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b101)) .
		  ("LFENCE" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal
			     ;; CPUID.01H:EDX.SSE2[bit 26]
			     (cpuid-flag
			      #ux_01
			      :reg #.*edx*
			      :bit 26)
			     0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . :mem)
		  (:reg    . #b110)) .
		  ("XSAVEOPT" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal (cr4-slice :cr4-osxsave (cr4)) 0)
			    (or
			     (equal
			      ;; CPUID.01H:ECX.XSAVE[bit 26]
			      (cpuid-flag
			       #ux_01
			       :reg #.*ecx*
			       :bit 26)
			      0)
			     (equal
			      ;; CPUID.(EAX=0DH,ECX=1):EAX.XSAVEOPT[bit 0]
			      (cpuid-flag
			       #ux_0D
			       :ecx #ux_01
			       :reg #.*eax*
			       :bit 0)
			      0))))
		   (:nm  . ((nm-cr0-ts-is-1)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b110)) .
		  ("MFENCE" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal
			     ;; CPUID.01H:EDX.SSE2[bit 26]
			     (cpuid-flag
			      #ux_01
			      :reg #.*edx*
			      :bit 26)
			     0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . :mem)
		  (:reg    . #b111)) .
		  ("CLFLUSH" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal
			     ;; CPUID.01H:EDX.CLFSH[bit 19]
			     (cpuid-flag
			      #ux_01
			      :reg #.*edx*
			      :bit 19)
			     0)))))
		(((:opcode . #ux0F_AE)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:reg    . #b111)) .
		  ("SFENCE" 0 :1a
		   (:ud  . ((ud-Lock-used)
			    (equal
			     ;; CPUID.01H:EDX.SSE[bit 25]
			     (cpuid-flag
			      #ux_01
			      :reg #.*edx*
			      :bit 25)
			     0)))))))

    (:Group-16 . ;; Covers opcode 0F 18, 0F 1A, and 0F 1B.
	       ((((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b000)) .
		  ("PREFETCHNTA" 0 :1a
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b001)) .
		  ("PREFETCHT0" 0 :1a
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b010)) .
		  ("PREFETCHT1" 0 :1a
		   (:ud  . ((ud-Lock-used)))))
		(((:opcode . #ux0F_18)
		  (:mod    . :mem)
		  (:reg    . #b011)) .
		  ("PREFETCHT2" 0 :1a
		   (:ud  . ((ud-Lock-used)))))
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
		  ("RESERVEDNOP" 0))

		(((:opcode . #ux0F_1A)
		  (:prefix . :no-prefix)
		  (:mod    . :mem)
		  (:feat   . (:mpx))) .
		  ("BNDLDX" 2 (rB) (M)
		   ;; Source: BNDLDX-Load Extended Bounds Using Address
		   ;; Translation, Intel Vol. 2 (May 2018 edition)
		   ;; "Any encoding of this instruction that does not specify
		   ;; base or index register will treat those registers as zero
		   ;; (constant)."
		   ;; This leads me to infer that even though the source operand
		   ;; is obtained from the SIB byte, we should not #UD when the
		   ;; SIB byte is not present (i.e., when ModR/M.r/m != #b100 --
		   ;; See Table 2-2 in Intel Vol. 2).
		   (:ud  . ((ud-Lock-used)
			    ;; [Shilpi] "ModRM.r/m" below is likely a typo in
			    ;; the Intel manuals.  It should be ModRM.reg,
			    ;; because the latter is used to encode the BND
			    ;; registers.
			    ;; - If ModRM.r/m and REX encodes BND4-BND15 when
			    ;;   Intel MPX is enabled.
			    (<= 4 (reg-index (modr/m->reg ModR/M) rex-byte #.*r*))
			    (if  (eql proc-mode #.*64-bit-mode*)
				;; RIP-relative addressing in 64-bit mode
				;; Source: Table 2-7 (RIP-Relative Addressing),
				;; Intel Vol. 2 (May 2018 edition)
				;; - If ModRM is RIP-relative
				(and (eql (modr/m->mod ModR/M) 0)
				     (or ;; SIB Byte not present
				      (eql (modr/m->r/m ModR/M) #b101)
				      (and ;; SIB Byte present
				       (eql (modr/m->r/m ModR/M) #b100)
				       (eql (sib->base sib) #b101)
				       (eql (sib->index sib) #b100))))
			      ;; In Compatibility/Protected Mode:
			      ;; - If 67H prefix is used and CS.D=1.
			      ;; - If 67H prefix is not used and CS.D=0.
			      (if (eql (prefixes->adr prefixes)
				       #.*addr-size-override*)
				  ;; cs.d = 1
				  (eql (cs.d) 1)
				;; cs.d = 0
				(eql (cs.d) 0)))))))
		;; Source: BNDLDX-Load Extended Bounds Using Address
		;; Translation, Intel Vol. 2 (May 2018 edition)
		;; "The reg-reg form of this instruction will remain a NOP."
		(((:opcode . #ux0F_1A)
		  (:mod    . #b11)
		  (:feat   . (:mpx))
		  (:prefix . :no-prefix)) .
		  ("RESERVEDNOP" 0))

		(((:opcode . #ux0F_1A)
		  (:prefix . :66)
		  (:feat   . (:mpx))) .
		  (:ALT
		   (("BNDMOV"    2 (rB) (mB))
		    ("BNDMOV"    2 (rB) (M)))
		   (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)
			    ;; - If ModRM.r/m and REX encodes BND4-BND15 when
			    ;;   Intel MPX is enabled.
			    (<= 4 (reg-index (modr/m->r/m ModR/M) rex-byte #.*b*))
			    ;; In Compatibility/Protected Mode:
			    ;; - If 67H prefix is used and CS.D=1.
			    ;; - If 67H prefix is not used and CS.D=0.
			    (if (and (not (eql proc-mode #.*64-bit-mode*))
				     (eql (prefixes->adr prefixes)
					  #.*addr-size-override*))
				;; cs.d = 1
				(eql (cs.d) 1)
			      ;; cs.d = 0
			      (eql (cs.d) 0))))))

		(((:opcode . #ux0F_1A)
		  (:prefix . :F3)
		  (:feat   . (:mpx))) .
		  ("BNDCL"    2 (rB) (E y)
		   (:ud  . ((ud-Lock-used)
			    ;; [Shilpi] "ModRM.r/m" below is likely a typo in
			    ;; the Intel manuals.  It should be ModRM.reg,
			    ;; because the latter is used to encode the BND
			    ;; registers.
			    ;; - If ModRM.r/m and REX encodes BND4-BND15 when
			    ;;   Intel MPX is enabled.
			    (<= 4 (reg-index (modr/m->reg ModR/M) rex-byte #.*r*))
			    (and (not (eql proc-mode #.*64-bit-mode*))
				 ;; In Compatibility/Protected Mode:
				 ;; - If 67H prefix is used and CS.D=1.
				 ;; - If 67H prefix is not used and CS.D=0.
				 (if (eql (prefixes->adr prefixes)
					  #.*addr-size-override*)
				     ;; cs.d = 1
				     (eql (cs.d) 1)
				   ;; cs.d = 0
				   (eql (cs.d) 0)))))))

		(((:opcode . #ux0F_1A)
		  (:prefix . :F2)
		  (:feat   . (:mpx))) .
		  ("BNDCU"    2 (rB) (E y)
		   (:ud  . ((ud-Lock-used)
			    ;; [Shilpi] "ModRM.r/m" below is likely a typo in
			    ;; the Intel manuals.  It should be ModRM.reg,
			    ;; because the latter is used to encode the BND
			    ;; registers.
			    ;; - If ModRM.r/m and REX encodes BND4-BND15 when
			    ;;   Intel MPX is enabled.
			    (<= 4 (reg-index (modr/m->reg ModR/M) rex-byte #.*r*))
			    (and (not (eql proc-mode #.*64-bit-mode*))
				 ;; In Compatibility/Protected Mode:
				 ;; - If 67H prefix is used and CS.D=1.
				 ;; - If 67H prefix is not used and CS.D=0.
				 (if (eql (prefixes->adr prefixes)
					  #.*addr-size-override*)
				     ;; cs.d = 1
				     (eql (cs.d) 1)
				   ;; cs.d = 0
				   (eql (cs.d) 0)))))))

		;; Non-MPX Encoding:
		(((:opcode . #ux0F_1A)) .
		 ("RESERVEDNOP" 0))

		(((:opcode . #ux0F_1B)
		  (:prefix . :no-prefix)
		  (:mod    . :mem)
		  (:feat   . (:mpx))) .
		  ("BNDSTX"    2 (M) (rB)
		   ;; Source: BNDSTX-Load Extended Bounds Using Address
		   ;; Translation, Intel Vol. 2 (May 2018 edition)
		   ;; "Any encoding of this instruction that does not specify
		   ;; base or index register will treat those registers as zero
		   ;; (constant)."
		   ;; Similar to BNDLDX.
		   (:ud  . ((ud-Lock-used)
			    ;; [Shilpi] "ModRM.r/m" below is likely a typo in
			    ;; the Intel manuals.  It should be ModRM.reg,
			    ;; because the latter is used to encode the BND
			    ;; registers.
			    ;; - If ModRM.r/m and REX encodes BND4-BND15 when
			    ;;   Intel MPX is enabled.
			    (<= 4 (reg-index (modr/m->reg ModR/M) rex-byte #.*r*))
			    (if  (eql proc-mode #.*64-bit-mode*)
				;; RIP-relative addressing in 64-bit mode
				;; Source: Table 2-7 (RIP-Relative Addressing),
				;; Intel Vol. 2 (May 2018 edition)
				;; - If ModRM is RIP-relative
				(and (eql (modr/m->mod ModR/M) 0)
				     (or ;; SIB Byte not present
				      (eql (modr/m->r/m ModR/M) #b101)
				      (and ;; SIB Byte present
				       (eql (modr/m->r/m ModR/M) #b100)
				       (eql (sib->base sib) #b101)
				       (eql (sib->index sib) #b100))))
			      ;; In Compatibility/Protected Mode:
			      ;; - If 67H prefix is used and CS.D=1.
			      ;; - If 67H prefix is not used and CS.D=0.
			      (if (eql (prefixes->adr prefixes)
				       #.*addr-size-override*)
				  ;; cs.d = 1
				  (eql (cs.d) 1)
				;; cs.d = 0
				(eql (cs.d) 0)))))))
		;; "The reg-reg form of this instruction will remain a NOP."
		(((:opcode . #ux0F_1B)
		  (:prefix . :no-prefix)
		  (:mod    . #b11)
		  (:feat   . (:mpx))) .
		  ("RESERVEDNOP" 0))

		(((:opcode . #ux0F_1B)
		  (:prefix .  :66)
		  (:feat   . (:mpx))) .
		  (:ALT
		   (("BNDMOV"    2 (mB) (rB))
		    ("BNDMOV"    2 (M) (rB)))
		   (:ud  . ((ud-Lock-used-Dest-not-Memory-Op)
			    ;; - If ModRM.r/m and REX encodes BND4-BND15 when
			    ;;   Intel MPX is enabled.
			    (<= 4 (reg-index (modr/m->r/m ModR/M) rex-byte #.*b*))
			    ;; In Compatibility/Protected Mode:
			    ;; - If 67H prefix is used and CS.D=1.
			    ;; - If 67H prefix is not used and CS.D=0.
			    (if (and (not (eql proc-mode #.*64-bit-mode*))
				     (eql (prefixes->adr prefixes)
					  #.*addr-size-override*))
				;; cs.d = 1
				(eql (cs.d) 1)
			      ;; cs.d = 0
			      (eql (cs.d) 0))))))

		(((:opcode . #ux0F_1B)
		  (:prefix .  :F3)
		  (:mod    . :mem)
		  (:feat   . (:mpx))) .
		  ("BNDMK"    2 (rB) (M y)
		   (:ud  . ((ud-Lock-used)
			    ;; [Shilpi] "ModRM.r/m" below is likely a typo in
			    ;; the Intel manuals.  It should be ModRM.reg,
			    ;; because the latter is used to encode the BND
			    ;; registers.
			    ;; - If ModRM.r/m and REX encodes BND4-BND15 when
			    ;;   Intel MPX is enabled.
			    (<= 4 (reg-index (modr/m->reg ModR/M) rex-byte #.*r*))
			    (if (eql proc-mode #.*64-bit-mode*)
				;; - If RIP-relative addressing is used.
				;; Source: Table 2-7 (RIP-Relative Addressing),
				;; Intel Vol. 2 (May 2018 edition)
				(and (eql (modr/m->mod ModR/M) 0)
				     (or ;; SIB Byte not present
				      (eql (modr/m->r/m ModR/M) #b101)
				      (and ;; SIB Byte present
				       (eql (modr/m->r/m ModR/M) #b100)
				       (eql (sib->base sib) #b101)
				       (eql (sib->index sib) #b100))))
			      ;; In Compatibility/Protected Mode:
			      ;; - If 67H prefix is used and CS.D=1.
			      ;; - If 67H prefix is not used and CS.D=0.
			      (if (eql (prefixes->adr prefixes)
				       #.*addr-size-override*)
				  ;; cs.d = 1
				  (eql (cs.d) 1)
				;; cs.d = 0
				(eql (cs.d) 0)))))))
		(((:opcode . #ux0F_1B)
		  (:prefix .  :F3)
		  (:mod    . #b11)
		  (:feat   . (:mpx))) .
		  ;; Source: BNDMK-Make Bounds, Intel Vol. 2 (May 2018 Edition)
		  ;; "The reg-reg form of this instruction retains legacy behavior
		  ;; (NOP)."
		  ("RESERVEDNOP" 0))

		(((:opcode . #ux0F_1B)
		  (:prefix .  :F2)
		  (:feat   . (:mpx))) .
		  ("BNDCN"    2 (rB) (E y)
		   2 (rB) (E y)
		   (:ud  . ((ud-Lock-used)
			    ;; [Shilpi] "ModRM.r/m" below is likely a typo in
			    ;; the Intel manuals.  It should be ModRM.reg,
			    ;; because the latter is used to encode the BND
			    ;; registers.
			    ;; - If ModRM.r/m and REX encodes BND4-BND15 when
			    ;;   Intel MPX is enabled.
			    (<= 4 (reg-index (modr/m->reg ModR/M) rex-byte #.*r*))
			    (and (not (eql proc-mode #.*64-bit-mode*))
				 ;; In Compatibility/Protected Mode:
				 ;; - If 67H prefix is used and CS.D=1.
				 ;; - If 67H prefix is not used and CS.D=0.
				 (if (eql (prefixes->adr prefixes)
					  #.*addr-size-override*)
				     ;; cs.d = 1
				     (eql (cs.d) 1)
				   ;; cs.d = 0
				   (eql (cs.d) 0)))))))

		;; Non-MPX Encoding:
		(((:opcode . #ux0F_1B)) .
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
		  ("BLSR" 2 (B y) (E y) :v
		   (:ex . ((chk-exc :type-vex-gpr (:bmi2))))))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b010)) .
		  ("BLSMSK" 2 (B y) (E y) :v
		   (:ex . ((chk-exc :type-vex-gpr (:bmi2))))))
		(((:opcode . #ux0F_38_F3)
		  (:vex    . t)
		  (:reg    . #b011)) .
		  ("BLSI" 2 (B y) (E y) :v
		   (:ex . ((chk-exc :type-vex-gpr (:bmi2))))))
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
;; Exception and VEX.L Field Encoding) of Intel Manuals, Vol. 2. (May 2018
;; edition).

(defconst *vex-0F-opcodes*
  '((#x10 ((:VEX :0F :LIG :F2 :WIG)                  ("MOVSD"               3 (V x)  (H x)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VMOVSD"               3 (V x)  (H x)  (W sd)))
	  ((:VEX :0F :LIG :F3 :WIG)                  ("VMOVSS"               3 (V x)  (H x)  (W ss)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VMOVSS"               3 (V x)  (H x)  (W ss)))
	  ((:VEX :0F :128 :66 :WIG)                  ("VMOVUPD"              2 (V pd) (W pd)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VMOVUPD"              2 (V pd) (W pd)))
	  ((:VEX :0F :128 :WIG)                      ("VMOVUPS"              2 (V ps) (W ps)))
	  ((:VEX :0F :256 :WIG)                      ("VMOVUPS"              2 (V ps) (W ps))))
    (#x11 ((:VEX :0F :LIG :F2 :WIG)                  ("VMOVSD"               3 (V x)  (H x)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VMOVSD"               3 (V x)  (H x)  (W sd)))
	  ((:VEX :0F :LIG :F3 :WIG)                  ("VMOVSS"               3 (V x)  (H x)  (W ss)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VMOVSS"               3 (V x)  (H x)  (W ss)))
	  ((:VEX :0F :128 :66 :WIG)                  ("VMOVUPD"              2 (V pd) (W pd)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VMOVUPD"              2 (V pd) (W pd)))
	  ((:VEX :0F :128 :WIG)                      ("VMOVUPS"              2 (V ps) (W ps)))
	  ((:VEX :0F :256 :WIG)                      ("VMOVUPS"              2 (V ps) (W ps))))
    (#x12 ((:VEX :0F :128 :F2 :WIG)                  ("VMOVDDUP"             2 (V x)  (W x)))
	  ((:VEX :0F :256 :F2 :WIG)                  ("VMOVDDUP"             2 (V x)  (W x)))
	  ((:VEX :0F :NDS :128 :WIG (:mod . #b11))   ("VMOVHLPS"             3 (V q)  (H q)  (U q)))
	  ((:VEX :0F :NDS :128 :66 :WIG (:mod . :mem)) ("VMOVLPD"              3 (V q)  (H q)  (M q)))
	  ((:VEX :0F :NDS :128 :WIG (:mod . :mem))   ("VMOVLPS"              3 (V q)  (H q)  (M q)))
	  ((:VEX :0F :128 :F3 :WIG)                  ("VMOVSLDUP"            2 (V x)  (W x)))
	  ((:VEX :0F :256 :F3 :WIG)                  ("VMOVSLDUP"            2 (V x)  (W x))))
    (#x13 ((:VEX :0F :128 :66 :WIG (:mod . :mem))    ("VMOVLPD"              3 (V q)  (H q)  (M q)))
	  ((:VEX :0F :128 :WIG (:mod . :mem))        ("VMOVLPS"              3 (V q)  (H q)  (M q))))
    (#x14 ((:VEX :0F :NDS :128 :66 :WIG)             ("VUNPCKLPD"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VUNPCKLPD"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VUNPCKLPS"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VUNPCKLPS"            3 (V x)  (H x)  (W x))))
    (#x15 ((:VEX :0F :NDS :128 :66 :WIG)             ("VUNPCKHPD"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VUNPCKHPD"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VUNPCKHPS"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VUNPCKHPS"            3 (V x)  (H x)  (W x))))
    (#x16 ((:VEX :0F :NDS :128 :66 :WIG (:mod . :mem)) ("VMOVHPD"              3 (V dq)  (H q)  (M q) :v1))
	  ((:VEX :0F :NDS :128 :WIG (:mod . :mem))   ("VMOVHPS"              3 (V dq)  (H q)  (M q) :v1))
	  ((:VEX :0F :NDS :128 :WIG (:mod . #b11))   ("VMOVLHPS"             3 (V dq)  (H q)  (U q)))
	  ((:VEX :0F :128 :F3 :WIG)                  ("VMOVSHDUP"            2 (V x)   (W x)))
	  ((:VEX :0F :256 :F3 :WIG)                  ("VMOVSHDUP"            2 (V x)   (W x))))
    (#x17 ((:VEX :0F :128 :66 :WIG (:mod . :mem))    ("VMOVHPD"              3 (V dq)  (H q)  (M q) :v1))
	  ((:VEX :0F :128 :WIG (:mod . :mem))        ("VMOVHPS"              3 (V dq)  (H q)  (M q) :v1)))
    (#x28 ((:VEX :0F :128 :66 :WIG)                  ("VMOVAPD"              2 (V pd)  (W pd)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VMOVAPD"              2 (V pd)  (W pd)))
	  ((:VEX :0F :128 :WIG)                      ("VMOVAPS"              2 (V ps)  (W ps)))
	  ((:VEX :0F :256 :WIG)                      ("VMOVAPS"              2 (V ps)  (W ps))))
    (#x29 ((:VEX :0F :128 :66 :WIG)                  ("VMOVAPD"              2 (V pd)  (W pd)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VMOVAPD"              2 (V pd)  (W pd)))
	  ((:VEX :0F :128 :WIG)                      ("VMOVAPS"              2 (V ps)  (W ps)))
	  ((:VEX :0F :256 :WIG)                      ("VMOVAPS"              2 (V ps)  (W ps))))
    (#x2A ((:VEX :0F :NDS :LIG :F2 :W0)              ("VCVTSI2SD"            3 (V sd)  (H sd)  (E y)))
	  ((:VEX :0F :NDS :LIG :F2 :W1)              ("VCVTSI2SD"            3 (V sd)  (H sd)  (E y)))
	  ((:VEX :0F :NDS :LIG :F3 :W0)              ("VCVTSI2SS"            3 (V ss)  (H ss)  (E y)))
	  ((:VEX :0F :NDS :LIG :F3 :W1)              ("VCVTSI2SS"            3 (V ss)  (H ss)  (E y))))
    (#x2B ((:VEX :0F :128 :66 :WIG (:mod . :mem))    ("VMOVNTPD"             2 (M pd)  (V pd)))
	  ((:VEX :0F :256 :66 :WIG (:mod . :mem))    ("VMOVNTPD"             2 (M pd)  (V pd)))
	  ((:VEX :0F :128 :WIG (:mod . :mem))        ("VMOVNTPS"             2 (M ps)  (V ps)))
	  ((:VEX :0F :256 :WIG (:mod . :mem))        ("VMOVNTPS"             2 (M ps)  (V ps))))
    ;; Software should ensure VCVTTSD2SI, VC(VTTSS2SI are encoded with
    ;; VEX.L-0. Encoding VCVTTSD2SI with VEX(.L-1 may encounter unpredictable
    ;; behavior across different processor g(enerations.
    (#x2C ((:VEX :0F :LIG :F2 :W0)                   ("VCVTTSD2SI"           2 (G y)   (W sd)))
	  ((:VEX :0F :LIG :F2 :W1)                   ("VCVTTSD2SI"           2 (G y)   (W sd)))
	  ((:VEX :0F :LIG :F3 :W0)                   ("VCVTTSS2SI"           2 (G y)   (W ss)))
	  ((:VEX :0F :LIG :F3 :W1)                   ("VCVTTSS2SI"           2 (G y)   (W ss))))
    ;; Software should ensure VCVTSD2SI, VCV(TSS2SI are encoded with
    ;; VEX.L-0. Encoding VCVTSD2SI with VEX.(L-1 may encounter unpredictable
    ;; behavior across different processor g(enerations.
    (#x2D ((:VEX :0F :LIG :F2 :W0)                   ("VCVTSD2SI"            2 (G y)   (W sd)))
	  ((:VEX :0F :LIG :F2 :W1)                   ("VCVTSD2SI"            2 (G y)   (W sd)))
	  ((:VEX :0F :LIG :F3 :W0)                   ("VCVTSS2SI"            2 (G y)   (W ss)))
	  ((:VEX :0F :LIG :F3 :W1)                   ("VCVTSS2SI"            2 (G y)   (W ss))))
    (#x2E ((:VEX :0F :LIG :66 :WIG)                  ("VUCOMISD"             2 (V sd)  (W sd)))
	  ((:VEX :0F :LIG :WIG)                      ("VUCOMISS"             2 (V ss)  (W ss))))
    (#x2F ((:VEX :0F :LIG :66 :WIG)                  ("VCOMISD"              2 (V sd)  (W sd)))
	  ((:VEX :0F :LIG :WIG)                      ("VCOMISS"              2 (V ss)  (W ss))))
    (#x41 ((:VEX :0F :L1 :66 :W0 (:mod . #b11))      ("KANDB"                3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:VEX :0F :L1 :66 :W1 (:mod . #b11))      ("KANDD"                3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:VEX :0F :L1 :W1 (:mod . #b11))          ("KANDQ"                3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:VEX :0F :NDS :L1 :W0 (:mod . #b11))     ("KANDW"                3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x42 ((:VEX :0F :L1 :66 :W0 (:mod . #b11))      ("KANDNB"               3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:VEX :0F :L1 :66 :W1 (:mod . #b11))      ("KANDND"               3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:VEX :0F :L1 :W1 (:mod . #b11))          ("KANDNQ"               3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:VEX :0F :NDS :L1 :W0 (:mod . #b11))     ("KANDNW"               3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x44 ((:VEX :0F :L0 :66 :W0 (:mod . #b11))      ("KNOTB"                2 (K-reg b) (K-r/m b)))
	  ((:VEX :0F :L0 :66 :W1 (:mod . #b11))      ("KNOTD"                2 (K-reg d) (K-r/m d)))
	  ((:VEX :0F :L0 :W1 (:mod . #b11))          ("KNOTQ"                2 (K-reg q) (K-r/m q)))
	  ((:VEX :0F :L0 :W0 (:mod . #b11))          ("KNOTW"                2 (K-reg w) (K-r/m w))))
    (#x45 ((:VEX :0F :L1 :66 :W0 (:mod . #b11))      ("KORB"                 3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:VEX :0F :L1 :66 :W1 (:mod . #b11))      ("KORD"                 3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:VEX :0F :L1 :W1 (:mod . #b11))          ("KORQ"                 3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:VEX :0F :NDS :L1 :W0 (:mod . #b11))     ("KORW"                 3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x46 ((:VEX :0F :L1 :66 :W0 (:mod . #b11))      ("KXNORB"               3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:VEX :0F :L1 :66 :W1 (:mod . #b11))      ("KXNORD"               3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:VEX :0F :L1 :W1 (:mod . #b11))          ("KXNORQ"               3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:VEX :0F :NDS :L1 :W0 (:mod . #b11))     ("KXNORW"               3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x47 ((:VEX :0F :L1 :66 :W0 (:mod . #b11))      ("KXORB"                3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:VEX :0F :L1 :66 :W1 (:mod . #b11))      ("KXORD"                3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:VEX :0F :L1 :W1 (:mod . #b11))          ("KXORQ"                3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:VEX :0F :NDS :L1 :W0 (:mod . #b11))     ("KXORW"                3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x4A ((:VEX :0F :L1 :66 :W0 (:mod . #b11))      ("KADDB"                3 (K-reg b) (K-vex b) (K-r/m b)))
	  ((:VEX :0F :L1 :66 :W1 (:mod . #b11))      ("KADDD"                3 (K-reg d) (K-vex d) (K-r/m d)))
	  ((:VEX :0F :L1 :W1 (:mod . #b11))          ("KADDQ"                3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:VEX :0F :L1 :W0 (:mod . #b11))          ("KADDW"                3 (K-reg w) (K-vex w) (K-r/m w))))
    (#x4B ((:VEX :0F :NDS :L1 :66 :W0 (:mod . #b11)) ("KUNPCKBW"             3 (K-reg w) (K-vex w) (K-r/m w)))
	  ((:VEX :0F :NDS :L1 :W1 (:mod . #b11))     ("KUNPCKDQ"             3 (K-reg q) (K-vex q) (K-r/m q)))
	  ((:VEX :0F :NDS :L1 :W0 (:mod . #b11))     ("KUNPCKWD"             3 (K-reg d) (K-vex d) (K-r/m d))))
    (#x50 ((:VEX :0F :128 :66 :WIG)                  ("VMOVMSKPD"            2 (G y)  (U pd)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VMOVMSKPD"            2 (G y)  (U pd)))
	  ((:VEX :0F :128 :WIG)                      ("VMOVMSKPS"            2 (G y)  (U ps)))
	  ((:VEX :0F :256 :WIG)                      ("VMOVMSKPS"            2 (G y)  (U ps))))
    (#x51 ((:VEX :0F :128 :66 :WIG)                  ("VSQRTPD"              2 (V pd)  (W pd)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VSQRTPD"              2 (V pd)  (W pd)))
	  ((:VEX :0F :128 :WIG)                      ("VSQRTPS"              2 (V ps)  (W ps)))
	  ((:VEX :0F :256 :WIG)                      ("VSQRTPS"              2 (V ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VSQRTSD"              3 (V sd)  (H sd)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VSQRTSS"              3 (V ss)  (H ss)  (W ss))))
    (#x52 ((:VEX :0F :128 :WIG)                      ("VRSQRTPS"             2 (V ps)  (W ps)))
	  ((:VEX :0F :256 :WIG)                      ("VRSQRTPS"             2 (V ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VRSQRTSS"             3 (V ss)  (H ss)  (W ss))))
    (#x53 ((:VEX :0F :128 :WIG)                      ("VRCPPS"               2 (V ps)  (W ps)))
	  ((:VEX :0F :256 :WIG)                      ("VRCPPS"               2 (V ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VRCPSS"               3 (V ss)  (H ss)  (W ss))))
    (#x54 ((:VEX :0F :NDS :128 :66)                  ("VANDPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66)                  ("VANDPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128)                      ("VANDPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256)                      ("VANDPS"               3 (V ps)  (H ps)  (W ps))))
    (#x55 ((:VEX :0F :NDS :128 :66)                  ("VANDNPD"              3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66)                  ("VANDNPD"              3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128)                      ("VANDNPS"              3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256)                      ("VANDNPS"              3 (V ps)  (H ps)  (W ps))))
    (#x56 ((:VEX :0F :NDS :128 :66)                  ("VORPD"                3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66)                  ("VORPD"                3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128)                      ("VORPS"                3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256)                      ("VORPS"                3 (V ps)  (H ps)  (W ps))))
    (#x57 ((:VEX :0F :NDS :128 :66 :WIG)             ("VXORPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VXORPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VXORPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VXORPS"               3 (V ps)  (H ps)  (W ps))))
    (#x58 ((:VEX :0F :NDS :128 :66 :WIG)             ("VADDPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VADDPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VADDPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VADDPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VADDSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VADDSS"               3 (V ss)  (H ss)  (W ss))))
    (#x59 ((:VEX :0F :NDS :128 :66 :WIG)             ("VMULPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VMULPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VMULPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VMULPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VMULSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VMULSS"               3 (V ss)  (H ss)  (W ss))))
    (#x5A ((:VEX :0F :128 :66 :WIG)                  ("VCVTPD2PS"            2 (V ps)  (W pd)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VCVTPD2PS"            2 (V ps)  (W pd)))
	  ((:VEX :0F :128 :WIG)                      ("VCVTPS2PD"            2 (V pd)  (W ps)))
	  ((:VEX :0F :256 :WIG)                      ("VCVTPS2PD"            2 (V pd)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VCVTSD2SS"            3 (V ss)  (H x)   (W sd)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VCVTSS2SD"            3 (V sd)  (H x)   (W ss))))
    (#x5B ((:VEX :0F :128 :WIG)                      ("VCVTDQ2PS"            2 (V ps)  (W dq)))
	  ((:VEX :0F :256 :WIG)                      ("VCVTDQ2PS"            2 (V ps)  (W dq)))
	  ((:VEX :0F :128 :66 :WIG)                  ("VCVTPS2DQ"            2 (V dq)  (W ps)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VCVTPS2DQ"            2 (V dq)  (W ps)))
	  ((:VEX :0F :128 :F3 :WIG)                  ("VCVTTPS2DQ"           2 (V dq)  (W ps)))
	  ((:VEX :0F :256 :F3 :WIG)                  ("VCVTTPS2DQ"           2 (V dq)  (W ps))))
    (#x5C ((:VEX :0F :NDS :128 :66 :WIG)             ("VSUBPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VSUBPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VSUBPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VSUBPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VSUBSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VSUBSS"               3 (V ss)  (H ss)  (W ss))))
    (#x5D ((:VEX :0F :NDS :128 :66 :WIG)             ("VMINPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VMINPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VMINPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VMINPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VMINSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VMINSS"               3 (V ss)  (H ss)  (W ss))))
    (#x5E ((:VEX :0F :NDS :128 :66 :WIG)             ("VDIVPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VDIVPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VDIVPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VDIVPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VDIVSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VDIVSS"               3 (V ss)  (H ss)  (W ss))))
    (#x5F ((:VEX :0F :NDS :128 :66 :WIG)             ("VMAXPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VMAXPD"               3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :WIG)                 ("VMAXPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :WIG)                 ("VMAXPS"               3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VMAXSD"               3 (V sd)  (H sd)  (W sd)))
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VMAXSS"               3 (V ss)  (H ss)  (W ss))))
    (#x60 ((:VEX :0F :NDS :256 :66 :WIG)             ("VPUNPCKLBW"           3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPUNPCKLBW"           3 (V x)  (H x)  (W x))))
    (#x61 ((:VEX :0F :NDS :256 :66 :WIG)             ("VPUNPCKLWD"           3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPUNPCKLWD"           3 (V x)  (H x)  (W x))))
    (#x62 ((:VEX :0F :NDS :256 :66 :WIG)             ("VPUNPCKLDQ"           3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPUNPCKLDQ"           3 (V x)  (H x)  (W x))))
    (#x63 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPACKSSWB"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPACKSSWB"            3 (V x)  (H x)  (W x))))
    (#x64 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPCMPGTB"             3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPCMPGTB"             3 (V x)  (H x)  (W x))))
    (#x65 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPCMPGTW"             3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPCMPGTW"             3 (V x)  (H x)  (W x))))
    (#x66 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPCMPGTD"             3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPCMPGTD"             3 (V x)  (H x)  (W x))))
    (#x67 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPACKUSWB"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPACKUSWB"            3 (V x)  (H x)  (W x))))
    (#x68 ((:VEX :0F :NDS :256 :66 :WIG)             ("VPUNPCKHBW"           3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPUNPCKHBW"           3 (V x)  (H x)  (W x))))
    (#x69 ((:VEX :0F :NDS :256 :66 :WIG)             ("VPUNPCKHWD"           3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPUNPCKHWD"           3 (V x)  (H x)  (W x))))
    (#x6A ((:VEX :0F :NDS :256 :66 :WIG)             ("VPUNPCKHDQ"           3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPUNPCKHDQ"           3 (V x)  (H x)  (W x))))
    (#x6B ((:VEX :0F :NDS :128 :66 :WIG)             ("VPACKSSDW"            3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPACKSSDW"            3 (V x)  (H x)  (W x))))
    (#x6C ((:VEX :0F :NDS :256 :66 :WIG)             ("VPUNPCKLQDQ"          3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPUNPCKLQDQ"          3 (V x)  (H x)  (W x))))
    (#x6D ((:VEX :0F :NDS :256 :66 :WIG)             ("VPUNPCKHQDQ"          3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPUNPCKHQDQ"          3 (V x)  (H x)  (W x))))
    (#x6E ((:VEX :0F :128 :66 :W1)                   ("VMOVQ"                2 (V q)    (W q)))
	  ((:VEX :0F :128 :66 :W0)                   ("VMOVD"                2 (V q)    (W q))))
    (#x6F ((:VEX :0F :128 :66 :WIG)                  ("VMOVDQA"              2 (V x)  (W x)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VMOVDQA"              2 (V x)  (W x)))
	  ((:VEX :0F :128 :F3 :WIG)                  ("VMOVDQU"              2 (V x)  (W x)))
	  ((:VEX :0F :256 :F3 :WIG)                  ("VMOVDQU"              2 (V x)  (W x))))
    (#x70 ((:VEX :0F :128 :66 :WIG)                  ("VPSHUFD"              3 (V x)   (W x)   (I b))) ;; ib
	  ((:VEX :0F :256 :66 :WIG)                  ("VPSHUFD"              3 (V x)   (W x)   (I b))) ;; ib
	  ((:VEX :0F :128 :F3 :WIG)                  ("VPSHUFHW"             3 (V x)   (W x)   (I b))) ;; ib
	  ((:VEX :0F :256 :F3 :WIG)                  ("VPSHUFHW"             3 (V x)   (W x)   (I b))) ;; ib
	  ((:VEX :0F :128 :F2 :WIG)                  ("VPSHUFLW"             3 (V x)   (W x)   (I b))) ;; ib
	  ((:VEX :0F :256 :F2 :WIG)                  ("VPSHUFLW"             3 (V x)   (W x)   (I b)))) ;; ib
    (#x71 ((:VEX :0F :NDD :128 :66 :WIG (:reg . 2))  ("VPSRLVW"              3 (V x)   (H x)  (W x))) ;; /2 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 2))  ("VPSRLVW"              3 (V x)   (H x)  (W x))) ;; /2 ib
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 4))  ("VPSRAVW"              3 (V x)   (H x)   (W x))) ;; /4 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 4))  ("VPSRAVW"              3 (V x)   (H x)   (W x))) ;; /4 ib
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 6))  ("VPSLLVW"              3 (V x)  (H x)  (W x))) ;; /6 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 6))  ("VPSLLVW"              3 (V x)  (H x)  (W x)))) ;; /6 ib
    (#x72 ((:VEX :0F :NDD :128 :66 :WIG (:reg . 2))  ("VPSLLVD"              3 (V x)  (H x)  (W x))) ;; /2 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 2))  ("VPSLLVD"              3 (V x)  (H x)  (W x))) ;; /2 ib
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 4))  ("VPSRAVW"              3 (V x)   (H x)   (W x))) ;; /4 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 4))  ("VPSRAVW"              3 (V x)   (H x)   (W x))) ;; /4 ib
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 6))  ("VPSLLVW"              3 (V x)  (H x)  (W x))) ;; /6 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 6))  ("VPSLLVW"              3 (V x)  (H x)  (W x)))) ;; /6 ib
    (#x73 ((:VEX :0F :NDD :128 :66 :WIG (:reg . 2))  ("VPSRLVQ"              3 (V x)   (H x)  (W x))) ;; /2 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 2))  ("VPSRLVQ"              3 (V x)   (H x)  (W x))) ;; /2 ib
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 3))  ("VPSRLDQ"              3 (H x) (U x) (I b) :1a)) ;; /3 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 3))  ("VPSRLDQ"              3 (H x) (U x) (I b) :1a)) ;; /3 ib
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 6))  ("VPSLLQ"               3 (V x)  (H x)  (W x))) ;; /6 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 6))  ("VPSLLQ"               3 (V x)  (H x)  (W x))) ;; /6 ib
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 7))  ("VPSLLDQ"              3 (H x) (U x) (I b) :1a)) ;; /7 ib
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 7))  ("VPSLLDQ"              3 (H x) (U x) (I b) :1a))) ;; /7 ib
    (#x74 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPCMPEQB"             3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPCMPEQB"             3 (V x)   (H x)  (W x))))
    (#x75 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPCMPEQW"             3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPCMPEQW"             3 (V x)   (H x)  (W x))))
    (#x76 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPCMPEQD"             3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPCMPEQD"             3 (V x)   (H x)  (W x))))
    (#x77 ((:VEX :0F :256 :WIG)                      ("VZEROALL"             0))
	  ((:VEX :0F :128 :WIG)                      ("VZEROUPPER"           0)))
    (#x7C ((:VEX :0F :NDS :128 :66 :WIG)             ("VHADDPD"              3 (V pd)   (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VHADDPD"              3 (V pd)   (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :F2 :WIG)             ("VHADDPS"              3 (V ps)   (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :F2 :WIG)             ("VHADDPS"              3 (V ps)   (H ps)  (W ps))))
    (#x7D ((:VEX :0F :NDS :128 :66 :WIG)             ("VHSUBPD"              3 (V pd)   (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VHSUBPD"              3 (V pd)   (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :F2 :WIG)             ("VHSUBPS"              3 (V ps)   (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :F2 :WIG)             ("VHSUBPS"              3 (V ps)   (H ps)  (W ps))))
    (#x7E ((:VEX :0F :128 :66 :W0)                   ("VMOVD"                2 (E y)    (V y)))
	  ((:VEX :0F :128 :66 :W1)                   ("VMOVQ"                2 (V q)    (W q)))
	  ((:VEX :0F :128 :F3 :WIG)                  ("VMOVQ"                2 (V q)    (W q))))
    (#x7F ((:VEX :0F :128 :66 :WIG)                  ("VMOVDQA"              2 (V x)  (W x)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VMOVDQA"              2 (V x)  (W x)))
	  ((:VEX :0F :128 :F3 :WIG)                  ("VMOVDQU"              2 (V x)  (W x)))
	  ((:VEX :0F :256 :F3 :WIG)                  ("VMOVDQU"              2 (V x)  (W x))))
    (#x90 ((:VEX :0F :L0 :66 :W0)                    ("KMOVB"                2 (K-reg b) (K-r/m b)))
	  ((:VEX :0F :L0 :66 :W1)                    ("KMOVD"                2 (K-reg d) (K-r/m d)))
	  ((:VEX :0F :L0 :W1)                        ("KMOVQ"                2 (K-reg q) (K-r/m q)))
	  ((:VEX :0F :L0 :W0)                        ("KMOVW"                2 (K-reg w) (K-r/m w))))
    (#x91 ((:VEX :0F :L0 :66 :W0 (:mod . :mem))      ("KMOVB"                2 (K-r/m b) (K-reg b)))
	  ((:VEX :0F :L0 :66 :W1 (:mod . :mem))      ("KMOVD"                2 (K-r/m d) (K-reg d)))
	  ((:VEX :0F :L0 :W1 (:mod . :mem))          ("KMOVQ"                2 (K-r/m q) (K-reg q)))
	  ((:VEX :0F :L0 :W0 (:mod . :mem))          ("KMOVW"                2 (K-r/m w) (K-reg w))))
    (#x92 ((:VEX :0F :L0 :66 :W0 (:mod . #b11))      ("KMOVB"                2 (K-reg b) (K-r/m b)))
	  ((:VEX :0F :L0 :F2 :W0 (:mod . #b11))      ("KMOVD"                2 (K-reg d) (K-r/m d)))
	  ((:VEX :0F :L0 :F2 :W1 (:mod . #b11))      ("KMOVQ"                2 (K-reg q) (K-r/m q)))
	  ((:VEX :0F :L0 :W0 (:mod . #b11))          ("KMOVW"                2 (K-reg w) (K-r/m w))))
    (#x93 ((:VEX :0F :L0 :66 :W0 (:mod . #b11))      ("KMOVB"                2 (K-reg b) (K-r/m b)))
	  ((:VEX :0F :L0 :F2 :W0 (:mod . #b11))      ("KMOVD"                2 (K-reg d) (K-r/m d)))
	  ((:VEX :0F :L0 :F2 :W1 (:mod . #b11))      ("KMOVQ"                2 (K-reg q) (K-r/m q)))
	  ((:VEX :0F :L0 :W0 (:mod . #b11))          ("KMOVW"                2 (K-reg w) (K-r/m w))))
    (#x98 ((:VEX :0F :L0 :66 :W0 (:mod . #b11))      ("KORTESTB"             2 (K-reg b) (K-r/m b)))
	  ((:VEX :0F :L0 :66 :W1 (:mod . #b11))      ("KORTESTD"             2 (K-reg d) (K-r/m d)))
	  ((:VEX :0F :L0 :W1 (:mod . #b11))          ("KORTESTQ"             2 (K-reg q) (K-r/m q)))
	  ((:VEX :0F :L0 :W0 (:mod . #b11))          ("KORTESTW"             2 (K-reg w) (K-r/m w))))
    (#x99 ((:VEX :0F :L0 :66 :W0 (:mod . #b11))      ("KTESTB"               2 (K-reg b) (K-r/m b)))
	  ((:VEX :0F :L0 :66 :W1 (:mod . #b11))      ("KTESTD"               2 (K-reg d) (K-r/m d)))
	  ((:VEX :0F :L0 :W1 (:mod . #b11))          ("KTESTQ"               2 (K-reg q) (K-r/m q)))
	  ((:VEX :0F :L0 :W0 (:mod . #b11))          ("KTESTW"               2 (K-reg w) (K-r/m w))))
    (#xAE ((:VEX :0F :LZ :WIG (:reg . 2))            ("VLDMXCSR"             0 :1a))
	  ((:VEX :0F :LZ :WIG (:reg . 3))            ("VSTMXCSR"             0 :1a)))
    (#xC2 ((:VEX :0F :NDS :128 :66 :WIG)             ("VCMPPD"               4 (V pd)  (H pd)  (W pd)  (I b))) ;; ib
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VCMPPD"               4 (V pd)  (H pd)  (W pd)  (I b))) ;; ib
	  ((:VEX :0F :NDS :128 :WIG)                 ("VCMPPS"               4 (V ps)  (H ps)  (W ps)  (I b))) ;; ib
	  ((:VEX :0F :NDS :256 :WIG)                 ("VCMPPS"               4 (V ps)  (H ps)  (W ps)  (I b))) ;; ib
	  ((:VEX :0F :NDS :LIG :F2 :WIG)             ("VCMPSD"               4 (V sd)  (H sd)  (W sd)  (I b))) ;; ib
	  ((:VEX :0F :NDS :LIG :F3 :WIG)             ("VCMPSS"               4 (V ss)  (H ss)  (W ss)  (I b)))) ;; ib
    (#xC4 ((:VEX :0F :NDS :128 :66 :W0)              ("VPINSRW"              4 (V dq)  (H dq) (R y)  (I b)))) ;; ib
    (#xC5 ((:VEX :0F :128 :66 :W0)                   ("VPEXTRW"              3 (G d)   (U dq) (I b)))) ;; ib
    (#xC6 ((:VEX :0F :NDS :128 :66 :WIG)             ("VSHUFPD"              4 (V pd)  (H pd)  (W pd)  (I b))) ;; ib
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VSHUFPD"              4 (V pd)  (H pd)  (W pd)  (I b))) ;; ib
	  ((:VEX :0F :NDS :128 :WIG)                 ("VSHUFPS"              4 (V ps)  (H ps)  (W ps)  (I b))) ;; ib
	  ((:VEX :0F :NDS :256 :WIG)                 ("VSHUFPS"              4 (V ps)  (H ps)  (W ps)  (I b)))) ;; ib
    (#xD0 ((:VEX :0F :NDS :128 :66 :WIG)             ("VADDSUBPD"            3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VADDSUBPD"            3 (V pd)  (H pd)  (W pd)))
	  ((:VEX :0F :NDS :128 :F2 :WIG)             ("VADDSUBPS"            3 (V ps)  (H ps)  (W ps)))
	  ((:VEX :0F :NDS :256 :F2 :WIG)             ("VADDSUBPS"            3 (V ps)  (H ps)  (W ps))))
    (#xD1 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSRLW"               3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSRLW"               3 (V x)   (H x)  (W x))))
    (#xD2 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSRLD"               3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSRLD"               3 (V x)   (H x)  (W x))))
    (#xD3 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSRLQ"               3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSRLQ"               3 (V x)   (H x)  (W x))))
    (#xD4 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPADDQ"               3 (V x)   (H x)  (W x) ))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPADDQ"               3 (V x)   (H x)  (W x))))
    (#xD5 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPMULLW"              3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPMULLW"              3 (V x)   (H x)  (W x))))
    (#xD6 ((:VEX :0F :128 :66 :WIG)                  ("VMOVQ"                2 (V q)    (W q))))
    (#xD7 ((:VEX :0F :128 :66 :WIG)                  ("VPMOVMSKB"            2 (G d)   (U x)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VPMOVMSKB"            2 (G d)   (U x))))
    (#xD8 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSUBUSB"             3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSUBUSB"             3 (V x)   (H x)  (W x))))
    (#xD9 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSUBUSW"             3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSUBUSW"             3 (V x)   (H x)  (W x))))
    (#xDA ((:VEX :0F :NDS :128 :66)                  ("VPMINUB"              3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66)                  ("VPMINUB"              3 (V x)   (H x)  (W x))))
    (#xDB ((:VEX :0F :NDS :128 :66 :WIG)             ("VPAND"                3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPAND"                3 (V x)   (H x)  (W x))))
    (#xDC ((:VEX :0F :NDS :128 :66 :WIG)             ("VPADDUSB"             3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPADDUSB"             3 (V x)   (H x)  (W x))))
    (#xDD ((:VEX :0F :NDS :128 :66 :WIG)             ("VPADDUSW"             3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPADDUSW"             3 (V x)   (H x)  (W x))))
    (#xDE ((:VEX :0F :NDS :128 :66)                  ("VPMAXUB"              3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66)                  ("VPMAXUB"              3 (V x)   (H x)  (W x))))
    (#xDF ((:VEX :0F :NDS :128 :66 :WIG)             ("VPANDN"               3 (V x)   (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPANDN"               3 (V x)   (H x)  (W x))))
    (#xE0 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPAVGB"               3 (V x)   (H x)   (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPAVGB"               3 (V x)   (H x)   (W x))))
    (#xE1 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSRAW"               3 (V x)   (H x)   (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSRAW"               3 (V x)   (H x)   (W x))))
    (#xE2 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSRAD"               3 (V x)   (H x)   (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSRAD"               3 (V x)   (H x)   (W x))))
    (#xE3 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPAVGW"               3 (V x)   (H x)   (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPAVGW"               3 (V x)   (H x)   (W x))))
    (#xE4 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPMULHUW"             3 (V x)   (H x)   (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPMULHUW"             3 (V x)   (H x)   (W x))))
    (#xE5 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPMULHW"              3 (V x)   (H x)   (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPMULHW"              3 (V x)   (H x)   (W x))))
    (#xE6 ((:VEX :0F :128 :F3 :WIG)                  ("VCVTDQ2PD"            2 (V x)   (W pd)))
	  ((:VEX :0F :256 :F3 :WIG)                  ("VCVTDQ2PD"            2 (V x)   (W pd)))
	  ((:VEX :0F :128 :F2 :WIG)                  ("VCVTPD2DQ"            2 (V x)   (W pd)))
	  ((:VEX :0F :256 :F2 :WIG)                  ("VCVTPD2DQ"            2 (V x)   (W pd)))
	  ((:VEX :0F :128 :66 :WIG)                  ("VCVTTPD2DQ"           2 (V x)   (W pd)))
	  ((:VEX :0F :256 :66 :WIG)                  ("VCVTTPD2DQ"           2 (V x)   (W pd))))
    (#xE7 ((:VEX :0F :128 :66 :WIG (:mod . :mem))    ("VMOVNTDQ"             2 (M x)   (V x)))
	  ((:VEX :0F :256 :66 :WIG (:mod . :mem))    ("VMOVNTDQ"             2 (M x)   (V x))))
    (#xE8 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSUBSB"              3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSUBSB"              3 (V x)  (H x)  (W x))))
    (#xE9 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSUBSW"              3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSUBSW"              3 (V x)  (H x)  (W x))))
    (#xEA ((:VEX :0F :NDS :128 :66)                  ("VPMINSW"              3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66)                  ("VPMINSW"              3 (V x)  (H x)  (W x))))
    (#xEB ((:VEX :0F :NDS :128 :66 :WIG)             ("VPOR"                 3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPOR"                 3 (V x)  (H x)  (W x))))
    (#xEC ((:VEX :0F :NDS :128 :66 :WIG)             ("VPADDSB"              3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPADDSB"              3 (V x)  (H x)  (W x))))
    (#xED ((:VEX :0F :NDS :128 :66 :WIG)             ("VPADDSW"              3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPADDSW"              3 (V x)  (H x)  (W x))))
    (#xEE ((:VEX :0F :NDS :128 :66 :WIG)             ("VPMAXSW"              3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPMAXSW"              3 (V x)  (H x)  (W x))))
    (#xEF ((:VEX :0F :NDS :128 :66 :WIG)             ("VPXOR"                3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPXOR"                3 (V x)  (H x)  (W x))))
    (#xF0 ((:VEX :0F :128 :F2 :WIG (:mod . :mem))    ("VLDDQU"               2 (V x)  (M x)))
	  ((:VEX :0F :256 :F2 :WIG (:mod . :mem))    ("VLDDQU"               2 (V x)  (M x))))
    (#xF1 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSLLW"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSLLW"               3 (V x)  (H x)  (W x))))
    (#xF2 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSLLD"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSLLD"               3 (V x)  (H x)  (W x))))
    (#xF3 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSLLQ"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSLLQ"               3 (V x)  (H x)  (W x))))
    (#xF4 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPMULUDQ"             3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPMULUDQ"             3 (V x)  (H x)  (W x))))
    (#xF5 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPMADDWD"             3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPMADDWD"             3 (V x)  (H x)  (W x))))
    (#xF6 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSADBW"              3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSADBW"              3 (V x)  (H x)  (W x))))
    (#xF7 ((:VEX :0F :128 :66 :WIG)                  ("VMASKMOVDQU"          2 (V dq) (U dq))))
    (#xF8 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSUBB"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSUBB"               3 (V x)  (H x)  (W x))))
    (#xF9 ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSUBW"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSUBW"               3 (V x)  (H x)  (W x))))
    (#xFA ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSUBD"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSUBD"               3 (V x)  (H x)  (W x))))
    (#xFB ((:VEX :0F :NDS :256 :66 :WIG)             ("VPSUBQ"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :128 :66 :WIG)             ("VPSUBQ"               3 (V x)  (H x)  (W x))))
    (#xFC ((:VEX :0F :NDS :128 :66 :WIG)             ("VPADDB"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPADDB"               3 (V x)  (H x)  (W x))))
    (#xFD ((:VEX :0F :NDS :128 :66 :WIG)             ("VPADDW"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPADDW"               3 (V x)  (H x)  (W x))))
    (#xFE ((:VEX :0F :NDS :128 :66 :WIG)             ("VPADDD"               3 (V x)  (H x)  (W x)))
	  ((:VEX :0F :NDS :256 :66 :WIG)             ("VPADDD"               3 (V x)  (H x)  (W x))))))

(defconst *vex-0F38-opcodes*
  '((#x0 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPSHUFB"              3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPSHUFB"              3 (V x) (H x) (W x)))) ;;  ib
    (#x1 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPHADDW"              3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPHADDW"              3 (V x) (H x) (W x)))) ;;  ib
    (#x2 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPHADDD"              3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPHADDD"              3 (V x) (H x) (W x)))) ;;  ib
    (#x3 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPHADDSW"             3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPHADDSW"             3 (V x) (H x) (W x)))) ;;  ib
    (#x4 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPMADDUBSW"           3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPMADDUBSW"           3 (V x) (H x) (W x)))) ;;  ib
    (#x5 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPHSUBW"              3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPHSUBW"              3 (V x) (H x) (W x)))) ;;  ib
    (#x6 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPHSUBD"              3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPHSUBD"              3 (V x) (H x) (W x)))) ;;  ib
    (#x7 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPHSUBSW"             3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPHSUBSW"             3 (V x) (H x) (W x)))) ;;  ib
    (#x8 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPSIGNB"              3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPSIGNB"              3 (V x) (H x) (W x)))) ;;  ib
    (#x9 ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPSIGNW"              3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPSIGNW"              3 (V x) (H x) (W x)))) ;;  ib
    (#xA ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPSIGND"              3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPSIGND"              3 (V x) (H x) (W x)))) ;;  ib
    (#xB ((:VEX :0F38 :NDS :128 :66 :WIG)            ("VPMULHRSW"            3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :WIG)            ("VPMULHRSW"            3 (V x) (H x) (W x)))) ;;  ib
    (#xC ((:VEX :0F38 :NDS :128 :66 :W0)             ("VPERMILPS"            3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :W0)             ("VPERMILPS"            3 (V x) (H x) (W x)))) ;;  ib
    (#xD ((:VEX :0F38 :NDS :128 :66 :W0)             ("VPERMILPD"            3 (V x) (H x) (W x))) ;;  ib
	 ((:VEX :0F38 :NDS :256 :66 :W0)             ("VPERMILPD"            3 (V x) (H x) (W x)))) ;;  ib
    (#xE ((:VEX :0F38 :128 :66 :W0)                  ("VTESTPS"              2 (V x) (W x))) ;;  ib
	 ((:VEX :0F38 :256 :66 :W0)                  ("VTESTPS"              2 (V x) (W x)))) ;;  ib
    (#xF ((:VEX :0F38 :128 :66 :W0)                  ("VTESTPD"              2 (V x) (W x))) ;;  ib
	 ((:VEX :0F38 :256 :66 :W0)                  ("VTESTPD"              2 (V x) (W x)))) ;;  ib
    (#x13 ((:VEX :0F38 :128 :66 :W0)                 ("VCVTPH2PS"            3 (V x)  (W x)  (I b))) ;;  ib
	  ((:VEX :0F38 :256 :66 :W0)                 ("VCVTPH2PS"            3 (V x)  (W x)  (I b)))) ;;  ib
    (#x16 ((:VEX :0F38 :256 :66 :W0)                 ("VPERMPS"              3 (V qq) (H qq) (W qq)))) ;;  ib
    (#x17 ((:VEX :0F38 :128 :66 :WIG)                ("VPTEST"               2 (V x)  (W x))) ;;  ib
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPTEST"               2 (V x)  (W x))))
    (#x18 ((:VEX :0F38 :128 :66 :W0 (:mod . :mem))   ("VBROADCASTSS"         2 (V x)  (W d))) ;; AVX
	  ((:VEX :0F38 :256 :66 :W0 (:mod . :mem))   ("VBROADCASTSS"         2 (V x)  (W d))) ;; AVX
	  ((:VEX :0F38 :256 :66 :W0 (:mod . #b11))   ("VBROADCASTSS"         2 (V x)  (W d))) ;; AVX2
	  ((:VEX :0F38 :128 :66 :W0 (:mod . #b11))   ("VBROADCASTSS"         2 (V x)  (W d)))) ;; AVX2
    (#x19 ((:VEX :0F38 :256 :66 :W0 (:mod . :mem))   ("VBROADCASTSD"         2 (V qq) (W q))) ;; AVX
	  ((:VEX :0F38 :256 :66 :W0 (:mod . #b11))   ("VBROADCASTSD"         2 (V qq) (W q)))) ;; AVX2
    (#x1A ((:VEX :0F38 :256 :66 :W0 (:mod . :mem))   ("VBROADCASTF128"       2 (V qq) (M dq))))
    (#x1C ((:VEX :0F38 :128 :66 :WIG)                ("VPABSB"               2 (V x)  (W x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPABSB"               2 (V x)  (W x))))
    (#x1D ((:VEX :0F38 :128 :66 :WIG)                ("VPABSW"               2 (V x)  (W x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPABSW"               2 (V x)  (W x))))
    (#x1E ((:VEX :0F38 :128 :66 :WIG)                ("VPABSD"               2 (V x)  (W x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPABSD"               2 (V x)  (W x))))
    (#x20 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVSXBW"            2 (V x) (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVSXBW"            2 (V x) (U x))))
    (#x21 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVSXBD"            2 (V x) (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVSXBD"            2 (V x) (U x))))
    (#x22 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVSXBQ"            2 (V x) (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVSXBQ"            2 (V x) (U x))))
    (#x23 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVSXWD"            2 (V x) (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVSXWD"            2 (V x) (U x))))
    (#x24 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVSXWQ"            2 (V x) (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVSXWQ"            2 (V x) (U x))))
    (#x25 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVSXDQ"            2 (V x) (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVSXDQ"            2 (V x) (U x))))
    (#x28 ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPMULDQ"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPMULDQ"              3 (V x) (H x) (W x))))
    (#x29 ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPCMPEQQ"             3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPCMPEQQ"             3 (V x) (H x) (W x))))
    (#x2A ((:VEX :0F38 :128 :66 :WIG (:mod . :mem))  ("VMOVNTDQA"            2 (V x) (M x)))
	  ((:VEX :0F38 :256 :66 :WIG (:mod . :mem))  ("VMOVNTDQA"            2 (V x) (M x))))
    (#x2B ((:VEX :0F38 :NDS :128 :66)                ("VPACKUSDW"            3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66)                ("VPACKUSDW"            3 (V x) (H x) (W x))))
    (#x2C ((:VEX :0F38 :NDS :128 :66 :W0 (:mod . :mem)) ("VMASKMOVPS"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0 (:mod . :mem)) ("VMASKMOVPS"           3 (V x) (H x) (M x))))
    (#x2D ((:VEX :0F38 :NDS :128 :66 :W0 (:mod . :mem)) ("VMASKMOVPD"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0 (:mod . :mem)) ("VMASKMOVPD"           3 (V x) (H x) (M x))))
    (#x2E ((:VEX :0F38 :NDS :128 :66 :W0 (:mod . :mem)) ("VMASKMOVPS"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0 (:mod . :mem)) ("VMASKMOVPS"           3 (V x) (H x) (M x))))
    (#x2F ((:VEX :0F38 :NDS :128 :66 :W0 (:mod . :mem)) ("VMASKMOVPD"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0 (:mod . :mem)) ("VMASKMOVPD"           3 (V x) (H x) (M x))))
    (#x30 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVZXBW"            2 (V x)  (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVZXBW"            2 (V x)  (U x))))
    (#x31 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVZXBD"            2 (V x)  (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVZXBD"            2 (V x)  (U x))))
    (#x32 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVZXBQ"            2 (V x)  (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVZXBQ"            2 (V x)  (U x))))
    (#x33 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVZXWD"            2 (V x)  (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVZXWD"            2 (V x)  (U x))))
    (#x34 ((:VEX :0F38 :128 :66 :WIG)                ("VPMOVZXWQ"            2 (V x)  (U x)))
	  ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVZXWQ"            2 (V x)  (U x))))
    (#x35 ((:VEX :0F38 :256 :66 :WIG)                ("VPMOVZXDQ"            2 (V x)  (U x))))
    (#x36 ((:VEX :0F38 :NDS :256 :66 :W0)            ("VPERMD"               3 (V qq) (H qq) (W qq))))
    (#x37 ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPCMPGTQ"             3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPCMPGTQ"             3 (V x) (H x) (W x))))
    (#x38 ((:VEX :0F38 :NDS :128 :66)                ("VPMINSB"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66)                ("VPMINSB"              3 (V x) (H x) (W x))))
    (#x39 ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPMINSD"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPMINSD"              3 (V x) (H x) (W x))))
    (#x3A ((:VEX :0F38 :NDS :128 :66)                ("VPMINUW"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66)                ("VPMINUW"              3 (V x) (H x) (W x))))
    (#x3B ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPMINUD"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPMINUD"              3 (V x) (H x) (W x))))
    (#x3C ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPMAXSB"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPMAXSB"              3 (V x) (H x) (W x))))
    (#x3D ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPMAXSD"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPMAXSD"              3 (V x) (H x) (W x))))
    (#x3E ((:VEX :0F38 :NDS :128 :66)                ("VPMAXUW"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66)                ("VPMAXUW"              3 (V x) (H x) (W x))))
    (#x3F ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPMAXUD"              3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPMAXUD"              3 (V x) (H x) (W x))))
    (#x40 ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VPMULLD"              3 (V x)  (H x)    (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :WIG)           ("VPMULLD"              3 (V x)  (H x)    (W x))))
    (#x41 ((:VEX :0F38 :128 :66 :WIG)                ("VPHMINPOSUW"          2 (V dq) (W dq))))
    (#x45 ((:VEX :0F38 :NDS :128 :66 :W0)            ("VPSRLVD"              3  (V x) (H x)    (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VPSRLVD"              3  (V x) (H x)    (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W1)            ("VPSRLVQ"              3  (V x) (H x)    (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VPSRLVQ"              3  (V x) (H x)    (W x))))
    (#x46 ((:VEX :0F38 :NDS :128 :66 :W0)            ("VPSRAVD"              3  (V x) (H x)    (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VPSRAVD"              3  (V x) (H x)    (W x))))
    (#x47 ((:VEX :0F38 :NDS :128 :66 :W0)            ("VPSLLVD"              3  (V x) (H x)    (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VPSLLVD"              3  (V x) (H x)    (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W1)            ("VPSLLVQ"              3  (V x) (H x)    (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VPSLLVQ"              3  (V x) (H x)    (W x))))
    (#x58 ((:VEX :0F38 :128 :66 :W0)                 ("VPBROADCASTD"         2  (V x)  (W x)))
	  ((:VEX :0F38 :256 :66 :W0)                 ("VPBROADCASTD"         2  (V x)  (W x))))
    (#x59 ((:VEX :0F38 :128 :66 :W0)                 ("VPBROADCASTQ"         2  (V x)  (W x)))
	  ((:VEX :0F38 :256 :66 :W0)                 ("VPBROADCASTQ"         2  (V x)  (W x))))
    (#x5A ((:VEX :0F38 :256 :66 :W0 (:mod . :mem))   ("VBROADCASTI128"       2  (V qq) (M dq))))
    (#x78 ((:VEX :0F38 :128 :66 :W0)                 ("VPBROADCASTB"         2 (V x) (W x)))
	  ((:VEX :0F38 :256 :66 :W0)                 ("VPBROADCASTB"         2 (V x) (W x))))
    (#x79 ((:VEX :0F38 :128 :66 :W0)                 ("VPBROADCASTW"         2 (V x) (W x)))
	  ((:VEX :0F38 :256 :66 :W0)                 ("VPBROADCASTW"         2 (V x) (W x))))
    (#x8C ((:VEX :0F38 :NDS :128 :66 :W0 (:mod . :mem)) ("VPMASKMOVD"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0 (:mod . :mem)) ("VPMASKMOVD"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :128 :66 :W1 (:mod . :mem)) ("VPMASKMOVQ"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1 (:mod . :mem)) ("VPMASKMOVQ"           3 (V x) (H x) (M x))))
    (#x8E ((:VEX :0F38 :NDS :128 :66 :W0 (:mod . :mem)) ("VPMASKMOVD"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0 (:mod . :mem)) ("VPMASKMOVD"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :128 :66 :W1 (:mod . :mem)) ("VPMASKMOVQ"           3 (V x) (H x) (M x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1 (:mod . :mem)) ("VPMASKMOVQ"           3 (V x) (H x) (M x))))
    (#x90 ((:VEX :0F38 :DDS :128 :66 :W0)            ("VPGATHERDD"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VPGATHERDD"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W1)            ("VPGATHERDQ"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VPGATHERDQ"           3 (V x) (H x) (W x))))
    (#x91 ((:VEX :0F38 :DDS :128 :66 :W0)            ("VPGATHERQD"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VPGATHERQD"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W1)            ("VPGATHERQQ"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VPGATHERQQ"           3 (V x) (H x) (W x))))
    (#x92 ((:VEX :0F38 :DDS :128 :66 :W1)            ("VGATHERDPD"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VGATHERDPD"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W0)            ("VGATHERDPS"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VGATHERDPS"           3 (V x) (H x) (W x))))
    (#x93 ((:VEX :0F38 :DDS :128 :66 :W1)            ("VGATHERQPD"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VGATHERQPD"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W0)            ("VGATHERQPS"           3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VGATHERQPS"           3 (V x) (H x) (W x))))
    (#x96 ((:VEX :0F38 :DDS :128 :66 :W1)            ("VFMADDSUB132PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VFMADDSUB132PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W0)            ("VFMADDSUB132PS"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VFMADDSUB132PS"       3 (V x) (H x) (W x))))
    (#x97 ((:VEX :0F38 :DDS :128 :66 :W1)            ("VFMSUBADD132PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VFMSUBADD132PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W0)            ("VFMSUBADD132PS"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VFMSUBADD132PS"       3 (V x) (H x) (W x))))
    (#x98 ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFMADD132PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFMADD132PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFMADD132PS"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFMADD132PS"          3 (V x) (H x) (W x))))
    (#x99 ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFMADD132SD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFMADD132SS"          3 (V x) (H x) (W x))))
    (#x9A ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFMSUB132PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFMSUB132PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFMSUB132PS"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFMSUB132PS"          3 (V x) (H x) (W x))))
    (#x9B ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFMSUB132SD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFMSUB132SS"          3 (V x) (H x) (W x))))
    (#x9C ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFNMADD132PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFNMADD132PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFNMADD132PS"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFNMADD132PS"         3 (V x) (H x) (W x))))
    (#x9D ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFNMADD132SD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFNMADD132SS"         3 (V x) (H x) (W x))))
    (#x9E ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFNMSUB132PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFNMSUB132PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFNMSUB132PS"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFNMSUB132PS"         3 (V x) (H x) (W x))))
    (#x9F ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFNMSUB132SD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFNMSUB132SS"         3 (V x) (H x) (W x))))
    (#xA6 ((:VEX :0F38 :DDS :128 :66 :W1)            ("VFMADDSUB213PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VFMADDSUB213PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W0)            ("VFMADDSUB213PS"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VFMADDSUB213PS"       3 (V x) (H x) (W x))))
    (#xA7 ((:VEX :0F38 :DDS :128 :66 :W1)            ("VFMSUBADD213PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VFMSUBADD213PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W0)            ("VFMSUBADD213PS"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VFMSUBADD213PS"       3 (V x) (H x) (W x))))
    (#xA8 ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFMADD213PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFMADD213PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFMADD213PS"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFMADD213PS"          3 (V x) (H x) (W x))))
    (#xA9 ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFMADD213SD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFMADD213SS"          3 (V x) (H x) (W x))))
    (#xAA ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFMSUB213PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFMSUB213PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFMSUB213PS"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFMSUB213PS"          3 (V x) (H x) (W x))))
    (#xAB ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFMSUB213SD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFMSUB213SS"          3 (V x) (H x) (W x))))
    (#xAC ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFNMADD213PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFNMADD213PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFNMADD213PS"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFNMADD213PS"         3 (V x) (H x) (W x))))
    (#xAD ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFNMADD213SD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFNMADD213SS"         3 (V x) (H x) (W x))))
    (#xAE ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFNMSUB213PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFNMSUB213PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFNMSUB213PS"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFNMSUB213PS"         3 (V x) (H x) (W x))))
    (#xAF ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFNMSUB213SD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFNMSUB213SS"         3 (V x) (H x) (W x))))
    (#xB6 ((:VEX :0F38 :DDS :128 :66 :W1)            ("VFMADDSUB231PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VFMADDSUB231PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W0)            ("VFMADDSUB231PS"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VFMADDSUB231PS"       3 (V x) (H x) (W x))))
    (#xB7 ((:VEX :0F38 :DDS :128 :66 :W1)            ("VFMSUBADD231PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W1)            ("VFMSUBADD231PD"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :128 :66 :W0)            ("VFMSUBADD231PS"       3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :256 :66 :W0)            ("VFMSUBADD231PS"       3 (V x) (H x) (W x))))
    (#xB8 ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFMADD231PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFMADD231PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFMADD231PS"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFMADD231PS"          3 (V x) (H x) (W x))))
    (#xB9 ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFMADD231SD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFMADD231SS"          3 (V x) (H x) (W x))))
    (#xBA ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFMSUB231PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFMSUB231PD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFMSUB231PS"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFMSUB231PS"          3 (V x) (H x) (W x))))
    (#xBB ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFMSUB231SD"          3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFMSUB231SS"          3 (V x) (H x) (W x))))
    (#xBC ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFNMADD231PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFNMADD231PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFNMADD231PS"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFNMADD231PS"         3 (V x) (H x) (W x))))
    (#xBD ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFNMADD231SD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFNMADD231SS"         3 (V x) (H x) (W x))))
    (#xBE ((:VEX :0F38 :NDS :128 :66 :W1)            ("VFNMSUB231PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W1)            ("VFNMSUB231PD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :128 :66 :W0)            ("VFNMSUB231PS"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :NDS :256 :66 :W0)            ("VFNMSUB231PS"         3 (V x) (H x) (W x))))
    (#xBF ((:VEX :0F38 :DDS :LIG :66 :W1)            ("VFNMSUB231SD"         3 (V x) (H x) (W x)))
	  ((:VEX :0F38 :DDS :LIG :66 :W0)            ("VFNMSUB231SS"         3 (V x) (H x) (W x))))
    (#xDB ((:VEX :0F38 :128 :66 :WIG)                ("VAESIMC"              2 (V dq) (W dq))))
    (#xDC ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VAESENC"              3 (V dq) (H dq) (W dq))))
    (#xDD ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VAESENCLAST"          3 (V dq) (H dq) (W dq))))
    (#xDE ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VAESDEC"              3 (V dq) (H dq) (W dq))))
    (#xDF ((:VEX :0F38 :NDS :128 :66 :WIG)           ("VAESDECLAST"          3 (V dq) (H dq) (W dq))))
    (#xF2 ((:VEX :0F38 :NDS :LZ :W0)                 ("ANDN"                 3 (G y)  (B y)  (E y)))
	  ((:VEX :0F38 :NDS :LZ :W1)                 ("ANDN"                 3 (G y)  (B y)  (E y))))
    (#xF3 ((:VEX :0F38 :NDD :LZ :W0 (:reg . 1))      ("BLSR"                 2 (B y) (E y) :v))
	  ((:VEX :0F38 :NDD :LZ :W1 (:reg . 1))      ("BLSR"                 2 (B y) (E y) :v))
	  ((:VEX :0F38 :NDD :LZ :W0 (:reg . 2))      ("BLSMSK"               2 (B y) (E y) :v))
	  ((:VEX :0F38 :NDD :LZ :W1 (:reg . 2))      ("BLSMSK"               2 (B y) (E y) :v))
	  ((:VEX :0F38 :NDD :LZ :W0 (:reg . 3))      ("BLSI"                 2 (B y) (E y) :v))
	  ((:VEX :0F38 :NDD :LZ :W1 (:reg . 3))      ("BLSI"                 2 (B y) (E y) :v)))
    (#xF5 ((:VEX :0F38 :NDS :LZ :W0)                 ("BZHI"                 3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :W1)                 ("BZHI"                 3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :F2 :W0)             ("PDEP"                 3 (G y)  (B y)  (E y)))
	  ((:VEX :0F38 :NDS :LZ :F2 :W1)             ("PDEP"                 3 (G y)  (B y)  (E y)))
	  ((:VEX :0F38 :NDS :LZ :F3 :W0)             ("PEXT"                 3 (G y)  (B y)  (E y)))
	  ((:VEX :0F38 :NDS :LZ :F3 :W1)             ("PEXT"                 3 (G y)  (B y)  (E y))))
    (#xF6 ((:VEX :0F38 :NDD :LZ :F2 :W0)             ("MULX"                 3 (B y)  (G y)  (:rDX)  (E y)))
	  ((:VEX :0F38 :NDD :LZ :F2 :W1)             ("MULX"                 3 (B y)  (G y)  (:rDX)  (E y))))
    (#xF7 ((:VEX :0F38 :NDS :LZ :W0)                 ("BEXTR"                3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :W1)                 ("BEXTR"                3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :F3 :W0)             ("SARX"                 3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :F3 :W1)             ("SARX"                 3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :66 :W0)             ("SHLX"                 3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :66 :W1)             ("SHLX"                 3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :F2 :W0)             ("SHRX"                 3 (G y)  (E y)  (B y)))
	  ((:VEX :0F38 :NDS :LZ :F2 :W1)             ("SHRX"                 3 (G y)  (E y)  (B y))))))

(defconst *vex-0F3A-opcodes*
  '((#x0 ((:VEX :0F3A :256 :66 :W1)                  ("VPERMQ"               3 (V qq)  (W qq)  (I b))))
    (#x1 ((:VEX :0F3A :256 :66 :W1)                  ("VPERMPD"              3 (V qq)  (W qq)  (I b))))
    (#x2 ((:VEX :0F3A :NDS :128 :66 :W0)             ("VPBLENDD"             4 (V x)   (H x)   (W x)  (I b)))
	 ((:VEX :0F3A :NDS :256 :66 :W0)             ("VPBLENDD"             4 (V x)   (H x)   (W x)  (I b))))
    (#x4 ((:VEX :0F3A :128 :66 :W0)                  ("VPERMILPS"            3 (V x) (H x) (W x)))
	 ((:VEX :0F3A :256 :66 :W0)                  ("VPERMILPS"            3 (V x) (H x) (W x))))
    (#x5 ((:VEX :0F3A :128 :66 :W0)                  ("VPERMILPD"            3 (V x) (H x) (W x)))
	 ((:VEX :0F3A :256 :66 :W0)                  ("VPERMILPD"            3 (V x) (H x) (W x))))
    (#x6 ((:VEX :0F3A :NDS :256 :66 :W0)             ("VPERM2F128"           4 (V qq) (H qq) (W qq) (I b))))
    (#x8 ((:VEX :0F3A :128 :66 :WIG)                 ("VROUNDPS"             3 (V x)  (W x)  (I b)))
	 ((:VEX :0F3A :256 :66 :WIG)                 ("VROUNDPS"             3 (V x)  (W x)  (I b))))
    (#x9 ((:VEX :0F3A :128 :66 :WIG)                 ("VROUNDPD"             3 (V x)  (W x)  (I b)))
	 ((:VEX :0F3A :256 :66 :WIG)                 ("VROUNDPD"             3 (V x)  (W x)  (I b))))
    (#xA ((:VEX :0F3A :NDS :LIG :66 :WIG)            ("VROUNDSS"             3 (V ss) (W ss) (I b))))
    (#xB ((:VEX :0F3A :NDS :LIG :66 :WIG)            ("VROUNDSD"             3 (V sd) (W sd) (I b))))
    (#xC ((:VEX :0F3A :NDS :128 :66 :WIG)            ("VBLENDPS"             4 (V x)  (H x)  (W x) (I b)))
	 ((:VEX :0F3A :NDS :256 :66 :WIG)            ("VBLENDPS"             4 (V x)  (H x)  (W x) (I b))))
    (#xD ((:VEX :0F3A :NDS :128 :66 :WIG)            ("VBLENDPD"             4 (V x)  (H x)  (W x) (I b)))
	 ((:VEX :0F3A :NDS :256 :66 :WIG)            ("VBLENDPD"             4 (V x)  (H x)  (W x) (I b))))
    (#xE ((:VEX :0F3A :NDS :128 :66 :WIG)            ("VPBLENDW"             4 (V x)  (H x)  (W x) (I b)))
	 ((:VEX :0F3A :NDS :256 :66 :WIG)            ("VPBLENDW"             4 (V x)  (H x)  (W x) (I b))))
    (#xF ((:VEX :0F3A :NDS :128 :66 :WIG)            ("VPALIGNR"             4 (V x)  (H x)  (W x) (I b)))
	 ((:VEX :0F3A :NDS :256 :66 :WIG)            ("VPALIGNR"             4 (V x)  (H x)  (W x) (I b))))
    (#x14 ((:VEX :0F3A :128 :66 :W0)                 ("VPEXTRB"              3 (R d)  (V dq)  (I b))))
    (#x15 ((:VEX :0F3A :128 :66 :W0)                 ("VPEXTRW"              3 (G d)   (U dq) (I b))))
    (#x16 ((:VEX :0F3A :128 :66 :W0)                 ("VPEXTRD"              3 (E y)  (V dq)  (I b)))
	  ((:VEX :0F3A :128 :66 :W1)                 ("VPEXTRQ"              3 (E y)  (V dq)  (I b))))
    (#x17 ((:VEX :0F3A :128 :66 :WIG)                ("VEXTRACTPS"           3 (E d)  (V dq)  (I b))))
    (#x18 ((:VEX :0F3A :NDS :256 :66 :W0)            ("VINSERTF128"          4 (V qq) (H qq) (W qq) (I b))))
    (#x19 ((:VEX :0F3A :256 :66 :W0)                 ("VEXTRACTF128"         3 (W dq) (V qq) (I b))))
    (#x1D ((:VEX :0F3A :128 :66 :W0)                 ("VCVTPS2PH"            3 (W x)  (V x)  (I b)))
	  ((:VEX :0F3A :256 :66 :W0)                 ("VCVTPS2PH"            3 (W x)  (V x)  (I b))))
    (#x20 ((:VEX :0F3A :NDS :128 :66 :W0)            ("VPINSRB"              4 (V dq) (H dq) (R y)  (I b))))
    (#x21 ((:VEX :0F3A :NDS :128 :66 :WIG)           (:ALT
						    (("VINSERTPS"          4   (V dq) (H dq) (U dq) (I b))
						     ("VINSERTPS"          4   (V dq) (H dq) (M d) (I b))))))
    (#x22 ((:VEX :0F3A :NDS :128 :66 :W0)            ("VPINSRD"              4 (V dq) (H dq) (E y)  (I b)))
	  ((:VEX :0F3A :NDS :128 :66 :W1)            ("VPINSRQ"              4 (V dq) (H dq) (E y)  (I b))))
    (#x30 ((:VEX :0F3A :L0 :66 :W0 (:mod . #b11))    ("KSHIFTRB"             3 (K-reg b) (K-r/m b) (I b)))
	  ((:VEX :0F3A :L0 :66 :W1 (:mod . #b11))    ("KSHIFTRW"             3 (K-reg w) (K-r/m w) (I b))))
    (#x31 ((:VEX :0F3A :L0 :66 :W0 (:mod . #b11))    ("KSHIFTRD"             3 (K-reg d) (K-r/m d) (I b)))
	  ((:VEX :0F3A :L0 :66 :W1 (:mod . #b11))    ("KSHIFTRQ"             3 (K-reg q) (K-r/m q) (I b))))
    (#x32 ((:VEX :0F3A :L0 :66 :W0 (:mod . #b11))    ("KSHIFTLB"             3 (K-reg b) (K-r/m b) (I b)))
	  ((:VEX :0F3A :L0 :66 :W1 (:mod . #b11))    ("KSHIFTLW"             3 (K-reg w) (K-r/m w) (I b))))
    (#x33 ((:VEX :0F3A :L0 :66 :W0 (:mod . #b11))    ("KSHIFTLD"             3 (K-reg d) (K-r/m d) (I b)))
	  ((:VEX :0F3A :L0 :66 :W1 (:mod . #b11))    ("KSHIFTLQ"             3 (K-reg q) (K-r/m q) (I b))))
    (#x38 ((:VEX :0F3A :NDS :256 :66 :W0)            ("VINSERTI128"          4 (V qq) (H qq) (W qq) (I b)))) ;;  ib
    (#x39 ((:VEX :0F3A :256 :66 :W0)                 ("VEXTRACTI128"         3 (W dq) (V qq) (I b)))) ;;  ib
    (#x40 ((:VEX :0F3A :NDS :128 :66 :WIG)           ("VDPPS"                4 (V x)  (H x)  (W x)  (I b))) ;;  ib
	  ((:VEX :0F3A :NDS :256 :66 :WIG)           ("VDPPS"                4 (V x)  (H x)  (W x)  (I b)))) ;;  ib
    (#x41 ((:VEX :0F3A :NDS :128 :66 :WIG)           ("VDPPD"                4 (V dq) (H dq) (W dq) (I b)))) ;;  ib
    (#x42 ((:VEX :0F3A :NDS :128 :66 :WIG)           ("VMPSADBW"             4 (V x)  (H x)  (W x)  (I b))) ;;  ib
	  ((:VEX :0F3A :NDS :256 :66 :WIG)           ("VMPSADBW"             4 (V x)  (H x)  (W x)  (I b)))) ;;  ib
    (#x44 ((:VEX :0F3A :NDS :128 :66 :WIG)           ("VPCLMULQDQ"           4 (V dq) (H dq) (W dq) (I b)))) ;;  ib
    (#x46 ((:VEX :0F3A :NDS :256 :66 :W0)            ("VPERM2I128"           4 (V qq) (H qq) (W qq) (I b)))) ;;  ib
    (#x4A ((:VEX :0F3A :NDS :128 :66 :W0)            ("VBLENDVPS"            4 (V x)  (H x)  (W x)  (L x))) ;;  /is4
	  ((:VEX :0F3A :NDS :256 :66 :W0)            ("VBLENDVPS"            4 (V x)  (H x)  (W x)  (L x)))) ;;  /is4
    (#x4B ((:VEX :0F3A :NDS :128 :66 :W0)            ("VBLENDVPD"            4 (V x)  (H x)  (W x)  (L x))) ;;  /is4
	  ((:VEX :0F3A :NDS :256 :66 :W0)            ("VBLENDVPD"            4 (V x)  (H x)  (W x)  (L x)))) ;;  /is4
    (#x4C ((:VEX :0F3A :NDS :128 :66 :W0)            ("VPBLENDVB"            4 (V x)  (H x)  (W x)  (L x))) ;;  /is4
	  ((:VEX :0F3A :NDS :256 :66 :W0)            ("VPBLENDVB"            4 (V x)  (H x)  (W x)  (L x)))) ;;  /is4
    (#x60 ((:VEX :0F3A :128 :66)                     ("VPCMPESTRM"           3 (V dq)  (W dq)  (I b)))) ;;  ib
    (#x61 ((:VEX :0F3A :128 :66)                     ("VPCMPESTRI"           3 (V dq)  (W dq)  (I b)))) ;;  ib
    (#x62 ((:VEX :0F3A :128 :66 :WIG)                ("VPCMPISTRM"           3 (V dq)  (W dq)  (I b)))) ;;  ib
    (#x63 ((:VEX :0F3A :128 :66 :WIG)                ("VPCMPISTRI"           3 (V dq)  (W dq)  (I b)))) ;;  ib
    (#xDF ((:VEX :0F3A :128 :66 :WIG)                ("AESKEYGENASSIST"      3 (V dq)  (W dq)  (I b)))) ;;  ib
    (#xF0 ((:VEX :0F3A :LZ :F2 :W0)                  ("RORX"                 3 (G y)  (E y)  (I b))) ;;  ib
	  ((:VEX :0F3A :LZ :F2 :W1)                  ("RORX"                 3 (G y)  (E y)  (I b))))))

;; ----------------------------------------------------------------------

;; EVEX-encoded instructions:

(defconst *evex-0F-opcodes*
  '((#x10 ((:EVEX :0F :LIG :F2 :W1)                 "VMOVSD")       ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VMOVSD")       ;;
	  ((:EVEX :0F :LIG :F3 :W0)                 "VMOVSS")       ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VMOVSS")       ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VMOVUPD")      ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VMOVUPD")      ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VMOVUPD")      ;;
	  ((:EVEX :0F :128 :W0)                     "VMOVUPS")      ;;
	  ((:EVEX :0F :256 :W0)                     "VMOVUPS")      ;;
	  ((:EVEX :0F :512 :W0)                     "VMOVUPS"))     ;;
    (#x11 ((:EVEX :0F :LIG :F2 :W1)                 "VMOVSD")       ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VMOVSD")       ;;
	  ((:EVEX :0F :LIG :F3 :W0)                 "VMOVSS")       ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VMOVSS")       ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VMOVUPD")      ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VMOVUPD")      ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VMOVUPD")      ;;
	  ((:EVEX :0F :128 :W0)                     "VMOVUPS")      ;;
	  ((:EVEX :0F :256 :W0)                     "VMOVUPS")      ;;
	  ((:EVEX :0F :512 :W0)                     "VMOVUPS"))     ;;
    (#x12 ((:EVEX :0F :128 :F2 :W1)                 "VMOVDDUP")     ;;
	  ((:EVEX :0F :256 :F2 :W1)                 "VMOVDDUP")     ;;
	  ((:EVEX :0F :512 :F2 :W1)                 "VMOVDDUP")     ;;
	  ((:EVEX :0F :NDS :128 :W0 (:mod . #b11))  "VMOVHLPS")     ;;
	  ((:EVEX :0F :NDS :128 :66 :W1)            "VMOVLPD")      ;;
	  ((:EVEX :0F :NDS :128 :W0 (:mod . :mem))  "VMOVLPS")      ;;
	  ((:EVEX :0F :128 :F3 :W0)                 "VMOVSLDUP")    ;;
	  ((:EVEX :0F :256 :F3 :W0)                 "VMOVSLDUP")    ;;
	  ((:EVEX :0F :512 :F3 :W0)                 "VMOVSLDUP"))   ;;
    (#x13 ((:EVEX :0F :128 :66 :W1)                 "VMOVLPD")      ;;
	  ((:EVEX :0F :128 :W0)                     "VMOVLPS"))     ;;
    (#x14 ((:EVEX :0F :NDS :128 :66 :W1)            "VUNPCKLPD")    ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VUNPCKLPD")    ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VUNPCKLPD")    ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VUNPCKLPS")    ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VUNPCKLPS")    ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VUNPCKLPS"))   ;;
    (#x15 ((:EVEX :0F :NDS :128 :66 :W1)            "VUNPCKHPD")    ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VUNPCKHPD")    ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VUNPCKHPD")    ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VUNPCKHPS")    ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VUNPCKHPS")    ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VUNPCKHPS"))   ;;
    (#x16 ((:EVEX :0F :NDS :128 :66 :W1)            "VMOVHPD")      ;;
	  ((:EVEX :0F :NDS :128 :W0 (:mod . :mem))  "VMOVHPS")      ;;
	  ((:EVEX :0F :NDS :128 :W0 (:mod . #b11))  "VMOVLHPS")     ;;
	  ((:EVEX :0F :128 :F3 :W0)                 "VMOVSHDUP")    ;;
	  ((:EVEX :0F :256 :F3 :W0)                 "VMOVSHDUP")    ;;
	  ((:EVEX :0F :512 :F3 :W0)                 "VMOVSHDUP"))   ;;
    (#x17 ((:EVEX :0F :128 :66 :W1)                 "VMOVHPD")      ;;
	  ((:EVEX :0F :128 :W0)                     "VMOVHPS"))     ;;
    (#x28 ((:EVEX :0F :128 :66 :W1)                 "VMOVAPD")      ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VMOVAPD")      ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VMOVAPD")      ;;
	  ((:EVEX :0F :128 :W0)                     "VMOVAPS")      ;;
	  ((:EVEX :0F :256 :W0)                     "VMOVAPS")      ;;
	  ((:EVEX :0F :512 :W0)                     "VMOVAPS"))     ;;
    (#x29 ((:EVEX :0F :128 :66 :W1)                 "VMOVAPD")      ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VMOVAPD")      ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VMOVAPD")      ;;
	  ((:EVEX :0F :128 :W0)                     "VMOVAPS")      ;;
	  ((:EVEX :0F :256 :W0)                     "VMOVAPS")      ;;
	  ((:EVEX :0F :512 :W0)                     "VMOVAPS"))     ;;
    (#x2A ((:EVEX :0F :NDS :LIG :F2 :W0)            "VCVTSI2SD")    ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VCVTSI2SD")    ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VCVTSI2SS")    ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W1)            "VCVTSI2SS"))   ;;
    (#x2B ((:EVEX :0F :128 :66 :W1)                 "VMOVNTPD")     ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VMOVNTPD")     ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VMOVNTPD")     ;;
	  ((:EVEX :0F :128 :W0)                     "VMOVNTPS")     ;;
	  ((:EVEX :0F :256 :W0)                     "VMOVNTPS")     ;;
	  ((:EVEX :0F :512 :W0)                     "VMOVNTPS"))    ;;
    (#x2C ((:EVEX :0F :LIG :F2 :W0)                 "VCVTTSD2SI")   ;;
	  ((:EVEX :0F :LIG :F2 :W1)                 "VCVTTSD2SI")   ;;
	  ((:EVEX :0F :LIG :F3 :W0)                 "VCVTTSS2SI")   ;;
	  ((:EVEX :0F :LIG :F3 :W1)                 "VCVTTSS2SI"))  ;;
    (#x2D ((:EVEX :0F :LIG :F2 :W0)                 "VCVTSD2SI")    ;;
	  ((:EVEX :0F :LIG :F2 :W1)                 "VCVTSD2SI")    ;;
	  ((:EVEX :0F :LIG :F3 :W0)                 "VCVTSS2SI")    ;;
	  ((:EVEX :0F :LIG :F3 :W1)                 "VCVTSS2SI"))   ;;
    (#x2E ((:EVEX :0F :LIG :66 :W1)                 "VUCOMISD")     ;;
	  ((:EVEX :0F :LIG :W0)                     "VUCOMISS"))    ;;
    (#x2F ((:EVEX :0F :LIG :66 :W1)                 "VCOMISD")      ;;
	  ((:EVEX :0F :LIG :W0)                     "VCOMISS"))     ;;
    (#x51 ((:EVEX :0F :128 :66 :W1)                 "VSQRTPD")      ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VSQRTPD")      ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VSQRTPD")      ;;
	  ((:EVEX :0F :128 :W0)                     "VSQRTPS")      ;;
	  ((:EVEX :0F :256 :W0)                     "VSQRTPS")      ;;
	  ((:EVEX :0F :512 :W0)                     "VSQRTPS")      ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VSQRTSD")      ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VSQRTSS"))     ;;
    (#x54 ((:EVEX :0F :NDS :128 :66 :W1)            "VANDPD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VANDPD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VANDPD")       ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VANDPS")       ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VANDPS")       ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VANDPS"))      ;;
    (#x55 ((:EVEX :0F :NDS :128 :66 :W1)            "VANDNPD")      ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VANDNPD")      ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VANDNPD")      ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VANDNPS")      ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VANDNPS")      ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VANDNPS"))     ;;
    (#x56 ((:EVEX :0F :NDS :128 :66 :W1)            "VORPD")        ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VORPD")        ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VORPD")        ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VORPS")        ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VORPS")        ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VORPS"))       ;;
    (#x57 ((:EVEX :0F :NDS :128 :66 :W1)            "VXORPD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VXORPD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VXORPD")       ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VXORPS")       ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VXORPS")       ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VXORPS"))      ;;
    (#x58 ((:EVEX :0F :NDS :128 :66 :W1)            "VADDPD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VADDPD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VADDPD")       ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VADDPS")       ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VADDPS")       ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VADDPS")       ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VADDSD")       ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VADDSS"))      ;;
    (#x59 ((:EVEX :0F :NDS :128 :66 :W1)            "VMULPD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VMULPD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VMULPD")       ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VMULPS")       ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VMULPS")       ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VMULPS")       ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VMULSD")       ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VMULSS"))      ;;
    (#x5A ((:EVEX :0F :128 :66 :W1)                 "VCVTPD2PS")    ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VCVTPD2PS")    ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VCVTPD2PS")    ;;
	  ((:EVEX :0F :128 :W0)                     "VCVTPS2PD")    ;;
	  ((:EVEX :0F :256 :W0)                     "VCVTPS2PD")    ;;
	  ((:EVEX :0F :512 :W0)                     "VCVTPS2PD")    ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VCVTSD2SS")    ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VCVTSS2SD"))   ;;
    (#x5B ((:EVEX :0F :128 :W0)                     "VCVTDQ2PS")    ;;
	  ((:EVEX :0F :256 :W0)                     "VCVTDQ2PS")    ;;
	  ((:EVEX :0F :512 :W0)                     "VCVTDQ2PS")    ;;
	  ((:EVEX :0F :128 :66 :W0)                 "VCVTPS2DQ")    ;;
	  ((:EVEX :0F :256 :66 :W0)                 "VCVTPS2DQ")    ;;
	  ((:EVEX :0F :512 :66 :W0)                 "VCVTPS2DQ")    ;;
	  ((:EVEX :0F :128 :W1)                     "VCVTQQ2PS")    ;;
	  ((:EVEX :0F :256 :W1)                     "VCVTQQ2PS")    ;;
	  ((:EVEX :0F :512 :W1)                     "VCVTQQ2PS")    ;;
	  ((:EVEX :0F :128 :F3 :W0)                 "VCVTTPS2DQ")   ;;
	  ((:EVEX :0F :256 :F3 :W0)                 "VCVTTPS2DQ")   ;;
	  ((:EVEX :0F :512 :F3 :W0)                 "VCVTTPS2DQ"))  ;;
    (#x5C ((:EVEX :0F :NDS :128 :66 :W1)            "VSUBPD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VSUBPD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VSUBPD")       ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VSUBPS")       ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VSUBPS")       ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VSUBPS")       ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VSUBSD")       ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VSUBSS"))      ;;
    (#x5D ((:EVEX :0F :NDS :128 :66 :W1)            "VMINPD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VMINPD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VMINPD")       ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VMINPS")       ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VMINPS")       ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VMINPS")       ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VMINSD")       ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VMINSS"))      ;;
    (#x5E ((:EVEX :0F :NDS :128 :66 :W1)            "VDIVPD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VDIVPD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VDIVPD")       ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VDIVPS")       ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VDIVPS")       ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VDIVPS")       ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VDIVSD")       ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VDIVSS"))      ;;
    (#x5F ((:EVEX :0F :NDS :128 :66 :W1)            "VMAXPD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VMAXPD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VMAXPD")       ;;
	  ((:EVEX :0F :NDS :128 :W0)                "VMAXPS")       ;;
	  ((:EVEX :0F :NDS :256 :W0)                "VMAXPS")       ;;
	  ((:EVEX :0F :NDS :512 :W0)                "VMAXPS")       ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VMAXSD")       ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VMAXSS"))      ;;
    (#x60 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPUNPCKLBW")   ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPUNPCKLBW")   ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPUNPCKLBW"))  ;;
    (#x61 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPUNPCKLWD")   ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPUNPCKLWD")   ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPUNPCKLWD"))  ;;
    (#x62 ((:EVEX :0F :NDS :128 :66 :W0)            "VPUNPCKLDQ")   ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPUNPCKLDQ")   ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPUNPCKLDQ"))  ;;
    (#x63 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPACKSSWB")    ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPACKSSWB")    ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPACKSSWB"))   ;;
    (#x64 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPCMPGTB")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPCMPGTB")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPCMPGTB"))    ;;
    (#x65 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPCMPGTW")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPCMPGTW")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPCMPGTW"))    ;;
    (#x66 ((:EVEX :0F :NDS :128 :66 :W0)            "VPCMPGTD")     ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPCMPGTD")     ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPCMPGTD"))    ;;
    (#x67 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPACKUSWB")    ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPACKUSWB")    ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPACKUSWB"))   ;;
    (#x68 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPUNPCKHBW")   ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPUNPCKHBW")   ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPUNPCKHBW"))  ;;
    (#x69 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPUNPCKHWD")   ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPUNPCKHWD")   ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPUNPCKHWD"))  ;;
    (#x6A ((:EVEX :0F :NDS :128 :66 :W0)            "VPUNPCKHDQ")   ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPUNPCKHDQ")   ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPUNPCKHDQ"))  ;;
    (#x6B ((:EVEX :0F :NDS :128 :66 :W0)            "VPACKSSDW")    ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPACKSSDW")    ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPACKSSDW"))   ;;
    (#x6C ((:EVEX :0F :NDS :128 :66 :W1)            "VPUNPCKLQDQ")  ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPUNPCKLQDQ")  ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPUNPCKLQDQ")) ;;
    (#x6D ((:EVEX :0F :NDS :128 :66 :W1)            "VPUNPCKHQDQ")  ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPUNPCKHQDQ")  ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPUNPCKHQDQ")) ;;
    (#x6E ((:EVEX :0F :128 :66 :W0)                 "VMOVD")        ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VMOVQ"))       ;;
    (#x6F ((:EVEX :0F :128 :66 :W0)                 "VMOVDQA32")    ;;
	  ((:EVEX :0F :256 :66 :W0)                 "VMOVDQA32")    ;;
	  ((:EVEX :0F :512 :66 :W0)                 "VMOVDQA32")    ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VMOVDQA64")    ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VMOVDQA64")    ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VMOVDQA64")    ;;
	  ((:EVEX :0F :128 :F2 :W1)                 "VMOVDQU16")    ;;
	  ((:EVEX :0F :256 :F2 :W1)                 "VMOVDQU16")    ;;
	  ((:EVEX :0F :512 :F2 :W1)                 "VMOVDQU16")    ;;
	  ((:EVEX :0F :128 :F3 :W0)                 "VMOVDQU32")    ;;
	  ((:EVEX :0F :256 :F3 :W0)                 "VMOVDQU32")    ;;
	  ((:EVEX :0F :512 :F3 :W0)                 "VMOVDQU32")    ;;
	  ((:EVEX :0F :128 :F3 :W1)                 "VMOVDQU64")    ;;
	  ((:EVEX :0F :256 :F3 :W1)                 "VMOVDQU64")    ;;
	  ((:EVEX :0F :512 :F3 :W1)                 "VMOVDQU64")    ;;
	  ((:EVEX :0F :128 :F2 :W0)                 "VMOVDQU8")     ;;
	  ((:EVEX :0F :256 :F2 :W0)                 "VMOVDQU8")     ;;
	  ((:EVEX :0F :512 :F2 :W0)                 "VMOVDQU8"))    ;;
    (#x70 ((:EVEX :0F :128 :66 :W0)                 "VPSHUFD")      ;;  ib
	  ((:EVEX :0F :256 :66 :W0)                 "VPSHUFD")      ;;  ib
	  ((:EVEX :0F :512 :66 :W0)                 "VPSHUFD")      ;;  ib
	  ((:EVEX :0F :128 :F3 :WIG)                "VPSHUFHW")     ;;  ib
	  ((:EVEX :0F :256 :F3 :WIG)                "VPSHUFHW")     ;;  ib
	  ((:EVEX :0F :512 :F3 :WIG)                "VPSHUFHW")     ;;  ib
	  ((:EVEX :0F :128 :F2 :WIG)                "VPSHUFLW")     ;;  ib
	  ((:EVEX :0F :256 :F2 :WIG)                "VPSHUFLW")     ;;  ib
	  ((:EVEX :0F :512 :F2 :WIG)                "VPSHUFLW"))    ;;  ib
    (#x71 ((:EVEX :0F :NDD :128 :66 :WIG (:REG . 2)) "VPSRLW")      ;; /2 ib
	  ((:EVEX :0F :NDD :256 :66 :WIG (:REG . 2)) "VPSRLW")      ;;  /2 ib
	  ((:EVEX :0F :NDD :512 :66 :WIG (:REG . 2)) "VPSRLW")      ;;  /2 ib
	  ((:EVEX :0F :NDD :128 :66 :WIG (:REG . 4)) "VPSRAW")      ;;  /4 ib
	  ((:EVEX :0F :NDD :256 :66 :WIG (:REG . 4)) "VPSRAW")      ;;  /4 ib
	  ((:EVEX :0F :NDD :512 :66 :WIG (:REG . 4)) "VPSRAW")      ;;  /4 ib
	  ((:EVEX :0F :NDD :128 :66 :WIG (:REG . 6)) "VPSLLW")      ;;  /6 ib
	  ((:EVEX :0F :NDD :256 :66 :WIG (:REG . 6)) "VPSLLW")      ;;  /6 ib
	  ((:EVEX :0F :NDD :512 :66 :WIG (:REG . 6)) "VPSLLW"))     ;;  /6 ib
    (#x72 ((:EVEX :0F :NDD :128 :66 :W0 (:REG . 0)) "VPRORD")       ;;  /0 ib
	  ((:EVEX :0F :NDD :128 :66 :W1 (:REG . 0)) "VPRORD")       ;;  /0 ib
	  ((:EVEX :0F :NDD :256 :66 :W0 (:REG . 0)) "VPRORD")       ;;  /0 ib
	  ((:EVEX :0F :NDD :256 :66 :W1 (:REG . 0)) "VPRORD")       ;;  /0 ib
	  ((:EVEX :0F :NDD :512 :66 :W0 (:REG . 0)) "VPRORD")       ;;  /0 ib
	  ((:EVEX :0F :NDD :512 :66 :W1 (:REG . 0)) "VPRORD")       ;;  /0 ib
	  ((:EVEX :0F :NDD :128 :66 :W0 (:REG . 1)) "VPROLD")       ;;  /1 ib
	  ((:EVEX :0F :NDD :128 :66 :W1 (:REG . 1)) "VPROLD")       ;;  /1 ib
	  ((:EVEX :0F :NDD :256 :66 :W0 (:REG . 1)) "VPROLD")       ;;  /1 ib
	  ((:EVEX :0F :NDD :256 :66 :W1 (:REG . 1)) "VPROLD")       ;;  /1 ib
	  ((:EVEX :0F :NDD :512 :66 :W0 (:REG . 1)) "VPROLD")       ;;  /1 ib
	  ((:EVEX :0F :NDD :512 :66 :W1 (:REG . 1)) "VPROLD")       ;;  /1 ib
	  ((:EVEX :0F :NDD :128 :66 :W0 (:REG . 2)) "VPSRLD")       ;;  /2 ib
	  ((:EVEX :0F :NDD :256 :66 :W0 (:REG . 2)) "VPSRLD")       ;;  /2 ib
	  ((:EVEX :0F :NDD :512 :66 :W0 (:REG . 2)) "VPSRLD")       ;;  /2 ib
	  ((:EVEX :0F :NDD :128 :66 :W0 (:REG . 4)) "VPSRAD")       ;;  /4 ib
	  ((:EVEX :0F :NDD :128 :66 :W1 (:REG . 4)) "VPSRAD")       ;;  /4 ib
	  ((:EVEX :0F :NDD :256 :66 :W0 (:REG . 4)) "VPSRAD")       ;;  /4 ib
	  ((:EVEX :0F :NDD :256 :66 :W1 (:REG . 4)) "VPSRAD")       ;;  /4 ib
	  ((:EVEX :0F :NDD :512 :66 :W0 (:REG . 4)) "VPSRAD")       ;;  /4 ib
	  ((:EVEX :0F :NDD :512 :66 :W1 (:REG . 4)) "VPSRAD")       ;;  /4 ib
	  ((:EVEX :0F :NDD :128 :66 :W0 (:REG . 6)) "VPSLLD")       ;;  /6 ib
	  ((:EVEX :0F :NDD :256 :66 :W0 (:REG . 6)) "VPSLLD")       ;;  /6 ib
	  ((:EVEX :0F :NDD :512 :66 :W0 (:REG . 6)) "VPSLLD"))      ;;  /6 ib
    (#x73 ((:EVEX :0F :NDD :128 :66 :W1 (:REG . 2)) "VPSRLQ")       ;;  /2 ib
	  ((:EVEX :0F :NDD :256 :66 :W1 (:REG . 2)) "VPSRLQ")       ;;  /2 ib
	  ((:EVEX :0F :NDD :512 :66 :W1 (:REG . 2)) "VPSRLQ")       ;;  /2 ib
	  ((:EVEX :0F :NDD :128 :66 :WIG (:REG . 3)) "VPSRLDQ")     ;;  /3 ib
	  ((:EVEX :0F :NDD :256 :66 :WIG (:REG . 3)) "VPSRLDQ")     ;;  /3 ib
	  ((:EVEX :0F :NDD :512 :66 :WIG (:REG . 3)) "VPSRLDQ")     ;;  /3 ib
	  ((:EVEX :0F :NDD :128 :66 :W1 (:REG . 6)) "VPSLLQ")       ;;  /6 ib
	  ((:EVEX :0F :NDD :256 :66 :W1 (:REG . 6)) "VPSLLQ")       ;;  /6 ib
	  ((:EVEX :0F :NDD :512 :66 :W1 (:REG . 6)) "VPSLLQ")       ;;  /6 ib
	  ((:EVEX :0F :NDD :128 :66 :WIG (:REG . 7)) "VPSLLDQ")     ;;  /7 ib
	  ((:EVEX :0F :NDD :256 :66 :WIG (:REG . 7)) "VPSLLDQ")     ;;  /7 ib
	  ((:EVEX :0F :NDD :512 :66 :WIG (:REG . 7)) "VPSLLDQ"))    ;;  /7 ib
    (#x74 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPCMPEQB")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPCMPEQB")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPCMPEQB"))    ;;
    (#x75 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPCMPEQW")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPCMPEQW")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPCMPEQW"))    ;;
    (#x76 ((:EVEX :0F :NDS :128 :66 :W0)            "VPCMPEQD")     ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPCMPEQD")     ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPCMPEQD"))    ;;
    (#x78 ((:EVEX :0F :256 :W1)                     "VCVTTPD2UDQ")  ;;  02
	  ((:EVEX :0F :128 :W1)                     "VCVTTPD2UDQ")  ;;
	  ((:EVEX :0F :512 :W1)                     "VCVTTPD2UDQ")  ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VCVTTPD2UQQ")  ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VCVTTPD2UQQ")  ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VCVTTPD2UQQ")  ;;
	  ((:EVEX :0F :128 :W0)                     "VCVTTPS2UDQ")  ;;
	  ((:EVEX :0F :256 :W0)                     "VCVTTPS2UDQ")  ;;
	  ((:EVEX :0F :512 :W0)                     "VCVTTPS2UDQ")  ;;
	  ((:EVEX :0F :128 :66 :W0)                 "VCVTTPS2UQQ")  ;;
	  ((:EVEX :0F :256 :66 :W0)                 "VCVTTPS2UQQ")  ;;
	  ((:EVEX :0F :512 :66 :W0)                 "VCVTTPS2UQQ")  ;;
	  ((:EVEX :0F :LIG :F2 :W0)                 "VCVTTSD2USI")  ;;
	  ((:EVEX :0F :LIG :F2 :W1)                 "VCVTTSD2USI")  ;;
	  ((:EVEX :0F :LIG :F3 :W0)                 "VCVTTSS2USI")  ;;
	  ((:EVEX :0F :LIG :F3 :W1)                 "VCVTTSS2USI")) ;;
    (#x79 ((:EVEX :0F :128 :W1)                     "VCVTPD2UDQ")   ;;
	  ((:EVEX :0F :256 :W1)                     "VCVTPD2UDQ")   ;;
	  ((:EVEX :0F :512 :W1)                     "VCVTPD2UDQ")   ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VCVTPD2UQQ")   ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VCVTPD2UQQ")   ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VCVTPD2UQQ")   ;;
	  ((:EVEX :0F :128 :W0)                     "VCVTPS2UDQ")   ;;
	  ((:EVEX :0F :256 :W0)                     "VCVTPS2UDQ")   ;;
	  ((:EVEX :0F :512 :W0)                     "VCVTPS2UDQ")   ;;
	  ((:EVEX :0F :128 :66 :W0)                 "VCVTPS2UQQ")   ;;
	  ((:EVEX :0F :256 :66 :W0)                 "VCVTPS2UQQ")   ;;
	  ((:EVEX :0F :512 :66 :W0)                 "VCVTPS2UQQ")   ;;
	  ((:EVEX :0F :LIG :F2 :W0)                 "VCVTSD2USI")   ;;
	  ((:EVEX :0F :LIG :F2 :W1)                 "VCVTSD2USI")   ;;
	  ((:EVEX :0F :LIG :F3 :W0)                 "VCVTSS2USI")   ;;
	  ((:EVEX :0F :LIG :F3 :W1)                 "VCVTSS2USI"))  ;;
    (#x7A ((:EVEX :0F :128 :66 :W1)                 "VCVTTPD2QQ")   ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VCVTTPD2QQ")   ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VCVTTPD2QQ")   ;;
	  ((:EVEX :0F :128 :66 :W0)                 "VCVTTPS2QQ")   ;;
	  ((:EVEX :0F :256 :66 :W0)                 "VCVTTPS2QQ")   ;;
	  ((:EVEX :0F :512 :66 :W0)                 "VCVTTPS2QQ")   ;;
	  ((:EVEX :0F :128 :F3 :W0)                 "VCVTUDQ2PD")   ;;
	  ((:EVEX :0F :256 :F3 :W0)                 "VCVTUDQ2PD")   ;;
	  ((:EVEX :0F :512 :F3 :W0)                 "VCVTUDQ2PD")   ;;
	  ((:EVEX :0F :128 :F2 :W0)                 "VCVTUDQ2PS")   ;;
	  ((:EVEX :0F :256 :F2 :W0)                 "VCVTUDQ2PS")   ;;
	  ((:EVEX :0F :512 :F2 :W0)                 "VCVTUDQ2PS")   ;;
	  ((:EVEX :0F :128 :F3 :W1)                 "VCVTUQQ2PD")   ;;
	  ((:EVEX :0F :256 :F3 :W1)                 "VCVTUQQ2PD")   ;;
	  ((:EVEX :0F :512 :F3 :W1)                 "VCVTUQQ2PD")   ;;
	  ((:EVEX :0F :128 :F2 :W1)                 "VCVTUQQ2PS")   ;;
	  ((:EVEX :0F :256 :F2 :W1)                 "VCVTUQQ2PS")   ;;
	  ((:EVEX :0F :512 :F2 :W1)                 "VCVTUQQ2PS"))  ;;
    (#x7B ((:EVEX :0F :128 :66 :W1)                 "VCVTPD2QQ")    ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VCVTPD2QQ")    ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VCVTPD2QQ")    ;;
	  ((:EVEX :0F :128 :66 :W0)                 "VCVTPS2QQ")    ;;
	  ((:EVEX :0F :256 :66 :W0)                 "VCVTPS2QQ")    ;;
	  ((:EVEX :0F :512 :66 :W0)                 "VCVTPS2QQ")    ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W0)            "VCVTUSI2SD")   ;;
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VCVTUSI2SD")   ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VCVTUSI2SS")   ;;
	  ((:EVEX :0F :NDS :LIG :F3 :W1)            "VCVTUSI2SS"))  ;;
    (#x7E ((:EVEX :0F :128 :66 :W0)                 "VMOVD")        ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VMOVQ")        ;;
	  ((:EVEX :0F :128 :F3 :W1)                 "VMOVQ"))       ;;
    (#x7F ((:EVEX :0F :128 :66 :W0)                 "VMOVDQA32")    ;;
	  ((:EVEX :0F :256 :66 :W0)                 "VMOVDQA32")    ;;
	  ((:EVEX :0F :512 :66 :W0)                 "VMOVDQA32")    ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VMOVDQA64")    ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VMOVDQA64")    ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VMOVDQA64")    ;;
	  ((:EVEX :0F :128 :F2 :W1)                 "VMOVDQU16")    ;;
	  ((:EVEX :0F :256 :F2 :W1)                 "VMOVDQU16")    ;;
	  ((:EVEX :0F :512 :F2 :W1)                 "VMOVDQU16")    ;;
	  ((:EVEX :0F :128 :F3 :W0)                 "VMOVDQU32")    ;;
	  ((:EVEX :0F :256 :F3 :W0)                 "VMOVDQU32")    ;;
	  ((:EVEX :0F :512 :F3 :W0)                 "VMOVDQU32")    ;;
	  ((:EVEX :0F :128 :F3 :W1)                 "VMOVDQU64")    ;;
	  ((:EVEX :0F :256 :F3 :W1)                 "VMOVDQU64")    ;;
	  ((:EVEX :0F :512 :F3 :W1)                 "VMOVDQU64")    ;;
	  ((:EVEX :0F :128 :F2 :W0)                 "VMOVDQU8")     ;;
	  ((:EVEX :0F :256 :F2 :W0)                 "VMOVDQU8")     ;;
	  ((:EVEX :0F :512 :F2 :W0)                 "VMOVDQU8"))    ;;
    (#xC2 ((:EVEX :0F :NDS :128 :66 :W1)            "VCMPPD")       ;;  ib
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VCMPPD")       ;;  ib
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VCMPPD")       ;;  ib
	  ((:EVEX :0F :NDS :128 :W0)                "VCMPPS")       ;;  ib
	  ((:EVEX :0F :NDS :256 :W0)                "VCMPPS")       ;;  ib
	  ((:EVEX :0F :NDS :512 :W0)                "VCMPPS")       ;;  ib
	  ((:EVEX :0F :NDS :LIG :F2 :W1)            "VCMPSD")       ;;  ib
	  ((:EVEX :0F :NDS :LIG :F3 :W0)            "VCMPSS"))      ;;  ib
    (#xC4 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPINSRW"))     ;;  ib
    (#xC5 ((:EVEX :0F :128 :66 :WIG)                "VPEXTRW"))     ;;  ib
    (#xC6 ((:EVEX :0F :NDS :128 :66 :W1)            "VSHUFPD")      ;;  ib
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VSHUFPD")      ;;  ib
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VSHUFPD")      ;;  ib
	  ((:EVEX :0F :NDS :128 :W0)                "VSHUFPS")      ;;  ib
	  ((:EVEX :0F :NDS :256 :W0)                "VSHUFPS")      ;;  ib
	  ((:EVEX :0F :NDS :512 :W0)                "VSHUFPS"))     ;;  ib
    (#xD1 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSRLW")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSRLW")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSRLW"))      ;;
    (#xD2 ((:EVEX :0F :NDS :128 :66 :W0)            "VPSRLD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPSRLD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPSRLD"))      ;;
    (#xD3 ((:EVEX :0F :NDS :128 :66 :W1)            "VPSRLQ")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPSRLQ")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPSRLQ"))      ;;
    (#xD4 ((:EVEX :0F :NDS :512 :66 :W1)            "VPADDQ")       ;;
	  ((:EVEX :0F :NDS :128 :66 :W1)            "VPADDQ")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPADDQ"))      ;;
    (#xD5 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPMULLW")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPMULLW")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPMULLW"))     ;;
    (#xD6 ((:EVEX :0F :128 :66 :W1)                 "VMOVQ"))       ;;
    (#xD8 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSUBUSB")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSUBUSB")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSUBUSB"))    ;;
    (#xD9 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSUBUSW")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSUBUSW")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSUBUSW"))    ;;
    (#xDA ((:EVEX :0F :NDS :128 :66)                "VPMINUB")      ;;
	  ((:EVEX :0F :NDS :256 :66)                "VPMINUB")      ;;
	  ((:EVEX :0F :NDS :512 :66)                "VPMINUB"))     ;;
    (#xDB ((:EVEX :0F :NDS :512 :66 :W0)            "VPANDD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPANDQ")       ;;
	  ((:EVEX :0F :NDS :128 :66 :W0)            "VPANDD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPANDD")       ;;
	  ((:EVEX :0F :NDS :128 :66 :W1)            "VPANDQ")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPANDQ"))      ;;
    (#xDC ((:EVEX :0F :NDS :128 :66 :WIG)           "VPADDUSB")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPADDUSB")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPADDUSB"))    ;;
    (#xDD ((:EVEX :0F :NDS :128 :66 :WIG)           "VPADDUSW")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPADDUSW")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPADDUSW"))    ;;
    (#xDE ((:EVEX :0F :NDS :128 :66 :WIG)           "VPMAXUB")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPMAXUB")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPMAXUB"))     ;;
    (#xDF ((:EVEX :0F :NDS :128 :66 :W0)            "VPANDND")      ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPANDND")      ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPANDND")      ;;
	  ((:EVEX :0F :NDS :128 :66 :W1)            "VPANDNQ")      ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPANDNQ")      ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPANDNQ"))     ;;
    (#xE0 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPAVGB")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPAVGB")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPAVGB"))      ;;
    (#xE1 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSRAW")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSRAW")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSRAW"))      ;;
    (#xE2 ((:EVEX :0F :NDS :128 :66 :W0)            "VPSRAD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPSRAD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPSRAD")       ;;
	  ((:EVEX :0F :NDS :128 :66 :W1)            "VPSRAQ")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPSRAQ")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPSRAQ"))      ;;
    (#xE3 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPAVGW")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPAVGW")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPAVGW"))      ;;
    (#xE4 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPMULHUW")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPMULHUW")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPMULHUW"))    ;;
    (#xE5 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPMULHW")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPMULHW")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPMULHW"))     ;;
    (#xE6 ((:EVEX :0F :128 :F3 :W0)                 "VCVTDQ2PD")    ;;
	  ((:EVEX :0F :256 :F3 :W0)                 "VCVTDQ2PD")    ;;
	  ((:EVEX :0F :512 :F3 :W0)                 "VCVTDQ2PD")    ;;
	  ((:EVEX :0F :128 :F2 :W1)                 "VCVTPD2DQ")    ;;
	  ((:EVEX :0F :256 :F2 :W1)                 "VCVTPD2DQ")    ;;
	  ((:EVEX :0F :512 :F2 :W1)                 "VCVTPD2DQ")    ;;
	  ((:EVEX :0F :128 :F3 :W1)                 "VCVTQQ2PD")    ;;
	  ((:EVEX :0F :256 :F3 :W1)                 "VCVTQQ2PD")    ;;
	  ((:EVEX :0F :512 :F3 :W1)                 "VCVTQQ2PD")    ;;
	  ((:EVEX :0F :128 :66 :W1)                 "VCVTTPD2DQ")   ;;
	  ((:EVEX :0F :256 :66 :W1)                 "VCVTTPD2DQ")   ;;
	  ((:EVEX :0F :512 :66 :W1)                 "VCVTTPD2DQ"))  ;;
    (#xE7 ((:EVEX :0F :128 :66 :W0)                 "VMOVNTDQ")     ;;
	  ((:EVEX :0F :256 :66 :W0)                 "VMOVNTDQ")     ;;
	  ((:EVEX :0F :512 :66 :W0)                 "VMOVNTDQ"))    ;;
    (#xE8 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSUBSB")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSUBSB")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSUBSB"))     ;;
    (#xE9 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSUBSW")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSUBSW")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSUBSW"))     ;;
    (#xEA ((:EVEX :0F :NDS :128 :66 :WIG)           "VPMINSW")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPMINSW")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPMINSW"))     ;;
    (#xEB ((:EVEX :0F :NDS :128 :66 :W0)            "VPORD")        ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPORD")        ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPORD")        ;;
	  ((:EVEX :0F :NDS :128 :66 :W1)            "VPORQ")        ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPORQ")        ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPORQ"))       ;;
    (#xEC ((:EVEX :0F :NDS :128 :66 :WIG)           "VPADDSB")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPADDSB")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPADDSB"))     ;;
    (#xED ((:EVEX :0F :NDS :128 :66 :WIG)           "VPADDSW")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPADDSW")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPADDSW"))     ;;
    (#xEE ((:EVEX :0F :NDS :128 :66 :WIG)           "VPMAXSW")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPMAXSW")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPMAXSW"))     ;;
    (#xEF ((:EVEX :0F :NDS :128 :66 :W0)            "VPXORD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPXORD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPXORD")       ;;
	  ((:EVEX :0F :NDS :128 :66 :W1)            "VPXORQ")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPXORQ")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPXORQ"))      ;;
    (#xF1 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSLLW")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSLLW")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSLLW"))      ;;
    (#xF2 ((:EVEX :0F :NDS :128 :66 :W0)            "VPSLLD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPSLLD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPSLLD"))      ;;
    (#xF3 ((:EVEX :0F :NDS :128 :66 :W1)            "VPSLLQ")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPSLLQ")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPSLLQ"))      ;;
    (#xF4 ((:EVEX :0F :NDS :128 :66 :W1)            "VPMULUDQ")     ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPMULUDQ")     ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPMULUDQ"))    ;;
    (#xF5 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPMADDWD")     ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPMADDWD")     ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPMADDWD"))    ;;
    (#xF6 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSADBW")      ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSADBW")      ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSADBW"))     ;;
    (#xF8 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSUBB")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSUBB")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSUBB"))      ;;
    (#xF9 ((:EVEX :0F :NDS :128 :66 :WIG)           "VPSUBW")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPSUBW")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPSUBW"))      ;;
    (#xFA ((:EVEX :0F :NDS :128 :66 :W0)            "VPSUBD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPSUBD")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W0)            "VPSUBD"))      ;;
    (#xFB ((:EVEX :0F :NDS :128 :66 :W1)            "VPSUBQ")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W1)            "VPSUBQ")       ;;
	  ((:EVEX :0F :NDS :512 :66 :W1)            "VPSUBQ"))      ;;
    (#xFC ((:EVEX :0F :NDS :128 :66 :WIG)           "VPADDB")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPADDB")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPADDB"))      ;;
    (#xFD ((:EVEX :0F :NDS :128 :66 :WIG)           "VPADDW")       ;;
	  ((:EVEX :0F :NDS :256 :66 :WIG)           "VPADDW")       ;;
	  ((:EVEX :0F :NDS :512 :66 :WIG)           "VPADDW"))      ;;
    (#xFE ((:EVEX :0F :NDS :512 :66 :W0)            "VPADDD")       ;;
	  ((:EVEX :0F :NDS :128 :66 :W0)            "VPADDD")       ;;
	  ((:EVEX :0F :NDS :256 :66 :W0)            "VPADDD"))))    ;;

(defconst *evex-0F38-opcodes*
  '((#x0 ((:EVEX :0F38 :NDS :128 :66 :WIG)          "VPSHUFB")
	 ((:EVEX :0F38 :NDS :256 :66 :WIG)          "VPSHUFB")
	 ((:EVEX :0F38 :NDS :512 :66 :WIG)          "VPSHUFB"))
    (#x4 ((:EVEX :0F38 :NDS :128 :66 :WIG)          "VPMADDUBSW")
	 ((:EVEX :0F38 :NDS :256 :66 :WIG)          "VPMADDUBSW")
	 ((:EVEX :0F38 :NDS :512 :66 :WIG)          "VPMADDUBSW"))
    (#xB ((:EVEX :0F38 :NDS :128 :66 :WIG)          "VPMULHRSW")
	 ((:EVEX :0F38 :NDS :256 :66 :WIG)          "VPMULHRSW")
	 ((:EVEX :0F38 :NDS :512 :66 :WIG)          "VPMULHRSW"))
    (#xC ((:EVEX :0F38 :NDS :128 :66 :W0)           "VPERMILPS")
	 ((:EVEX :0F38 :NDS :256 :66 :W0)           "VPERMILPS")
	 ((:EVEX :0F38 :NDS :512 :66 :W0)           "VPERMILPS"))
    (#xD ((:EVEX :0F38 :NDS :128 :66 :W1)           "VPERMILPD")
	 ((:EVEX :0F38 :NDS :256 :66 :W1)           "VPERMILPD")
	 ((:EVEX :0F38 :NDS :512 :66 :W1)           "VPERMILPD"))
    (#x10 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVUSWB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVUSWB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVUSWB")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPSRLVW")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPSRLVW")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPSRLVW"))
    (#x11 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVUSDB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVUSDB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVUSDB")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPSRAVW")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPSRAVW")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPSRAVW"))
    (#x12 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVUSQB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVUSQB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVUSQB")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPSLLVW")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPSLLVW")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPSLLVW"))
    (#x13 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVUSDW")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVUSDW")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVUSDW")
	  ((:EVEX :0F38 :128 :66 :W0)               "VCVTPH2PS")
	  ((:EVEX :0F38 :256 :66 :W0)               "VCVTPH2PS")
	  ((:EVEX :0F38 :512 :66 :W0)               "VCVTPH2PS"))
    (#x14 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVUSQW")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVUSQW")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVUSQW")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPRORVD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPRORVD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPRORVD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPRORVQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPRORVQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPRORVQ"))
    (#x15 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVUSQD")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVUSQD")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVUSQD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPROLVD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPROLVD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPROLVD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPROLVQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPROLVQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPROLVQ"))
    (#x16 ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPERMPD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPERMPD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPERMPS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPERMPS"))
    (#x18 ((:EVEX :0F38 :128 :66 :W0)               "VBROADCASTSS")
	  ((:EVEX :0F38 :256 :66 :W0)               "VBROADCASTSS")
	  ((:EVEX :0F38 :512 :66 :W0)               "VBROADCASTSS"))
    (#x19 ((:EVEX :0F38 :256 :66 :W0)               "VBROADCASTF32X2")
	  ((:EVEX :0F38 :512 :66 :W0)               "VBROADCASTF32X2")
	  ((:EVEX :0F38 :256 :66 :W1)               "VBROADCASTSD")
	  ((:EVEX :0F38 :512 :66 :W1)               "VBROADCASTSD"))
    (#x1A ((:EVEX :0F38 :256 :66 :W0)               "VBROADCASTF32X4")
	  ((:EVEX :0F38 :512 :66 :W0)               "VBROADCASTF32X4")
	  ((:EVEX :0F38 :256 :66 :W1)               "VBROADCASTF64X2")
	  ((:EVEX :0F38 :512 :66 :W1)               "VBROADCASTF64X2"))
    (#x1B ((:EVEX :0F38 :512 :66 :W0)               "VBROADCASTF32X8")
	  ((:EVEX :0F38 :512 :66 :W1)               "VBROADCASTF64X4"))
    (#x1C ((:EVEX :0F38 :128 :66 :WIG)              "VPABSB")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPABSB")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPABSB"))
    (#x1D ((:EVEX :0F38 :128 :66 :WIG)              "VPABSW")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPABSW")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPABSW"))
    (#x1E ((:EVEX :0F38 :128 :66 :W0)               "VPABSD")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPABSD")
	  ;; The :512 version below is incorrectly listed in the Intel manuals
	  ;; (May 2018 edition) in the instruction description page for
	  ;; PABSSB/PABSW/PABSD/PABSQ.  But we know it must exist because
	  ;; there's a variant which requires an AVX512F feature flag.
	  ((:EVEX :0F38 :512 :66 :W1)               "VPABSD"))
    (#x1F ((:EVEX :0F38 :128 :66 :W1)               "VPABSQ")
	  ((:EVEX :0F38 :256 :66 :W1)               "VPABSQ")
	  ((:EVEX :0F38 :512 :66 :W1)               "VPABSQ"))
    (#x20 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVSWB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVSWB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVSWB")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVSXBW")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVSXBW")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVSXBW"))
    (#x21 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVSDB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVSDB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVSDB")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVSXBD")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVSXBD")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVSXBD"))
    (#x22 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVSQB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVSQB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVSQB")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVSXBQ")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVSXBQ")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVSXBQ"))
    (#x23 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVSDW")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVSDW")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVSDW")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVSXWD")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVSXWD")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVSXWD"))
    (#x24 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVSQW")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVSQW")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVSQW")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVSXWQ")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVSXWQ")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVSXWQ"))
    (#x25 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVSQD")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVSQD")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVSQD")
	  ((:EVEX :0F38 :128 :66 :W0)               "VPMOVSXDQ")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPMOVSXDQ")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPMOVSXDQ"))
    (#x26 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPTESTMB")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPTESTMB")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPTESTMB")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPTESTMW")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPTESTMW")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPTESTMW")
	  ((:EVEX :0F38 :NDS :128 :F3 :W0)          "VPTESTNMB")
	  ((:EVEX :0F38 :NDS :256 :F3 :W0)          "VPTESTNMB")
	  ((:EVEX :0F38 :NDS :512 :F3 :W0)          "VPTESTNMB")
	  ((:EVEX :0F38 :NDS :128 :F3 :W1)          "VPTESTNMW")
	  ((:EVEX :0F38 :NDS :256 :F3 :W1)          "VPTESTNMW")
	  ((:EVEX :0F38 :NDS :512 :F3 :W1)          "VPTESTNMW"))
    (#x27 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPTESTMD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPTESTMD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPTESTMD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPTESTMQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPTESTMQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPTESTMQ")
	  ((:EVEX :0F38 :NDS :128 :F3 :W0)          "VPTESTNMD")
	  ((:EVEX :0F38 :NDS :256 :F3 :W0)          "VPTESTNMD")
	  ((:EVEX :0F38 :NDS :512 :F3 :W0)          "VPTESTNMD")
	  ((:EVEX :0F38 :NDS :128 :F3 :W1)          "VPTESTNMQ")
	  ((:EVEX :0F38 :NDS :256 :F3 :W1)          "VPTESTNMQ")
	  ((:EVEX :0F38 :NDS :512 :F3 :W1)          "VPTESTNMQ"))
    (#x28 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVM2B")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVM2B")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVM2B")
	  ((:EVEX :0F38 :128 :F3 :W1)               "VPMOVM2W")
	  ((:EVEX :0F38 :256 :F3 :W1)               "VPMOVM2W")
	  ((:EVEX :0F38 :512 :F3 :W1)               "VPMOVM2W")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPMULDQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPMULDQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPMULDQ"))
    (#x29 ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPCMPEQQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPCMPEQQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPCMPEQQ")
	  ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVB2M")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVB2M")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVB2M")
	  ((:EVEX :0F38 :128 :F3 :W1)               "VPMOVW2M")
	  ((:EVEX :0F38 :256 :F3 :W1)               "VPMOVW2M")
	  ((:EVEX :0F38 :512 :F3 :W1)               "VPMOVW2M"))
    (#x2A ((:EVEX :0F38 :128 :66 :W0)               "VMOVNTDQA")
	  ((:EVEX :0F38 :256 :66 :W0)               "VMOVNTDQA")
	  ((:EVEX :0F38 :512 :66 :W0)               "VMOVNTDQA")
	  ((:EVEX :0F38 :128 :F3 :W1)               "VPBROADCASTMB2Q")
	  ((:EVEX :0F38 :256 :F3 :W1)               "VPBROADCASTMB2Q")
	  ((:EVEX :0F38 :512 :F3 :W1)               "VPBROADCASTMB2Q"))
    (#x2B ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPACKUSDW")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPACKUSDW")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPACKUSDW"))
    (#x2C ((:EVEX :0F38 :NDS :128 :66 :W1)          "VSCALEFPD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VSCALEFPD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VSCALEFPD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VSCALEFPS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VSCALEFPS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VSCALEFPS"))
    (#x2D ((:EVEX :0F38 :NDS :LIG :66 :W1)          "VSCALEFSD")
	  ((:EVEX :0F38 :NDS :LIG :66 :W0)          "VSCALEFSS"))
    (#x30 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVWB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVWB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVWB")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVZXBW")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVZXBW")
	  ((:EVEX :0F38 :128 :66)                   "VPMOVZXBW"))
    (#x31 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVDB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVDB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVDB")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVZXBD")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVZXBD")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVZXBD"))
    (#x32 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVQB")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVQB")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVQB")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVZXBQ")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVZXBQ")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVZXBQ"))
    (#x33 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVDW")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVDW")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVDW")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVZXWD")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVZXWD")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVZXWD"))
    (#x34 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVQW")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVQW")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVQW")
	  ((:EVEX :0F38 :128 :66 :WIG)              "VPMOVZXWQ")
	  ((:EVEX :0F38 :256 :66 :WIG)              "VPMOVZXWQ")
	  ((:EVEX :0F38 :512 :66 :WIG)              "VPMOVZXWQ"))
    (#x35 ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVQD")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVQD")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVQD")
	  ((:EVEX :0F38 :128 :66 :W0)               "VPMOVZXDQ")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPMOVZXDQ")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPMOVZXDQ"))
    (#x36 ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPERMD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPERMD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPERMQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPERMQ"))
    (#x37 ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPCMPGTQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPCMPGTQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPCMPGTQ"))
    (#x38 ((:EVEX :0F38 :NDS :128 :66 :WIG)         "VPMINSB")
	  ((:EVEX :0F38 :NDS :256 :66 :WIG)         "VPMINSB")
	  ((:EVEX :0F38 :NDS :512 :66 :WIG)         "VPMINSB")
	  ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVM2D")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVM2D")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVM2D")
	  ((:EVEX :0F38 :128 :F3 :W1)               "VPMOVM2Q")
	  ((:EVEX :0F38 :256 :F3 :W1)               "VPMOVM2Q")
	  ((:EVEX :0F38 :512 :F3 :W1)               "VPMOVM2Q"))
    (#x39 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPMINSD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPMINSD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPMINSD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPMINSQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPMINSQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPMINSQ")
	  ((:EVEX :0F38 :128 :F3 :W0)               "VPMOVD2M")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPMOVD2M")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPMOVD2M")
	  ((:EVEX :0F38 :128 :F3 :W1)               "VPMOVQ2M")
	  ((:EVEX :0F38 :256 :F3 :W1)               "VPMOVQ2M")
	  ((:EVEX :0F38 :512 :F3 :W1)               "VPMOVQ2M"))
    (#x3A ((:EVEX :0F38 :128 :F3 :W0)               "VPBROADCASTMW2D")
	  ((:EVEX :0F38 :256 :F3 :W0)               "VPBROADCASTMW2D")
	  ((:EVEX :0F38 :512 :F3 :W0)               "VPBROADCASTMW2D")
	  ((:EVEX :0F38 :NDS :128 :66)              "VPMINUW")
	  ((:EVEX :0F38 :NDS :256 :66)              "VPMINUW")
	  ((:EVEX :0F38 :NDS :512 :66)              "VPMINUW"))
    (#x3B ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPMINUD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPMINUD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPMINUD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPMINUQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPMINUQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPMINUQ"))
    (#x3C ((:EVEX :0F38 :NDS :128 :66 :WIG)         "VPMAXSB")
	  ((:EVEX :0F38 :NDS :256 :66 :WIG)         "VPMAXSB")
	  ((:EVEX :0F38 :NDS :512 :66 :WIG)         "VPMAXSB"))
    (#x3D ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPMAXSD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPMAXSD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPMAXSD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPMAXSQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPMAXSQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPMAXSQ"))
    (#x3E ((:EVEX :0F38 :NDS :128 :66 :WIG)         "VPMAXUW")
	  ((:EVEX :0F38 :NDS :256 :66 :WIG)         "VPMAXUW")
	  ((:EVEX :0F38 :NDS :512 :66 :WIG)         "VPMAXUW"))
    (#x3F ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPMAXUD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPMAXUD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPMAXUD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPMAXUQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPMAXUQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPMAXUQ"))
    (#x40 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPMULLD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPMULLD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPMULLD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPMULLQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPMULLQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPMULLQ"))
    (#x42 ((:EVEX :0F38 :128 :66 :W1)               "VGETEXPPD")
	  ((:EVEX :0F38 :256 :66 :W1)               "VGETEXPPD")
	  ((:EVEX :0F38 :512 :66 :W1)               "VGETEXPPD")
	  ((:EVEX :0F38 :128 :66 :W0)               "VGETEXPPS")
	  ((:EVEX :0F38 :256 :66 :W0)               "VGETEXPPS")
	  ((:EVEX :0F38 :512 :66 :W0)               "VGETEXPPS"))
    (#x43 ((:EVEX :0F38 :NDS :LIG :66 :W1)          "VGETEXPSD")
	  ((:EVEX :0F38 :NDS :LIG :66 :W0)          "VGETEXPSS"))
    (#x44 ((:EVEX :0F38 :128 :66 :W0)               "VPLZCNTD")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPLZCNTD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPLZCNTD")
	  ((:EVEX :0F38 :128 :66 :W1)               "VPLZCNTQ")
	  ((:EVEX :0F38 :256 :66 :W1)               "VPLZCNTQ")
	  ((:EVEX :0F38 :512 :66 :W1)               "VPLZCNTQ"))
    (#x45 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPSRLVD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPSRLVD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPSRLVD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPSRLVQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPSRLVQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPSRLVQ"))
    (#x46 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPSRAVD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPSRAVD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPSRAVD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPSRAVQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPSRAVQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPSRAVQ"))
    (#x47 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPSLLVD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPSLLVD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPSLLVD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPSLLVQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPSLLVQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPSLLVQ"))
    (#x4C ((:EVEX :0F38 :128 :66 :W1)               "VRCP14PD")
	  ((:EVEX :0F38 :256 :66 :W1)               "VRCP14PD")
	  ((:EVEX :0F38 :512 :66 :W1)               "VRCP14PD")
	  ((:EVEX :0F38 :128 :66 :W0)               "VRCP14PS")
	  ((:EVEX :0F38 :256 :66 :W0)               "VRCP14PS")
	  ((:EVEX :0F38 :512 :66 :W0)               "VRCP14PS"))
    (#x4D ((:EVEX :0F38 :NDS :LIG :66 :W1)          "VRCP14SD")
	  ((:EVEX :0F38 :NDS :LIG :66 :W0)          "VRCP14SS"))
    (#x4E ((:EVEX :0F38 :128 :66 :W1)               "VRSQRT14PD")
	  ((:EVEX :0F38 :256 :66 :W1)               "VRSQRT14PD")
	  ((:EVEX :0F38 :512 :66 :W1)               "VRSQRT14PD")
	  ((:EVEX :0F38 :128 :66 :W0)               "VRSQRT14PS")
	  ((:EVEX :0F38 :256 :66 :W0)               "VRSQRT14PS")
	  ((:EVEX :0F38 :512 :66 :W0)               "VRSQRT14PS"))
    (#x4F ((:EVEX :0F38 :NDS :LIG :66 :W1)          "VRSQRT14SD")
	  ((:EVEX :0F38 :NDS :LIG :66 :W0)          "VRSQRT14SS"))
    (#x52 ((:EVEX :0F38 :DDS :512 :F2 :W0)          "VP4DPWSSD"))
    (#x53 ((:EVEX :0F38 :DDS :512 :F2 :W0)          "VP4DPWSSDS"))
    (#x58 ((:EVEX :0F38 :128 :66 :W0)               "VPBROADCASTD")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPBROADCASTD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPBROADCASTD"))
    (#x59 ((:EVEX :0F38 :128 :66 :W0)               "VBROADCASTI32x2")
	  ((:EVEX :0F38 :256 :66 :W0)               "VBROADCASTI32x2")
	  ((:EVEX :0F38 :512 :66 :W0)               "VBROADCASTI32x2")
	  ((:EVEX :0F38 :128 :66 :W1)               "VPBROADCASTQ")
	  ((:EVEX :0F38 :256 :66 :W1)               "VPBROADCASTQ")
	  ((:EVEX :0F38 :512 :66 :W1)               "VPBROADCASTQ"))
    (#x5A ((:EVEX :0F38 :256 :66 :W0)               "VBROADCASTI32X4")
	  ((:EVEX :0F38 :512 :66 :W0)               "VBROADCASTI32X4")
	  ((:EVEX :0F38 :256 :66 :W1)               "VBROADCASTI64X2")
	  ((:EVEX :0F38 :512 :66 :W1)               "VBROADCASTI64X2"))
    (#x5B ((:EVEX :0F38 :512 :66 :W0)               "VBROADCASTI32X8")
	  ((:EVEX :0F38 :512 :66 :W1)               "VBROADCASTI64X4"))
    (#x64 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPBLENDMD")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPBLENDMD")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPBLENDMD")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPBLENDMQ")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPBLENDMQ")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPBLENDMQ"))
    (#x65 ((:EVEX :0F38 :NDS :128 :66 :W1)          "VBLENDMPD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VBLENDMPD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VBLENDMPD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VBLENDMPS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VBLENDMPS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VBLENDMPS"))
    (#x66 ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPBLENDMB")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPBLENDMB")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPBLENDMB")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPBLENDMW")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPBLENDMW")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPBLENDMW"))
    (#x75 ((:EVEX :0F38 :DDS :128 :66 :W0)          "VPERMI2B")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VPERMI2B")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VPERMI2B")
	  ((:EVEX :0F38 :DDS :128 :66 :W1)          "VPERMI2W")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VPERMI2W")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VPERMI2W"))
    (#x76 ((:EVEX :0F38 :DDS :128 :66 :W0)          "VPERMI2D")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VPERMI2D")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VPERMI2D")
	  ((:EVEX :0F38 :DDS :128 :66 :W1)          "VPERMI2Q")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VPERMI2Q")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VPERMI2Q"))
    (#x77 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VPERMI2PD")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VPERMI2PD")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VPERMI2PD")
	  ((:EVEX :0F38 :DDS :128 :66 :W0)          "VPERMI2PS")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VPERMI2PS")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VPERMI2PS"))
    (#x78 ((:EVEX :0F38 :128 :66 :W0)               "VPBROADCASTB")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPBROADCASTB")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPBROADCASTB"))
    (#x79 ((:EVEX :0F38 :128 :66 :W0)               "VPBROADCASTW")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPBROADCASTW")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPBROADCASTW"))
    (#x7A ((:EVEX :0F38 :128 :66 :W0)               "VPBROADCASTB")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPBROADCASTB")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPBROADCASTB"))
    (#x7B ((:EVEX :0F38 :128 :66 :W0)               "VPBROADCASTW")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPBROADCASTW")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPBROADCASTW"))
    (#x7C ((:EVEX :0F38 :128 :66 :W0)               "VPBROADCASTD")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPBROADCASTD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPBROADCASTD")
	  ((:EVEX :0F38 :128 :66 :W1)               "VPBROADCASTQ")
	  ((:EVEX :0F38 :256 :66 :W1)               "VPBROADCASTQ")
	  ((:EVEX :0F38 :512 :66 :W1)               "VPBROADCASTQ"))
    (#x7D ((:EVEX :0F38 :DDS :128 :66 :W0)          "VPERMT2B")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPERMT2B")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPERMT2B")
	  ((:EVEX :0F38 :DDS :128 :66 :W1)          "VPERMT2W")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VPERMT2W")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VPERMT2W"))
    (#x7E ((:EVEX :0F38 :DDS :128 :66 :W0)          "VPERMT2D")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VPERMT2D")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VPERMT2D")
	  ((:EVEX :0F38 :DDS :128 :66 :W1)          "VPERMT2Q")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VPERMT2Q")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VPERMT2Q"))
    (#x7F ((:EVEX :0F38 :DDS :128 :66 :W1)          "VPERMT2PD")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VPERMT2PD")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VPERMT2PD")
	  ((:EVEX :0F38 :DDS :128 :66 :W0)          "VPERMT2PS")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VPERMT2PS")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VPERMT2PS"))
    (#x83 ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPMULTISHIFTQB")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPMULTISHIFTQB")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPMULTISHIFTQB"))
    (#x88 ((:EVEX :0F38 :128 :66 :W1)               "VEXPANDPD")
	  ((:EVEX :0F38 :256 :66 :W1)               "VEXPANDPD")
	  ((:EVEX :0F38 :512 :66 :W1)               "VEXPANDPD")
	  ((:EVEX :0F38 :128 :66 :W0)               "VEXPANDPS")
	  ((:EVEX :0F38 :256 :66 :W0)               "VEXPANDPS")
	  ((:EVEX :0F38 :512 :66 :W0)               "VEXPANDPS"))
    (#x89 ((:EVEX :0F38 :128 :66 :W0)               "VPEXPANDD")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPEXPANDD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPEXPANDD")
	  ((:EVEX :0F38 :128 :66 :W1)               "VPEXPANDQ")
	  ((:EVEX :0F38 :256 :66 :W1)               "VPEXPANDQ")
	  ((:EVEX :0F38 :512 :66 :W1)               "VPEXPANDQ"))
    (#x8A ((:EVEX :0F38 :128 :66 :W1)               "VCOMPRESSPD")
	  ((:EVEX :0F38 :256 :66 :W1)               "VCOMPRESSPD")
	  ((:EVEX :0F38 :512 :66 :W1)               "VCOMPRESSPD")
	  ((:EVEX :0F38 :128 :66 :W0)               "VCOMPRESSPS")
	  ((:EVEX :0F38 :256 :66 :W0)               "VCOMPRESSPS")
	  ((:EVEX :0F38 :512 :66 :W0)               "VCOMPRESSPS"))
    (#x8B ((:EVEX :0F38 :128 :66 :W0)               "VPCOMPRESSD")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPCOMPRESSD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPCOMPRESSD")
	  ((:EVEX :0F38 :128 :66 :W1)               "VPCOMPRESSQ")
	  ((:EVEX :0F38 :256 :66 :W1)               "VPCOMPRESSQ")
	  ((:EVEX :0F38 :512 :66 :W1)               "VPCOMPRESSQ"))
    (#x8D ((:EVEX :0F38 :NDS :128 :66 :W0)          "VPERMB")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VPERMB")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VPERMB")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VPERMW")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VPERMW")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VPERMW"))
    (#x90 ((:EVEX :0F38 :128 :66 :W0)               "VPGATHERDD")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W0)               "VPGATHERDD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0)               "VPGATHERDD")  ;; /vsib
	  ((:EVEX :0F38 :128 :66 :W1)               "VPGATHERDQ")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W1)               "VPGATHERDQ")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1)               "VPGATHERDQ")) ;; /vsib
    (#x91 ((:EVEX :0F38 :128 :66 :W0)               "VPGATHERQD")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W0)               "VPGATHERQD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0)               "VPGATHERQD")  ;; /vsib
	  ((:EVEX :0F38 :128 :66 :W1)               "VPGATHERQQ")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W1)               "VPGATHERQQ")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1)               "VPGATHERQQ")) ;; /vsib
    (#x92 ((:EVEX :0F38 :128 :66 :W1)               "VGATHERDPD")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W1)               "VGATHERDPD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1)               "VGATHERDPD")  ;; /vsib
	  ((:EVEX :0F38 :128 :66 :W0)               "VGATHERDPS")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W0)               "VGATHERDPS")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0)               "VGATHERDPS")) ;; /vsib
    (#x93 ((:EVEX :0F38 :128 :66 :W1)               "VGATHERQPD")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W1)               "VGATHERQPD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1)               "VGATHERQPD")  ;; /vsib
	  ((:EVEX :0F38 :128 :66 :W0)               "VGATHERQPS")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W0)               "VGATHERQPS")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0)               "VGATHERQPS")) ;; /vsib
    (#x96 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VFMADDSUB132PD")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VFMADDSUB132PD")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VFMADDSUB132PD")
	  ((:EVEX :0F38 :DDS :128 :66 :W0)          "VFMADDSUB132PS")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VFMADDSUB132PS")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VFMADDSUB132PS"))
    (#x97 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VFMSUBADD132PD")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VFMSUBADD132PD")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VFMSUBADD132PD")
	  ((:EVEX :0F38 :DDS :128 :66 :W0)          "VFMSUBADD132PS")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VFMSUBADD132PS")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VFMSUBADD132PS"))
    (#x98 ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFMADD132PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFMADD132PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFMADD132PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFMADD132PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFMADD132PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFMADD132PS"))
    (#x99 ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFMADD132SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFMADD132SS"))
    (#x9A ((:EVEX :0F38 :DDS :512 :F2 :W0)          "V4FMADDPS")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFMSUB132PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFMSUB132PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFMSUB132PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFMSUB132PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFMSUB132PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFMSUB132PS"))
    (#x9B ((:EVEX :0F38 :DDS :LIG :F2 :W0)          "V4FMADDSS")
	  ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFMSUB132SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFMSUB132SS"))
    (#x9C ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFNMADD132PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFNMADD132PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFNMADD132PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFNMADD132PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFNMADD132PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFNMADD132PS"))
    (#x9D ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFNMADD132SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFNMADD132SS"))
    (#x9E ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFNMSUB132PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFNMSUB132PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFNMSUB132PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFNMSUB132PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFNMSUB132PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFNMSUB132PS"))
    (#x9F ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFNMSUB132SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFNMSUB132SS"))
    (#xA0 ((:EVEX :0F38 :128 :66 :W0)               "VPSCATTERDD")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W0)               "VPSCATTERDD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0)               "VPSCATTERDD")  ;; /vsib
	  ((:EVEX :0F38 :128 :66 :W1)               "VPSCATTERDQ")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W1)               "VPSCATTERDQ")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1)               "VPSCATTERDQ")) ;; /vsib
    (#xA1 ((:EVEX :0F38 :128 :66 :W0)               "VPSCATTERQD")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W0)               "VPSCATTERQD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0)               "VPSCATTERQD")  ;; /vsib
	  ((:EVEX :0F38 :128 :66 :W1)               "VPSCATTERQQ")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W1)               "VPSCATTERQQ")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1)               "VPSCATTERQQ")) ;; /vsib
    (#xA2 ((:EVEX :0F38 :128 :66 :W1)               "VSCATTERDPD")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W1)               "VSCATTERDPD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1)               "VSCATTERDPD")  ;; /vsib
	  ((:EVEX :0F38 :128 :66 :W0)               "VSCATTERDPS")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W0)               "VSCATTERDPS")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0)               "VSCATTERDPS")) ;; /vsib
    (#xA3 ((:EVEX :0F38 :128 :66 :W1)               "VSCATTERQPD")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W1)               "VSCATTERQPD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1)               "VSCATTERQPD")  ;; /vsib
	  ((:EVEX :0F38 :128 :66 :W0)               "VSCATTERQPS")  ;; /vsib
	  ((:EVEX :0F38 :256 :66 :W0)               "VSCATTERQPS")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0)               "VSCATTERQPS")) ;; /vsib
    (#xA6 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VFMADDSUB213PD")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VFMADDSUB213PD")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VFMADDSUB213PD")
	  ((:EVEX :0F38 :DDS :128 :66 :W0)          "VFMADDSUB213PS")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VFMADDSUB213PS")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VFMADDSUB213PS"))
    (#xA7 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VFMSUBADD213PD")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VFMSUBADD213PD")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VFMSUBADD213PD")
	  ((:EVEX :0F38 :DDS :128 :66 :W0)          "VFMSUBADD213PS")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VFMSUBADD213PS")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VFMSUBADD213PS"))
    (#xA8 ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFMADD213PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFMADD213PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFMADD213PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFMADD213PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFMADD213PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFMADD213PS"))
    (#xA9 ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFMADD213SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFMADD213SS"))
    (#xAA ((:EVEX :0F38 :DDS :512 :F2 :W0)          "V4FNMADDPS")
	  ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFMSUB213PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFMSUB213PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFMSUB213PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFMSUB213PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFMSUB213PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFMSUB213PS"))
    (#xAB ((:EVEX :0F38 :DDS :LIG :F2 :W0)         "V4FNMADDSS")
	  ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFMSUB213SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFMSUB213SS"))
    (#xAC ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFNMADD213PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFNMADD213PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFNMADD213PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFNMADD213PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFNMADD213PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFNMADD213PS"))
    (#xAD ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFNMADD213SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFNMADD213SS"))
    (#xAE ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFNMSUB213PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFNMSUB213PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFNMSUB213PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFNMSUB213PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFNMSUB213PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFNMSUB213PS"))
    (#xAF ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFNMSUB213SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFNMSUB213SS"))
    (#xB4 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VPMADD52LUQ")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VPMADD52LUQ")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VPMADD52LUQ"))
    (#xB5 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VPMADD52HUQ")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VPMADD52HUQ")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VPMADD52HUQ"))
    (#xB6 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VFMADDSUB231PD")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VFMADDSUB231PD")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VFMADDSUB231PD")
	  ((:EVEX :0F38 :DDS :128 :66 :W0)          "VFMADDSUB231PS")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VFMADDSUB231PS")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VFMADDSUB231PS"))
    (#xB7 ((:EVEX :0F38 :DDS :128 :66 :W1)          "VFMSUBADD231PD")
	  ((:EVEX :0F38 :DDS :256 :66 :W1)          "VFMSUBADD231PD")
	  ((:EVEX :0F38 :DDS :512 :66 :W1)          "VFMSUBADD231PD")
	  ((:EVEX :0F38 :DDS :128 :66 :W0)          "VFMSUBADD231PS")
	  ((:EVEX :0F38 :DDS :256 :66 :W0)          "VFMSUBADD231PS")
	  ((:EVEX :0F38 :DDS :512 :66 :W0)          "VFMSUBADD231PS"))
    (#xB8 ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFMADD231PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFMADD231PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFMADD231PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFMADD231PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFMADD231PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFMADD231PS"))
    (#xB9 ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFMADD231SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFMADD231SS"))
    (#xBA ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFMSUB231PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFMSUB231PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFMSUB231PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFMSUB231PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFMSUB231PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFMSUB231PS"))
    (#xBB ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFMSUB231SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFMSUB231SS"))
    (#xBC ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFNMADD231PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFNMADD231PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFNMADD231PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFNMADD231PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFNMADD231PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFNMADD231PS"))
    (#xBD ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFNMADD231SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFNMADD231SS"))
    (#xBE ((:EVEX :0F38 :NDS :128 :66 :W1)          "VFNMSUB231PD")
	  ((:EVEX :0F38 :NDS :256 :66 :W1)          "VFNMSUB231PD")
	  ((:EVEX :0F38 :NDS :512 :66 :W1)          "VFNMSUB231PD")
	  ((:EVEX :0F38 :NDS :128 :66 :W0)          "VFNMSUB231PS")
	  ((:EVEX :0F38 :NDS :256 :66 :W0)          "VFNMSUB231PS")
	  ((:EVEX :0F38 :NDS :512 :66 :W0)          "VFNMSUB231PS"))
    (#xBF ((:EVEX :0F38 :DDS :LIG :66 :W1)          "VFNMSUB231SD")
	  ((:EVEX :0F38 :DDS :LIG :66 :W0)          "VFNMSUB231SS"))
    (#xC4 ((:EVEX :0F38 :128 :66 :W0)               "VPCONFLICTD")
	  ((:EVEX :0F38 :256 :66 :W0)               "VPCONFLICTD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VPCONFLICTD")
	  ((:EVEX :0F38 :128 :66 :W1)               "VPCONFLICTQ")
	  ((:EVEX :0F38 :256 :66 :W1)               "VPCONFLICTQ")
	  ((:EVEX :0F38 :512 :66 :W1)               "VPCONFLICTQ"))
    (#xC6 ((:EVEX :0F38 :512 :66 :W0 (:REG . 1))    "VGATHERPF0DPS")   ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1 (:REG . 1))    "VGATHERPF0DPD")   ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0 (:REG . 2))    "VGATHERPF1DPS")   ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1 (:REG . 2))    "VGATHERPF1DPD")   ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0 (:REG . 5))    "VSCATTERPF0DPS")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1 (:REG . 5))    "VSCATTERPF0DPD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0 (:REG . 6))    "VSCATTERPF1DPS")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1 (:REG . 6))    "VSCATTERPF1DPD")) ;; /vsib
    (#xC7 ((:EVEX :0F38 :512 :66 :W0 (:REG . 1))    "VGATHERPF0QPS")   ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1 (:REG . 1))    "VGATHERPF0QPD")   ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0 (:REG . 2))    "VGATHERPF1QPS")   ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1 (:REG . 2))    "VGATHERPF1QPD")   ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0 (:REG . 5))    "VSCATTERPF0QPS")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1 (:REG . 5))    "VSCATTERPF0QPD")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W0 (:REG . 6))    "VSCATTERPF1QPS")  ;; /vsib
	  ((:EVEX :0F38 :512 :66 :W1 (:REG . 6))    "VSCATTERPF1QPD")) ;; /vsib
    (#xC8 ((:EVEX :0F38 :512 :66 :W1)               "VEXP2PD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VEXP2PS"))
    (#xCA ((:EVEX :0F38 :512 :66 :W1)               "VRCP28PD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VRCP28PS"))
    (#xCB ((:EVEX :0F38 :NDS :LIG :66 :W1)          "VRCP28SD")
	  ((:EVEX :0F38 :NDS :LIG :66 :W0)          "VRCP28SS"))
    (#xCC ((:EVEX :0F38 :512 :66 :W1)               "VRSQRT28PD")
	  ((:EVEX :0F38 :512 :66 :W0)               "VRSQRT28PS"))
    (#xCD ((:EVEX :0F38 :NDS :LIG :66 :W1)          "VRSQRT28SD")
	  ((:EVEX :0F38 :NDS :LIG :66 :W0)          "VRSQRT28SS"))))

(defconst *evex-0F3A-opcodes*
  '((#x0 ((:EVEX :0F3A :256 :66 :W1)                "VPERMQ")         ;; ib
	 ((:EVEX :0F3A :512 :66 :W1)                "VPERMQ"))        ;; ib
    (#x1 ((:EVEX :0F3A :256 :66 :W1)                "VPERMPD")        ;; ib
	 ((:EVEX :0F3A :512 :66 :W1)                "VPERMPD"))       ;; ib
    (#x3 ((:EVEX :0F3A :NDS :128 :66 :W0)           "VALIGND")        ;; ib
	 ((:EVEX :0F3A :NDS :128 :66 :W1)           "VALIGNQ")        ;; ib
	 ((:EVEX :0F3A :NDS :256 :66 :W0)           "VALIGND")        ;; ib
	 ((:EVEX :0F3A :NDS :256 :66 :W1)           "VALIGNQ")        ;; ib
	 ((:EVEX :0F3A :NDS :512 :66 :W0)           "VALIGND")        ;; ib
	 ((:EVEX :0F3A :NDS :512 :66 :W1)           "VALIGNQ"))       ;; ib
    (#x4 ((:EVEX :0F3A :128 :66 :W0)                "VPERMILPS")      ;; ib
	 ((:EVEX :0F3A :256 :66 :W0)                "VPERMILPS")      ;; ib
	 ((:EVEX :0F3A :512 :66 :W0)                "VPERMILPS"))     ;; ib
    (#x5 ((:EVEX :0F3A :128 :66 :W1)                "VPERMILPD")      ;; ib
	 ((:EVEX :0F3A :256 :66 :W1)                "VPERMILPD")      ;; ib
	 ((:EVEX :0F3A :512 :66 :W1)                "VPERMILPD"))     ;; ib
    (#x8 ((:EVEX :0F3A :128 :66 :W0)                "VRNDSCALEPS")    ;; ib
	 ((:EVEX :0F3A :256 :66 :W0)                "VRNDSCALEPS")    ;; ib
	 ((:EVEX :0F3A :512 :66 :W0)                "VRNDSCALEPS"))   ;; ib
    (#x9 ((:EVEX :0F3A :128 :66 :W1)                "VRNDSCALEPD")    ;; ib
	 ((:EVEX :0F3A :256 :66 :W1)                "VRNDSCALEPD")    ;; ib
	 ((:EVEX :0F3A :512 :66 :W1)                "VRNDSCALEPD"))   ;; ib
    (#xA ((:EVEX :0F3A :NDS :LIG :66 :W0)           "VRNDSCALESS"))   ;; ib
    (#xB ((:EVEX :0F3A :NDS :LIG :66 :W1)           "VRNDSCALESD"))   ;; ib
    (#xF ((:EVEX :0F3A :NDS :128 :66 :WIG)          "VPALIGNR")       ;; ib
	 ((:EVEX :0F3A :NDS :256 :66 :WIG)          "VPALIGNR")       ;; ib
	 ((:EVEX :0F3A :NDS :512 :66 :WIG)          "VPALIGNR"))      ;; ib
    (#x14 ((:EVEX :0F3A :128 :66 :WIG)              "VPEXTRB"))       ;; ib
    (#x15 ((:EVEX :0F3A :128 :66 :WIG)              "VPEXTRW"))       ;; ib
    (#x16 ((:EVEX :0F3A :128 :66 :W0)               "VPEXTRD")        ;; ib
	  ((:EVEX :0F3A :128 :66 :W1)               "VPEXTRQ"))       ;; ib
    (#x17 ((:EVEX :0F3A :128 :66 :WIG)              "VEXTRACTPS"))    ;; ib
    (#x18 ((:EVEX :0F3A :NDS :256 :66 :W0)          "VINSERTF32X4")   ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VINSERTF64X2")   ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VINSERTF32X4")   ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VINSERTF64X2"))  ;; ib
    (#x19 ((:EVEX :0F3A :256 :66 :W0)               "VEXTRACTF32X4")  ;; ib
	  ((:EVEX :0F3A :256 :66 :W1)               "VEXTRACTF64X2")  ;; ib
	  ((:EVEX :0F3A :512 :66 :W0)               "VEXTRACTF32x4")  ;; ib
	  ((:EVEX :0F3A :512 :66 :W1)               "VEXTRACTF64X2")) ;; ib
    (#x1A ((:EVEX :0F3A :NDS :512 :66 :W0)          "VINSERTF32X4")   ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VINSERTF64X2"))  ;; ib
    (#x1B ((:EVEX :0F3A :512 :66 :W0)               "VEXTRACTF32x4")  ;; ib
	  ((:EVEX :0F3A :512 :66 :W1)               "VEXTRACTF64X2")) ;; ib
    (#x1D ((:EVEX :0F3A :128 :66 :W0)               "VCVTPS2PH")      ;; ib
	  ((:EVEX :0F3A :256 :66 :W0)               "VCVTPS2PH")      ;; ib
	  ((:EVEX :0F3A :512 :66 :W0)               "VCVTPS2PH"))     ;; ib
    (#x1E ((:EVEX :0F3A :NDS :128 :66 :W0)          "VPCMPD")         ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W0)          "VPCMPD")         ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VPCMPD")         ;; ib
	  ((:EVEX :0F3A :NDS :128 :66 :W1)          "VPCMPQ")         ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VPCMPQ")         ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VPCMPQ"))        ;; ib
    (#x1F ((:EVEX :0F3A :NDS :128 :66 :W0)          "VPCMPD")         ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W0)          "VPCMPD")         ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VPCMPD")         ;; ib
	  ((:EVEX :0F3A :NDS :128 :66 :W1)          "VPCMPQ")         ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VPCMPQ")         ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VPCMPQ"))        ;; ib
    (#x20 ((:EVEX :0F3A :NDS :128 :66 :WIG)         "VPINSRB"))       ;; ib
    (#x21 ((:EVEX :0F3A :NDS :128 :66 :W0)          "VINSERTPS"))     ;; ib
    (#x22 ((:EVEX :0F3A :NDS :128 :66 :W0)          "VPINSRD")        ;; ib
	  ((:EVEX :0F3A :NDS :128 :66 :W1)          "VPINSRQ"))       ;; ib
    (#x23 ((:EVEX :0F3A :NDS :256 :66 :W0)          "VSHUFF32X4")     ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VSHUFF64X2")     ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VSHUFF32x4")     ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VSHUFF64x2"))    ;; ib
    (#x25 ((:EVEX :0F3A :DDS :128 :66 :W0)          "VPTERNLOGD")     ;; ib
	  ((:EVEX :0F3A :DDS :128 :66 :W1)          "VPTERNLOGQ")     ;; ib
	  ((:EVEX :0F3A :DDS :256 :66 :W0)          "VPTERNLOGD")     ;; ib
	  ((:EVEX :0F3A :DDS :256 :66 :W1)          "VPTERNLOGQ")     ;; ib
	  ((:EVEX :0F3A :DDS :512 :66 :W0)          "VPTERNLOGD")     ;; ib
	  ((:EVEX :0F3A :DDS :512 :66 :W1)          "VPTERNLOGQ"))    ;; ib
    (#x26 ((:EVEX :0F3A :128 :66 :W1)               "VGETMANTPD")     ;; ib
	  ((:EVEX :0F3A :256 :66 :W1)               "VGETMANTPD")     ;; ib
	  ((:EVEX :0F3A :512 :66 :W1)               "VGETMANTPD")     ;; ib
	  ((:EVEX :0F3A :128 :66 :W0)               "VGETMANTPS")     ;; ib
	  ((:EVEX :0F3A :256 :66 :W0)               "VGETMANTPS")     ;; ib
	  ((:EVEX :0F3A :512 :66 :W0)               "VGETMANTPS"))    ;; ib
    (#x27 ((:EVEX :0F3A :NDS :LIG :66 :W1)          "VGETMANTSD")     ;; ib
	  ((:EVEX :0F3A :NDS :LIG :66 :W0)          "VGETMANTSS"))    ;; ib
    (#x38 ((:EVEX :0F3A :NDS :256 :66 :W0)          "VINSERTI32X4")   ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VINSERTI64X2")   ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VINSERTI32X4")   ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VINSERTI64X2"))  ;; ib
    (#x39 ((:EVEX :0F3A :256 :66 :W0)               "VEXTRACTI32X4")  ;; ib
	  ((:EVEX :0F3A :256 :66 :W1)               "VEXTRACTI64X2")  ;; ib
	  ((:EVEX :0F3A :512 :66 :W0)               "VEXTRACTI32x4")  ;; ib
	  ((:EVEX :0F3A :512 :66 :W1)               "VEXTRACTI64X2")) ;; ib
    (#x3A ((:EVEX :0F3A :NDS :512 :66 :W0)          "VINSERTI32X4")   ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VINSERTI64X2"))  ;; ib
    (#x3B ((:EVEX :0F3A :512 :66 :W0)               "VEXTRACTI32x4")  ;; ib
	  ((:EVEX :0F3A :512 :66 :W1)               "VEXTRACTI64X2")) ;; ib
    (#x3E ((:EVEX :0F3A :NDS :128 :66 :W0)          "VPCMPB")         ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W0)          "VPCMPB")         ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VPCMPB")         ;; ib
	  ((:EVEX :0F3A :NDS :128 :66 :W1)          "VPCMPW")         ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VPCMPW"))        ;; ib
    (#x3F ((:EVEX :0F3A :NDS :128 :66 :W0)          "VPCMPB")         ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W0)          "VPCMPB")         ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VPCMPB")         ;; ib
	  ((:EVEX :0F3A :NDS :128 :66 :W1)          "VPCMPW")         ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VPCMPW")         ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VPCMPW"))        ;; ib
    (#x42 ((:EVEX :0F3A :NDS :128 :66 :W0)          "VDBPSADBW")      ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W0)          "VDBPSADBW")      ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VDBPSADBW"))     ;; ib
    (#x43 ((:EVEX :0F3A :NDS :256 :66 :W0)          "VSHUFI32X4")     ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VSHUFI64X2")     ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VSHUFI32x4")     ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VSHUFI64x2"))    ;; ib
    (#x50 ((:EVEX :0F3A :NDS :128 :66 :W1)          "VRANGEPD")       ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VRANGEPD")       ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VRANGEPD")       ;; ib
	  ((:EVEX :0F3A :NDS :128 :66 :W0)          "VRANGEPS")       ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W0)          "VRANGEPS")       ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VRANGEPS"))      ;; ib
    (#x51 ((:EVEX :0F3A :NDS :LIG :66 :W1)          "VRANGESD")       ;;
	  ((:EVEX :0F3A :NDS :LIG :66 :W0)          "VRANGESS"))      ;;
    (#x54 ((:EVEX :0F3A :NDS :128 :66 :W1)          "VFIXUPIMMPD")    ;; ib
	  ((:EVEX :0F3A :NDS :256 :66 :W1)          "VFIXUPIMMPD")    ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W1)          "VFIXUPIMMPD")    ;; ib
	  ((:EVEX :0F3A :NDS :512 :66 :W0)          "VFIXUPIMMPS")    ;; ib
	  ((:EVEX :0F3A :NDS :128 :66 :W0)          "VFIXUPIMMPS")    ;;
	  ((:EVEX :0F3A :NDS :256 :66 :W0)          "VFIXUPIMMPS"))   ;;
    (#x55 ((:EVEX :0F3A :NDS :LIG :66 :W1)          "VFIXUPIMMSD")    ;; ib
	  ((:EVEX :0F3A :NDS :LIG :66 :W0)          "VFIXUPIMMSS"))   ;; ib
    (#x56 ((:EVEX :0F3A :128 :66 :W1)               "VREDUCEPD")      ;; ib
	  ((:EVEX :0F3A :256 :66 :W1)               "VREDUCEPD")      ;; ib
	  ((:EVEX :0F3A :512 :66 :W1)               "VREDUCEPD")      ;; ib
	  ((:EVEX :0F3A :128 :66 :W0)               "VREDUCEPS")      ;; ib
	  ((:EVEX :0F3A :256 :66 :W0)               "VREDUCEPS")      ;; ib
	  ((:EVEX :0F3A :512 :66 :W0)               "VREDUCEPS"))     ;; ib
    (#x57 ((:EVEX :0F3A :NDS :LIG :66 :W0)          "VREDUCESS")      ;; ib
	  ((:EVEX :0F3A :NDS :LIG :66 :W1)          "VREDUCESD"))     ;;
    (#x66 ((:EVEX :0F3A :128 :66 :W1)               "VFPCLASSPD")     ;; ib
	  ((:EVEX :0F3A :256 :66 :W1)               "VFPCLASSPD")     ;; ib
	  ((:EVEX :0F3A :512 :66 :W1)               "VFPCLASSPD")     ;; ib
	  ((:EVEX :0F3A :128 :66 :W0)               "VFPCLASSPS")     ;; ib
	  ((:EVEX :0F3A :256 :66 :W0)               "VFPCLASSPS")     ;; ib
	  ((:EVEX :0F3A :512 :66 :W0)               "VFPCLASSPS"))    ;; ib
    (#x67 ((:EVEX :0F3A :LIG :66 :W1)               "VFPCLASSSD")     ;; ib
	  ((:EVEX :0F3A :LIG :66 :W0)               "VFPCLASSSS"))))

;; ----------------------------------------------------------------------

;; Well-formedness of our representation of opcode maps:

;; TL;DR: See functions opcode-map-p and avx-maps-well-formed-p.

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
   (list :EXT :ALT)
   *group-numbers*
   *simple-cells-standalone-legal-keywords*))

(define simple-cells-legal-keyword-p (k)
  (member-equal k *simple-cells-legal-keywords*))

(define semantic-function-info-p (info)
  :short "Is the semantic function annotation well-formed?"
  :long "<p>This function is used to detect whether the semantic function
  annotation is well-formed.  This is important, because these annotations are
  used to generate code that dispatches control to the appropriate instruction
  semantic function.</p>"
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

(define remove-semantic-function-info ((info true-listp))
  (if (endp info)
      nil
    (b* ((elem (car info))
	 (rest (cdr info)))
      (if (and (consp elem)
	       (equal (car elem) :FN))
	  rest
	(cons elem (remove-semantic-function-info rest)))))

  ///

  (defthm true-listp-remove-semantic-function-info
    (implies (true-listp info)
	     (true-listp (remove-semantic-function-info info)))))

(define get-semantic-function-info ((info true-listp))
  :short "Retrieve semantic function annotation from an opcode cell in the
  opcode map"
  (if (endp info)
      nil
    (b* ((elem (car info))
	 (rest (cdr info)))
      (if (semantic-function-info-p elem)
	  elem
	(get-semantic-function-info rest))))
  ///

  (defthm semantic-function-info-p-of-get-semantic-function-info
    (implies (true-listp info)
	     (semantic-function-info-p (get-semantic-function-info info)))
    :hints (("Goal" :in-theory (e/d (semantic-function-info-p) ())))))


(define exception-elem-p (x)
  :short "Kinds of exceptions detected during decode time"
  :long "<p>Note that we do not detect ALL the conditions under which these
  exceptions can be thrown --- we focus only on those conditions that can occur
  during instruction-decode time.</p>"
  :enabled t
  (and (consp x)
       (member (car x) '(:UD :NM :GP :EX))
       (true-listp (cdr x))))

(define exception-info-p (info)
  :short "Is the decode-time exception annotation well-formed?"
  (or (null info)
      (and (consp info)
	   (exception-elem-p (first info))
	   (exception-info-p (rest info)))))

(define remove-exception-info ((info true-listp))
  (if (endp info)
      nil
    (b* ((elem (car info))
	 (rest (cdr info)))
      (if (and (consp elem)
	       (member (car elem) '(:UD :NM :GP)))
	  (remove-exception-info rest)
	(cons elem (remove-exception-info rest)))))

  ///

  (defthm true-listp-remove-exception-info
    (implies (true-listp info)
	     (true-listp (remove-exception-info info)))))

(define get-exception-info ((info true-listp))
  :short "Retrieve exception-related annotation from an opcode cell in the
  opcode map"
  (if (endp info)
      nil
    (b* ((elem (car info))
	 (rest (cdr info)))
      (if (exception-elem-p elem)
	  (cons elem (get-exception-info rest))
	(get-exception-info rest))))
  ///

  (defthm exception-info-p-of-get-exception-info
    (implies (true-listp info)
	     (exception-info-p (get-exception-info info)))
    :hints (("Goal" :in-theory (e/d (exception-info-p) ())))))

(define simple-cell-addressing-info-p ((info true-listp))
  :short "Is the operand addressing info. in an opcode cell well-formed?"
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
       (exception-info (get-exception-info rest))
       (semantic-info (get-semantic-function-info rest))
       (new-rest (remove-exception-info rest))
       (new-rest (remove-semantic-function-info new-rest)))
    (and
     (semantic-function-info-p semantic-info)
     (exception-info-p exception-info)
     (or
      (and (stringp first)
	   (simple-cell-addressing-info-p new-rest))
      ;; We don't expect addressing info. for group numbers right there in the
      ;; cell --- there's indirection.  Go to
      ;; *opcode-extensions-by-group-number* for addressing details of these
      ;; opcodes.
      (and (member-equal first *group-numbers*)
	   (or
	    ;; For all other Groups.
	    (member-equal :1a new-rest)
	    ;; For Group-17.
	    (member-equal :v new-rest))
	   ;; The following is unnecessary because we know
	   ;; remove-semantic-function-info returns a true-listp.  However, it
	   ;; forces the output of this function to be a boolean (member-equal
	   ;; sucks so bad).
	   (true-listp new-rest))
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

(define simple-cell-aux-p (cell)
  (or (basic-simple-cell-p cell)
      (b* (((unless (true-listp cell)) nil)
	   (first (car cell))
	   (rest (cdr cell))
	   (exception-info (get-exception-info rest))
	   (semantic-info (get-semantic-function-info rest))
	   (new-rest (remove-exception-info rest))
	   (new-rest (remove-semantic-function-info new-rest)))
	(cond ((equal first :ALT)
	       (and
		(consp new-rest)
		;; (true-listp new-rest)
		(basic-simple-cells-p (car new-rest))
		(equal (cdr new-rest) nil)
		(semantic-function-info-p semantic-info)
		(exception-info-p exception-info)))
	      (t nil))))
  ///
  (defthm simple-cell-aux-p-implies-true-listp
    (implies (simple-cell-aux-p cell)
	     (true-listp cell))
    :rule-classes :forward-chaining))

(defconst *opcode-descriptor-legal-keys*
  '(:opcode :reg :prefix :mod :r/m :vex :evex :mode :feat))

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
	   ((unless (simple-cell-aux-p opcode-cell))
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
    :hints (("Goal" :in-theory (e/d (opcode-descriptor-list-p) ()))))

  (defthm opcode-descriptor-list-p-implies-alistp
    (implies (opcode-descriptor-list-p x)
	     (alistp x))
    :hints (("Goal" :in-theory (e/d (opcode-descriptor-p) ())))))

(define simple-cell-p (cell)
  (or (simple-cell-aux-p cell)
      (b* (((unless (true-listp cell)) nil)
	   (first (car cell))
	   (rest (cdr cell)))
	(cond ((equal first :EXT)
	       (opcode-descriptor-list-p rest))
	      (t nil))))
  ///
  (defthm simple-cell-p-implies-true-listp
    (implies (simple-cell-p cell)
	     (true-listp cell))
    :rule-classes :forward-chaining))

(defconst *mandatory-prefixes*
  '(:66 :F3 :F2))

;; Reference: Section 3.1.1.2 (Opcode Column in the Instruction Summary Table
;; (Instructions with VEX prefix)), Intel Manual, Vol. 2A (May 2018 edition)

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
  :short "Is the information related to a single opcode (or an 'opcode cell')
  in the opcode maps well-formed?"
  (cond ((alistp cell) (compound-cell-p cell))
	((true-listp cell) (simple-cell-p cell))
	(t nil))
  ///
  (defthm opcode-cell-p-implies-true-listp
    (implies (opcode-cell-p cell)
	     (true-listp cell))
    :rule-classes :forward-chaining))

(define opcode-row-p (row)
  :short "Is an opcode row (that describes 16 opcodes, ranging from @('0xn0')
  to @('0xnF'), where @('n') is a nibble, @('0x0 <= n <= 0xF')) well-formed?"
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
  :short "Is an opcode map (that describes 256 opcodes, ranging from 0x00 to
  0xFF) well formed?"
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
  :short "Does this opcode row describe 16 opcodes?"
  (if (endp x)
      t
    (and (equal (len (car x)) 16)
	 (len-of-each-row-okay-p (cdr x)))))

(define opcode-extensions-map-p (map)
  :short "Is the opcode-extensions map (source: Table A-6, Intel Volume 2 (May
  2018 edition)) well-formed?"
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
  '(:vex :unused-vvvv :NDS :NDD :DDS :128 :256 :L0 :L1 :LIG
    :LZ :no-prefix :66 :F2 :F3 :0F :0F38 :0F3A :W0 :W1 :WIG))

(defconst *evex-prefix-cases*
  ;; EVEX: [NDS|NDD|DDS].[128|256|512|LIG|LZ].[66|F2|F3].[0F|0F38|0F3A].[W0|W1|WIG]
  (append '(:evex :512) (remove :v *vex-prefix-cases*)))

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
  :short "Are the VEX/EVEX opcode maps well-formed?"
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
 (define find-bad-cell-row (x)
   (and (consp x)
	(or (and (not (opcode-cell-p (first x)))
		 (first x))
	    (find-bad-cell-row (rest x))))))

(local
 (define find-bad-cell-map (x)
   ;; Helpful when debugging issues with opcode maps...
   (and (consp x)
	(or (find-bad-cell-row (first x))
	    (find-bad-cell-map (rest x))))))

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


;; More VEX and EVEX checks: are the opcode variants for a particular opcode
;; unique?  In other words, is the encoding unambiguous?  If not, that means
;; we've left out some cases.

(local
 (define sort-and-rem-dup-elems ((lst true-list-listp))
   (if (endp lst)
       nil
     (cons (remove-duplicates-equal
	    (acl2::merge-sort-lexorder (car lst)))
	   (sort-and-rem-dup-elems (cdr lst))))))

(local
 (define no-permp-equal ((l true-list-listp))
   (no-duplicatesp-equal (sort-and-rem-dup-elems l))))

(local
 (define no-duplicate-encodings-p
   ((map (avx-maps-well-formed-p map vex?))
    (vex? booleanp))
   :guard-hints (("Goal" :in-theory (e/d (avx-maps-well-formed-p
					  avx-opcode-cases-okp)
					 ())))
   (if (endp map)
       t
     (b* ((first (car map))
	  ((mv opcode variants)
	   (mv (car first) (cdr first)))
	  (var-desc-list (strip-cars variants))
	  ((unless (no-permp-equal var-desc-list))
	   (cw "~% Vex?: ~p0 Opcode: ~s1 " vex? (str::hexify opcode))
	   (cw "   Opcode variants: ~p0 ~%" variants)))
       (no-duplicate-encodings-p (cdr map) vex?)))))

(local
 (defthm vex-encoding-unambiguous
   (and (no-duplicate-encodings-p *vex-0F-opcodes* t)
	(no-duplicate-encodings-p *vex-0F38-opcodes* t)
	(no-duplicate-encodings-p *vex-0F3A-opcodes* t))))

(local
 (defthm evex-encoding-unambiguous
   (and (no-duplicate-encodings-p *evex-0F-opcodes* nil)
	(no-duplicate-encodings-p *evex-0F38-opcodes* nil)
	(no-duplicate-encodings-p *evex-0F3A-opcodes* nil))))

;; ----------------------------------------------------------------------

;; Some Exceptions-Related Tables Lifted from the Intel Manuals (May 2018
;; Edition):

(defconst *vex-exc-type-map*
  ;; Source: Table 2-15: Instructions in each Exception Class. Intel Manuals,
  ;; Vol. 2 (May 2018 Edition)
  '((:type-1 ("(V)MOVAPD" "(V)MOVAPS" "(V)MOVDQA" "(V)MOVNTDQ" "(V)MOVNTDQA"
	      "(V)MOVNTPD" "(V)MOVNTPS"))
    (:type-2 ("(V)ADDPD" "(V)ADDPS" "(V)ADDSUBPD" "(V)ADDSUBPS" "(V)CMPPD"
	      "(V)CMPPS" "(V)CVTDQ2PS" "(V)CVTPD2DQ" "(V)CVTPD2PS" "(V)CVTPS2DQ"
	      "(V)CVTTPD2DQ" "(V)CVTTPS2DQ" "(V)DIVPD" "(V)DIVPS" "(V)DPPD*"
	      "(V)DPPS*" "VFMADD132PD" "VFMADD213PD" "VFMADD231PD" "VFMADD132PS"
	      "VFMADD213PS" "VFMADD231PS" "VFMADDSUB132PD" "VFMADDSUB213PD"
	      "VFMADDSUB231PD" "VFMADDSUB132PS" "VFMADDSUB213PS" "VFMADDSUB231PS"
	      "VFMSUBADD132PD" "VFMSUBADD213PD" "VFMSUBADD231PD" "VFMSUBADD132PS"
	      "VFMSUBADD213PS" "VFMSUBADD231PS" "VFMSUB132PD"
	      "VFMSUB213PD" "VFMSUB231PD" "VFMSUB132PS" "VFMSUB213PS"
	      "VFMSUB231PS" "VFNMADD132PD" "VFNMADD213PD" "VFNMADD231PD"
	      "VFNMADD132PS" "VFNMADD213PS" "VFNMADD231PS" "VFNMSUB132PD"
	      "VFNMSUB213PD" "VFNMSUB231PD" "VFNMSUB132PS" "VFNMSUB213PS"
	      "VFNMSUB231PS" "(V)HADDPD" "(V)HADDPS" "(V)HSUBPD"
	      "(V)HSUBPS" "(V)MAXPD" "(V)MAXPS" "(V)MINPD" "(V)MINPS"
	      "(V)MULPD" "(V)MULPS" "(V)ROUNDPS" "(V)SQRTPD" "(V)SQRTPS"
	      "(V)SUBPD" "(V)SUBPS"))
    (:type-3 ("(V)ADDSD" "(V)ADDSS" "(V)CMPSD" "(V)CMPSS" "(V)COMISD"
	      "(V)COMISS" "(V)CVTPS2PD" "(V)CVTSD2SI" "(V)CVTSD2SS" "(V)CVTSI2SD"
	      "(V)CVTSI2SS" "(V)CVTSS2SD" "(V)CVTSS2SI" "(V)CVTTSD2SI" "(V)CVTTSS2SI"
	      "(V)DIVSD" "(V)DIVSS" "VFMADD132SD" "VFMADD213SD" "VFMADD231SD"
	      "VFMADD132SS" "VFMADD213SS" "VFMADD231SS" "VFMSUB132SD"
	      "VFMSUB213SD" "VFMSUB231SD" "VFMSUB132SS" "VFMSUB213SS"
	      "VFMSUB231SS" "VFNMADD132SD" "VFNMADD213SD" "VFNMADD231SD"
	      "VFNMADD132SS" "VFNMADD213SS" "VFNMADD231SS" "VFNMSUB132SD"
	      "VFNMSUB213SD" "VFNMSUB231SD" "VFNMSUB132SS" "VFNMSUB213SS"
	      "VFNMSUB231SS" "(V)MAXSD" "(V)MAXSS" "(V)MINSD" "(V)MINSS"
	      "(V)MULSD" "(V)MULSS" "(V)ROUNDSD" "(V)ROUNDSS" "(V)SQRTSD"
	      "(V)SQRTSS" "(V)SUBSD" "(V)SUBSS" "(V)UCOMISD" "(V)UCOMISS"))
    (:type-4 ("(V)AESDEC" "(V)AESDECLAST" "(V)AESENC" "(V)AESENCLAST" "(V)AESIMC"
	      "(V)AESKEYGENASSIST" "(V)ANDPD" "(V)ANDPS" "(V)ANDNPD" "(V)ANDNPS"
	      "(V)BLENDPD" "(V)BLENDPS" "VBLENDVPD" "VBLENDVPS" "(V)LDDQU***"
	      "(V)MASKMOVDQU" "(V)PTEST" "VTESTPS" "VTESTPD" "(V)MOVDQU*"
	      "(V)MOVSHDUP" "(V)MOVSLDUP" "(V)MOVUPD*" "(V)MOVUPS*" "(V)MPSADBW"
	      "(V)ORPD" "(V)ORPS" "(V)PABSB" "(V)PABSW" "(V)PABSD"
	      "(V)PACKSSWB" "(V)PACKSSDW" "(V)PACKUSWB" "(V)PACKUSDW" "(V)PADDB"
	      "(V)PADDW" "(V)PADDD" "(V)PADDQ" "(V)PADDSB" "(V)PADDSW"
	      "(V)PADDUSB" "(V)PADDUSW" "(V)PALIGNR" "(V)PAND" "(V)PANDN"
	      "(V)PAVGB" "(V)PAVGW" "(V)PBLENDVB" "(V)PBLENDW" "(V)PCMP(E/I)STRI/M***"
	      "(V)PCMPEQB" "(V)PCMPEQW" "(V)PCMPEQD" "(V)PCMPEQQ" "(V)PCMPGTB"
	      "(V)PCMPGTW" "(V)PCMPGTD" "(V)PCMPGTQ" "(V)PCLMULQDQ" "(V)PHADDW"
	      "(V)PHADDD" "(V)PHADDSW" "(V)PHMINPOSUW" "(V)PHSUBD" "(V)PHSUBW"
	      "(V)PHSUBSW" "(V)PMADDWD" "(V)PMADDUBSW" "(V)PMAXSB" "(V)PMAXSW"
	      "(V)PMAXSD" "(V)PMAXUB" "(V)PMAXUW" "(V)PMAXUD" "(V)PMINSB"
	      "(V)PMINSW" "(V)PMINSD" "(V)PMINUB" "(V)PMINUW" "(V)PMINUD"
	      "(V)PMULHUW" "(V)PMULHRSW" "(V)PMULHW" "(V)PMULLW" "(V)PMULLD"
	      "(V)PMULUDQ" "(V)PMULDQ" "(V)POR" "(V)PSADBW" "(V)PSHUFB"
	      "(V)PSHUFD" "(V)PSHUFHW" "(V)PSHUFLW" "(V)PSIGNB" "(V)PSIGNW"
	      "(V)PSIGND" "(V)PSLLW" "(V)PSLLD" "(V)PSLLQ" "(V)PSRAW"
	      "(V)PSRAD" "(V)PSRLW" "(V)PSRLD" "(V)PSRLQ" "(V)PSUBB"
	      "(V)PSUBW" "(V)PSUBD" "(V)PSUBQ" "(V)PSUBSB" "(V)PSUBSW"
	      "(V)PUNPCKHBW" "(V)PUNPCKHWD" "(V)PUNPCKHDQ" "(V)PUNPCKHQDQ"
	      "(V)PUNPCKLBW" "(V)PUNPCKLWD" "(V)PUNPCKLDQ" "(V)PUNPCKLQDQ"
	      "(V)PXOR" "(V)RCPPS" "(V)RSQRTPS" "(V)SHUFPD" "(V)SHUFPS"
	      "(V)UNPCKHPD" "(V)UNPCKHPS" "(V)UNPCKLPD" "(V)UNPCKLPS"
	      "(V)XORPD" "(V)XORPS" "VPBLENDD" "VPERMD" "VPERMPS"
	      "VPERMPD" "VPERMQ" "VPSLLVD" "VPSLLVQ" "VPSRAVD"
	      "VPSRLVD" "VPSRLVQ" "VPERMILPD" "VPERMILPS" "VPERM2F128"))
    (:type-5 ("(V)CVTDQ2PD" "(V)EXTRACTPS" "(V)INSERTPS" "(V)MOVD" "(V)MOVQ"
	      "(V)MOVDDUP" "(V)MOVLPD" "(V)MOVLPS" "(V)MOVHPD" "(V)MOVHPS"
	      "(V)MOVSD" "(V)MOVSS" "(V)PEXTRB" "(V)PEXTRD" "(V)PEXTRW"
	      "(V)PEXTRQ" "(V)PINSRB" "(V)PINSRD" "(V)PINSRW" "(V)PINSRQ"
	      "(V)RCPSS" "(V)RSQRTSS" "(V)PMOVSX/ZX" "VLDMXCSR*" "VSTMXCSR"))
    (:type-6 ("VEXTRACTF128" "VBROADCASTSS" "VBROADCASTSD" "VBROADCASTF128" "VINSERTF128"
	      "VMASKMOVPS" "VMASKMOVPD" "VPMASKMOVD" "VPMASKMOVQ" "VBROADCASTI128"
	      "VPBROADCASTB" "VPBROADCASTD" "VPBROADCASTW" "VPBROADCASTQ" "VEXTRACTI128"
	      "VINSERTI128" "VPERM2I128"))
    (:type-7 ("(V)MOVLHPS" "(V)MOVHLPS" "(V)MOVMSKPD" "(V)MOVMSKPS" "(V)PMOVMSKB"
	      "(V)PSLLDQ" "(V)PSRLDQ" "(V)PSLLW" "(V)PSLLD" "(V)PSLLQ"
	      "(V)PSRAW" "(V)PSRAD" "(V)PSRLW" "(V)PSRLD" "(V)PSRLQ"))
    (:type-8 ("VZEROALL" "VZEROUPPER"))
    (:type-11 ("VCVTPH2PS" "VCVTPS2PH"))
    (:type-12 ("VGATHERDPS" "VGATHERDPD" "VGATHERQPS" "VGATHERQPD" "VPGATHERDD"
	       "VPGATHERDQ" "VPGATHERQD" "VPGATHERQQ"))))

(defconst *evex-exc-type-map*
  ;; Source: Table 2-43: EVEX Instructions in each Exception Class. Intel
  ;; Manuals, Vol. 2 (May 2018 Edition)
  '((:type-E1   ("VMOVAPD" "VMOVAPS" "VMOVDQA32" "VMOVDQA64"))
    (:type-E1NF ("VMOVNTDQ" "VMOVNTDQA" "VMOVNTPD" "VMOVNTPS"))
    (:type-E2   ("VADDPD" "VADDPS" "VCMPPD" "VCMPPS" "VCVTDQ2PS"
		 "VCVTPD2DQ" "VCVTPD2PS" "VCVTPS2DQ" "VCVTTPD2DQ" "VCVTTPS2DQ"
		 "VDIVPD" "VDIVPS" "V4FMADDPS"
		 ("VFMADD" ("PS" "PD")) ("VFMSUBADD" ("PS" "PD"))
		 ("VFMSUB" ("PS" "PD")) ("VFNMADD" ("PS" "PD"))
		 ("VFNMSUB" ("PS" "PD"))
		 "V4FNMADDPS" "VMAXPD" "VMAXPS" "VMINPD" "VMINPS"
		 "VMULPD" "VMULPS" "VSQRTPD" "VSQRTPS" "VSUBPD"
		 "VSUBPS" "VCVTPD2QQ" "VCVTPD2UQQ" "VCVTPD2UDQ" "VCVTPS2UDQS"
		 "VCVTQQ2PD" "VCVTQQ2PS" "VCVTTPD2DQ" "VCVTTPD2QQ" "VCVTTPD2UDQ"
		 "VEXP2PD" "VCVTTPD2UQQ" "VEXP2PS" "VCVTTPS2DQ" "VCVTTPS2UDQ"
		 "VCVTUDQ2PS" "VCVTUQQ2PD" "VCVTUQQ2PS" "VFIXUPIMMPD" "VFIXUPIMMPS"
		 "VGETEXPPD" "VGETEXPPS" "VGETMANTPD" "VGETMANTPS" "VRANGEPD"
		 "VRANGEPS" "VREDUCEPD" "VREDUCEPS" "VRNDSCALEPD" "VRNDSCALEPS"
		 "VSCALEFPD" "VSCALEFPS" "VRCP28PD" "VRCP28PS" "VRSQRT28PD"
		 "VRSQRT28PS"))
    (:type-E3   ("VADDSD" "VADDSS" "VCMPSD" "VCMPSS" "VCVTPS2PD"
		 "VCVTSD2SS" "VCVTSS2SD" "VDIVSD" "VDIVSS" "VMAXSD"
		 "VMAXSS" "VMINSD" "VMINSS" "VMULSD" "VMULSS"
		 "VSQRTSD" "VSQRTSS" "VSUBSD" "VSUBSS" "VCVTPS2QQ"
		 "VCVTPS2UQQ" "VCVTTPS2QQ" "VCVTTPS2UQQ"
		 ("VFMADD" ("SS" "SD")) "V4FMADDSS" "V4FNMADDSS"
		 ("VFMSUB" ("SS" "SD")) ("VFNMADD" ("SS" "SD"))
		 ("VFNMSUB" ("SS" "SD")) ("VFNMSUB" ("SS" "SD"))
		 "VFIXUPIMMSD" "VFIXUPIMMSS" "VGETEXPSD" "VGETEXPSS" "VGETMANTSD"
		 "VGETMANTSS" "VRANGESD" "VRANGESS" "VREDUCESD" "VREDUCESS"
		 "VRNDSCALESD" "VRNDSCALESS" "VSCALEFSD" "VSCALEFSS" "VRCP28SD"
		 "VRCP28SS" "VRSQRT28SD" "VRSQRT28SS"))
    (:type-E3NF ("VCOMISD" "VCOMISS" "VCVTSD2SI" "VCVTSI2SD" "VCVTSI2SS"
		 "VCVTSS2SI" "VCVTTSD2SI" "VCVTTSS2SI" "VUCOMISD" "VUCOMISS"
		 "VCVTSD2USI" "VCVTTSD2USI" "VCVTSS2USI" "VCVTTSS2USI" "VCVTUSI2SD"
		 "VCVTUSI2SS"))
    (:type-E4   ("VANDPD" "VANDPS" "VANDNPD" "VANDNPS" "VORPD"
		 "VORPS" "VPABSD" "VPABSQ" "VPADDD" "VPADDQ"
		 "VPANDD" "VPANDQ" "VPANDND" "VPANDNQ" "VPCMPEQD"
		 "VPCMPEQQ" "VPCMPGTD" "VPCMPGTQ" "VPMAXSD" "VPMAXSQ"
		 "VPMAXUD" "VPMAXUQ" "VPMINSD" "VPMINSQ" "VPMINUD"
		 "VPMINUQ" "VPMULLD" "VPMULLQ" "VPMULUDQ" "VPMULDQ"
		 "VPORD" "VPORQ" "VPSUBD" "VPSUBUSB" "VPSUBUSW"
		 "VPSUBQ" "VPXORD" "VPXORQ" "VXORPD" "VXORPS"
		 "VPSLLVD" "VPSLLVQ" "VBLENDMPD" "VBLENDMPS" "VPBLENDMD"
		 "VPBLENDMB" "VPBLENDMW" "VPBLENDMQ" "VFPCLASSPD" "VPSRLVD"
		 "VPSRLVQ" "VP4DPWSSD" "VP4DPWSSDS" "VFPCLASSPS" "VPCMPD"
		 "VPCMPQ" "VPCMPUD" "VPCMPUQ" "VPLZCNTD" "VPLZCNTQ"
		 "VPRORD" "VPROLVD" "VPROLVQ" "VPRORVD" "VPRORVQ"
		 "VPROLD" "VPROLQ" "VPSLLD" "VPSLLQ" "VPSRAD"
		 "VPSRAQ" "VPSRLD" "VPSRLQ" "VPTERNLOGD" "VPTERNLOGQ"
		 "VPTESTMD" "VPTESTMQ" "VPTESTNMD" "VPTESTNMQ" "VRCP14PD"
		 "VRCP14PS" "VRSQRT14PD" "VRSQRT14PS" "VPCONFLICTD" "VPCONFLICTQ"
		 "VPSRAVW" "VPSRAVD" "VPSRAVW" "VPSRAVQ" "VPMADD52LUQ" "VPMADD52HUQ"))
    (:type-E4.nb ("VMOVUPD" "VMOVUPS" "VMOVDQU8" "VMOVDQU16" "VMOVDQU32"
		  "VMOVDQU64" "VPCMPB" "VPCMPW" "VPCMPUB" "VPCMPUW"
		  "VEXPANDPD" "VEXPANDPS" "VPCOMPRESSD" "VPCOMPRESSQ" "VPEXPANDD"
		  "VPEXPANDQ" "VCOMPRESSPD" "VCOMPRESSPS" "VPABSB" "VPABSW"
		  "VPADDB" "VPADDW" "VPADDSB" "VPADDSW" "VPADDUSB"
		  "VPADDUSW" "VPAVGB" "VPAVGW" "VPCMPEQB" "VPCMPEQW"
		  "VPCMPGTB" "VPCMPGTW" "VPMAXSB" "VPMAXSW" "VPMAXUB"
		  "VPMAXUW" "VPMINSB" "VPMINSW" "VPMINUB" "VPMINUW"
		  "VPMULHRSW" "VPMULHUW" "VPMULHW" "VPMULLW" "VPSUBB"
		  "VPSUBW" "VPSUBSB" "VPSUBSW" "VPTESTMB" "VPTESTMW"
		  "VPTESTNMB" "VPTESTNMW" "VPSLLW" "VPSRAW" "VPSRLW"
		  "VPSLLVW" "VPSRLVW"))
    (:type-E4NF  ("VPACKSSDW" "VPACKUSDW VPSHUFD" "VPUNPCKHDQ" "VPUNPCKHQDQ" "VPUNPCKLDQ"
		  "VPUNPCKLQDQ" "VSHUFPD" "VSHUFPS" "VUNPCKHPD" "VUNPCKHPS"
		  "VUNPCKLPD" "VUNPCKLPS" "VPERMD" "VPERMPS" "VPERMPD"
		  "VPERMQ" "VALIGND" "VALIGNQ" "VPERMI2D" "VPERMI2PS"
		  "VPERMI2PD" "VPERMI2Q" "VPERMT2D" "VPERMT2PS" "VPERMT2Q"
		  "VPERMT2PD" "VPERMILPD" "VPERMILPS" "VSHUFI32X4" "VSHUFI64X2"
		  "VSHUFF32x4" "VSHUFF32X4" "VSHUFF64X2" "VPMULTISHIFTQB"))
    (:type-E4NF.nb ("VDBPSADBW" "VPACKSSWB" "VPACKUSWB" "VPALIGNR" "VPMADDWD"
		    "VPMADDUBSW" "VMOVSHDUP" "VMOVSLDUP" "VPSADBW" "VPSHUFB"
		    "VPSHUFHW" "VPSHUFLW" "VPSLLDQ" "VPSRLDQ" "VPSLLW"
		    "VPSRAW" "VPSRLW" "VPSLLD" "VPSLLQ" "VPSRAD"
		    "VPSRAQ" "VPSRLD" "VPSRLQ" "VPUNPCKHBW" "VPUNPCKHWD"
		    "VPUNPCKLBW" "VPUNPCKLWD" "VPERMW" "VPERMI2W" "VPERMT2W"
		    "VPERMB" "VPERMI2B" "VPERMT2B"))
    (:type-E5   ("VCVTDQ2PD" "PMOVSXBW" "PMOVSXBW" "PMOVSXBD" "PMOVSXBQ"
		 "PMOVSXWD" "PMOVSXWQ" "PMOVSXDQ" "PMOVZXBW" "PMOVZXBD"
		 "PMOVZXBQ" "PMOVZXWD" "PMOVZXWQ" "PMOVZXDQ" "VCVTUDQ2PD"))
    (:type-E5NF ("VMOVDDUP"))
    (:type-E6   ("VBROADCASTSS" "VBROADCASTSD" "VBROADCASTF32X4"
		 "VBROADCASTI32X4" "VPBROADCASTB" "VPBROADCASTD"
		 "VPBROADCASTW" "VPBROADCASTQ" "VBROADCASTI32x2"
		 "VBROADCASTF32X2" "VBROADCASTF32X4" "VBROADCASTF64X2"
		 "VBROADCASTF32X8" "VBROADCASTF64X4" "VBROADCASTI32X2"
		 "VBROADCASTI32X4" "VBROADCASTI64X2" "VBROADCASTI32X8"
		 "VBROADCASTI64X4" "VFPCLASSSD" "VFPCLASSSS"
		 "VPMOVQB" "VPMOVSQB" "VPMOVUSQB" "VPMOVQW"
		 "VPMOVSQW" "VPMOVUSQW" "VPMOVQD" "VPMOVSQD"
		 "VPMOVUSQD" "VPMOVDB" "VPMOVSDB" "VPMOVUSDB"
		 "VPMOVDW" "VPMOVSDW" "VPMOVUSDW"))
    (:type-E6NF ("VEXTRACTF32X4" "VEXTRACTF64X2" "VEXTRACTF32X8" "VINSERTF32X4"
		 "VINSERTF64X2" "VINSERTF64X4" "VINSERTF32X8" "VINSERTI32X4"
		 "VINSERTI64X2" "VINSERTI64X4" "VINSERTI32X8" "VEXTRACTI32X4"
		 "VEXTRACTI64X2" "VEXTRACTI32X8" "VEXTRACTI64X4" "VPBROADCASTMB2Q"
		 "VPBROADCASTMW2D" "VPMOVWB" "VPMOVSWB" "VPMOVUSWB" "VEXTRACTF32x4"))
    (:type-E7NM.1284 ("VMOVLHPS" "VMOVHLPS"))
    (:type-E7NM  ("VPMOVM2B" "VPMOVM2D" "VPMOVM2Q" "VPMOVM2W" "VPMOVB2M"
		  "VPMOVD2M" "VPMOVQ2M" "VPMOVW2M"))
    (:type-E9NF  ("VEXTRACTPS" "VINSERTPS" "VMOVHPD" "VMOVHPS" "VMOVLPD"
		  "VMOVLPS" "VMOVD" "VMOVQ" "VPEXTRB" "VPEXTRD"
		  "VPEXTRW" "VPEXTRQ" "VPINSRB" "VPINSRD" "VPINSRW"
		  "VPINSRQ"))
    (:type-E10   ("VMOVSD" "VMOVSS" "VRCP14SD" "VRCP14SS" "VRSQRT14SD"
		  "VRSQRT14SS"))
    (:type-E10NF ("VCVTSI2SD" "VCVTUSI2SD"))
    (:type-E11   ("VCVTPH2PS" "VCVTPS2PH"))
    (:type-E12   ("VGATHERDPS" "VGATHERDPD" "VGATHERQPS" "VGATHERQPD" "VPGATHERDD"
		  "VPGATHERDQ" "VPGATHERQD" "VPGATHERQQ" "VPSCATTERDD" "VPSCATTERDQ"
		  "VPSCATTERQD" "VPSCATTERQQ" "VSCATTERDPD" "VSCATTERDPS" "VSCATTERQPD"
		  "VSCATTERQPS"))
    (:type-E12NP ("VGATHERPF0DPD" "VGATHERPF0DPS" "VGATHERPF0QPD" "VGATHERPF0QPS"
		  "VGATHERPF1DPD" "VGATHERPF1DPS" "VGATHERPF1QPD" "VGATHERPF1QPS"
		  "VSCATTERPF0DPD" "VSCATTERPF0DPS" "VSCATTERPF0QPD" "VSCATTERPF0QPS"
		  "VSCATTERPF1DPD" "VSCATTERPF1DPS" "VSCATTERPF1QPD" "VSCATTERPF1QPS"))))


(local
 (define add-rev-map (lst key rslt)
   (if (atom lst) rslt
     (add-rev-map (rest lst) key
		  (cons (cons (first lst) key) rslt)))))


(local
 (define mk-rev-map ((alst alistp) &key (rslt 'nil))
   (if (atom alst) rslt
     (mk-rev-map (rest alst)
		 :rslt (add-rev-map (and (consp (cdar alst))
					 (cadar alst))
				    (caar alst) rslt)))))

(local (defconst *evex-exc-op-types*
	 ;; Map opcode name to exc-type.
	 (mk-rev-map *evex-exc-type-map*)))

(local
 (define or-subs ((mtch string-listp) (op stringp))
   (and (consp mtch)
	(or (str::isubstrp (first mtch) op)
	    (or-subs (rest mtch) op)))))

(local
 (define match-elem-p (mtch (op stringp))
   (cond ((stringp mtch)
	  (str::isubstrp mtch op))
	 ((string-listp mtch)
	  (or-subs mtch op)))))

(local
 (define match-lstp (mtch (op stringp))
   (or (atom mtch)
       (and (match-elem-p (first mtch) op)
	    (match-lstp (rest mtch) op)))))

(local
 (define match-op-exc ((op stringp) mtch) ;; this isn't right but first cut..
   (if (stringp mtch)
       (or (str::isubstrp op mtch)
	   (str::isubstrp mtch op))
     (match-lstp mtch op))))

(local
 (define find-op-exc-type ((op stringp) (map alistp))
   (cond ((endp map)
	  (er hard? 'find-op-exc-type
	      "did not find op:~x0" op))
	 ((match-op-exc op (caar map))
	  (cdar map))
	 (t (find-op-exc-type op (cdr map))))))


;; Finally, we have some additional functions for computing the evex and vex
;; exc-type maps from the opcode maps (additional entries may need to be added
;; to the opcode maps).

(local
 (define find-cell-for-opcode ((ndx natp) (row opcode-row-p))
   :measure (len row)
   :returns (cell opcode-cell-p :hyp :guard)
   (cond ((atom row)
	  (er hard? 'find-cell-for-opcode
	      "Did not find ndx ~p0!" ndx))
	 ((zp ndx) (first row))
	 (t (find-cell-for-opcode (1- ndx) (rest row))))))

(local
 (define find-row-for-opcode ((ndx natp) (map opcode-map-p))
   :guard-hints (("Goal" :in-theory (enable opcode-map-p)))
   :measure (len map)
   :returns (row opcode-row-p :hyp :guard
		 :hints (("Goal" :in-theory (enable opcode-map-p))))
   (cond ((atom map)
	  (er hard? 'find-row-for-opcode
	      "Did not find ndx ~p0!" ndx))
	 ((zp ndx) (first map))
	 (t (find-row-for-opcode (1- ndx) (rest map))))))

(local
 (define find-chk-exc (x (pref symbolp) (name stringp))
   (cond ((atom x) nil)
	 ((eq (first x) 'chk-exc)
	  (and (consp (rest x))
	       (first (rest x))))
	 ((and (symbolp (first x))
	       (member-eq (first x)
			  '(:66
			    :F2 :F3 :no-prefix
			    :v66  :vF2  :vF3  :v
			    :ev66 :evF2 :evF3 :ev)))
	  (and (or (eq (first x) pref)
		   (and (eq pref :66)
			(member-eq (first x) '(:66 :v66 :ev66)))
		   (and (eq pref :F2)
			(member-eq (first x) '(:F2 :vF2 :evF2)))
		   (and (eq pref :F3)
			(member-eq (first x) '(:F3 :vF3 :evF3)))
		   (and (eq pref :no-prefix)
			(member-eq (first x) '(:v :ev :no-prefix))))
	       (find-chk-exc (rest x) pref name)))
	 ((stringp (first x)) ;; must be opcode name for this check to work..
	  (and (or (str::isubstrp (first x) name)
		   (str::isubstrp name (first x)))
	       (find-chk-exc (rest x) pref name)))
	 (t (or (find-chk-exc (first x) pref name)
		(find-chk-exc (rest x) pref name))))))

(local
 (define drop-assoc-eq ((key symbolp) (alst alistp))
   :returns (rslt alistp :hyp :guard)
   (cond ((endp alst) ())
	 ((eq key (caar alst)) (drop-assoc-eq key (cdr alst)))
	 (t (cons (car alst) (drop-assoc-eq key (cdr alst)))))))

(local
 (define find-op-name (x)
   (cond ((stringp x) x)
	 ((atom x) nil)
	 (t (or (find-op-name (car x))
		(find-op-name (cdr x)))))))

(local
 (define make-keys-into-lists ((alst alistp))
   (if (endp alst) ()
     (cons (list (list (caar alst)) (cdar alst))
	   (make-keys-into-lists (cdr alst))))))

(local
 (define avx-keys-chk-exc ((lsts true-list-listp) ops
			   (vex? booleanp)
			   (cell opcode-cell-p)
			   &key
			   ((rslt alistp) 'nil))
   (if (endp lsts) (make-keys-into-lists rslt)
     (b* ((kwd-lst (first lsts))
	  (pref (cond ((member-eq :66 kwd-lst) :66)
		      ((member-eq :F2 kwd-lst) :F2)
		      ((member-eq :F3 kwd-lst) :F3)
		      (t :no-prefix)))
	  (name (and (consp ops) (find-op-name (car ops))))
	  ((when (not (stringp name)))
	   (er hard? 'avx-keys-chk-exc "internal error!: ~x0" ops))
	  (exc-type (if vex? nil
		      (find-op-exc-type name *evex-exc-op-types*)))
	  (exc-type (and (symbolp exc-type) exc-type))
	  (exc-type (or exc-type (find-chk-exc cell pref name)))
	  (exc-type (and (symbolp exc-type) exc-type))
	  (exc-type (or exc-type :BOZO))
	  (prev (assoc-eq pref rslt))
	  (rslt (cond ((atom prev)
		       (acons pref exc-type rslt))
		      ((eq exc-type (cdr prev))
		       rslt)
		      (t (acons pref :BOZO (drop-assoc-eq pref rslt))))))
       (avx-keys-chk-exc (rest lsts) (and (consp ops) (rest ops)) vex? cell
			 :rslt rslt)))))

(local
 (define avx-find-chk-exc ((map (avx-maps-well-formed-p map vex?))
			   (vex? booleanp)
			   (legacy-map opcode-map-p))
   :guard-hints (("Goal" :in-theory (enable avx-maps-well-formed-p)))
   (if (endp map) ()
     (b* ((first (car map))
	  (opcode (nfix (car first)))
	  (cell (find-cell-for-opcode
		 (logand opcode 15)
		 (find-row-for-opcode (ash opcode -4)
				      legacy-map)))
	  (info (cdr first))
	  ((when (not (alistp info)))
	   (er hard? 'avx-find-chk-exc "internal error1!"))
	  (lsts (strip-cars info))
	  (ops  (strip-cdrs info))
	  ((when (not (true-list-listp lsts)))
	   (er hard? 'avx-find-chk-exc "internal error2!")))
       (cons (list (str::hexify opcode) (avx-keys-chk-exc lsts ops vex? cell))
	     (avx-find-chk-exc (rest map) vex? legacy-map))))))


#| leaving these here for possible correspondence checks to be added in the future..

(avx-find-chk-exc *vex-0F-opcodes* t *two-byte-opcode-map-lst*)
(avx-find-chk-exc *vex-0F38-opcodes* t *0F-38-three-byte-opcode-map-lst*)
(avx-find-chk-exc *vex-0F3A-opcodes* t *0F-3A-three-byte-opcode-map-lst*)

(avx-find-chk-exc *evex-0F-opcodes* nil *two-byte-opcode-map-lst*)
(avx-find-chk-exc *evex-0F38-opcodes* nil *0F-38-three-byte-opcode-map-lst*)
(avx-find-chk-exc *evex-0F3A-opcodes* nil *0F-3A-three-byte-opcode-map-lst*)

|#

;;;;;;;;;;;;;; VEX exc type constants ;;;;;;;;;;;;;;;;;;;;;;

(defconst *vex-0F-exc-types*
  '((#ux10 (((:no-prefix) :type-4)
	    ((:66) :type-4)
	    ((:F3) :type-5)
	    ((:F2) :type-5)))
    (#ux11 (((:no-prefix) :type-4)
	    ((:66) :type-4)
	    ((:F3) :type-5)
	    ((:F2) :type-5)))
    (#ux12 (((:F3) :type-4)
	    ;; BOZO Rob -- fix with updated tables:
	    ;;            ((:no-prefix (:mod . #b11)) :type-5)
	    ;;            ((:no-prefix (:mod . :mem)) :type-7)
	    ((:no-prefix) :type-7)
	    ((:66) :type-5)
	    ((:F2) :type-5)))
    (#ux13 (((:no-prefix) :type-5)
	    ((:66) :type-5)))
    (#ux14 (((:no-prefix) :type-4)
	    ((:66) :type-4)))
    (#ux15 (((:no-prefix) :type-4)
	    ((:66) :type-4)))
    (#ux16 (((:F3) :type-4)
	    ;; BOZO Rob -- fix with updated tables:
	    ;;            ((:no-prefix (:mod . #b11)) :type-5)
	    ;;            ((:no-prefix (:mod . :mem)) :type-7)
	    ((:no-prefix) :type-7)
	    ((:66) :type-5)))
    (#ux17 (((:no-prefix) :type-5)
	    ((:66) :type-5)))
    (#ux28 (((:no-prefix) :type-1)
	    ((:66) :type-1)))
    (#ux29 (((:no-prefix) :type-1)
	    ((:66) :type-1)))
    (#ux2A (((:F3) :type-3) ((:F2) :type-3)))
    (#ux2B (((:no-prefix) :type-1)
	    ((:66) :type-1)))
    (#ux2C (((:F3) :type-3) ((:F2) :type-3)))
    (#ux2D (((:F3) :type-3) ((:F2) :type-3)))
    (#ux2E (((:no-prefix) :type-3)
	    ((:66) :type-3)))
    (#ux2F (((:no-prefix) :type-3)
	    ((:66) :type-3)))
    (#ux41 (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux42 (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux44 (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux45 (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux46 (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux47 (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux4A (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux4B (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux50 (((:no-prefix) :type-7)
	    ((:66) :type-7)))
    (#ux51 (((:F3) :type-3)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-2)
	    ((:66) :type-2)))
    (#ux52 (((:F3) :type-5)
	    ((:no-prefix) :type-4)))
    (#ux53 (((:F3) :type-5)
	    ((:no-prefix) :type-4)))
    (#ux54 (((:no-prefix) :type-4)
	    ((:66) :type-4)))
    (#ux55 (((:no-prefix) :type-4)
	    ((:66) :type-4)))
    (#ux56 (((:no-prefix) :type-4)
	    ((:66) :type-4)))
    (#ux57 (((:no-prefix) :type-4)
	    ((:66) :type-4)))
    (#ux58 (((:F3) :type-3)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-4)
	    ((:66) :type-4)))
    (#ux59 (((:F3) :type-3)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-2)
	    ((:66) :type-2)))
    (#ux5A (((:F3) :type-3)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-3)
	    ((:66) :type-3)))
    (#ux5B (((:F3) :type-2)
	    ((:66) :type-2)
	    ((:no-prefix) :type-2)))
    (#ux5C (((:F3) :type-3)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-2)
	    ((:66) :type-2)))
    (#ux5D (((:F3) :type-2)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-2)
	    ((:66) :type-2)))
    (#ux5E (((:F3) :type-3)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-2)
	    ((:66) :type-2)))
    (#ux5F (((:F3) :type-3)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-2)
	    ((:66) :type-2)))
    (#ux60 (((:66) :type-4)))
    (#ux61 (((:66) :type-4)))
    (#ux62 (((:66) :type-4)))
    (#ux63 (((:66) :type-4)))
    (#ux64 (((:66) :type-4)))
    (#ux65 (((:66) :type-4)))
    (#ux66 (((:66) :type-4)))
    (#ux67 (((:66) :type-4)))
    (#ux68 (((:66) :type-4)))
    (#ux69 (((:66) :type-4)))
    (#ux6A (((:66) :type-4)))
    (#ux6B (((:66) :type-4)))
    (#ux6C (((:66) :type-4)))
    (#ux6D (((:66) :type-4)))
    (#ux6E (((:66) :type-5)))
    (#ux6F (((:F3) :type-4) ((:66) :type-1)))
    (#ux70 (((:F2) :type-4)
	    ((:F3) :type-4)
	    ((:66) :type-4)))
    (#ux71 (((:66) :type-7)))
    (#ux72 (((:66) :type-7)))
    (#ux73 (((:66) :type-4)))
    (#ux74 (((:66) :type-4)))
    (#ux75 (((:66) :type-4)))
    (#ux76 (((:66) :type-4)))
    (#ux77 (((:no-prefix) :type-8)))
    (#ux7C (((:F2) :type-2) ((:66) :type-2)))
    (#ux7D (((:F2) :type-2) ((:66) :type-2)))
    (#ux7E (((:F3) :type-5) ((:66) :type-5)))
    (#ux7F (((:F3) :type-4) ((:66) :type-1)))
    (#ux90 (((:no-prefix) :type-k21) ((:66) :type-k21)))
    (#ux91 (((:no-prefix) :type-k21) ((:66) :type-k21)))
    (#ux92 (((:no-prefix) :type-k20)
	    ((:F2) :type-k20)
	    ((:66) :type-k20)))
    (#ux93 (((:no-prefix) :type-k20)
	    ((:F2) :type-k20)
	    ((:66) :type-k20)))
    (#ux98 (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#ux99 (((:no-prefix) :type-k20) ((:66) :type-k20)))
    (#uxAE (((:no-prefix) :type-5)))
    (#uxC2 (((:F3) :type-3)
	    ((:F2) :type-3)
	    ((:no-prefix) :type-2)
	    ((:66) :type-2)))
    (#uxC4 (((:66) :type-5)))
    (#uxC5 (((:66) :type-5)))
    (#uxC6 (((:no-prefix) :type-4)
	    ((:66) :type-4)))
    (#uxD0 (((:F2) :type-4) ((:66) :type-4)))
    (#uxD1 (((:66) :type-4)))
    (#uxD2 (((:66) :type-4)))
    (#uxD3 (((:66) :type-4)))
    (#uxD4 (((:66) :type-4)))
    (#uxD5 (((:66) :type-4)))
    (#uxD6 (((:66) :type-4)))
    (#uxD7 (((:66) :type-7)))
    (#uxD8 (((:66) :type-4)))
    (#uxD9 (((:66) :type-4)))
    (#uxDA (((:66) :type-4)))
    (#uxDB (((:66) :type-4)))
    (#uxDC (((:66) :type-4)))
    (#uxDD (((:66) :type-4)))
    (#uxDE (((:66) :type-4)))
    (#uxDF (((:66) :type-4)))
    (#uxE0 (((:66) :type-4)))
    (#uxE1 (((:66) :type-4)))
    (#uxE2 (((:66) :type-4)))
    (#uxE3 (((:66) :type-4)))
    (#uxE4 (((:66) :type-4)))
    (#uxE5 (((:66) :type-4)))
    (#uxE6 (((:66) :type-2)
	    ((:F2) :type-2)
	    ((:F3) :type-5)))
    (#uxE7 (((:66) :type-1)))
    (#uxE8 (((:66) :type-4)))
    (#uxE9 (((:66) :type-4)))
    (#uxEA (((:66) :type-4)))
    (#uxEB (((:66) :type-4)))
    (#uxEC (((:66) :type-4)))
    (#uxED (((:66) :type-4)))
    (#uxEE (((:66) :type-4)))
    (#uxEF (((:66) :type-4)))
    (#uxF0 (((:F2) :type-4)))
    (#uxF1 (((:66) :type-4)))
    (#uxF2 (((:66) :type-4)))
    (#uxF3 (((:66) :type-4)))
    (#uxF4 (((:66) :type-4)))
    (#uxF5 (((:66) :type-4)))
    (#uxF6 (((:66) :type-4)))
    (#uxF7 (((:66) :type-4)))
    (#uxF8 (((:66) :type-4)))
    (#uxF9 (((:66) :type-4)))
    (#uxFA (((:66) :type-4)))
    (#uxFB (((:66) :type-4)))
    (#uxFC (((:66) :type-4)))
    (#uxFD (((:66) :type-4)))
    (#uxFE (((:66) :type-4)))))

(defconst *vex-0F38-exc-types*
  '((#ux0 (((:66) :type-4)))
    (#ux1 (((:66) :type-4)))
    (#ux2 (((:66) :type-4)))
    (#ux3 (((:66) :type-4)))
    (#ux4 (((:66) :type-4)))
    (#ux5 (((:66) :type-4)))
    (#ux6 (((:66) :type-4)))
    (#ux7 (((:66) :type-4)))
    (#ux8 (((:66) :type-4)))
    (#ux9 (((:66) :type-4)))
    (#uxA (((:66) :type-4)))
    (#uxB (((:66) :type-4)))
    (#uxC (((:66) :type-4)))
    (#uxD (((:66) :type-4)))
    (#uxE (((:66) :type-4)))
    (#uxF (((:66) :type-4)))
    (#ux13 (((:66) :type-11)))
    (#ux16 (((:66) :type-4)))
    (#ux17 (((:66) :type-4)))
    (#ux18 (((:66) :type-6)))
    (#ux19 (((:66) :type-6)))
    (#ux1A (((:66) :type-6)))
    (#ux1C (((:66) :type-4)))
    (#ux1D (((:66) :type-4)))
    (#ux1E (((:66) :type-4)))
    (#ux20 (((:66) :type-5)))
    (#ux21 (((:66) :type-5)))
    (#ux22 (((:66) :type-5)))
    (#ux23 (((:66) :type-5)))
    (#ux24 (((:66) :type-5)))
    (#ux25 (((:66) :type-5)))
    (#ux28 (((:66) :type-4)))
    (#ux29 (((:66) :type-4)))
    (#ux2A (((:66) :type-1)))
    (#ux2B (((:66) :type-4)))
    (#ux2C (((:66) :type-6)))
    (#ux2D (((:66) :type-6)))
    (#ux2E (((:66) :type-6)))
    (#ux2F (((:66) :type-6)))
    (#ux30 (((:66) :type-5)))
    (#ux31 (((:66) :type-5)))
    (#ux32 (((:66) :type-5)))
    (#ux33 (((:66) :type-5)))
    (#ux34 (((:66) :type-5)))
    (#ux35 (((:66) :type-5)))
    (#ux36 (((:66) :type-4)))
    (#ux37 (((:66) :type-4)))
    (#ux38 (((:66) :type-4)))
    (#ux39 (((:66) :type-4)))
    (#ux3A (((:66) :type-4)))
    (#ux3B (((:66) :type-4)))
    (#ux3C (((:66) :type-4)))
    (#ux3D (((:66) :type-4)))
    (#ux3E (((:66) :type-4)))
    (#ux3F (((:66) :type-4)))
    (#ux40 (((:66) :type-4)))
    (#ux41 (((:66) :type-4)))
    (#ux45 (((:66) :type-4)))
    (#ux46 (((:66) :type-4)))
    (#ux47 (((:66) :type-4)))
    (#ux58 (((:66) :type-7)))
    (#ux59 (((:66) :type-7)))
    (#ux5A (((:66) :type-6)))
    (#ux78 (((:66) :type-7)))
    (#ux79 (((:66) :type-7)))
    (#ux8C (((:66) :type-6)))
    (#ux8E (((:66) :type-6)))
    (#ux90 (((:66) :type-12)))
    (#ux91 (((:66) :type-12)))
    (#ux92 (((:66) :type-12)))
    (#ux93 (((:66) :type-12)))
    (#ux96 (((:66) :type-2)))
    (#ux97 (((:66) :type-2)))
    (#ux98 (((:66) :type-2)))
    (#ux99 (((:66) :type-2)))
    (#ux9A (((:66) :type-2)))
    (#ux9B (((:66) :type-2)))
    (#ux9C (((:66) :type-2)))
    (#ux9D (((:66) :type-2)))
    (#ux9E (((:66) :type-2)))
    (#ux9F (((:66) :type-2)))
    (#uxA6 (((:66) :type-2)))
    (#uxA7 (((:66) :type-2)))
    (#uxA8 (((:66) :type-2)))
    (#uxA9 (((:66) :type-2)))
    (#uxAA (((:66) :type-2)))
    (#uxAB (((:66) :type-2)))
    (#uxAC (((:66) :type-2)))
    (#uxAD (((:66) :type-2)))
    (#uxAE (((:66) :type-2)))
    (#uxAF (((:66) :type-2)))
    (#uxB6 (((:66) :type-2)))
    (#uxB7 (((:66) :type-2)))
    (#uxB8 (((:66) :type-2)))
    (#uxB9 (((:66) :type-2)))
    (#uxBA (((:66) :type-2)))
    (#uxBB (((:66) :type-2)))
    (#uxBC (((:66) :type-2)))
    (#uxBD (((:66) :type-2)))
    (#uxBE (((:66) :type-2)))
    (#uxBF (((:66) :type-2)))
    (#uxDB (((:66) :type-4)))
    (#uxDC (((:66) :type-4)))
    (#uxDD (((:66) :type-4)))
    (#uxDE (((:66) :type-4)))
    (#uxDF (((:66) :type-4)))
    (#uxF2 (((:no-prefix) :type-vex-gpr)))
    (#uxF3 (((:no-prefix) :type-vex-gpr)))
    (#uxF5 (((:F3) :type-vex-gpr)
	    ((:F2) :type-vex-gpr)
	    ((:no-prefix) :type-vex-gpr)))
    (#uxF6 (((:F2) :type-vex-gpr)))
    (#uxF7 (((:F2) :type-vex-gpr)
	    ((:66) :type-vex-gpr)
	    ((:F3) :type-vex-gpr)
	    ((:no-prefix) :type-vex-gpr)))))

(defconst *vex-0F3A-exc-types*
  '((#ux0 (((:66) :type-4)))
    (#ux1 (((:66) :type-4)))
    (#ux2 (((:66) :type-4)))
    (#ux4 (((:66) :type-4)))
    (#ux5 (((:66) :type-4)))
    (#ux6 (((:66) :type-6)))
    (#ux8 (((:66) :type-2)))
    (#ux9 (((:66) :type-2)))
    (#uxA (((:66) :type-3)))
    (#uxB (((:66) :type-3)))
    (#uxC (((:66) :type-4)))
    (#uxD (((:66) :type-4)))
    (#uxE (((:66) :type-4)))
    (#uxF (((:66) :type-4)))
    (#ux14 (((:66) :type-5)))
    (#ux15 (((:66) :type-5)))
    (#ux16 (((:66) :type-5)))
    (#ux17 (((:66) :type-5)))
    (#ux18 (((:66) :type-6)))
    (#ux19 (((:66) :type-6)))
    (#ux1D (((:66) :type-11)))
    (#ux20 (((:66) :type-5)))
    (#ux21 (((:66) :type-5)))
    (#ux22 (((:66) :type-5)))
    (#ux30 (((:66) :type-k20)))
    (#ux31 (((:66) :type-k20)))
    (#ux32 (((:66) :type-k20)))
    (#ux33 (((:66) :type-k20)))
    (#ux38 (((:66) :type-6)))
    (#ux39 (((:66) :type-6)))
    (#ux40 (((:66) :type-2)))
    (#ux41 (((:66) :type-2)))
    (#ux42 (((:66) :type-4)))
    (#ux44 (((:66) :type-4)))
    (#ux46 (((:66) :type-6)))
    (#ux4A (((:66) :type-4)))
    (#ux4B (((:66) :type-4)))
    (#ux4C (((:66) :type-4)))
    (#ux60 (((:66) :type-4)))
    (#ux61 (((:66) :type-4)))
    (#ux62 (((:66) :type-4)))
    (#ux63 (((:66) :type-4)))
    (#uxDF (((:66) :type-4)))
    (#uxF0 (((:F2) :type-vex-gpr)))))


;;;;;;;;;;;;;; EVEX exc type constants ;;;;;;;;;;;;;;;;;;;;;;

(defconst *evex-0F-exc-types*
  `((#ux10 (((:no-prefix) :type-E4.NB)
	    ((:66) :type-E4.NB)
	    ((:F3) :type-E10)
	    ((:F2) :type-E10)))
    (#ux11 (((:no-prefix) :type-E4.NB)
	    ((:66) :type-E4.NB)
	    ((:F3) :type-E10)
	    ((:F2) :type-E10)))
    (#ux12 (((:F3) :type-E4NF.NB)
	    ;; BOZO Rob -- fix this:
;;            ((:no-prefix (:mod . #b11)) :type-E9NF)
	    ;;            ((:no-prefix (:mod . :mem)) :type-E7NM)
	    ((:no-prefix) :type-E7NM)
	    ((:66) :type-E9NF)
	    ((:F2) :type-E9NF)))
    (#ux13 (((:no-prefix) :type-E9NF)
	    ((:66) :type-E9NF)))
    (#ux14 (((:no-prefix) :type-E4NF)
	    ((:66) :type-E4NF)))
    (#ux15 (((:no-prefix) :type-E4NF)
	    ((:66) :type-E4NF)))
    (#ux16 (((:F3) :type-E4NF.NB)
	    ;; BOZO Rob -- fix this:
;;            ((:no-prefix (:mod . #b11)) :type-E9NF)
	    ;;            ((:no-prefix (:mod . :mem)) :type-E7NM)
	    ((:no-prefix) :type-E7NM)
	    ((:66) :type-E9NF)))
    (#ux17 (((:no-prefix) :type-E9NF)
	    ((:66) :type-E9NF)))
    (#ux28 (((:no-prefix) :type-E1)
	    ((:66) :type-E1)))
    (#ux29 (((:no-prefix) :type-E1)
	    ((:66) :type-E1)))
    (#ux2A (((:F3) :type-E3NF)
	    ((:F2) :type-E10NF)))
    (#ux2B (((:no-prefix) :type-E1NF)
	    ((:66) :type-E1NF)))
    (#ux2C (((:F3) :type-E3NF) ((:F2) :type-E3NF)))
    (#ux2D (((:F3) :type-E3NF) ((:F2) :type-E3NF)))
    (#ux2E (((:no-prefix) :type-E3NF)
	    ((:66) :type-E3NF)))
    (#ux2F (((:no-prefix) :type-E3NF)
	    ((:66) :type-E3NF)))
    (#ux51 (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E2)
	    ((:66) :type-E2)))
    (#ux54 (((:no-prefix) :type-E4)
	    ((:66) :type-E4)))
    (#ux55 (((:no-prefix) :type-E4)
	    ((:66) :type-E4)))
    (#ux56 (((:no-prefix) :type-E4)
	    ((:66) :type-E4)))
    (#ux57 (((:no-prefix) :type-E4)
	    ((:66) :type-E4)))
    (#ux58 (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E2)
	    ((:66) :type-E2)))
    (#ux59 (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E2)
	    ((:66) :type-E2)))
    (#ux5A (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E3)
	    ((:66) :type-E2)))
    (#ux5B (((:F3) :type-E2)
	    ((:66) :type-E2)
	    ((:no-prefix) :type-E2)))
    (#ux5C (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E2)
	    ((:66) :type-E2)))
    (#ux5D (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E2)
	    ((:66) :type-E2)))
    (#ux5E (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E2)
	    ((:66) :type-E2)))
    (#ux5F (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E2)
	    ((:66) :type-E2)))
    (#ux60 (((:66) :type-E4NF.NB)))
    (#ux61 (((:66) :type-E4NF.NB)))
    (#ux62 (((:66) :type-E4NF)))
    (#ux63 (((:66) :type-E4NF.NB)))
    (#ux64 (((:66) :type-E4.NB)))
    (#ux65 (((:66) :type-E4.NB)))
    (#ux66 (((:66) :type-E4)))
    (#ux67 (((:66) :type-E4NF.NB)))
    (#ux68 (((:66) :type-E4NF.NB)))
    (#ux69 (((:66) :type-E4NF.NB)))
    (#ux6A (((:66) :type-E4NF)))
    (#ux6B (((:66) :type-E4NF)))
    (#ux6C (((:66) :type-E4NF)))
    (#ux6D (((:66) :type-E4NF)))
    (#ux6E (((:66) :type-E9NF)))
    (#ux6F (((:F3) :type-E9NF)
	    ((:F2) :type-E9NF)
	    ((:66) :type-E9NF)))
    (#ux70 (((:F2) :type-E4NF.NB)
	    ((:F3) :type-E4NF.NB)
	    ((:66) :type-E4NF)))
    (#ux71 (((:66) :type-E4NF.NB)))
    (#ux72 (((:66) :type-E4NF)))
    (#ux73 (((:66) :type-E4NF.NB)))
    (#ux74 (((:66) :type-E4.NB)))
    (#ux75 (((:66) :type-E4.NB)))
    (#ux76 (((:66) :type-E4)))
    (#ux78 (((:F3) :type-E3NF)
	    ((:F2) :type-E3NF)
	    ((:66) :type-E2)
	    ((:no-prefix) :type-E2)))
    (#ux79 (((:F3) :type-E3NF)
	    ((:F2) :type-E3NF)
	    ((:66) :type-E2)
	    ((:no-prefix) :type-E2)))
    (#ux7A (((:F3) :type-E2)
	    ((:F2) :type-E2)
	    ((:66) :type-E2)))
    (#ux7B (((:F3) :type-E3NF)
	    ((:F2) :type-E10NF)
	    ((:66) :type-E2)))
    (#ux7E (((:F3) :type-E9NF)
	    ((:66) :type-E9NF)))
    (#ux7F (((:F3) :type-E9NF)
	    ((:F2) :type-E9NF)
	    ((:66) :type-E9NF)))
    (#uxC2 (((:F3) :type-E3)
	    ((:F2) :type-E3)
	    ((:no-prefix) :type-E2)
	    ((:66) :type-E2)))
    (#uxC4 (((:66) :type-E9NF)))
    (#uxC5 (((:66) :type-E9NF)))
    (#uxC6 (((:no-prefix) :type-E4NF)
	    ((:66) :type-E4NF)))
    (#uxD1 (((:66) :type-E4NF.NB)))
    (#uxD2 (((:66) :type-E4NF.NB)))
    (#uxD3 (((:66) :type-E4NF.NB)))
    (#uxD4 (((:66) :type-E4)))
    (#uxD5 (((:66) :type-E4.NB)))
    (#uxD6 (((:66) :type-E9NF)))
    (#uxD8 (((:66) :type-E4)))
    (#uxD9 (((:66) :type-E4)))
    (#uxDA (((:66) :type-E4.NB)))
    (#uxDB (((:66) :type-E4)))
    (#uxDC (((:66) :type-E4.NB)))
    (#uxDD (((:66) :type-E4.NB)))
    (#uxDE (((:66) :type-E4.NB)))
    (#uxDF (((:66) :type-E4)))
    (#uxE0 (((:66) :type-E4.NB)))
    (#uxE1 (((:66) :type-E4NF.NB)))
    (#uxE2 (((:66) :type-E4NF.NB)))
    (#uxE3 (((:66) :type-E4.NB)))
    (#uxE4 (((:66) :type-E4.NB)))
    (#uxE5 (((:66) :type-E4.NB)))
    (#uxE6 (((:66) :type-E2)
	    ((:F3) :type-E2)
	    ((:F2) :type-E2)))
    (#uxE7 (((:66) :type-E1NF)))
    (#uxE8 (((:66) :type-E4.NB)))
    (#uxE9 (((:66) :type-E4.NB)))
    (#uxEA (((:66) :type-E4.NB)))
    (#uxEB (((:66) :type-E4)))
    (#uxEC (((:66) :type-E4.NB)))
    (#uxED (((:66) :type-E4.NB)))
    (#uxEE (((:66) :type-E4.NB)))
    (#uxEF (((:66) :type-E4)))
    (#uxF1 (((:66) :type-E4NF.NB)))
    (#uxF2 (((:66) :type-E4NF.NB)))
    (#uxF3 (((:66) :type-E4NF.NB)))
    (#uxF4 (((:66) :type-E4)))
    (#uxF5 (((:66) :type-E4NF.NB)))
    (#uxF6 (((:66) :type-E4NF.NB)))
    (#uxF8 (((:66) :type-E4.NB)))
    (#uxF9 (((:66) :type-E4.NB)))
    (#uxFA (((:66) :type-E4)))
    (#uxFB (((:66) :type-E4)))
    (#uxFC (((:66) :type-E4.NB)))
    (#uxFD (((:66) :type-E4.NB)))
    (#uxFE (((:66) :type-E4)))))

(defconst *evex-0f38-exc-types*
  '((#ux0 (((:66) :type-E4NF.NB)))
    (#ux4 (((:66) :type-E4NF.NB)))
    (#uxB (((:66) :type-E4.NB)))
    (#uxC (((:66) :type-E4NF)))
    (#uxD (((:66) :type-E4NF)))
    (#ux10 (((:66) :type-E4.NB)
	    ((:F3) :type-E6NF)))
    (#ux11 (((:66) :type-E4) ((:F3) :type-E6)))
    (#ux12 (((:66) :type-E4.NB)
	    ((:F3) :type-E6)))
    (#ux13 (((:66) :type-E11) ((:F3) :type-E6)))
    (#ux14 (((:66) :type-E4) ((:F3) :type-E6)))
    (#ux15 (((:66) :type-E4) ((:F3) :type-E6)))
    (#ux16 (((:66) :type-E4NF)))
    (#ux18 (((:66) :type-E6)))
    (#ux19 (((:66) :type-E6)))
    (#ux1A (((:66) :type-E6)))
    (#ux1B (((:66) :type-E6)))
    (#ux1C (((:66) :type-E4.NB)))
    (#ux1D (((:66) :type-E4.NB)))
    (#ux1E (((:66) :type-E4)))
    (#ux1F (((:66) :type-E4)))
    (#ux20 (((:66) :type-E5) ((:F3) :type-E6NF)))
    (#ux21 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux22 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux23 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux24 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux25 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux26 (((:F3) :type-E4.NB)
	    ((:66) :type-E4.NB)))
    (#ux27 (((:F3) :type-E4) ((:66) :type-E4)))
    (#ux28 (((:66) :type-E4) ((:F3) :type-E7NM)))
    (#ux29 (((:F3) :type-E7NM) ((:66) :type-E4)))
    (#ux2A (((:F3) :type-E6NF)
	    ((:66) :type-E1NF)))
    (#ux2B (((:66) :type-E4NF)))
    (#ux2C (((:66) :type-E2)))
    (#ux2D (((:66) :type-E3)))
    (#ux30 (((:66) :type-E5) ((:F3) :type-E6NF)))
    (#ux31 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux32 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux33 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux34 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux35 (((:66) :type-E5) ((:F3) :type-E6)))
    (#ux36 (((:66) :type-E4NF)))
    (#ux37 (((:66) :type-E4)))
    (#ux38 (((:F3) :type-E7NM)
	    ((:66) :type-E4.NB)))
    (#ux39 (((:F3) :type-E7NM) ((:66) :type-E4)))
    (#ux3A (((:66) :type-E4.NB)
	    ((:F3) :type-E6NF)))
    (#ux3B (((:66) :type-E4)))
    (#ux3C (((:66) :type-E4.NB)))
    (#ux3D (((:66) :type-E4)))
    (#ux3E (((:66) :type-E4.NB)))
    (#ux3F (((:66) :type-E4)))
    (#ux40 (((:66) :type-E4)))
    (#ux42 (((:66) :type-E2)))
    (#ux43 (((:66) :type-E3)))
    (#ux44 (((:66) :type-E4)))
    (#ux45 (((:66) :type-E4)))
    (#ux46 (((:66) :type-E4)))
    (#ux47 (((:66) :type-E4)))
    (#ux4C (((:66) :type-E4)))
    (#ux4D (((:66) :type-E10)))
    (#ux4E (((:66) :type-E4)))
    (#ux4F (((:66) :type-E10)))
    (#ux52 (((:F2) :type-E4)))
    (#ux53 (((:F2) :type-E4)))
    (#ux58 (((:66) :type-E6)))
    (#ux59 (((:66) :type-E6)))
    (#ux5A (((:66) :type-E6)))
    (#ux5B (((:66) :type-E6)))
    (#ux64 (((:66) :type-E4)))
    (#ux65 (((:66) :type-E4)))
    (#ux66 (((:66) :type-E4)))
    (#ux75 (((:66) :type-E4NF.NB)))
    (#ux76 (((:66) :type-E4NF)))
    (#ux77 (((:66) :type-E4NF)))
    (#ux78 (((:66) :type-E6)))
    (#ux79 (((:66) :type-E6)))
    (#ux7A (((:66) :type-E6)))
    (#ux7B (((:66) :type-E6)))
    (#ux7C (((:66) :type-E6)))
    (#ux7D (((:66) :type-E4NF.NB)))
    (#ux7E (((:66) :type-E4NF)))
    (#ux7F (((:66) :type-E4NF)))
    (#ux83 (((:66) :type-E4NF)))
    (#ux88 (((:66) :type-E4.NB)))
    (#ux89 (((:66) :type-E4.NB)))
    (#ux8A (((:66) :type-E4.NB)))
    (#ux8B (((:66) :type-E4.NB)))
    (#ux8D (((:66) :type-E4NF.NB)))
    (#ux90 (((:66) :type-E12)))
    (#ux91 (((:66) :type-E12)))
    (#ux92 (((:66) :type-E12)))
    (#ux93 (((:66) :type-E12)))
    (#ux96 (((:66) :type-E2)))
    (#ux97 (((:66) :type-E2)))
    (#ux98 (((:66) :type-E2)))
    (#ux99 (((:66) :type-E3)))
    (#ux9A (((:66) :type-E2) ((:F2) :type-E2)))
    (#ux9B (((:66) :type-E3) ((:F2) :type-E3)))
    (#ux9C (((:66) :type-E2)))
    (#ux9D (((:66) :type-E3)))
    (#ux9E (((:66) :type-E2)))
    (#ux9F (((:66) :type-E3)))
    (#uxA0 (((:66) :type-E12)))
    (#uxA1 (((:66) :type-E12)))
    (#uxA2 (((:66) :type-E12)))
    (#uxA3 (((:66) :type-E12)))
    (#uxA6 (((:66) :type-E2)))
    (#uxA7 (((:66) :type-E2)))
    (#uxA8 (((:66) :type-E2)))
    (#uxA9 (((:66) :type-E3)))
    (#uxAA (((:66) :type-E2) ((:F2) :type-E2)))
    (#uxAB (((:66) :type-E3) ((:F2) :type-E3)))
    (#uxAC (((:66) :type-E2)))
    (#uxAD (((:66) :type-E3)))
    (#uxAE (((:66) :type-E2)))
    (#uxAF (((:66) :type-E3)))
    (#uxB4 (((:66) :type-E4)))
    (#uxB5 (((:66) :type-E4)))
    (#uxB6 (((:66) :type-E2)))
    (#uxB7 (((:66) :type-E2)))
    (#uxB8 (((:66) :type-E2)))
    (#uxB9 (((:66) :type-E3)))
    (#uxBA (((:66) :type-E2)))
    (#uxBB (((:66) :type-E3)))
    (#uxBC (((:66) :type-E2)))
    (#uxBD (((:66) :type-E3)))
    (#uxBE (((:66) :type-E2)))
    (#uxBF (((:66) :type-E3)))
    (#uxC4 (((:66) :type-E4)))
    (#uxC6 (((:66) :type-E12NP)))
    (#uxC7 (((:66) :type-E12NP)))
    (#uxC8 (((:66) :type-E2)))
    (#uxCA (((:66) :type-E2)))
    (#uxCB (((:66) :type-E3)))
    (#uxCC (((:66) :type-E2)))
    (#uxCD (((:66) :type-E3)))))

(defconst *evex-0f3A-exc-types*
  '((#ux0 (((:66) :type-E4NF)))
    (#ux1 (((:66) :type-E4NF)))
    (#ux3 (((:66) :type-E4NF)))
    (#ux4 (((:66) :type-E4NF)))
    (#ux5 (((:66) :type-E4NF)))
    (#ux8 (((:66) :type-E2)))
    (#ux9 (((:66) :type-E2)))
    (#uxA (((:66) :type-E3)))
    (#uxB (((:66) :type-E3)))
    (#uxF (((:66) :type-E4NF.NB)))
    (#ux14 (((:66) :type-E9NF)))
    (#ux15 (((:66) :type-E9NF)))
    (#ux16 (((:66) :type-E9NF)))
    (#ux17 (((:66) :type-E9NF)))
    (#ux18 (((:66) :type-E6NF)))
    (#ux19 (((:66) :type-E6NF)))
    (#ux1A (((:66) :type-E6NF)))
    (#ux1B (((:66) :type-E6NF)))
    (#ux1D (((:66) :type-E11)))
    (#ux1E (((:66) :type-E4)))
    (#ux1F (((:66) :type-E4)))
    (#ux20 (((:66) :type-E9NF)))
    (#ux21 (((:66) :type-E9NF)))
    (#ux22 (((:66) :type-E9NF)))
    (#ux23 (((:66) :type-E4NF)))
    (#ux25 (((:66) :type-E4)))
    (#ux26 (((:66) :type-E2)))
    (#ux27 (((:66) :type-E3)))
    (#ux38 (((:66) :type-E6NF)))
    (#ux39 (((:66) :type-E6NF)))
    (#ux3A (((:66) :type-E6NF)))
    (#ux3B (((:66) :type-E6NF)))
    (#ux3E (((:66) :type-E4.NB)))
    (#ux3F (((:66) :type-E4.NB)))
    (#ux42 (((:66) :type-E4NF.NB)))
    (#ux43 (((:66) :type-E4NF)))
    (#ux50 (((:66) :type-E2)))
    (#ux51 (((:66) :type-E3)))
    (#ux54 (((:66) :type-E2)))
    (#ux55 (((:66) :type-E3)))
    (#ux56 (((:66) :type-E2)))
    (#ux57 (((:66) :type-E3)))
    (#ux66 (((:66) :type-E4)))
    (#ux67 (((:66) :type-E6)))))

(define avx-exc-type-elem-p (x)
  :enabled t
  (and (consp x)
       (consp (cdr x))
       (null (cddr x))
       (true-listp (car x))
       (symbolp (cadr x))))

(define avx-exc-type-cell-p (x)
  :enabled t
  (or (null x)
      (and (consp x)
	   (avx-exc-type-elem-p (car x))
	   (avx-exc-type-cell-p (cdr x)))))

(define avx-exc-type-map-p (x)
  :enabled t
  (or (null x)
      (and (consp x)
	   (consp (car x))
	   (natp (caar x))
	   (consp (cdar x))
	   (null (cddar x))
	   (avx-exc-type-cell-p (cadar x))
	   (avx-exc-type-map-p (cdr x)))))

(local
 (defthm vex-exc-type-maps-well-formed
   (and (avx-exc-type-map-p *vex-0F-exc-types*)
	(avx-exc-type-map-p *vex-0F38-exc-types*)
	(avx-exc-type-map-p *vex-0F3A-exc-types*)
	(equal (strip-cars *vex-0F-exc-types*)
	       (strip-cars *vex-0F-opcodes*))
	(equal (strip-cars *vex-0F38-exc-types*)
	       (strip-cars *vex-0F38-opcodes*))
	(equal (strip-cars *vex-0F3A-exc-types*)
	       (strip-cars *vex-0F3A-opcodes*)))))

(local
 (defthm evex-exc-type-maps-well-formed
   (and (avx-exc-type-map-p *evex-0F-exc-types*)
	(avx-exc-type-map-p *evex-0F38-exc-types*)
	(avx-exc-type-map-p *evex-0F3A-exc-types*)
	(equal (strip-cars *evex-0F-exc-types*)
	       (strip-cars *evex-0F-opcodes*))
	(equal (strip-cars *evex-0F38-exc-types*)
	       (strip-cars *evex-0F38-opcodes*))
	(equal (strip-cars *evex-0F3A-exc-types*)
	       (strip-cars *evex-0F3A-opcodes*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; And finally again... we add tables for looking up CPUID feature flags for
;;;; each opcode:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; [Shilpi] Intel manuals (May 2018 edition) don't list any AVX* flag when BMI*
;; flag (in VEX/EVEX-encoded instructions) is mentioned.  Oversight?

(defconst *vex-0F-op-features*
  '((#x10 ((:VEX :256 :0F :WIG)
	   ("VMOVUPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VMOVUPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VMOVUPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VMOVUPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F3 :0F :WIG)
	   ("VMOVSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VMOVSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F2 :0F :WIG)
	   ("VMOVSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VMOVSD" (:CPUID-FLAG :AVX))))
    (#x11 ((:VEX :256 :0F :WIG)
	   ("VMOVUPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VMOVUPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VMOVUPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VMOVUPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F3 :0F :WIG)
	   ("VMOVSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VMOVSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F2 :0F :WIG)
	   ("VMOVSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VMOVSD" (:CPUID-FLAG :AVX))))
    (#x12 ((:VEX :256 :F3 :0F :WIG)
	   ("VMOVSLDUP" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F3 :0F :WIG)
	   ("VMOVSLDUP" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG (:mod . :mem))
	   ("VMOVLPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG (:mod . :mem))
	   ("VMOVLPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG (:mod . #b11))
	   ("VMOVHLPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :F2 :0F :WIG)
	   ("VMOVDDUP" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F2 :0F :WIG)
	   ("VMOVDDUP" (:CPUID-FLAG :AVX))))
    (#x13 ((:VEX :128 :0F :WIG (:mod . :mem))
	   ("VMOVLPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG (:mod . :mem))
	   ("VMOVLPD" (:CPUID-FLAG :AVX))))
    (#x14 ((:VEX :NDS :256 :0F :WIG)
	   ("VUNPCKLPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VUNPCKLPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VUNPCKLPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VUNPCKLPD" (:CPUID-FLAG :AVX))))
    (#x15 ((:VEX :NDS :256 :0F :WIG)
	   ("VUNPCKHPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VUNPCKHPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VUNPCKHPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VUNPCKHPD" (:CPUID-FLAG :AVX))))
    (#x16 ((:VEX :256 :F3 :0F :WIG)
	   ("VMOVSHDUP" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F3 :0F :WIG)
	   ("VMOVSHDUP" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG (:mod . #b11))
	   ("VMOVLHPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG (:mod . :mem))
	   ("VMOVHPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG (:mod . :mem))
	   ("VMOVHPD" (:CPUID-FLAG :AVX))))
    (#x17 ((:VEX :128 :0F :WIG (:mod . :mem))
	   ("VMOVHPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG (:mod . :mem))
	   ("VMOVHPD" (:CPUID-FLAG :AVX))))
    (#x28 ((:VEX :256 :0F :WIG)
	   ("VMOVAPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VMOVAPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VMOVAPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VMOVAPD" (:CPUID-FLAG :AVX))))
    (#x29 ((:VEX :256 :0F :WIG)
	   ("VMOVAPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VMOVAPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VMOVAPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VMOVAPD" (:CPUID-FLAG :AVX))))
    (#x2A ((:VEX :NDS :LIG :F3 :0F :W1)
	   ("VCVTSI2SS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F3 :0F :W0)
	   ("VCVTSI2SS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :W1)
	   ("VCVTSI2SD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :W0)
	   ("VCVTSI2SD" (:CPUID-FLAG :AVX))))
    (#x2B ((:VEX :256 :0F :WIG (:mod . :mem))
	   ("VMOVNTPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG (:mod . :mem))
	   ("VMOVNTPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG (:mod . :mem))
	   ("VMOVNTPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG (:mod . :mem))
	   ("VMOVNTPD" (:CPUID-FLAG :AVX))))
    (#x2C ((:VEX :LIG :F3 :0F :W1)
	   ("VCVTTSS2SI" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F3 :0F :W0)
	   ("VCVTTSS2SI" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F2 :0F :W1)
	   ("VCVTTSD2SI" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F2 :0F :W0)
	   ("VCVTTSD2SI" (:CPUID-FLAG :AVX))))
    (#x2D ((:VEX :LIG :F3 :0F :W1)
	   ("VCVTSS2SI" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F3 :0F :W0)
	   ("VCVTSS2SI" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F2 :0F :W1)
	   ("VCVTSD2SI" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :F2 :0F :W0)
	   ("VCVTSD2SI" (:CPUID-FLAG :AVX))))
    (#x2E ((:VEX :LIG :0F :WIG)
	   ("VUCOMISS" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :66 :0F :WIG)
	   ("VUCOMISD" (:CPUID-FLAG :AVX))))
    (#x2F ((:VEX :LIG :0F :WIG)
	   ("VCOMISS" (:CPUID-FLAG :AVX)))
	  ((:VEX :LIG :66 :0F :WIG)
	   ("VCOMISD" (:CPUID-FLAG :AVX))))
    (#x41 ((:VEX :L1 :66 :0F :W1 (:mod . #b11))
	   ("KANDD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :0F :W1 (:mod . #b11))
	   ("KANDQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :66 :0F :W0 (:mod . #b11))
	   ("KANDB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :NDS :L1 :0F :W0 (:mod . #b11))
	   ("KANDW" (:CPUID-FLAG :AVX512F))))
    (#x42 ((:VEX :L1 :66 :0F :W1 (:mod . #b11))
	   ("KANDND" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :0F :W1 (:mod . #b11))
	   ("KANDNQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :66 :0F :W0 (:mod . #b11))
	   ("KANDNB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :NDS :L1 :0F :W0 (:mod . #b11))
	   ("KANDNW" (:CPUID-FLAG :AVX512F))))
    (#x44 ((:VEX :L0 :66 :0F :W1 (:mod . #b11))
	   ("KNOTD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :0F :W1 (:mod . #b11))
	   ("KNOTQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F :W0 (:mod . #b11))
	   ("KNOTB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :0F :W0 (:mod . #b11))
	   ("KNOTW" (:CPUID-FLAG :AVX512F))))
    (#x45 ((:VEX :L1 :66 :0F :W1 (:mod . #b11))
	   ("KORD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :0F :W1 (:mod . #b11))
	   ("KORQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :66 :0F :W0 (:mod . #b11))
	   ("KORB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :NDS :L1 :0F :W0 (:mod . #b11))
	   ("KORW" (:CPUID-FLAG :AVX512F))))
    (#x46 ((:VEX :L1 :66 :0F :W1 (:mod . #b11))
	   ("KXNORD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :0F :W1 (:mod . #b11))
	   ("KXNORQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :66 :0F :W0 (:mod . #b11))
	   ("KXNORB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :NDS :L1 :0F :W0 (:mod . #b11))
	   ("KXNORW" (:CPUID-FLAG :AVX512F))))
    (#x47 ((:VEX :L1 :66 :0F :W1 (:mod . #b11))
	   ("KXORD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :0F :W1 (:mod . #b11))
	   ("KXORQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :66 :0F :W0 (:mod . #b11))
	   ("KXORB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :NDS :L1 :0F :W0 (:mod . #b11))
	   ("KXORW" (:CPUID-FLAG :AVX512F))))
    (#x4A ((:VEX :L1 :66 :0F :W1 (:mod . #b11))
	   ("KADDD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :0F :W1 (:mod . #b11))
	   ("KADDQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L1 :66 :0F :W0 (:mod . #b11))
	   ("KADDB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L1 :0F :W0 (:mod . #b11))
	   ("KADDW" (:CPUID-FLAG :AVX512DQ))))
    (#x4B ((:VEX :NDS :L1 :0F :W1 (:mod . #b11))
	   ("KUNPCKDQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :NDS :L1 :0F :W0 (:mod . #b11))
	   ("KUNPCKWD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :NDS :L1 :66 :0F :W0 (:mod . #b11))
	   ("KUNPCKBW" (:CPUID-FLAG :AVX512F))))
    (#x50 ((:VEX :256 :0F :WIG)
	   ("VMOVMSKPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VMOVMSKPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VMOVMSKPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VMOVMSKPD" (:CPUID-FLAG :AVX))))
    (#x51 ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VSQRTSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VSQRTSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :0F :WIG)
	   ("VSQRTPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VSQRTPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VSQRTPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VSQRTPD" (:CPUID-FLAG :AVX))))
    (#x52 ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VRSQRTSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :0F :WIG)
	   ("VRSQRTPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VRSQRTPS" (:CPUID-FLAG :AVX))))
    (#x53 ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VRCPSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :0F :WIG)
	   ("VRCPPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VRCPPS" (:CPUID-FLAG :AVX))))
    (#x54 ((:VEX :NDS :128 :66 :0F)
	   ("VANDPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F)
	   ("VANDPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F)
	   ("VANDPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F)
	   ("VANDPS" (:CPUID-FLAG :AVX))))
    (#x55 ((:VEX :NDS :128 :66 :0F)
	   ("VANDNPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F)
	   ("VANDNPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F)
	   ("VANDNPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F)
	   ("VANDNPS" (:CPUID-FLAG :AVX))))
    (#x56 ((:VEX :NDS :128 :66 :0F)
	   ("VORPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F)
	   ("VORPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F)
	   ("VORPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F)
	   ("VORPS" (:CPUID-FLAG :AVX))))
    (#x57 ((:VEX :NDS :256 :0F :WIG)
	   ("VXORPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VXORPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VXORPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VXORPD" (:CPUID-FLAG :AVX))))
    (#x58 ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VADDSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VADDSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F :WIG)
	   ("VADDPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VADDPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VADDPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VADDPD" (:CPUID-FLAG :AVX))))
    (#x59 ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VMULSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VMULSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F :WIG)
	   ("VMULPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VMULPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VMULPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VMULPD" (:CPUID-FLAG :AVX))))
    (#x5A ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VCVTSS2SD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VCVTSD2SS" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :0F :WIG)
	   ("VCVTPS2PD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VCVTPS2PD" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VCVTPD2PS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VCVTPD2PS" (:CPUID-FLAG :AVX))))
    (#x5B ((:VEX :256 :F3 :0F :WIG)
	   ("VCVTTPS2DQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F3 :0F :WIG)
	   ("VCVTTPS2DQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VCVTPS2DQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VCVTPS2DQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :0F :WIG)
	   ("VCVTDQ2PS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :0F :WIG)
	   ("VCVTDQ2PS" (:CPUID-FLAG :AVX))))
    (#x5C ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VSUBSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VSUBSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F :WIG)
	   ("VSUBPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VSUBPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VSUBPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VSUBPD" (:CPUID-FLAG :AVX))))
    (#x5D ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VMINSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VMINSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F :WIG)
	   ("VMINPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VMINPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VMINPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VMINPD" (:CPUID-FLAG :AVX))))
    (#x5E ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VDIVSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VDIVSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F :WIG)
	   ("VDIVPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VDIVPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VDIVPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VDIVPD" (:CPUID-FLAG :AVX))))
    (#x5F ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VMAXSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VMAXSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F :WIG)
	   ("VMAXPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VMAXPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VMAXPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VMAXPD" (:CPUID-FLAG :AVX))))
    (#x60 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKLBW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKLBW" (:CPUID-FLAG :AVX))))
    (#x61 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKLWD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKLWD" (:CPUID-FLAG :AVX))))
    (#x62 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKLDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKLDQ" (:CPUID-FLAG :AVX))))
    (#x63 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPACKSSWB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPACKSSWB" (:CPUID-FLAG :AVX))))
    (#x64 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPCMPGTB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPCMPGTB" (:CPUID-FLAG :AVX))))
    (#x65 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPCMPGTW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPCMPGTW" (:CPUID-FLAG :AVX))))
    (#x66 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPCMPGTD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPCMPGTD" (:CPUID-FLAG :AVX))))
    (#x67 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPACKUSWB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPACKUSWB" (:CPUID-FLAG :AVX))))
    (#x68 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKHBW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKHBW" (:CPUID-FLAG :AVX))))
    (#x69 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKHWD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKHWD" (:CPUID-FLAG :AVX))))
    (#x6A ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKHDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKHDQ" (:CPUID-FLAG :AVX))))
    (#x6B ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPACKSSDW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPACKSSDW" (:CPUID-FLAG :AVX))))
    (#x6C ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKLQDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKLQDQ" (:CPUID-FLAG :AVX))))
    (#x6D ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKHQDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKHQDQ" (:CPUID-FLAG :AVX))))
    (#x6E ((:VEX :128 :66 :0F :W1)
	   ("VMOVQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :W0)
	   ("VMOVD" (:CPUID-FLAG :AVX))))
    (#x6F ((:VEX :256 :F3 :0F :WIG)
	   ("VMOVDQU" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F3 :0F :WIG)
	   ("VMOVDQU" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VMOVDQA" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VMOVDQA" (:CPUID-FLAG :AVX))))
    (#x70 ((:VEX :256 :F2 :0F :WIG)
	   ("VPSHUFLW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :F2 :0F :WIG)
	   ("VPSHUFLW" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :F3 :0F :WIG)
	   ("VPSHUFHW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :F3 :0F :WIG)
	   ("VPSHUFHW" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VPSHUFD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VPSHUFD" (:CPUID-FLAG :AVX))))
    (#x71 ((:VEX :NDD :256 :66 :0F :WIG (:REG . #x2))
	   ("VPSRLW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDD :128 :66 :0F :WIG (:REG . #x2))
	   ("VPSRLW" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDD :256 :66 :0F :WIG (:REG . #x4))
	   ("VPSRAW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDD :128 :66 :0F :WIG (:REG . #x4))
	   ("VPSRAW" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDD :256 :66 :0F :WIG (:REG . #x6))
	   ("VPSLLW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDD :128 :66 :0F :WIG (:REG . #x6))
	   ("VPSLLW" (:CPUID-FLAG :AVX))))
    (#x72 ((:VEX :0F :NDD :128 :66 :WIG (:reg . 2))
	   ("VPSRLD" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 2))
	   ("VPSRAD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 4))
	   ("VPSRAD" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 4))
	   ("VPSRAVW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :0F :NDD :128 :66 :WIG (:reg . 6))
	   ("VPSLLVW" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 6))
	   ("VPSLLVW" (:CPUID-FLAG :AVX2))))
    (#x73 ((:VEX :NDD :128 :66 :0F :WIG (:REG . #x2))
	   ("VPSRLQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F :NDD :256 :66 :WIG (:REG . #x2))
	   ("VPSRLVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDD :256 :66 :0F :WIG (:REG . #x3))
	   ("VPSRLDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDD :128 :66 :0F :WIG (:REG . #x3))
	   ("VPSRLDQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDD :128 :66 :0F :WIG (:REG . #x6))
	   ("VPSLLQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F :NDD :256 :66 :WIG (:reg . 6))
	   ("VPSLLQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDD :256 :66 :0F :WIG (:REG . #x7))
	   ("VPSLLDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDD :128 :66 :0F :WIG (:REG . #x7))
	   ("VPSLLDQ" (:CPUID-FLAG :AVX))))
    (#x74 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPCMPEQB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPCMPEQB" (:CPUID-FLAG :AVX))))
    (#x75 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPCMPEQW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPCMPEQW" (:CPUID-FLAG :AVX))))
    (#x76 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPCMPEQD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPCMPEQD" (:CPUID-FLAG :AVX))))
    (#x77 ((:VEX :128 :0F :WIG)
	   ("VZEROUPPER" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :0F :WIG)
	   ("VZEROALL" (:CPUID-FLAG :AVX))))
    (#x7C ((:VEX :NDS :256 :F2 :0F :WIG)
	   ("VHADDPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :F2 :0F :WIG)
	   ("VHADDPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VHADDPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VHADDPD" (:CPUID-FLAG :AVX))))
    (#x7D ((:VEX :NDS :256 :F2 :0F :WIG)
	   ("VHSUBPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :F2 :0F :WIG)
	   ("VHSUBPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VHSUBPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VHSUBPD" (:CPUID-FLAG :AVX))))
    (#x7E ((:VEX :128 :F3 :0F :WIG)
	   ("VMOVQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :W1)
	   ("VMOVQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :W0)
	   ("VMOVD" (:CPUID-FLAG :AVX))))
    (#x7F ((:VEX :256 :F3 :0F :WIG)
	   ("VMOVDQU" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F3 :0F :WIG)
	   ("VMOVDQU" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :66 :0F :WIG)
	   ("VMOVDQA" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VMOVDQA" (:CPUID-FLAG :AVX))))
    (#x90 ((:VEX :L0 :66 :0F :W1)
	   ("KMOVD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :0F :W1)
	   ("KMOVQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F :W0)
	   ("KMOVB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :0F :W0)
	   ("KMOVW" (:CPUID-FLAG :AVX512F))))
    (#x91 ((:VEX :L0 :66 :0F :W1 (:mod . :mem))
	   ("KMOVD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :0F :W1 (:mod . :mem))
	   ("KMOVQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F :W0 (:mod . :mem))
	   ("KMOVB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :0F :W0 (:mod . :mem))
	   ("KMOVW" (:CPUID-FLAG :AVX512F))))
    (#x92 ((:VEX :L0 :F2 :0F :W0 (:mod . #b11))
	   ("KMOVD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :F2 :0F :W1 (:mod . #b11))
	   ("KMOVQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F :W0 (:mod . #b11))
	   ("KMOVB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :0F :W0 (:mod . #b11))
	   ("KMOVW" (:CPUID-FLAG :AVX512F))))
    (#x93 ((:VEX :L0 :F2 :0F :W0 (:mod . #b11))
	   ("KMOVD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :F2 :0F :W1 (:mod . #b11))
	   ("KMOVQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F :W0 (:mod . #b11))
	   ("KMOVB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :0F :W0 (:mod . #b11))
	   ("KMOVW" (:CPUID-FLAG :AVX512F))))
    (#x98 ((:VEX :L0 :66 :0F :W1 (:mod . #b11))
	   ("KORTESTD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :0F :W1 (:mod . #b11))
	   ("KORTESTQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F :W0 (:mod . #b11))
	   ("KORTESTB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :0F :W0 (:mod . #b11))
	   ("KORTESTW" (:CPUID-FLAG :AVX512F))))
    (#x99 ((:VEX :L0 :66 :0F :W1 (:mod . #b11))
	   ("KTESTD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :0F :W1 (:mod . #b11))
	   ("KTESTQ" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F :W0 (:mod . #b11))
	   ("KTESTB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :0F :W0 (:mod . #b11))
	   ("KTESTW" (:CPUID-FLAG :AVX512DQ))))
    (#xAE ((:VEX :LZ :0F :WIG (:REG . #x3))
	   ("VSTMXCSR" (:CPUID-FLAG :AVX)))
	  ((:VEX :LZ :0F :WIG (:REG . #x2))
	   ("VLDMXCSR" (:CPUID-FLAG :AVX))))
    (#xC2 ((:VEX :NDS :LIG :F3 :0F :WIG)
	   ("VCMPSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :LIG :F2 :0F :WIG)
	   ("VCMPSD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :0F :WIG)
	   ("VCMPPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VCMPPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VCMPPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VCMPPD" (:CPUID-FLAG :AVX))))
    (#xC4 ((:VEX :NDS :128 :66 :0F :W0)
	   ("VPINSRW" (:CPUID-FLAG :AVX))))
    (#xC5 ((:VEX :128 :66 :0F :W0)
	   ("VPEXTRW" (:CPUID-FLAG :AVX))))
    (#xC6 ((:VEX :NDS :256 :0F :WIG)
	   ("VSHUFPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :0F :WIG)
	   ("VSHUFPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VSHUFPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VSHUFPD" (:CPUID-FLAG :AVX))))
    (#xD0 ((:VEX :NDS :256 :F2 :0F :WIG)
	   ("VADDSUBPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :F2 :0F :WIG)
	   ("VADDSUBPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VADDSUBPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VADDSUBPD" (:CPUID-FLAG :AVX))))
    (#xD1 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSRLW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSRLW" (:CPUID-FLAG :AVX))))
    (#xD2 ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSRLD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSRLD" (:CPUID-FLAG :AVX2))))
    (#xD3 ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSRLQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSRLQ" (:CPUID-FLAG :AVX2))))
    (#xD4 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPADDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPADDQ" (:CPUID-FLAG :AVX))))
    (#xD5 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPMULLW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPMULLW" (:CPUID-FLAG :AVX))))
    (#xD6 ((:VEX :128 :66 :0F :WIG)
	   ("VMOVQ" (:CPUID-FLAG :AVX))))
    (#xD7 ((:VEX :256 :66 :0F :WIG)
	   ("VPMOVMSKB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VPMOVMSKB" (:CPUID-FLAG :AVX))))
    (#xD8 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBUSB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBUSB" (:CPUID-FLAG :AVX))))
    (#xD9 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBUSW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBUSW" (:CPUID-FLAG :AVX))))
    (#xDA ((:VEX :NDS :128 :66 :0F)
	   ("VPMINUB" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F)
	   ("VPMINUB" (:CPUID-FLAG :AVX))))
    (#xDB ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPAND" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPAND" (:CPUID-FLAG :AVX))))
    (#xDC ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPADDUSB" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPADDUSB" (:CPUID-FLAG :AVX2))))
    (#xDD ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPADDUSW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPADDUSW" (:CPUID-FLAG :AVX))))
    (#xDE ((:VEX :NDS :128 :66 :0F)
	   ("VPMAXUB" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F)
	   ("VPMAXUB" (:CPUID-FLAG :AVX))))
    (#xDF ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPANDN" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPANDN" (:CPUID-FLAG :AVX))))
    (#xE0 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPAVGB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPAVGB" (:CPUID-FLAG :AVX))))
    (#xE1 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSRAW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSRAW" (:CPUID-FLAG :AVX))))
    (#xE2 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSRAD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSRAD" (:CPUID-FLAG :AVX))))
    (#xE3 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPAVGW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPAVGW" (:CPUID-FLAG :AVX))))
    (#xE4 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPMULHUW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPMULHUW" (:CPUID-FLAG :AVX))))
    (#xE5 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPMULHW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPMULHW" (:CPUID-FLAG :AVX))))
    (#xE6 ((:VEX :256 :66 :0F :WIG)
	   ("VCVTTPD2DQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG)
	   ("VCVTTPD2DQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :F2 :0F :WIG)
	   ("VCVTPD2DQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F2 :0F :WIG)
	   ("VCVTPD2DQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :256 :F3 :0F :WIG)
	   ("VCVTDQ2PD" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F3 :0F :WIG)
	   ("VCVTDQ2PD" (:CPUID-FLAG :AVX))))
    (#xE7 ((:VEX :256 :66 :0F :WIG (:mod . :mem))
	   ("VMOVNTDQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F :WIG (:mod . :mem))
	   ("VMOVNTDQ" (:CPUID-FLAG :AVX))))
    (#xE8 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBSB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBSB" (:CPUID-FLAG :AVX))))
    (#xE9 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBSW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBSW" (:CPUID-FLAG :AVX))))
    (#xEA ((:VEX :NDS :128 :66 :0F)
	   ("VPMINSW" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F)
	   ("VPMINSW" (:CPUID-FLAG :AVX))))
    (#xEB ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPOR" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPOR" (:CPUID-FLAG :AVX))))
    (#xEC ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPADDSB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPADDSB" (:CPUID-FLAG :AVX))))
    (#xED ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPADDSW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPADDSW" (:CPUID-FLAG :AVX))))
    (#xEE ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPMAXSW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPMAXSW" (:CPUID-FLAG :AVX))))
    (#xEF ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPXOR" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPXOR" (:CPUID-FLAG :AVX))))
    (#xF0 ((:VEX :256 :F2 :0F :WIG (:mod . :mem))
	   ("VLDDQU" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :F2 :0F :WIG (:mod . :mem))
	   ("VLDDQU" (:CPUID-FLAG :AVX))))
    (#xF1 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSLLW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSLLW" (:CPUID-FLAG :AVX))))
    (#xF2 ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSLLD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSLLD" (:CPUID-FLAG :AVX2))))
    (#xF3 ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSLLQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSLLQ" (:CPUID-FLAG :AVX2))))
    (#xF4 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPMULUDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPMULUDQ" (:CPUID-FLAG :AVX))))
    (#xF5 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPMADDWD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPMADDWD" (:CPUID-FLAG :AVX))))
    (#xF6 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSADBW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSADBW" (:CPUID-FLAG :AVX))))
    (#xF7 ((:VEX :128 :66 :0F :WIG)
	   ("VMASKMOVDQU" (:CPUID-FLAG :AVX))))
    (#xF8 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBB" (:CPUID-FLAG :AVX))))
    (#xF9 ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBW" (:CPUID-FLAG :AVX))))
    (#xFA ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBD" (:CPUID-FLAG :AVX))))
    (#xFB ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBQ" (:CPUID-FLAG :AVX))))
    (#xFC ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPADDB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPADDB" (:CPUID-FLAG :AVX))))
    (#xFD ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPADDW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPADDB" (:CPUID-FLAG :AVX))))
    (#xFE ((:VEX :NDS :256 :66 :0F :WIG)
	   ("VPADDD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F :WIG)
	   ("VPADDD" (:CPUID-FLAG :AVX))))))

(defconst *vex-0F38-op-features*
  '((#x0 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPSHUFB" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPSHUFB" (:CPUID-FLAG :AVX))))
    (#x1 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPHADDW" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPHADDW" (:CPUID-FLAG :AVX))))
    (#x2 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPHADDD" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPHADDD" (:CPUID-FLAG :AVX))))
    (#x3 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPHADDSW" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPHADDSW" (:CPUID-FLAG :AVX))))
    (#x4 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPMADDUBSW" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPMADDUBSW" (:CPUID-FLAG :AVX))))
    (#x5 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPHSUBW" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPHSUBW" (:CPUID-FLAG :AVX))))
    (#x6 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPHSUBD" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPHSUBD" (:CPUID-FLAG :AVX))))
    (#x7 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPHSUBSW" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPHSUBSW" (:CPUID-FLAG :AVX))))
    (#x8 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPSIGNB" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPSIGNB" (:CPUID-FLAG :AVX))))
    (#x9 ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPSIGNW" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPSIGNW" (:CPUID-FLAG :AVX))))
    (#xA ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPSIGND" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPSIGND" (:CPUID-FLAG :AVX))))
    (#xB ((:VEX :NDS :256 :66 :0F38 :WIG)
	  ("VPMULHRSW" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F38 :WIG)
	  ("VPMULHRSW" (:CPUID-FLAG :AVX))))
    (#xC ((:VEX :NDS :256 :66 :0F38 :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX)))
	 ((:VEX :NDS :128 :66 :0F38 :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX))))
    (#xD ((:VEX :NDS :256 :66 :0F38 :W0)
	  ("VPERMILPD" (:CPUID-FLAG :AVX)))
	 ((:VEX :NDS :128 :66 :0F38 :W0)
	  ("VPERMILPD" (:CPUID-FLAG :AVX))))
    (#xE ((:VEX :256 :66 :0F38 :W0)
	  ("VTESTPS" (:CPUID-FLAG :AVX)))
	 ((:VEX :128 :66 :0F38 :W0)
	  ("VTESTPS" (:CPUID-FLAG :AVX))))
    (#xF ((:VEX :256 :66 :0F38 :W0)
	  ("VTESTPD" (:CPUID-FLAG :AVX)))
	 ((:VEX :128 :66 :0F38 :W0)
	  ("VTESTPD" (:CPUID-FLAG :AVX))))
    (#x13 ((:VEX :256 :66 :0F38 :W0)
	   ("VCVTPH2PS" (:CPUID-FLAG :F16C)))
	  ((:VEX :128 :66 :0F38 :W0)
	   ("VCVTPH2PS" (:CPUID-FLAG :F16C))))
    (#x16 ((:VEX :256 :66 :0F38 :W0)
	   ("VPERMPS" (:CPUID-FLAG :AVX2))))
    (#x17 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPTEST" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPTEST" (:CPUID-FLAG :AVX))))
    (#x18 ((:VEX :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VBROADCASTSS" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :W0 (:mod . :mem))
	   ("VBROADCASTSS" (:CPUID-FLAG :AVX2)))
	  ((:VEX :256 :66 :0F38 :W0 (:mod . #b11))
	   ("VBROADCASTSS" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F38 :W0 (:mod . #b11))
	   ("VBROADCASTSS" (:CPUID-FLAG :AVX))))
    (#x19 ((:VEX :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VBROADCASTSD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :256 :66 :0F38 :W0 (:mod . #b11))
	   ("VBROADCASTSD" (:CPUID-FLAG :AVX))))
    (#x1A ((:VEX :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VBROADCASTF128" (:CPUID-FLAG :AVX))))
    (#x1C ((:VEX :256 :66 :0F38 :WIG)
	   ("VPABSB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPABSB" (:CPUID-FLAG :AVX))))
    (#x1D ((:VEX :256 :66 :0F38 :WIG)
	   ("VPABSW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPABSW" (:CPUID-FLAG :AVX))))
    (#x1E ((:VEX :256 :66 :0F38 :WIG)
	   ("VPABSD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPABSD" (:CPUID-FLAG :AVX))))
    (#x20 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXBW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXBW" (:CPUID-FLAG :AVX))))
    (#x21 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXBD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXBD" (:CPUID-FLAG :AVX))))
    (#x22 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXBQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXBQ" (:CPUID-FLAG :AVX))))
    (#x23 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXWD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXWD" (:CPUID-FLAG :AVX))))
    (#x24 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXWQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXWQ" (:CPUID-FLAG :AVX))))
    (#x25 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXDQ" (:CPUID-FLAG :AVX))))
    (#x28 ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMULDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMULDQ" (:CPUID-FLAG :AVX))))
    (#x29 ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPCMPEQQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPCMPEQQ" (:CPUID-FLAG :AVX))))
    (#x2A ((:VEX :256 :66 :0F38 :WIG (:mod . :mem))
	   ("VMOVNTDQA" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG (:mod . :mem))
	   ("VMOVNTDQA" (:CPUID-FLAG :AVX))))
    (#x2B ((:VEX :0F38 :NDS :128 :66)
	   ("VPACKUSDW" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F38 :NDS :256 :66)
	   ("VPACKUSDW" (:CPUID-FLAG :AVX2))))
    (#x2C ((:VEX :NDS :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VMASKMOVPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F38 :W0 (:mod . :mem))
	   ("VMASKMOVPS" (:CPUID-FLAG :AVX))))
    (#x2D ((:VEX :NDS :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VMASKMOVPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F38 :W0 (:mod . :mem))
	   ("VMASKMOVPD" (:CPUID-FLAG :AVX))))
    (#x2E ((:VEX :NDS :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VMASKMOVPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F38 :W0 (:mod . :mem))
	   ("VMASKMOVPS" (:CPUID-FLAG :AVX))))
    (#x2F ((:VEX :NDS :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VMASKMOVPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F38 :W0 (:mod . :mem))
	   ("VMASKMOVPD" (:CPUID-FLAG :AVX))))
    (#x30 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXBW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXBW" (:CPUID-FLAG :AVX))))
    (#x31 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXBD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXBD" (:CPUID-FLAG :AVX))))
    (#x32 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXBQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXBQ" (:CPUID-FLAG :AVX))))
    (#x33 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXWD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXWD" (:CPUID-FLAG :AVX))))
    (#x34 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXWQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXWQ" (:CPUID-FLAG :AVX))))
    (#x35 ((:VEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXDQ" (:CPUID-FLAG :AVX2))))
    (#x36 ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VPERMD" (:CPUID-FLAG :AVX2))))
    (#x37 ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPCMPGTQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPCMPGTQ" (:CPUID-FLAG :AVX))))
    (#x38 ((:VEX :0F38 :NDS :128 :66)
	   ("VPMINSB" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F38 :NDS :256 :66)
	   ("VPMINSB" (:CPUID-FLAG :AVX2))))
    (#x39 ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMINSD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMINSD" (:CPUID-FLAG :AVX))))
    (#x3A ((:VEX :0F38 :NDS :128 :66)
	   ("VPMINUW" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F38 :NDS :256 :66)
	   ("VPMINUW" (:CPUID-FLAG :AVX2))))
    (#x3B ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMINUD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMINUD" (:CPUID-FLAG :AVX))))
    (#x3C ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMAXSB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMAXSB" (:CPUID-FLAG :AVX))))
    (#x3D ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMAXSD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMAXSD" (:CPUID-FLAG :AVX))))
    (#x3E ((:VEX :0F38 :NDS :128 :66)
	   ("VPMAXUW" (:CPUID-FLAG :AVX)))
	  ((:VEX :0F38 :NDS :256 :66)
	   ("VPMAXUW" (:CPUID-FLAG :AVX2))))
    (#x3F ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMAXUD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMAXUD" (:CPUID-FLAG :AVX))))
    (#x40 ((:VEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMULLD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMULLD" (:CPUID-FLAG :AVX))))
    (#x41 ((:VEX :128 :66 :0F38 :WIG)
	   ("VPHMINPOSUW" (:CPUID-FLAG :AVX))))
    (#x45 ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VPSRLVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VPSRLVD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VPSRLVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VPSRLVD" (:CPUID-FLAG :AVX2))))
    (#x46 ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VPSRAVD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VPSRAVD" (:CPUID-FLAG :AVX2))))
    (#x47 ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VPSLLVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VPSLLVD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VPSLLVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VPSLLVD" (:CPUID-FLAG :AVX2))))
    (#x58 ((:VEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTD" (:CPUID-FLAG :AVX2))))
    (#x59 ((:VEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTQ" (:CPUID-FLAG :AVX2))))
    (#x5A ((:VEX :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VBROADCASTI128" (:CPUID-FLAG :AVX2))))
    (#x78 ((:VEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTB" (:CPUID-FLAG :AVX2))))
    (#x79 ((:VEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTW" (:CPUID-FLAG :AVX2))))
    (#x8C ((:VEX :NDS :256 :66 :0F38 :W1 (:mod . :mem))
	   ("VPMASKMOVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W1 (:mod . :mem))
	   ("VPMASKMOVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VPMASKMOVD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W0 (:mod . :mem))
	   ("VPMASKMOVD" (:CPUID-FLAG :AVX2))))
    (#x8E ((:VEX :NDS :256 :66 :0F38 :W1 (:mod . :mem))
	   ("VPMASKMOVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W1 (:mod . :mem))
	   ("VPMASKMOVQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :256 :66 :0F38 :W0 (:mod . :mem))
	   ("VPMASKMOVD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F38 :W0 (:mod . :mem))
	   ("VPMASKMOVD" (:CPUID-FLAG :AVX2))))
    (#x90 ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VPGATHERDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VPGATHERDQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VPGATHERDD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VPGATHERDD" (:CPUID-FLAG :AVX2))))
    (#x91 ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VPGATHERQQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VPGATHERQQ" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VPGATHERQD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VPGATHERQD" (:CPUID-FLAG :AVX2))))
    (#x92 ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VGATHERDPS" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VGATHERDPS" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VGATHERDPD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VGATHERDPD" (:CPUID-FLAG :AVX2))))
    (#x93 ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VGATHERQPS" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VGATHERQPS" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VGATHERQPD" (:CPUID-FLAG :AVX2)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VGATHERQPD" (:CPUID-FLAG :AVX2))))
    (#x96 ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VFMADDSUB132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VFMADDSUB132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VFMADDSUB132PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VFMADDSUB132PD" (:CPUID-FLAG :FMA))))
    (#x97 ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VFMSUBADD132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VFMSUBADD132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VFMSUBADD132PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VFMSUBADD132PD" (:CPUID-FLAG :FMA))))
    (#x98 ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFMADD132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFMADD132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFMADD132PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFMADD132PD" (:CPUID-FLAG :FMA))))
    (#x99 ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMADD132SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMADD132SD" (:CPUID-FLAG :FMA))))
    (#x9A ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFMSUB132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFMSUB132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFMSUB132PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFMSUB132PD" (:CPUID-FLAG :FMA))))
    (#x9B ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMSUB132SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMSUB132SD" (:CPUID-FLAG :FMA))))
    (#x9C ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMADD132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMADD132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMADD132PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMADD132PD" (:CPUID-FLAG :FMA))))
    (#x9D ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMADD132SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMADD132SD" (:CPUID-FLAG :FMA))))
    (#x9E ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMSUB132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMSUB132PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMSUB132PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMSUB132PD" (:CPUID-FLAG :FMA))))
    (#x9F ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMSUB132SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMSUB132SD" (:CPUID-FLAG :FMA))))
    (#xA6 ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VFMADDSUB213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VFMADDSUB213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VFMADDSUB213PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VFMADDSUB213PD" (:CPUID-FLAG :FMA))))
    (#xA7 ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VFMSUBADD213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VFMSUBADD213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VFMSUBADD213PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VFMSUBADD213PD" (:CPUID-FLAG :FMA))))
    (#xA8 ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFMADD213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFMADD213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFMADD213PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFMADD213PD" (:CPUID-FLAG :FMA))))
    (#xA9 ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMADD213SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMADD213SD" (:CPUID-FLAG :FMA))))
    (#xAA ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFMSUB213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFMSUB213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFMSUB213PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFMSUB213PD" (:CPUID-FLAG :FMA))))
    (#xAB ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMSUB213SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMSUB213SD" (:CPUID-FLAG :FMA))))
    (#xAC ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMADD213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMADD213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMADD213PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMADD213PD" (:CPUID-FLAG :FMA))))
    (#xAD ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMADD213SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMADD213SD" (:CPUID-FLAG :FMA))))
    (#xAE ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMSUB213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMSUB213PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMSUB213PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMSUB213PD" (:CPUID-FLAG :FMA))))
    (#xAF ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMSUB213SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMSUB213SD" (:CPUID-FLAG :FMA))))
    (#xB6 ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VFMADDSUB231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VFMADDSUB231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VFMADDSUB231PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VFMADDSUB231PD" (:CPUID-FLAG :FMA))))
    (#xB7 ((:VEX :DDS :256 :66 :0F38 :W0)
	   ("VFMSUBADD231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W0)
	   ("VFMSUBADD231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :256 :66 :0F38 :W1)
	   ("VFMSUBADD231PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :128 :66 :0F38 :W1)
	   ("VFMSUBADD231PD" (:CPUID-FLAG :FMA))))
    (#xB8 ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFMADD231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFMADD231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFMADD231PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFMADD231PD" (:CPUID-FLAG :FMA))))
    (#xB9 ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMADD231SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMADD231SD" (:CPUID-FLAG :FMA))))
    (#xBA ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFMSUB231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFMSUB231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFMSUB231PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFMSUB231PD" (:CPUID-FLAG :FMA))))
    (#xBB ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMSUB231SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMSUB231SD" (:CPUID-FLAG :FMA))))
    (#xBC ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMADD231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMADD231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMADD231PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMADD231PD" (:CPUID-FLAG :FMA))))
    (#xBD ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMADD231SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMADD231SD" (:CPUID-FLAG :FMA))))
    (#xBE ((:VEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMSUB231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMSUB231PS" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMSUB231PD" (:CPUID-FLAG :FMA)))
	  ((:VEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMSUB231PD" (:CPUID-FLAG :FMA))))
    (#xBF ((:VEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMSUB231SS" (:CPUID-FLAG :FMA)))
	  ((:VEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMSUB231SD" (:CPUID-FLAG :FMA))))
    (#xDB ((:VEX :128 :66 :0F38 :WIG)
	   ("VAESIMC" (:CPUID-FLAG :AES :AVX))))
    (#xDC ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VAESENC" (:CPUID-FLAG :AES :AVX))))
    (#xDD ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VAESENCLAST" (:CPUID-FLAG :AES :AVX))))
    (#xDE ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VAESDEC" (:CPUID-FLAG :AES :AVX))))
    (#xDF ((:VEX :NDS :128 :66 :0F38 :WIG)
	   ("VAESDECLAST" (:CPUID-FLAG :AES :AVX))))
    (#xF2 ((:VEX :NDS :LZ :0F38 :W0)
	   ("ANDN" (:CPUID-FLAG :BMI1)))
	  ((:VEX :NDS :LZ :0F38 :W1)
	   ("ANDN" (:CPUID-FLAG :BMI1))))
    (#xF3 ((:VEX :NDD :LZ :0F38 :W1 (:REG . #x1))
	   ("BLSR" (:CPUID-FLAG :BMI1)))
	  ((:VEX :NDD :LZ :0F38 :W0 (:REG . #x1))
	   ("BLSR" (:CPUID-FLAG :BMI1)))
	  ((:VEX :NDD :LZ :0F38 :W1 (:REG . #x2))
	   ("BLSMSK" (:CPUID-FLAG :BMI1)))
	  ((:VEX :NDD :LZ :0F38 :W0 (:REG . #x2))
	   ("BLSMSK" (:CPUID-FLAG :BMI1)))
	  ((:VEX :NDD :LZ :0F38 :W1 (:REG . #x3))
	   ("BLSI" (:CPUID-FLAG :BMI1)))
	  ((:VEX :NDD :LZ :0F38 :W0 (:REG . #x3))
	   ("BLSI" (:CPUID-FLAG :BMI1))))
    (#xF5 ((:VEX :NDS :LZ :F3 :0F38 :W1)
	   ("PEXT" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :F3 :0F38 :W0)
	   ("PEXT" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :F2 :0F38 :W1)
	   ("PDEP" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :F2 :0F38 :W0)
	   ("PDEP" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :0F38 :W1)
	   ("BZHI" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :0F38 :W0)
	   ("BZHI" (:CPUID-FLAG :BMI2))))
    (#xF6 ((:VEX :NDD :LZ :F2 :0F38 :W1)
	   ("MULX" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDD :LZ :F2 :0F38 :W0)
	   ("MULX" (:CPUID-FLAG :BMI2))))
    (#xF7 ((:VEX :NDS :LZ :F2 :0F38 :W1)
	   ("SHRX" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :66 :0F38 :W1)
	   ("SHLX" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :F3 :0F38 :W1)
	   ("SARX" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :F2 :0F38 :W0)
	   ("SHRX" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :66 :0F38 :W0)
	   ("SHLX" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :F3 :0F38 :W0)
	   ("SARX" (:CPUID-FLAG :BMI2)))
	  ((:VEX :NDS :LZ :0F38 :W1)
	   ("BEXTR" (:CPUID-FLAG :BMI1)))
	  ((:VEX :NDS :LZ :0F38 :W0)
	   ("BEXTR" (:CPUID-FLAG :BMI1))))))

(defconst *vex-0F3A-op-features*
  '((#x0 ((:VEX :256 :66 :0F3A :W1)
	  ("VPERMQ" (:CPUID-FLAG :AVX2))))
    (#x1 ((:VEX :256 :66 :0F3A :W1)
	  ("VPERMPD" (:CPUID-FLAG :AVX2))))
    (#x2 ((:VEX :NDS :256 :66 :0F3A :W0)
	  ("VPBLENDD" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F3A :W0)
	  ("VPBLENDD" (:CPUID-FLAG :AVX2))))
    (#x4 ((:VEX :256 :66 :0F3A :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX)))
	 ((:VEX :128 :66 :0F3A :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX))))
    (#x5 ((:VEX :256 :66 :0F3A :W0)
	  ("VPERMILPD" (:CPUID-FLAG :AVX)))
	 ((:VEX :128 :66 :0F3A :W0)
	  ("VPERMILPD" (:CPUID-FLAG :AVX))))
    (#x6 ((:VEX :NDS :256 :66 :0F3A :W0)
	  ("VPERM2F128" (:CPUID-FLAG :AVX))))
    (#x8 ((:VEX :256 :66 :0F3A :WIG)
	  ("VROUNDPS" (:CPUID-FLAG :AVX)))
	 ((:VEX :128 :66 :0F3A :WIG)
	  ("VROUNDPS" (:CPUID-FLAG :AVX))))
    (#x9 ((:VEX :256 :66 :0F3A :WIG)
	  ("VROUNDPD" (:CPUID-FLAG :AVX)))
	 ((:VEX :128 :66 :0F3A :WIG)
	  ("VROUNDPD" (:CPUID-FLAG :AVX))))
    (#xA ((:VEX :NDS :LIG :66 :0F3A :WIG)
	  ("VROUNDSS" (:CPUID-FLAG :AVX))))
    (#xB ((:VEX :NDS :LIG :66 :0F3A :WIG)
	  ("VROUNDSD" (:CPUID-FLAG :AVX))))
    (#xC ((:VEX :NDS :256 :66 :0F3A :WIG)
	  ("VBLENDPS" (:CPUID-FLAG :AVX)))
	 ((:VEX :NDS :128 :66 :0F3A :WIG)
	  ("VBLENDPS" (:CPUID-FLAG :AVX))))
    (#xD ((:VEX :NDS :256 :66 :0F3A :WIG)
	  ("VBLENDPD" (:CPUID-FLAG :AVX)))
	 ((:VEX :NDS :128 :66 :0F3A :WIG)
	  ("VBLENDPD" (:CPUID-FLAG :AVX))))
    (#xE ((:VEX :NDS :256 :66 :0F3A :WIG)
	  ("VPBLENDW" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F3A :WIG)
	  ("VPBLENDW" (:CPUID-FLAG :AVX))))
    (#xF ((:VEX :NDS :256 :66 :0F3A :WIG)
	  ("VPALIGNR" (:CPUID-FLAG :AVX2)))
	 ((:VEX :NDS :128 :66 :0F3A :WIG)
	  ("VPALIGNR" (:CPUID-FLAG :AVX))))
    (#x14 ((:VEX :128 :66 :0F3A :W0)
	   ("VPEXTRB" (:CPUID-FLAG :AVX))))
    (#x15 ((:VEX :128 :66 :0F3A :W0)
	   ("VPEXTRW" (:CPUID-FLAG :AVX))))
    (#x16 ((:VEX :128 :66 :0F3A :W1)
	   ("VPEXTRQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :128 :66 :0F3A :W0)
	   ("VPEXTRD" (:CPUID-FLAG :AVX))))
    (#x17 ((:VEX :128 :66 :0F3A :WIG)
	   ("reg/m32," (:CPUID-FLAG :AVX))))
    (#x18 ((:VEX :NDS :256 :66 :0F3A :W0)
	   ("VINSERTF128" (:CPUID-FLAG :AVX))))
    (#x19 ((:VEX :256 :66 :0F3A :W0)
	   ("xmm1/m128," (:CPUID-FLAG :AVX))))
    (#x1D ((:VEX :256 :66 :0F3A :W0)
	   ("VCVTPS2PH" (:CPUID-FLAG :F16C)))
	  ((:VEX :128 :66 :0F3A :W0)
	   ("VCVTPS2PH" (:CPUID-FLAG :F16C))))
    (#x20 ((:VEX :NDS :128 :66 :0F3A :W0)
	   ("VPINSRB" (:CPUID-FLAG :AVX))))
    (#x21 ((:VEX :NDS :128 :66 :0F3A :WIG)
	   ("VINSERTPS" (:CPUID-FLAG :AVX))))
    (#x22 ((:VEX :NDS :128 :66 :0F3A :W1)
	   ("VPINSRQ" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F3A :W0)
	   ("VPINSRD" (:CPUID-FLAG :AVX))))
    (#x30 ((:VEX :L0 :66 :0F3A :W0 (:mod . #b11))
	   ("KSHIFTRB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :66 :0F3A :W1 (:mod . #b11))
	   ("KSHIFTRW" (:CPUID-FLAG :AVX512F))))
    (#x31 ((:VEX :L0 :66 :0F3A :W0 (:mod . #b11))
	   ("KSHIFTRD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F3A :W1 (:mod . #b11))
	   ("KSHIFTRQ" (:CPUID-FLAG :AVX512BW))))
    (#x32 ((:VEX :L0 :66 :0F3A :W0 (:mod . #b11))
	   ("KSHIFTLB" (:CPUID-FLAG :AVX512DQ)))
	  ((:VEX :L0 :66 :0F3A :W1 (:mod . #b11))
	   ("KSHIFTLW" (:CPUID-FLAG :AVX512F))))
    (#x33 ((:VEX :L0 :66 :0F3A :W0 (:mod . #b11))
	   ("KSHIFTLD" (:CPUID-FLAG :AVX512BW)))
	  ((:VEX :L0 :66 :0F3A :W1 (:mod . #b11))
	   ("KSHIFTLQ" (:CPUID-FLAG :AVX512BW))))
    (#x38 ((:VEX :NDS :256 :66 :0F3A :W0)
	   ("VINSERTI128" (:CPUID-FLAG :AVX2))))
    (#x39 ((:VEX :256 :66 :0F3A :W0)
	   ("xmm1/m128," (:CPUID-FLAG :AVX2))))
    (#x40 ((:VEX :NDS :256 :66 :0F3A :WIG)
	   ("VDPPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F3A :WIG)
	   ("VDPPS" (:CPUID-FLAG :AVX))))
    (#x41 ((:VEX :NDS :128 :66 :0F3A :WIG)
	   ("VDPPD" (:CPUID-FLAG :AVX))))
    (#x42 ((:VEX :NDS :256 :66 :0F3A :WIG)
	   ("VMPSADBW" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F3A :WIG)
	   ("VMPSADBW" (:CPUID-FLAG :AVX))))
    (#x44 ((:VEX :NDS :128 :66 :0F3A :WIG)
	   ("VPCLMULQDQ" (:CPUID-FLAG :PCLMULQDQ :AVX))))
    (#x46 ((:VEX :NDS :256 :66 :0F3A :W0)
	   ("VPERM2I128" (:CPUID-FLAG :AVX2))))
    (#x4A ((:VEX :NDS :256 :66 :0F3A :W0)
	   ("VBLENDVPS" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F3A :W0)
	   ("VBLENDVPS" (:CPUID-FLAG :AVX))))
    (#x4B ((:VEX :NDS :256 :66 :0F3A :W0)
	   ("VBLENDVPD" (:CPUID-FLAG :AVX)))
	  ((:VEX :NDS :128 :66 :0F3A :W0)
	   ("VBLENDVPD" (:CPUID-FLAG :AVX))))
    (#x4C ((:VEX :NDS :256 :66 :0F3A :W0)
	   ("VPBLENDVB" (:CPUID-FLAG :AVX2)))
	  ((:VEX :NDS :128 :66 :0F3A :W0)
	   ("VPBLENDVB" (:CPUID-FLAG :AVX))))
    (#x60 ((:VEX :0F3A :128 :66)
	   ("VPCMPESTRM" (:CPUID-FLAG :AVX))))
    (#x61 ((:VEX :0F3A :128 :66)
	   ("VPCMPESTRI" (:CPUID-FLAG :AVX))))
    (#x62 ((:VEX :128 :66 :0F3A :WIG)
	   ("VPCMPISTRM" (:CPUID-FLAG :AVX))))
    (#x63 ((:VEX :128 :66 :0F3A :WIG)
	   ("VPCMPISTRI" (:CPUID-FLAG :AVX))))
    (#xDF ((:VEX :128 :66 :0F3A :WIG)
	   ("VAESKEYGENASSIST" (:CPUID-FLAG :AES :AVX))))
    (#xF0 ((:VEX :LZ :F2 :0F3A :W1)
	   ("RORX" (:CPUID-FLAG :BMI2)))
	  ((:VEX :LZ :F2 :0F3A :W0)
	   ("RORX" (:CPUID-FLAG :BMI2))))))

(defconst *evex-0F-op-features*
  '((#x10 ((:EVEX :512 :0F :W0)
	   ("VMOVUPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VMOVUPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VMOVUPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VMOVUPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VMOVUPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVUPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :LIG :F3 :0F :W0)
	   ("VMOVSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VMOVSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W1)
	   ("VMOVSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VMOVSD" (:CPUID-FLAG :AVX512F))))
    (#x11 ((:EVEX :512 :0F :W0)
	   ("VMOVUPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VMOVUPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VMOVUPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VMOVUPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VMOVUPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVUPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :LIG :F3 :0F :W0)
	   ("VMOVSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VMOVSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W1)
	   ("VMOVSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VMOVSD" (:CPUID-FLAG :AVX512F))))
    (#x12 ((:EVEX :512 :F3 :0F :W0)
	   ("VMOVSLDUP" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W0)
	   ("VMOVSLDUP" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W0)
	   ("VMOVSLDUP" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0 (:mod . :mem))
	   ("VMOVLPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VMOVLPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0 (:mod . #b11))
	   ("VMOVHLPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :F2 :0F :W1)
	   ("VMOVDDUP" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F2 :0F :W1)
	   ("VMOVDDUP" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F2 :0F :W1)
	   ("VMOVDDUP" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x13 ((:EVEX :128 :0F :W0)
	   ("VMOVLPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVLPD" (:CPUID-FLAG :AVX512F))))
    (#x14 ((:EVEX :NDS :512 :0F :W0)
	   ("VUNPCKLPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VUNPCKLPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VUNPCKLPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VUNPCKLPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VUNPCKLPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VUNPCKLPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x15 ((:EVEX :NDS :512 :0F :W0)
	   ("VUNPCKHPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VUNPCKHPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VUNPCKHPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VUNPCKHPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VUNPCKHPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VUNPCKHPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x16 ((:EVEX :512 :F3 :0F :W0)
	   ("VMOVSHDUP" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W0)
	   ("VMOVSHDUP" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W0)
	   ("VMOVSHDUP" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0 (:mod . #b11))
	   ("VMOVHLPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0 (:mod . :mem))
	   ("VMOVHPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VMOVHPD" (:CPUID-FLAG :AVX512F))))
    (#x17 ((:EVEX :128 :0F :W0)
	   ("VMOVHPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVHPD" (:CPUID-FLAG :AVX512F))))
    (#x28 ((:EVEX :512 :0F :W0)
	   ("VMOVAPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VMOVAPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VMOVAPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VMOVAPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VMOVAPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVAPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x29 ((:EVEX :512 :0F :W0)
	   ("VMOVAPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VMOVAPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VMOVAPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VMOVAPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VMOVAPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVAPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x2A ((:EVEX :NDS :LIG :F3 :0F :W1)
	   ("VCVTSI2SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VCVTSI2SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VCVTSI2SD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W0)
	   ("VCVTSI2SD" (:CPUID-FLAG :AVX512F))))
    (#x2B ((:EVEX :512 :0F :W0)
	   ("VMOVNTPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VMOVNTPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VMOVNTPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VMOVNTPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VMOVNTPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVNTPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x2C ((:EVEX :LIG :F3 :0F :W1)
	   ("VCVTTSS2SI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F3 :0F :W0)
	   ("VCVTTSS2SI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W1)
	   ("VCVTTSD2SI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W0)
	   ("VCVTTSD2SI" (:CPUID-FLAG :AVX512F))))
    (#x2D ((:EVEX :LIG :F3 :0F :W1)
	   ("VCVTSS2SI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F3 :0F :W0)
	   ("VCVTSS2SI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W1)
	   ("VCVTSD2SI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W0)
	   ("VCVTSD2SI" (:CPUID-FLAG :AVX512F))))
    (#x2E ((:EVEX :LIG :0F :W0)
	   ("VUCOMISS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :66 :0F :W1)
	   ("VUCOMISD" (:CPUID-FLAG :AVX512F))))
    (#x2F ((:EVEX :LIG :0F :W0)
	   ("VCOMISS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :66 :0F :W1)
	   ("VCOMISD" (:CPUID-FLAG :AVX512F))))
    (#x51 ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VSQRTSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VSQRTSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :0F :W0)
	   ("VSQRTPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VSQRTPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VSQRTPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VSQRTPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VSQRTPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VSQRTPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x54 ((:EVEX :NDS :512 :0F :W0)
	   ("VANDPS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VANDPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VANDPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VANDPD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VANDPD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VANDPD" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x55 ((:EVEX :NDS :512 :0F :W0)
	   ("VANDNPS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VANDNPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VANDNPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VANDNPD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VANDNPD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VANDNPD" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x56 ((:EVEX :NDS :512 :0F :W0)
	   ("VORPS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VORPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VORPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VORPD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VORPD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VORPD" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x57 ((:EVEX :NDS :512 :0F :W0)
	   ("VXORPS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VXORPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VXORPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VXORPD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VXORPD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VXORPD" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x58 ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VADDSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VADDSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :0F :W0)
	   ("VADDPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VADDPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VADDPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VADDPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VADDPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VADDPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x59 ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VMULSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VMULSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :0F :W0)
	   ("VMULPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VMULPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VMULPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VMULPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VMULPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VMULPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5A ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VCVTSS2SD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VCVTSD2SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :0F :W0)
	   ("VCVTPS2PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VCVTPS2PD" (:CPUID-FLAG :AVX512VL)))
	  ((:EVEX :128 :0F :W0)
	   ("VCVTPS2PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VCVTPD2PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VCVTPD2PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VCVTPD2PS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5B ((:EVEX :512 :0F :W1)
	   ("VCVTQQ2PS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :0F :W1)
	   ("VCVTQQ2PS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :0F :W1)
	   ("VCVTQQ2PS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :F3 :0F :W0)
	   ("VCVTTPS2DQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W0)
	   ("VCVTTPS2DQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W0)
	   ("VCVTTPS2DQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W0)
	   ("VCVTPS2DQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VCVTPS2DQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VCVTPS2DQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :0F :W0)
	   ("VCVTDQ2PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VCVTDQ2PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VCVTDQ2PS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5C ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VSUBSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VSUBSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :0F :W0)
	   ("VSUBPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VSUBPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VSUBPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VSUBPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VSUBPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VSUBPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5D ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VMINSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VMINSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :0F :W0)
	   ("VMINPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VMINPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VMINPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VMINPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VMINPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VMINPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5E ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VDIVSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VDIVSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :0F :W0)
	   ("VDIVPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VDIVPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VDIVPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VDIVPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VDIVPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VDIVPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5F ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VMAXSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VMAXSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :0F :W0)
	   ("VMAXPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VMAXPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VMAXPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VMAXPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VMAXPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VMAXPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x60 ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKLBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKLBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPUNPCKLBW" (:CPUID-FLAG :AVX512BW))))
    (#x61 ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKLWD" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKLWD" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPUNPCKLWD" (:CPUID-FLAG :AVX512BW))))
    (#x62 ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPUNPCKLDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPUNPCKLDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPUNPCKLDQ" (:CPUID-FLAG :AVX512F))))
    (#x63 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPACKSSWB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPACKSSWB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPACKSSWB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x64 ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPCMPGTB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPCMPGTB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPCMPGTB" (:CPUID-FLAG :AVX512BW))))
    (#x65 ((:EVEX :0F :NDS :128 :66 :WIG)
	   ("VPCMPGTW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :256 :66 :WIG)
	   ("VPCMPGTW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :512 :66 :WIG)
	   ("VPCMPGTW" (:CPUID-FLAG :AVX512BW))))
    (#x66 ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPCMPGTD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPCMPGTD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPCMPGTD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x67 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPACKUSWB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPACKUSWB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPACKUSWB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x68 ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKHBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKHBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPUNPCKHBW" (:CPUID-FLAG :AVX512BW))))
    (#x69 ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPUNPCKHWD" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPUNPCKHWD" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPUNPCKHWD" (:CPUID-FLAG :AVX512BW))))
    (#x6A ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPUNPCKHDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPUNPCKHDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPUNPCKHDQ" (:CPUID-FLAG :AVX512F))))
    (#x6B ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPACKSSDW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPACKSSDW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPACKSSDW" (:CPUID-FLAG :AVX512BW))))
    (#x6C ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPUNPCKLQDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPUNPCKLQDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPUNPCKLQDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x6D ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPUNPCKHQDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPUNPCKHQDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPUNPCKHQDQ" (:CPUID-FLAG :AVX512F))))
    (#x6E ((:EVEX :128 :66 :0F :W1)
	   ("VMOVQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VMOVD" (:CPUID-FLAG :AVX512F))))
    (#x6F ((:EVEX :512 :F3 :0F :W1)
	   ("VMOVDQU64" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W1)
	   ("VMOVDQU64" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W1)
	   ("VMOVDQU64" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F3 :0F :W0)
	   ("VMOVDQU32" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W0)
	   ("VMOVDQU32" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W0)
	   ("VMOVDQU32" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F2 :0F :W1)
	   ("VMOVDQU16" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F2 :0F :W1)
	   ("VMOVDQU16" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F2 :0F :W1)
	   ("VMOVDQU16" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :F2 :0F :W0)
	   ("VMOVDQU8" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F2 :0F :W0)
	   ("VMOVDQU8" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F2 :0F :W0)
	   ("VMOVDQU8" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VMOVDQA64" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VMOVDQA64" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVDQA64" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W0)
	   ("VMOVDQA32" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VMOVDQA32" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VMOVDQA32" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x70 ((:EVEX :512 :F2 :0F :WIG)
	   ("VPSHUFLW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F2 :0F :WIG)
	   ("VPSHUFLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F2 :0F :WIG)
	   ("VPSHUFLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :F3 :0F :WIG)
	   ("VPSHUFHW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F3 :0F :WIG)
	   ("VPSHUFHW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F3 :0F :WIG)
	   ("VPSHUFHW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :66 :0F :W0)
	   ("VPSHUFD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VPSHUFD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VPSHUFD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x71 ((:EVEX :0F :NDD :128 :66 :WIG (:REG . 2))
	   ("VPSRLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :256 :66 :WIG (:REG . 2))
	   ("VPSRLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :512 :66 :WIG (:REG . 2))
	   ("VPSRLW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :0F :NDD :128 :66 :WIG (:REG . 4))
	   ("VPSRAW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :256 :66 :WIG (:REG . 4))
	   ("VPSRAW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :0F :NDD :512 :66 :WIG (:REG . 4))
	   ("VPSRAW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :128 :66 :WIG (:REG . 6))
	   ("VPSLLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :256 :66 :WIG (:REG . 6))
	   ("VPSLLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :512 :66 :WIG (:REG . 6))
	   ("VPSLLW" (:CPUID-FLAG :AVX512BW))))
    (#x72 ((:EVEX :NDD :512 :66 :0F :W1 (:REG . #x0))
	   ("VPRORQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDD :512 :66 :0F :W0 (:REG . #x0))
	   ("VPRORD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDD :256 :66 :0F :W1 (:REG . #x0))
	   ("VPRORQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDD :256 :66 :0F :W0 (:REG . #x0))
	   ("VPRORD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDD :128 :66 :0F :W1 (:REG . #x0))
	   ("VPRORQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDD :128 :66 :0F :W0 (:REG . #x0))
	   ("VPRORD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDD :512 :66 :0F :W1 (:REG . #x1))
	   ("VPROLQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDD :512 :66 :0F :W0 (:REG . #x1))
	   ("VPROLD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDD :256 :66 :0F :W1 (:REG . #x1))
	   ("VPROLQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDD :256 :66 :0F :W0 (:REG . #x1))
	   ("VPROLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDD :128 :66 :0F :W1 (:REG . #x1))
	   ("VPROLQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDD :128 :66 :0F :W0 (:REG . #x1))
	   ("VPROLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :128 :66 :W0 (:REG . 2))
	   ("VPSRLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :256 :66 :W0 (:REG . 2))
	   ("VPSRLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :512 :66 :W0 (:REG . 2))
	   ("VPSRLD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :0F :NDD :128 :66 :W0 (:REG . 4))
	   ("VPSRAD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :128 :66 :W1 (:REG . 4))
	   ("VPSRAD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :256 :66 :W0 (:REG . 4))
	   ("VPSRAD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :256 :66 :W1 (:REG . 4))
	   ("VPSRAD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :512 :66 :W0 (:REG . 4))
	   ("VPSRAD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :0F :NDD :512 :66 :W1 (:REG . 4))
	   ("VPSRAD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :0F :NDD :128 :66 :W0 (:REG . 6))
	   ("VPSLLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :256 :66 :W0 (:REG . 6))
	   ("VPSLLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDD :512 :66 :W0 (:REG . 6))
	   ("VPSLLD" (:CPUID-FLAG :AVX512F))))
    (#x73 ((:EVEX :0F :NDD :128 :66 :W1 (:REG . 2))
	   ("VPSRLQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :256 :66 :W1 (:REG . 2))
	   ("VPSRLQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :512 :66 :W1 (:REG . 2))
	   ("VPSRLQ" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDD :512 :66 :0F :WIG (:REG . #x3))
	   ("VPSRLDQ" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDD :256 :66 :0F :WIG (:REG . #x3))
	   ("VPSRLDQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDD :128 :66 :0F :WIG (:REG . #x3))
	   ("VPSRLDQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :128 :66 :W1 (:REG . 6))
	   ("VPSLLQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :256 :66 :W1 (:REG . 6))
	   ("VPSLLQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDD :512 :66 :W1 (:REG . 6))
	   ("VPSLLQ" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDD :512 :66 :0F :WIG (:REG . #x7))
	   ("VPSLLDQ" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDD :256 :66 :0F :WIG (:REG . #x7))
	   ("VPSLLDQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDD :128 :66 :0F :WIG (:REG . #x7))
	   ("VPSLLDQ" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x74 ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPCMPEQB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPCMPEQB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPCMPEQB" (:CPUID-FLAG :AVX512BW))))
    (#x75 ((:EVEX :0F :NDS :128 :66 :WIG)
	   ("VPCMPEQW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :256 :66 :WIG)
	   ("VPCMPEQW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :512 :66 :WIG)
	   ("VPCMPEQW" (:CPUID-FLAG :AVX512BW))))
    (#x76 ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPCMPEQD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPCMPEQD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPCMPEQD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x78 ((:EVEX :LIG :F3 :0F :W1)
	   ("VCVTTSS2USI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F3 :0F :W0)
	   ("VCVTTSS2USI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W1)
	   ("VCVTTSD2USI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W0)
	   ("VCVTTSD2USI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :66 :0F :W0)
	   ("VCVTTPS2UQQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VCVTTPS2UQQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VCVTTPS2UQQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :0F :W0)
	   ("VCVTTPS2UDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VCVTTPS2UDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VCVTTPS2UDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VCVTTPD2UQQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VCVTTPD2UQQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VCVTTPD2UQQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :0F :W1)
	   ("VCVTTPD2UDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W1)
	   ("VCVTTPD2UDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W1)
	   ("VCVTTPD2UDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x79 ((:EVEX :LIG :F3 :0F :W1)
	   ("VCVTSS2USI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F3 :0F :W0)
	   ("VCVTSS2USI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W1)
	   ("VCVTSD2USI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :LIG :F2 :0F :W0)
	   ("VCVTSD2USI" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :66 :0F :W0)
	   ("VCVTPS2UQQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VCVTPS2UQQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VCVTPS2UQQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :0F :W0)
	   ("VCVTPS2UDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W0)
	   ("VCVTPS2UDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W0)
	   ("VCVTPS2UDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VCVTPD2UQQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VCVTPD2UQQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VCVTPD2UQQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :0F :W1)
	   ("VCVTPD2UDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :0F :W1)
	   ("VCVTPD2UDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :0F :W1)
	   ("VCVTPD2UDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x7A ((:EVEX :512 :F2 :0F :W1)
	   ("VCVTUQQ2PS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :F2 :0F :W1)
	   ("VCVTUQQ2PS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :F2 :0F :W1)
	   ("VCVTUQQ2PS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :F3 :0F :W1)
	   ("VCVTUQQ2PD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :F3 :0F :W1)
	   ("VCVTUQQ2PD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :F3 :0F :W1)
	   ("VCVTUQQ2PD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :F2 :0F :W0)
	   ("VCVTUDQ2PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F2 :0F :W0)
	   ("VCVTUDQ2PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F2 :0F :W0)
	   ("VCVTUDQ2PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F3 :0F :W0)
	   ("VCVTUDQ2PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W0)
	   ("VCVTUDQ2PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W0)
	   ("VCVTUDQ2PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W0)
	   ("VCVTTPS2QQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VCVTTPS2QQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VCVTTPS2QQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VCVTTPD2QQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VCVTTPD2QQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VCVTTPD2QQ" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x7B ((:EVEX :NDS :LIG :F3 :0F :W1)
	   ("VCVTUSI2SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VCVTUSI2SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VCVTUSI2SD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W0)
	   ("VCVTUSI2SD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :66 :0F :W0)
	   ("VCVTPS2QQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VCVTPS2QQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VCVTPS2QQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VCVTPD2QQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VCVTPD2QQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VCVTPD2QQ" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x7E ((:EVEX :128 :F3 :0F :W1)
	   ("VMOVQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VMOVD" (:CPUID-FLAG :AVX512F))))
    (#x7F ((:EVEX :512 :F3 :0F :W1)
	   ("VMOVDQU64" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W1)
	   ("VMOVDQU64" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W1)
	   ("VMOVDQU64" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F3 :0F :W0)
	   ("VMOVDQU32" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W0)
	   ("VMOVDQU32" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W0)
	   ("VMOVDQU32" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F2 :0F :W1)
	   ("VMOVDQU16" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F2 :0F :W1)
	   ("VMOVDQU16" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F2 :0F :W1)
	   ("VMOVDQU16" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :F2 :0F :W0)
	   ("VMOVDQU8" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F2 :0F :W0)
	   ("VMOVDQU8" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F2 :0F :W0)
	   ("VMOVDQU8" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VMOVDQA64" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VMOVDQA64" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VMOVDQA64" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F :W0)
	   ("VMOVDQA32" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VMOVDQA32" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VMOVDQA32" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xC2 ((:EVEX :NDS :LIG :F3 :0F :W0)
	   ("VCMPSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :F2 :0F :W1)
	   ("VCMPSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :0F :W0)
	   ("VCMPPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VCMPPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VCMPPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VCMPPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VCMPPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VCMPPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xC4 ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPINSRW" (:CPUID-FLAG :AVX512BW))))
    (#xC5 ((:EVEX :128 :66 :0F :WIG)
	   ("VPEXTRW" (:CPUID-FLAG :AVX512BW))))
    (#xC6 ((:EVEX :NDS :512 :0F :W0)
	   ("VSHUFPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :0F :W0)
	   ("VSHUFPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :0F :W0)
	   ("VSHUFPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VSHUFPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VSHUFPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VSHUFPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xD1 ((:EVEX :0F :NDS :128 :66 :WIG)
	   ("VPSRLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :256 :66 :WIG)
	   ("VPSRLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :512 :66 :WIG)
	   ("VPSRLW" (:CPUID-FLAG :AVX512BW))))
    (#xD2 ((:EVEX :0F :NDS :128 :66 :W0)
	   ("VPSRLD" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :256 :66 :W0)
	   ("VPSRLD" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :512 :66 :W0)
	   ("VPSRLD" (:CPUID-FLAG :AVX512BW))))
    (#xD3 ((:EVEX :0F :NDS :128 :66 :W1)
	   ("VPSRLQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :256 :66 :W1)
	   ("VPSRLQ" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :512 :66 :W1)
	   ("VPSRLQ" (:CPUID-FLAG :AVX512BW))))
    (#xD4 ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPADDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPADDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPADDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xD5 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPMULLW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPMULLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPMULLW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xD6 ((:EVEX :128 :66 :0F :W1)
	   ("VMOVQ" (:CPUID-FLAG :AVX512F))))
    (#xD8 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPSUBUSB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBUSB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBUSB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xD9 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPSUBUSW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBUSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBUSW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xDA ((:EVEX :0F :NDS :128 :66)
	   ("VPMINUB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :256 :66)
	   ("VPMINUB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :512 :66)
	   ("VPMINUB" (:CPUID-FLAG :AVX512BW))))
    (#xDB ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPANDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPANDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPANDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPANDD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPANDD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPANDD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xDC ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPADDUSB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPADDUSB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPADDUSB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xDD ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPADDUSW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPADDUSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPADDUSW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xDE ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPMAXUB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPMAXUB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPMAXUB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xDF ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPANDNQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPANDNQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPANDNQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPANDND" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPANDND" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPANDND" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xE0 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPAVGB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPAVGB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPAVGB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xE1 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPSRAW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPSRAW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPSRAW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xE2 ((:EVEX :0F :NDS :128 :66 :W0)
	   ("VPSRAD"  (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :256 :66 :W0)
	   ("VPSRAD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :512 :66 :W0)
	   ("VPSRAD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :0F :NDS :128 :66 :W1)
	   ("VPSRAQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :256 :66 :W1)
	   ("VPSRAQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :512 :66 :W1)
	   ("VPSRAQ" (:CPUID-FLAG :AVX512F))))
    (#xE3 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPAVGW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPAVGW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPAVGW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xE4 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPMULHUW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPMULHUW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPMULHUW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xE5 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPMULHW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPMULHW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPMULHW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xE6 ((:EVEX :512 :F3 :0F :W1)
	   ("VCVTQQ2PD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :F3 :0F :W1)
	   ("VCVTQQ2PD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :F3 :0F :W1)
	   ("VCVTQQ2PD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F :W1)
	   ("VCVTTPD2DQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W1)
	   ("VCVTTPD2DQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W1)
	   ("VCVTTPD2DQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F2 :0F :W1)
	   ("VCVTPD2DQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F2 :0F :W1)
	   ("VCVTPD2DQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F2 :0F :W1)
	   ("VCVTPD2DQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F3 :0F :W0)
	   ("VCVTDQ2PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F :W0)
	   ("VCVTDQ2PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F :W0)
	   ("VCVTDQ2PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xE7 ((:EVEX :512 :66 :0F :W0)
	   ("VMOVNTDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F :W0)
	   ("VMOVNTDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F :W0)
	   ("VMOVNTDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xE8 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPSUBSB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBSB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBSB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xE9 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPSUBSW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBSW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xEA ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPMINSW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPMINSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPMINSW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xEB ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPORQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPORQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPORQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPORD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPORD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPORD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xEC ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPADDSB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPADDSB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPADDSB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xED ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPADDSW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPADDSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPADDSW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xEE ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPMAXSW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPMAXSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPMAXSW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xEF ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPXORQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPXORQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPXORQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPXORD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPXORD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPXORD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xF1 ((:EVEX :0F :NDS :128 :66 :WIG)
	   ("VPSLLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :256 :66 :WIG)
	   ("VPSLLW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F :NDS :512 :66 :WIG)
	   ("VPSLLW" (:CPUID-FLAG :AVX512BW))))
    (#xF2 ((:EVEX :0F :NDS :128 :66 :W0)
	   ("VPSLLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :256 :66 :W0)
	   ("VPSLLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :512 :66 :W0)
	   ("VPSLLD" (:CPUID-FLAG :AVX512F))))
    (#xF3 ((:EVEX :0F :NDS :128 :66 :W1)
	   ("VPSLLQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :256 :66 :W1)
	   ("VPSLLQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :512 :66 :W1)
	   ("VPSLLQ" (:CPUID-FLAG :AVX512F))))
    (#xF4 ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPMULUDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPMULUDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPMULUDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xF5 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPMADDWD" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPMADDWD" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPMADDWD" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xF6 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPSADBW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPSADBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPSADBW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xF8 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPSUBB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xF9 ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPSUBW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPSUBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPSUBW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xFA ((:EVEX :0F :NDS :128 :66 :W0)
	   ("VPSUBD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :256 :66 :W0)
	   ("VPSUBD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F :NDS :512 :66 :W0)
	   ("VPSUBD" (:CPUID-FLAG :AVX512F))))
    (#xFB ((:EVEX :NDS :512 :66 :0F :W1)
	   ("VPSUBQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W1)
	   ("VPSUBQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W1)
	   ("VPSUBQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xFC ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPADDB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPADDB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPADDB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xFD ((:EVEX :NDS :512 :66 :0F :WIG)
	   ("VPADDW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F :WIG)
	   ("VPADDW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F :WIG)
	   ("VPADDW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xFE ((:EVEX :NDS :512 :66 :0F :W0)
	   ("VPADDD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F :W0)
	   ("VPADDD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F :W0)
	   ("VPADDD" (:CPUID-FLAG :AVX512VL :AVX512F))))))

(defconst *evex-0F38-op-features*
  '((#x0 ((:EVEX :NDS :512 :66 :0F38 :WIG)
	  ("VPSHUFB" (:CPUID-FLAG :AVX512BW)))
	 ((:EVEX :NDS :256 :66 :0F38 :WIG)
	  ("VPSHUFB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	 ((:EVEX :NDS :128 :66 :0F38 :WIG)
	  ("VPSHUFB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x4 ((:EVEX :NDS :512 :66 :0F38 :WIG)
	  ("VPMADDUBSW" (:CPUID-FLAG :AVX512BW)))
	 ((:EVEX :NDS :256 :66 :0F38 :WIG)
	  ("VPMADDUBSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	 ((:EVEX :NDS :128 :66 :0F38 :WIG)
	  ("VPMADDUBSW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xB ((:EVEX :NDS :512 :66 :0F38 :WIG)
	  ("VPMULHRSW" (:CPUID-FLAG :AVX512BW)))
	 ((:EVEX :NDS :256 :66 :0F38 :WIG)
	  ("VPMULHRSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	 ((:EVEX :NDS :128 :66 :0F38 :WIG)
	  ("VPMULHRSW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#xC ((:EVEX :NDS :512 :66 :0F38 :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :NDS :256 :66 :0F38 :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :NDS :128 :66 :0F38 :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xD ((:EVEX :NDS :512 :66 :0F38 :W1)
	  ("VPERMILPD" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :NDS :256 :66 :0F38 :W1)
	  ("VPERMILPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :NDS :128 :66 :0F38 :W1)
	  ("VPERMILPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x10 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPSRLVW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPSRLVW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPSRLVW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVUSWB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVUSWB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVUSWB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x11 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPSRAVW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPSRAVW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPSRAVW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVUSDB" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVUSDB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVUSDB" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x12 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPSLLVW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPSLLVW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPSLLVW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVUSQB" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVUSQB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVUSQB" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x13 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVUSDW" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVUSDW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVUSDW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VCVTPH2PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VCVTPH2PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VCVTPH2PS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x14 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPRORVQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPRORVD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPRORVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPRORVD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPRORVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPRORVD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVUSQW" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVUSQW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVUSQW" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x15 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPROLVQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPROLVD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPROLVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPROLVD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPROLVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPROLVD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVUSQD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVUSQD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVUSQD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x16 ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPERMPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPERMPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPERMPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPERMPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x18 ((:EVEX :512 :66 :0F38 :W0)
	   ("VBROADCASTSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VBROADCASTSS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VBROADCASTSS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x19 ((:EVEX :512 :66 :0F38 :W0)
	   ("VBROADCASTF32X2" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VBROADCASTF32X2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("VBROADCASTSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VBROADCASTSD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x1A ((:EVEX :512 :66 :0F38 :W1)
	   ("VBROADCASTF64X2" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VBROADCASTF64X2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VBROADCASTF32X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VBROADCASTF32X4" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x1B ((:EVEX :512 :66 :0F38 :W1)
	   ("VBROADCASTF64X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VBROADCASTF32X8" (:CPUID-FLAG :AVX512DQ))))
    (#x1C ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPABSB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPABSB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPABSB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x1D ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPABSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPABSW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPABSW" (:CPUID-FLAG :AVX512BW))))
    (#x1E ((:EVEX :0F38 :128 :66 :W0)
	   ("VPABSD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F38 :256 :66 :W0)
	   ("VPABSD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F38 :512 :66 :W1)
	   ("VPABSD" (:CPUID-FLAG :AVX512F))))
    (#x1F ((:EVEX :0F38 :128 :66 :W1)
	   ("VPABSQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F38 :256 :66 :W1)
	   ("VPABSQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :0F38 :512 :66 :W1)
	   ("VPABSQ" (:CPUID-FLAG :AVX512F))))
    (#x20 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVSWB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVSWB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVSWB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVSXBW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXBW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x21 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVSDB" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVSDB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVSDB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVSXBD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXBD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXBD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x22 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVSQB" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVSQB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVSQB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVSXBQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXBQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXBQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x23 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVSDW" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVSDW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVSDW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVSXWD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXWD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXWD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x24 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVSQW" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVSQW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVSQW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVSXWQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVSXWQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVSXWQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x25 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVSQD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVSQD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVSQD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPMOVSXDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPMOVSXDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPMOVSXDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x26 ((:EVEX :NDS :512 :F3 :0F38 :W1)
	   ("VPTESTNMW" (:CPUID-FLAG :AVX512F :AVX512BW)))
	  ((:EVEX :NDS :256 :F3 :0F38 :W1)
	   ("VPTESTNMW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :F3 :0F38 :W1)
	   ("VPTESTNMW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :F3 :0F38 :W0)
	   ("VPTESTNMB" (:CPUID-FLAG :AVX512F :AVX512BW)))
	  ((:EVEX :NDS :256 :F3 :0F38 :W0)
	   ("VPTESTNMB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :F3 :0F38 :W0)
	   ("VPTESTNMB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPTESTMW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPTESTMW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPTESTMW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPTESTMB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPTESTMB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPTESTMB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x27 ((:EVEX :NDS :512 :F3 :0F38 :W1)
	   ("VPTESTNMQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :F3 :0F38 :W1)
	   ("VPTESTNMQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :F3 :0F38 :W1)
	   ("VPTESTNMQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :F3 :0F38 :W0)
	   ("VPTESTNMD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :F3 :0F38 :W0)
	   ("VPTESTNMD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :F3 :0F38 :W0)
	   ("VPTESTNMD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPTESTMQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPTESTMQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPTESTMQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPTESTMD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPTESTMD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPTESTMD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x28 ((:EVEX :512 :F3 :0F38 :W1)
	   ("VPMOVM2W" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F3 :0F38 :W1)
	   ("VPMOVM2W" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F3 :0F38 :W1)
	   ("VPMOVM2W" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVM2B" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVM2B" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVM2B" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPMULDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPMULDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPMULDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x29 ((:EVEX :512 :F3 :0F38 :W1)
	   ("VPMOVW2M" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F3 :0F38 :W1)
	   ("VPMOVW2M" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F3 :0F38 :W1)
	   ("VPMOVW2M" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVB2M" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVB2M" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVB2M" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPCMPEQQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPCMPEQQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPCMPEQQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x2A ((:EVEX :512 :F3 :0F38 :W1)
	   ("VPBROADCASTMB2Q" (:CPUID-FLAG :AVX512CD)))
	  ((:EVEX :256 :F3 :0F38 :W1)
	   ("VPBROADCASTMB2Q" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :128 :F3 :0F38 :W1)
	   ("VPBROADCASTMB2Q" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VMOVNTDQA" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VMOVNTDQA" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VMOVNTDQA" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x2B ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPACKUSDW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPACKUSDW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPACKUSDW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x2C ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VSCALEFPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VSCALEFPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VSCALEFPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VSCALEFPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VSCALEFPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VSCALEFPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x2D ((:EVEX :NDS :LIG :66 :0F38 :W0)
	   ("VSCALEFSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :66 :0F38 :W1)
	   ("VSCALEFSD" (:CPUID-FLAG :AVX512F))))
    (#x30 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVWB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVWB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVWB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVZXBW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :0F38 :128 :66)
	   ("VPMOVZXBW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x31 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVDB" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVDB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVDB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVZXBD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXBD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXBD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x32 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVQB" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVQB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVQB" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVZXBQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXBQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXBQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x33 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVDW" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVDW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVDW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVZXWD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXWD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXWD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x34 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVQW" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVQW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVQW" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :WIG)
	   ("VPMOVZXWQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :WIG)
	   ("VPMOVZXWQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :WIG)
	   ("VPMOVZXWQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x35 ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVQD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVQD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVQD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPMOVZXDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPMOVZXDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPMOVZXDQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x36 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPERMQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPERMQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPERMD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPERMD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x37 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPCMPGTQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPCMPGTQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPCMPGTQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x38 ((:EVEX :512 :F3 :0F38 :W1)
	   ("VPMOVM2Q" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :F3 :0F38 :W1)
	   ("VPMOVM2Q" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :F3 :0F38 :W1)
	   ("VPMOVM2Q" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVM2D" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVM2D" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVM2D" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F38 :WIG)
	   ("VPMINSB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMINSB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMINSB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x39 ((:EVEX :512 :F3 :0F38 :W1)
	   ("VPMOVQ2M" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :F3 :0F38 :W1)
	   ("VPMOVQ2M" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :F3 :0F38 :W1)
	   ("VPMOVQ2M" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPMOVD2M" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPMOVD2M" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPMOVD2M" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPMINSQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPMINSQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPMINSQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPMINSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPMINSD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPMINSD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x3A ((:EVEX :512 :F3 :0F38 :W0)
	   ("VPBROADCASTMW2D" (:CPUID-FLAG :AVX512CD)))
	  ((:EVEX :256 :F3 :0F38 :W0)
	   ("VPBROADCASTMW2D" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :128 :F3 :0F38 :W0)
	   ("VPBROADCASTMW2D" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :0F38 :NDS :128 :66)
	   ("VPMINUW" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :0F38 :NDS :256 :66)
	   ("VPMINUW" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :0F38 :NDS :512 :66)
	   ("VPMINUW" (:CPUID-FLAG :AVX512CD))))
    (#x3B ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPMINUQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPMINUQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPMINUQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPMINUD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPMINUD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPMINUD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x3C ((:EVEX :NDS :512 :66 :0F38 :WIG)
	   ("VPMAXSB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMAXSB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMAXSB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x3D ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPMAXSQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPMAXSQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPMAXSQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPMAXSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPMAXSD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPMAXSD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x3E ((:EVEX :NDS :512 :66 :0F38 :WIG)
	   ("VPMAXUW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :WIG)
	   ("VPMAXUW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :WIG)
	   ("VPMAXUW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x3F ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPMAXUQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPMAXUQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPMAXUQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPMAXUD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPMAXUD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPMAXUD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x40 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPMULLQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPMULLQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPMULLQ" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPMULLD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPMULLD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPMULLD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x42 ((:EVEX :512 :66 :0F38 :W0)
	   ("VGETEXPPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VGETEXPPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VGETEXPPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("VGETEXPPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VGETEXPPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VGETEXPPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x43 ((:EVEX :NDS :LIG :66 :0F38 :W0)
	   ("VGETEXPSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :66 :0F38 :W1)
	   ("VGETEXPSD" (:CPUID-FLAG :AVX512F))))
    (#x44 ((:EVEX :512 :66 :0F38 :W1)
	   ("VPLZCNTQ" (:CPUID-FLAG :AVX512CD)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPLZCNTQ" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPLZCNTQ" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPLZCNTD" (:CPUID-FLAG :AVX512CD)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPLZCNTD" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPLZCNTD" (:CPUID-FLAG :AVX512VL :AVX512CD))))
    (#x45 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPSRLVQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPSRLVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPSRLVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPSRLVD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPSRLVD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPSRLVD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x46 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPSRAVQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPSRAVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPSRAVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPSRAVD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPSRAVD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPSRAVD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x47 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPSLLVQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPSLLVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPSLLVQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPSLLVD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPSLLVD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPSLLVD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x4C ((:EVEX :512 :66 :0F38 :W0)
	   ("VRCP14PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VRCP14PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VRCP14PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("VRCP14PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VRCP14PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VRCP14PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x4D ((:EVEX :NDS :LIG :66 :0F38 :W0)
	   ("VRCP14SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :66 :0F38 :W1)
	   ("VRCP14SD" (:CPUID-FLAG :AVX512F))))
    (#x4E ((:EVEX :512 :66 :0F38 :W0)
	   ("VRSQRT14PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VRSQRT14PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VRSQRT14PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("VRSQRT14PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VRSQRT14PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VRSQRT14PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x4F ((:EVEX :NDS :LIG :66 :0F38 :W0)
	   ("VRSQRT14SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :66 :0F38 :W1)
	   ("VRSQRT14SD" (:CPUID-FLAG :AVX512F))))
    (#x52 ((:EVEX :DDS :512 :F2 :0F38 :W0)
	   ("VP4DPWSSD" (:CPUID-FLAG :AVX512_4VNNIW))))
    (#x53 ((:EVEX :DDS :512 :F2 :0F38 :W0)
	   ("VP4DPWSSDS" (:CPUID-FLAG :AVX512_4VNNIW))))
    (#x58 ((:EVEX :512 :66 :0F38 :W0)
	   ("VPBROADCASTD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x59 ((:EVEX :512 :66 :0F38 :W0)
	   ("VBROADCASTI32x2" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VBROADCASTI32x2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VBROADCASTI32x2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("VPBROADCASTQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPBROADCASTQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPBROADCASTQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5A ((:EVEX :512 :66 :0F38 :W1)
	   ("VBROADCASTI64X2" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VBROADCASTI64X2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VBROADCASTI32X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VBROADCASTI32X4" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5B ((:EVEX :512 :66 :0F38 :W1)
	   ("VBROADCASTI64X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VBROADCASTI32X8" (:CPUID-FLAG :AVX512DQ))))
    (#x64 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPBLENDMQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPBLENDMQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPBLENDMQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPBLENDMD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPBLENDMD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPBLENDMD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x65 ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VBLENDMPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VBLENDMPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VBLENDMPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VBLENDMPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VBLENDMPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VBLENDMPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x66 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPBLENDMW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPBLENDMW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPBLENDMW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPBLENDMB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPBLENDMB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPBLENDMB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x75 ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VPERMI2W" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VPERMI2W" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VPERMI2W" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VPERMI2B" (:CPUID-FLAG :AVX512_VBMI)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VPERMI2B" (:CPUID-FLAG :AVX512VL :AVX512_VBMI)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VPERMI2B" (:CPUID-FLAG :AVX512VL :AVX512_VBMI))))
    (#x76 ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VPERMI2Q" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VPERMI2Q" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VPERMI2Q" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VPERMI2D" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VPERMI2D" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VPERMI2D" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x77 ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VPERMI2PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VPERMI2PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VPERMI2PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VPERMI2PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VPERMI2PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VPERMI2PS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x78 ((:EVEX :512 :66 :0F38 :W0)
	   ("VPBROADCASTB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x79 ((:EVEX :512 :66 :0F38 :W0)
	   ("VPBROADCASTW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x7A ((:EVEX :512 :66 :0F38 :W0)
	   ("VPBROADCASTB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x7B ((:EVEX :512 :66 :0F38 :W0)
	   ("VPBROADCASTW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x7C ((:EVEX :512 :66 :0F38 :W1)
	   ("VPBROADCASTQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPBROADCASTQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPBROADCASTQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPBROADCASTD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPBROADCASTD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPBROADCASTD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x7D ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VPERMT2W" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VPERMT2W" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VPERMT2W" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPERMT2B" (:CPUID-FLAG :AVX512_VBMI)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPERMT2B" (:CPUID-FLAG :AVX512VL :AVX512_VBMI)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VPERMT2B" (:CPUID-FLAG :AVX512VL :AVX512_VBMI))))
    (#x7E ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VPERMT2Q" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VPERMT2Q" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VPERMT2Q" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VPERMT2D" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VPERMT2D" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VPERMT2D" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x7F ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VPERMT2PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VPERMT2PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VPERMT2PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VPERMT2PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VPERMT2PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VPERMT2PS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x83 ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPMULTISHIFTQB" (:CPUID-FLAG :AVX512_VBMI)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPMULTISHIFTQB" (:CPUID-FLAG :AVX512_VBMI :AVX512VL)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPMULTISHIFTQB" (:CPUID-FLAG :AVX512_VBMI :AVX512VL))))
    (#x88 ((:EVEX :512 :66 :0F38 :W0)
	   ("zmm1" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("ymm1" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("xmm1" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("zmm1" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("ymm1" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("xmm1" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x89 ((:EVEX :512 :66 :0F38 :W1)
	   ("VPEXPANDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPEXPANDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPEXPANDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPEXPANDD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPEXPANDD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPEXPANDD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x8A ((:EVEX :512 :66 :0F38 :W0)
	   ("VCOMPRESSPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VCOMPRESSPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VCOMPRESSPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("VCOMPRESSPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VCOMPRESSPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VCOMPRESSPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x8B ((:EVEX :512 :66 :0F38 :W1)
	   ("VPCOMPRESSQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPCOMPRESSQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPCOMPRESSQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPCOMPRESSD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPCOMPRESSD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPCOMPRESSD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x8D ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VPERMW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VPERMW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VPERMW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VPERMB" (:CPUID-FLAG :AVX512_VBMI)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VPERMB" (:CPUID-FLAG :AVX512VL :AVX512_VBMI)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VPERMB" (:CPUID-FLAG :AVX512VL :AVX512_VBMI))))
    (#x90 ((:EVEX :512 :66 :0F38 :W1)
	   ("VPGATHERDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPGATHERDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPGATHERDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPGATHERDD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPGATHERDD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPGATHERDD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x91 ((:EVEX :512 :66 :0F38 :W1)
	   ("VPGATHERQQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPGATHERQQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPGATHERQQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPGATHERQD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPGATHERQD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPGATHERQD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x92 ((:EVEX :512 :66 :0F38 :W1)
	   ("VGATHERDPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VGATHERDPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VGATHERDPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VGATHERDPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VGATHERDPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VGATHERDPS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x93 ((:EVEX :512 :66 :0F38 :W1)
	   ("VGATHERQPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VGATHERQPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VGATHERQPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VGATHERQPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VGATHERQPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VGATHERQPS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x96 ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VFMADDSUB132PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VFMADDSUB132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VFMADDSUB132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VFMADDSUB132PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VFMADDSUB132PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VFMADDSUB132PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x97 ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VFMSUBADD132PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VFMSUBADD132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VFMSUBADD132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VFMSUBADD132PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VFMSUBADD132PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VFMSUBADD132PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x98 ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFMADD132PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFMADD132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFMADD132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFMADD132PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFMADD132PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFMADD132PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x99 ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMADD132SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMADD132SD" (:CPUID-FLAG :AVX512F))))
    (#x9A ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFMSUB132PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFMSUB132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFMSUB132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFMSUB132PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFMSUB132PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFMSUB132PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :F2 :0F38 :W0)
	   ("V4FMADDPS" (:CPUID-FLAG :AVX512_4FMAPS))))
    (#x9B ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMSUB132SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMSUB132SD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :F2 :0F38 :W0 :LIG)
	   ("V4FMADDSS" (:CPUID-FLAG :AVX512_4FMAPS))))
    (#x9C ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFNMADD132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMADD132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMADD132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFNMADD132PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMADD132PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMADD132PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x9D ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMADD132SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMADD132SD" (:CPUID-FLAG :AVX512F))))
    (#x9E ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFNMSUB132PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMSUB132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMSUB132PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFNMSUB132PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMSUB132PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMSUB132PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x9F ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMSUB132SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMSUB132SD" (:CPUID-FLAG :AVX512F))))
    (#xA0 ((:EVEX :512 :66 :0F38 :W1)
	   ("VPSCATTERDQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPSCATTERDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPSCATTERDQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPSCATTERDD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPSCATTERDD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPSCATTERDD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xA1 ((:EVEX :512 :66 :0F38 :W1)
	   ("VPSCATTERQQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPSCATTERQQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPSCATTERQQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPSCATTERQD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPSCATTERQD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPSCATTERQD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xA2 ((:EVEX :512 :66 :0F38 :W1)
	   ("VSCATTERDPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VSCATTERDPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VSCATTERDPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VSCATTERDPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VSCATTERDPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VSCATTERDPS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xA3 ((:EVEX :512 :66 :0F38 :W1)
	   ("VSCATTERQPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VSCATTERQPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VSCATTERQPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VSCATTERQPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VSCATTERQPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VSCATTERQPS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xA6 ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VFMADDSUB213PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VFMADDSUB213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VFMADDSUB213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VFMADDSUB213PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VFMADDSUB213PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VFMADDSUB213PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xA7 ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VFMSUBADD213PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VFMSUBADD213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VFMSUBADD213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VFMSUBADD213PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VFMSUBADD213PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VFMSUBADD213PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xA8 ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFMADD213PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFMADD213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFMADD213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFMADD213PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFMADD213PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFMADD213PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xA9 ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMADD213SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMADD213SD" (:CPUID-FLAG :AVX512F))))
    (#xAA ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFMSUB213PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFMSUB213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFMSUB213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFMSUB213PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFMSUB213PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFMSUB213PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :F2 :0F38 :W0)
	   ("V4FNMADDPS" (:CPUID-FLAG :AVX512_4FMAPS))))
    (#xAB ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMSUB213SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMSUB213SD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :F2 :0F38 :W0 :LIG)
	   ("V4FNMADDSS" (:CPUID-FLAG :AVX512_4FMAPS))))
    (#xAC ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFNMADD213PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMADD213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMADD213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFNMADD213PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMADD213PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMADD213PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xAD ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMADD213SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMADD213SD" (:CPUID-FLAG :AVX512F))))
    (#xAE ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFNMSUB213PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMSUB213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMSUB213PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFNMSUB213PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMSUB213PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMSUB213PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xAF ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMSUB213SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMSUB213SD" (:CPUID-FLAG :AVX512F))))
    (#xB4 ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VPMADD52LUQ" (:CPUID-FLAG :AVX512_IFMA)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VPMADD52LUQ" (:CPUID-FLAG :AVX512_IFMA :AVX512VL)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VPMADD52LUQ" (:CPUID-FLAG :AVX512_IFMA :AVX512VL))))
    (#xB5 ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VPMADD52HUQ" (:CPUID-FLAG :AVX512_IFMA)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VPMADD52HUQ" (:CPUID-FLAG :AVX512_IFMA :AVX512VL)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VPMADD52HUQ" (:CPUID-FLAG :AVX512_IFMA :AVX512VL))))
    (#xB6 ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VFMADDSUB231PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VFMADDSUB231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VFMADDSUB231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VFMADDSUB231PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VFMADDSUB231PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VFMADDSUB231PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xB7 ((:EVEX :DDS :512 :66 :0F38 :W0)
	   ("VFMSUBADD231PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W0)
	   ("VFMSUBADD231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W0)
	   ("VFMSUBADD231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F38 :W1)
	   ("VFMSUBADD231PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F38 :W1)
	   ("VFMSUBADD231PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F38 :W1)
	   ("VFMSUBADD231PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xB8 ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFMADD231PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFMADD231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFMADD231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFMADD231PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFMADD231PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFMADD231PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xB9 ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMADD231SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMADD231SD" (:CPUID-FLAG :AVX512F))))
    (#xBA ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFMSUB231PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFMSUB231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFMSUB231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFMSUB231PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFMSUB231PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFMSUB231PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xBB ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFMSUB231SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFMSUB231SD" (:CPUID-FLAG :AVX512F))))
    (#xBC ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFNMADD231PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMADD231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMADD231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFNMADD231PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMADD231PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMADD231PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xBD ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMADD231SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMADD231SD" (:CPUID-FLAG :AVX512F))))
    (#xBE ((:EVEX :NDS :512 :66 :0F38 :W0)
	   ("VFNMSUB231PS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W0)
	   ("VFNMSUB231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W0)
	   ("VFNMSUB231PS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F38 :W1)
	   ("VFNMSUB231PD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F38 :W1)
	   ("VFNMSUB231PD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F38 :W1)
	   ("VFNMSUB231PD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xBF ((:EVEX :DDS :LIG :66 :0F38 :W0)
	   ("VFNMSUB231SS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :LIG :66 :0F38 :W1)
	   ("VFNMSUB231SD" (:CPUID-FLAG :AVX512F))))
    (#xC4 ((:EVEX :512 :66 :0F38 :W1)
	   ("VPCONFLICTQ" (:CPUID-FLAG :AVX512CD)))
	  ((:EVEX :256 :66 :0F38 :W1)
	   ("VPCONFLICTQ" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :128 :66 :0F38 :W1)
	   ("VPCONFLICTQ" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :512 :66 :0F38 :W0)
	   ("VPCONFLICTD" (:CPUID-FLAG :AVX512CD)))
	  ((:EVEX :256 :66 :0F38 :W0)
	   ("VPCONFLICTD" (:CPUID-FLAG :AVX512VL :AVX512CD)))
	  ((:EVEX :128 :66 :0F38 :W0)
	   ("VPCONFLICTD" (:CPUID-FLAG :AVX512VL :AVX512CD))))
    (#xC6 ((:EVEX :512 :66 :0F38 :W1 (:REG . #x6))
	   ("VSCATTERPF1DPD" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W0 (:REG . #x6))
	   ("VSCATTERPF1DPS" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W1 (:REG . #x5))
	   ("VSCATTERPF0DPD" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W0 (:REG . #x5))
	   ("VSCATTERPF0DPS" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W1 (:REG . #x2))
	   ("VGATHERPF1DPD" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W0 (:REG . #x2))
	   ("VGATHERPF1DPS" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W1 (:REG . #x1))
	   ("VGATHERPF0DPD" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W0 (:REG . #x1))
	   ("VGATHERPF0DPS" (:CPUID-FLAG :AVX512PF))))
    (#xC7 ((:EVEX :512 :66 :0F38 :W1 (:REG . #x6))
	   ("VSCATTERPF1QPD" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W0 (:REG . #x6))
	   ("VSCATTERPF1QPS" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W1 (:REG . #x5))
	   ("VSCATTERPF0QPD" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W0 (:REG . #x5))
	   ("VSCATTERPF0QPS" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W1 (:REG . #x2))
	   ("VGATHERPF1QPD" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W0 (:REG . #x2))
	   ("VGATHERPF1QPS" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W1 (:REG . #x1))
	   ("VGATHERPF0QPD" (:CPUID-FLAG :AVX512PF)))
	  ((:EVEX :512 :66 :0F38 :W0 (:REG . #x1))
	   ("VGATHERPF0QPS" (:CPUID-FLAG :AVX512PF))))
    (#xC8 ((:EVEX :512 :66 :0F38 :W0)
	   ("zmm1" (:CPUID-FLAG :AVX512ER)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("zmm1" (:CPUID-FLAG :AVX512ER))))
    (#xCA ((:EVEX :512 :66 :0F38 :W0)
	   ("VRCP28PS" (:CPUID-FLAG :AVX512ER)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("VRCP28PD" (:CPUID-FLAG :AVX512ER))))
    (#xCB ((:EVEX :NDS :LIG :66 :0F38 :W0)
	   ("VRCP28SS" (:CPUID-FLAG :AVX512ER)))
	  ((:EVEX :NDS :LIG :66 :0F38 :W1)
	   ("VRCP28SD" (:CPUID-FLAG :AVX512ER))))
    (#xCC ((:EVEX :512 :66 :0F38 :W0)
	   ("VRSQRT28PS" (:CPUID-FLAG :AVX512ER)))
	  ((:EVEX :512 :66 :0F38 :W1)
	   ("VRSQRT28PD" (:CPUID-FLAG :AVX512ER))))
    (#xCD ((:EVEX :NDS :LIG :66 :0F38 :W0)
	   ("VRSQRT28SS" (:CPUID-FLAG :AVX512ER)))
	  ((:EVEX :NDS :LIG :66 :0F38 :W1)
	   ("VRSQRT28SD" (:CPUID-FLAG :AVX512ER))))))

(defconst *evex-0F3A-op-features*
  '((#x0 ((:EVEX :512 :66 :0F3A :W1)
	  ("VPERMQ" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :256 :66 :0F3A :W1)
	  ("VPERMQ" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x1 ((:EVEX :512 :66 :0F3A :W1)
	  ("VPERMPD" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :256 :66 :0F3A :W1)
	  ("VPERMPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x3 ((:EVEX :NDS :512 :66 :0F3A :W1)
	  ("VALIGNQ" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :NDS :512 :66 :0F3A :W0)
	  ("VALIGND" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :NDS :256 :66 :0F3A :W1)
	  ("VALIGNQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :NDS :256 :66 :0F3A :W0)
	  ("VALIGND" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :NDS :128 :66 :0F3A :W1)
	  ("VALIGNQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :NDS :128 :66 :0F3A :W0)
	  ("VALIGND" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x4 ((:EVEX :512 :66 :0F3A :W0)
	  ("ibVPERMILPS" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :256 :66 :0F3A :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :128 :66 :0F3A :W0)
	  ("VPERMILPS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x5 ((:EVEX :512 :66 :0F3A :W1)
	  ("VPERMILPD" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :256 :66 :0F3A :W1)
	  ("VPERMILPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :128 :66 :0F3A :W1)
	  ("VPERMILPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x8 ((:EVEX :512 :66 :0F3A :W0)
	  ("VRNDSCALEPS" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :256 :66 :0F3A :W0)
	  ("VRNDSCALEPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :128 :66 :0F3A :W0)
	  ("VRNDSCALEPS" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x9 ((:EVEX :512 :66 :0F3A :W1)
	  ("VRNDSCALEPD" (:CPUID-FLAG :AVX512F)))
	 ((:EVEX :256 :66 :0F3A :W1)
	  ("VRNDSCALEPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	 ((:EVEX :128 :66 :0F3A :W1)
	  ("VRNDSCALEPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#xA ((:EVEX :NDS :LIG :66 :0F3A :W0)
	  ("VRNDSCALESS" (:CPUID-FLAG :AVX512F))))
    (#xB ((:EVEX :NDS :LIG :66 :0F3A :W1)
	  ("VRNDSCALESD" (:CPUID-FLAG :AVX512F))))
    (#xF ((:EVEX :NDS :512 :66 :0F3A :WIG)
	  ("VPALIGNR" (:CPUID-FLAG :AVX512BW)))
	 ((:EVEX :NDS :256 :66 :0F3A :WIG)
	  ("VPALIGNR" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	 ((:EVEX :NDS :128 :66 :0F3A :WIG)
	  ("VPALIGNR" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x14 ((:EVEX :128 :66 :0F3A :WIG)
	   ("VPEXTRB" (:CPUID-FLAG :AVX512BW))))
    (#x15 ((:EVEX :128 :66 :0F3A :WIG)
	   ("VPEXTRW" (:CPUID-FLAG :AVX512BW))))
    (#x16 ((:EVEX :128 :66 :0F3A :W1)
	   ("VPEXTRQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :128 :66 :0F3A :W0)
	   ("VPEXTRD" (:CPUID-FLAG :AVX512DQ))))
    (#x17 ((:EVEX :128 :66 :0F3A :WIG)
	   ("VEXTRACTPS" (:CPUID-FLAG :AVX512F))))
    (#x18 ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VINSERTF64X2" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VINSERTF64X2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VINSERTF32X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VINSERTF32X4" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x19 ((:EVEX :512 :66 :0F3A :W1)
	   ("VEXTRACTF64X2" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F3A :W1)
	   ("VEXTRACTF64X2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F3A :W0)
	   ("VEXTRACTF32X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F3A :W0)
	   ("VEXTRACTF32X4" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x1A ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VINSERTF64X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VINSERTF32X8" (:CPUID-FLAG :AVX512DQ))))
    (#x1B ((:EVEX :512 :66 :0F3A :W1)
	   ("VEXTRACTF64X2" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :66 :0F3A :W0)
	   ("VEXTRACTF32x4" (:CPUID-FLAG :AVX512DQ))))
    (#x1D ((:EVEX :512 :66 :0F3A :W0)
	   ("VCVTPS2PH" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F3A :W0)
	   ("VCVTPS2PH" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F3A :W0)
	   ("VCVTPS2PH" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x1E ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VPCMPUQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VPCMPUQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F3A :W1)
	   ("VPCMPUQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VPCMPUD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VPCMPUD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VPCMPUD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x1F ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VPCMPQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VPCMPQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F3A :W1)
	   ("VPCMPQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VPCMPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VPCMPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VPCMPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x20 ((:EVEX :NDS :128 :66 :0F3A :WIG)
	   ("VPINSRB" (:CPUID-FLAG :AVX512BW))))
    (#x21 ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VINSERTPS" (:CPUID-FLAG :AVX512F))))
    (#x22 ((:EVEX :NDS :128 :66 :0F3A :W1)
	   ("VPINSRQ" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VPINSRD" (:CPUID-FLAG :AVX512DQ))))
    (#x23 ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VSHUFF64x2" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VSHUFF64X2" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VSHUFF32x4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VSHUFF32X4" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x25 ((:EVEX :DDS :512 :66 :0F3A :W1)
	   ("VPTERNLOGQ" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F3A :W1)
	   ("VPTERNLOGQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F3A :W1)
	   ("VPTERNLOGQ" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :512 :66 :0F3A :W0)
	   ("VPTERNLOGD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :DDS :256 :66 :0F3A :W0)
	   ("VPTERNLOGD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :DDS :128 :66 :0F3A :W0)
	   ("VPTERNLOGD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x26 ((:EVEX :512 :66 :0F3A :W0)
	   ("VGETMANTPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F3A :W0)
	   ("VGETMANTPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F3A :W0)
	   ("VGETMANTPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :512 :66 :0F3A :W1)
	   ("VGETMANTPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F3A :W1)
	   ("VGETMANTPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :128 :66 :0F3A :W1)
	   ("VGETMANTPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x27 ((:EVEX :NDS :LIG :66 :0F3A :W0)
	   ("VGETMANTSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :66 :0F3A :W1)
	   ("VGETMANTSD" (:CPUID-FLAG :AVX512F))))
    (#x38 ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VINSERTI64X2" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VINSERTI64X2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VINSERTI32X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VINSERTI32X4" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x39 ((:EVEX :512 :66 :0F3A :W1)
	   ("VEXTRACTI64X2" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F3A :W1)
	   ("VEXTRACTI64X2" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F3A :W0)
	   ("VEXTRACTI32x4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :256 :66 :0F3A :W0)
	   ("VEXTRACTI32X4" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x3A ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VINSERTI64X4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VINSERTI32X8" (:CPUID-FLAG :AVX512DQ))))
    (#x3B ((:EVEX :512 :66 :0F3A :W1)
	   ("VEXTRACTI64x2" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :512 :66 :0F3A :W0)
	   ("VEXTRACTI32x4" (:CPUID-FLAG :AVX512DQ))))
    (#x3E ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VPCMPUW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F3A :W1)
	   ("VPCMPUW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VPCMPUB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VPCMPUB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VPCMPUB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x3F ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VPCMPW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VPCMPW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F3A :W1)
	   ("VPCMPW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VPCMPB" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VPCMPB" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VPCMPB" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x42 ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VDBPSADBW" (:CPUID-FLAG :AVX512BW)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VDBPSADBW" (:CPUID-FLAG :AVX512VL :AVX512BW)))
	  ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VDBPSADBW" (:CPUID-FLAG :AVX512VL :AVX512BW))))
    (#x43 ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VSHUFI64x2" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VSHUFI64X2" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VSHUFI32x4" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VSHUFI32X4" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x50 ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VRANGEPS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VRANGEPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VRANGEPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VRANGEPD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VRANGEPD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :NDS :128 :66 :0F3A :W1)
	   ("VRANGEPD" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x51 ((:EVEX :NDS :LIG :66 :0F3A :W0)
	   ("VRANGESS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :LIG :66 :0F3A :W1)
	   ("VRANGESD" (:CPUID-FLAG :AVX512DQ))))
    (#x54 ((:EVEX :NDS :512 :66 :0F3A :W0)
	   ("VFIXUPIMMPS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W0)
	   ("VFIXUPIMMPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F3A :W0)
	   ("VFIXUPIMMPS" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :512 :66 :0F3A :W1)
	   ("VFIXUPIMMPD" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :256 :66 :0F3A :W1)
	   ("VFIXUPIMMPD" (:CPUID-FLAG :AVX512VL :AVX512F)))
	  ((:EVEX :NDS :128 :66 :0F3A :W1)
	   ("VFIXUPIMMPD" (:CPUID-FLAG :AVX512VL :AVX512F))))
    (#x55 ((:EVEX :NDS :LIG :66 :0F3A :W0)
	   ("VFIXUPIMMSS" (:CPUID-FLAG :AVX512F)))
	  ((:EVEX :NDS :LIG :66 :0F3A :W1)
	   ("VFIXUPIMMSD" (:CPUID-FLAG :AVX512F))))
    (#x56 ((:EVEX :512 :66 :0F3A :W0)
	   ("VREDUCEPS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F3A :W0)
	   ("VREDUCEPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F3A :W0)
	   ("VREDUCEPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F3A :W1)
	   ("VREDUCEPD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F3A :W1)
	   ("VREDUCEPD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F3A :W1)
	   ("VREDUCEPD" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x57 ((:EVEX :NDS :LIG :66 :0F3A :W0)
	   ("VREDUCESS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :NDS :LIG :66 :0F3A :W1)
	   ("VREDUCESD" (:CPUID-FLAG :AVX512DQ))))
    (#x66 ((:EVEX :512 :66 :0F3A :W0)
	   ("VFPCLASSPS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F3A :W0)
	   ("VFPCLASSPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F3A :W0)
	   ("VFPCLASSPS" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :512 :66 :0F3A :W1)
	   ("VFPCLASSPD" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :256 :66 :0F3A :W1)
	   ("VFPCLASSPD" (:CPUID-FLAG :AVX512VL :AVX512DQ)))
	  ((:EVEX :128 :66 :0F3A :W1)
	   ("VFPCLASSPD" (:CPUID-FLAG :AVX512VL :AVX512DQ))))
    (#x67 ((:EVEX :LIG :66 :0F3A :W0)
	   ("VFPCLASSSS" (:CPUID-FLAG :AVX512DQ)))
	  ((:EVEX :LIG :66 :0F3A :W1)
	   ("VFPCLASSSD" (:CPUID-FLAG :AVX512DQ))))))

(define avx-op-features-data-p (x)
  :enabled t
  (and (consp x)
       (consp (cdr x))
       (null (cddr x)) ;; 2-entry list
       (stringp (car x))
       (true-listp (cadr x))
       (consp (cadr x))
       (eq (car (cadr x)) :CPUID-FLAG)))

(define avx-op-features-elem-p (x)
  :enabled t
  (and (consp x)
       (consp (cdr x))
       (null (cddr x)) ;; 2-entry list
       (true-listp (car x))
       (avx-op-features-data-p (cadr x))))

(define avx-op-features-cell-p (x)
  :enabled t
  (or (null x)
      (and (consp x)
	   (consp (car x))
	   (avx-op-features-elem-p (car x))
	   (avx-op-features-cell-p (cdr x)))))

(define avx-op-features-map-p (x)
  :short "Are the VEX/EVEX feature maps well-formed?"
  :enabled t
  (or (null x)
      (and (consp x)
	   (consp (car x))
	   (natp (caar x)) ;; opcode
	   (avx-op-features-cell-p (cdar x))
	   (avx-op-features-map-p (cdr x)))))

(local
 (define perm-memberp ((e true-listp) (x true-list-listp))
   ;; (perm-memberp '(:a :b :c) '((:e :f :d) (:c :b :a))) = T
   ;; (perm-memberp '(:a :b :c) '((:e :f :d) (:c :b :x))) = NIL
   (if (endp x)
       nil
     (if (equal (acl2::merge-sort-lexorder e)
		(acl2::merge-sort-lexorder (car x)))
	 t
       (perm-memberp e (cdr x))))))

(local
 (define perm-subsetp ((a true-list-listp) (b true-list-listp))
   ;; Given two lists A and B like the following:
   ;; A = '((:a :b :c) (:d :e :f))
   ;; and
   ;; B = '((:e :f :d) (:c :b :a))
   ;; we return t if each element of A is a permutation of some element of B.
   (if (endp a)
       t
     (if (perm-memberp (car a) b)
	 (perm-subsetp (cdr a) b)
       (cw "~% ~p0 not a perm-subsetp of ~p1 ~%"
	   (car a) b)))))

(local
 (define avx-opcode-variants-ok-p ((map-a true-list-listp)
				   (map-b true-list-listp))
   ;; Are all the variants of each opcode in both the maps same?  We can
   ;; tolerate a different order of prefix-listing within each variant and a
   ;; different order of variant-listing within each opcode.
   (if (endp map-a)
       t
     (b* ((op-a (car map-a))
	  (op-b (car map-b))
	  (opcode-a (car op-a))
	  (opcode-b (car op-b))
	  ((unless (equal opcode-a opcode-b))
	   (cw "~% Opcodes ~p0 and ~p1 not equal! ~%"
	       opcode-a opcode-b))
	  (variants-a (cdr op-a))
	  (variants-b (cdr op-b)))
       (and (if (and (equal (len variants-a) (len variants-b))
		     (alistp variants-a)
		     (alistp variants-b)
		     (true-list-listp (strip-cars variants-a))
		     (true-list-listp (strip-cars variants-b))
		     (perm-subsetp (strip-cars variants-a) (strip-cars variants-b)))
		(avx-opcode-variants-ok-p (cdr map-a) (cdr map-b))
	      (b* ((- (cw "~% Problem in opcode: ~s0 ~%" (str::hexify opcode-a)))
		   (- (cw "~% variants-a:~%~p0 ~%"
			  variants-a))
		   (- (cw "~% variants-b:~%~p0 ~%"
			  variants-b)))
		nil)))))))

(local
 (defthm vex-op-features-maps-well-formed
   (and (avx-op-features-map-p *vex-0F-op-features*)
	(avx-op-features-map-p *vex-0F38-op-features*)
	(avx-op-features-map-p *vex-0F3A-op-features*)
	;; Check that the opcodes listed in the features map match those in the
	;; original map.
	(equal (strip-cars *vex-0F-op-features*)
	       (strip-cars *vex-0F-opcodes*))
	(equal (strip-cars *vex-0F38-op-features*)
	       (strip-cars *vex-0F38-opcodes*))
	(equal (strip-cars *vex-0F3A-op-features*)
	       (strip-cars *vex-0F3A-opcodes*))
	;; Check that the variants within each opcode in the features map match
	;; those in the original map.
	(avx-opcode-variants-ok-p
	 *vex-0F-opcodes* *vex-0F-op-features*)
	(avx-opcode-variants-ok-p
	 *vex-0F38-opcodes* *vex-0F38-op-features*)
	(avx-opcode-variants-ok-p
	 *vex-0F3A-opcodes* *vex-0F3A-op-features*))))

(local
 (defthm evex-op-features-maps-well-formed
   (and (avx-op-features-map-p *evex-0F-op-features*)
	(avx-op-features-map-p *evex-0F38-op-features*)
	(avx-op-features-map-p *evex-0F3A-op-features*)
	;; Check that the opcodes listed in the features map match those in the
	;; original map.
	(equal (strip-cars *evex-0F-op-features*)
	       (strip-cars *evex-0F-opcodes*))
	(equal (strip-cars *evex-0F38-op-features*)
	       (strip-cars *evex-0F38-opcodes*))
	(equal (strip-cars *evex-0F3A-op-features*)
	       (strip-cars *evex-0F3A-opcodes*))
	;; Check that the variants within each opcode in the features map match
	;; those in the original map.
	(avx-opcode-variants-ok-p
	 *evex-0F-opcodes* *evex-0F-op-features*)
	(avx-opcode-variants-ok-p
	 *evex-0F38-opcodes* *evex-0F38-op-features*)
	(avx-opcode-variants-ok-p
	 *evex-0F3A-opcodes* *evex-0F3A-op-features*))))

;; ----------------------------------------------------------------------

;; Some interesting resources related to x86 ISA instruction encoding:

;; -- http://www.sandpile.org/x86/opc_enc.htm

;; -- https://www.strchr.com/machine_code_redundancy

;; -- http://www.mlsite.net/blog/?p=76

;; -- http://www.mlsite.net/8086/#tbl_map1 --- this corresponds to
;;    Intel Manuals v24319102, which date back to 1999
;;    (http://datasheets.chipdb.org/Intel/x86/Intel%20Architecture/24319102.pdf).

;; ----------------------------------------------------------------------
