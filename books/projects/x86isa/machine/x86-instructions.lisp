;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "instructions-spec/arith-and-logic"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "instructions-spec/shifts-and-rotates"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "instructions-spec/multiplication"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "instructions-spec/division"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "instructions-spec/floating-point"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; All the instruction decoding and spec functions will be added to
;; this ruleset automatically if def-inst is used to define these
;; functions.
(def-ruleset instruction-decoding-and-spec-rules nil)

;; ======================================================================

(defsection x86-instructions
  :parents (machine)
  )

(defsection one-byte-opcodes
  :parents (x86-instructions)
  )

(defsection two-byte-opcodes
  :parents (x86-instructions)
  )

(defsection fp-opcodes
  :parents (x86-instructions)
  )

(defsection privileged-opcodes
  :parents (x86-instructions)
  )

(defsection x86-instruction-semantics
  :parents (x86-instructions)
  :short "Instruction Semantic Functions"
  :long "<p>The instruction semantic functions have dual roles:</p>

<ol>
 <li>They fetch the instruction's operands, as dictated by the decoded
  components of the instruction \(like the prefixes, SIB byte, etc.\)
  provided as input; these decoded components are provided by our x86
  decoder function @(see x86-fetch-decode-execute).</li>

<li> They contain or act as the functional specification of the
instructions.  For e.g., the functional specification function of the
ADD instruction returns two values: the appropriately truncated sum of
the operands and the modified flags. We do not deal with the x86 state
in these specifications.</li>
</ol>"
  )

;; ======================================================================
;; INSTRUCTIONS: (one-byte opcode map)
;; add, adc, sub, sbb, or, and, sub, xor, cmp, test
;; ======================================================================

(def-inst x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G

  :parents (one-byte-opcodes)

  :short "Operand Fetch and Execute for ADD, ADC, SUB, SBB, OR, AND,
  XOR, CMP, TEST: Addressing Mode = \(E,G\)"

  :long "<h3>Op/En = MR: \[OP R/M, REG\] or \[OP E G\]</h3>

  <p>where @('E') is the destination operand and @('G') is the source
  operand.  Note that @('E') stands for a general-purpose register or
  memory operand specified by the @('ModRM.r/m') field, and @('G')
  stands for a general-purpose register specified by the
  @('ModRM.reg') field.</p>

  \[OP R/M, REG\]  Flags Affected<br/>
  00, 01: ADD    c p a z s o<br/>
  08, 09: OR       p   z s   \(o and c cleared, a undefined\)<br/>
  10, 11: ADC    c p a z s o<br/>
  18, 19: SBB    c p a z s o<br/>
  20, 21: AND      p   z s   \(o and c cleared, a undefined\)<br/>
  28, 29: SUB    c p a z s o<br/>
  30, 31: XOR      p   z s   \(o and c cleared, a undefined\)<br/>
  38, 39: CMP    c p a z s o<br/>
  84, 85: TEST     p   z s   \(o and c cleared, a undefined\)<br/>"

  :operation t
  :guard-debug t
  :returns (x86 x86p :hyp (x86p x86))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'ADD #x00 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'ADD #x01 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'OR #x08 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'OR #x09 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'ADC #x10 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'ADC #x11 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'SBB #x18 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'SBB #x19 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'AND #x20 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'AND #x21 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'SUB #x28 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'SUB #x29 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'XOR #x30 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'XOR #x31 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'CMP #x38 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'CMP #x39 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'TEST #x84 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
    (add-to-implemented-opcodes-table 'TEST #x85 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G))

  :body

  (b* ((ctx 'x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock? (eql #.*lock*
		   (prefixes-slice :group-1-prefix prefixes)))
       ((when (and lock? (eql operation #.*OP-CMP*)))
	;; CMP does not allow a LOCK prefix.
	(!!ms-fresh :lock-prefix prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (byte-operand? (eql 0 (the (unsigned-byte 1)
			       (logand 1 opcode))))
       ((the (integer 1 8) operand-size)
	(select-operand-size byte-operand? rex-byte nil prefixes))

       (G (rgfi-size operand-size
		     (the (unsigned-byte 4)
		       (reg-index reg rex-byte #.*r*))
		     rex-byte x86))

       (p4? (eql #.*addr-size-override*
		 (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0 E (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) E-addr)
	    x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* operand-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Everything above this point is just further decoding the
       ;; instruction and fetching operands.

       ;; Instruction Specification:

       ;; Computing the flags and the result:
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv result
	    (the (unsigned-byte 32) output-rflags)
	    (the (unsigned-byte 32) undefined-flags))
	(gpr-arith/logic-spec operand-size operation E G input-rflags))

       ;; Updating the x86 state with the result and eflags.
       ((mv flg1 x86)
	(if (or (eql operation #.*OP-CMP*)
		(eql operation #.*OP-TEST*))
	    ;; CMP and TEST modify just the flags.
	    (mv nil x86)
	  (x86-operand-to-reg/mem
	   operand-size result
	   (the (signed-byte #.*max-linear-address-size*) E-addr)
	   rex-byte r/m mod x86)))
       ;; Note: If flg1 is non-nil, we bail out without changing the
       ;; x86 state.
       ((when flg1)
	(!!ms-fresh :x86-operand-to-reg/mem flg1))

       (x86 (write-user-rflags output-rflags undefined-flags x86))
       (x86 (!rip temp-rip x86)))

      x86))

(def-inst x86-add/adc/sub/sbb/or/and/xor/cmp-G-E

  :parents (one-byte-opcodes)

  :short "Operand Fetch and Execute for ADD, ADC, SUB, SBB, OR, AND,
  XOR, CMP: Addressing Mode = \(G,E\)"

  :long "<h3>Op/En = RM: \[OP REG, R/M\] or \[OP G, E\]</h3>

  <p>where @('G') is the destination operand and @('E') is the source
  operand.  Note that @('G') stands for a general-purpose register
  specified by the @('ModRM.reg') field, and @('E') stands for a
  general-purpose register or memory operand specified by the
  @('ModRM.r/m') field.</p>

  \[OP REG, R/M\]  Flags Affected<br/>
  02, 03: ADD   c p a z s o<br/>
  0A, 0B: OR      p   z s   \(o and c cleared, a undefined\) <br/>
  12, 13: ADC   c p a z s o<br/>
  1A, 1B: SBB   c p a z s o<br/>
  22, 23: AND     p   z s   \(o and c cleared, a undefined\) <br/>
  2A, 2B: SUB   c p a z s o<br/>
  32, 33: XOR     p   z s   \(o and c cleared, a undefined\) <br/>
  3A, 3B: CMP   c p a z s o <br/>"

  :operation t
  :guard (not (equal operation #.*OP-TEST*))

  :returns (x86 x86p :hyp (x86p x86))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'ADD #x02 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'ADD #x03 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'OR #x0A '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'OR #x0B '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'ADC #x12 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'ADC #x13 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'SBB #x1A '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'SBB #x1B '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'AND #x22 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'AND #x23 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'SUB #x2A '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'SUB #x2B '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'XOR #x32 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'XOR #x33 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'CMP #x3A '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
    (add-to-implemented-opcodes-table 'CMP #x3B '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E))

  :body

  (b* ((ctx 'x86-add/adc/sub/sbb/or/and/xor/cmp-G-E)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock*
		  (prefixes-slice :group-1-prefix prefixes)))
       ((when (and lock (eql operation #.*OP-CMP*)))
	;; CMP does not allow a LOCK prefix.
	(!!ms-fresh :lock-prefix prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (byte-operand? (eql 0 (the (unsigned-byte 1)
			       (logand 1 opcode))))
       ((the (integer 1 8) operand-size)
	(select-operand-size byte-operand? rex-byte nil prefixes))

       (G (rgfi-size operand-size
		     (the (unsigned-byte 4)
		       (reg-index reg rex-byte #.*r*))
		     rex-byte x86))

       (p4? (eql #.*addr-size-override*
		 (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0 E (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) E-addr)
	    x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* operand-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Everything above this point is just further decoding the
       ;; instruction and fetching operands.

       ;; Instruction Specification:

       ;; Computing the flags and the result:
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv result
	    (the (unsigned-byte 32) output-rflags)
	    (the (unsigned-byte 32) undefined-flags))
	(gpr-arith/logic-spec operand-size operation G E input-rflags))

       ;; Updating the x86 state with the result and eflags.
       (x86
	(if (eql operation #.*OP-CMP*)
	    ;; CMP modifies the flags only.
	    x86
	  (!rgfi-size operand-size (reg-index reg rex-byte #.*r*) result
		      rex-byte x86)))

       (x86 (write-user-rflags output-rflags undefined-flags x86))

       (x86 (!rip temp-rip x86)))

      x86))

(def-inst x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I

  :parents (one-byte-opcodes)

  :short "Operand Fetch and Execute for ADD, ADC, SUB, SBB, OR, AND,
  XOR, CMP, TEST: Addressing Mode = \(E, I\)"

  :long "<h3>Op/En = MI: \[OP R/M, IMM\] or \[OP E, I\]</h3>

  <p>where @('E') is the destination operand and @('I') is the source
  operand.  Note that @('E') stands for a general-purpose register or
  memory operand specified by the @('ModRM.r/m') field, and @('I')
  stands for immediate data.  All opcodes except those of TEST fall
  under group 1A, and have opcode extensions (ModR/M.reg field), as
  per Table A-6 of the Intel Manuals, Vol. 2.  The opcodes for TEST
  fall under Unary Group 3, and also have opcode extensions.</p>

  \[OP R/M, IMM\]  Flags Affected<br/>
  80-83 (000): ADD   c p a z s o<br/>
  80-83 (001): OR      p   z s   \(o and c cleared, a undefined\)<br/>
  80-83 (010): ADC   c p a z s o<br/>
  80-83 (011): SBB   c p a z s o<br/>
  80-83 (100): AND     p   z s   \(o and c cleared, a undefined\)<br/>
  80-83 (101): SUB   c p a z s o<br/>
  80-83 (110): XOR     p   z s   \(o and c cleared, a undefined\)<br/>
  80-83 (111): CMP   c p a z s o<br/>
  F6-F7 (000): TEST    p   z s   \(o and c cleared, a undefined\)<br/>"

  :operation t
  :guard-hints (("Goal" :in-theory (e/d (n08-to-i08
					 n16-to-i16
					 n32-to-i32
					 n64-to-i64)
					())))

  :returns (x86 x86p :hyp (x86p x86))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'ADD #x80 '(:reg 0)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'ADD #x81 '(:reg 0)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'ADD #x82 '(:reg 0)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'ADD #x83 '(:reg 0)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)

    (add-to-implemented-opcodes-table 'OR #x80 '(:reg 2)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'OR #x81 '(:reg 2)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'OR #x82 '(:reg 2)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'OR #x83 '(:reg 2)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)

    (add-to-implemented-opcodes-table 'ADC #x80 '(:reg 2)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'ADC #x81 '(:reg 2)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'ADC #x82 '(:reg 2)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'ADC #x83 '(:reg 2)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)

    (add-to-implemented-opcodes-table 'SBB #x80 '(:reg 3)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'SBB #x81 '(:reg 3)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'SBB #x82 '(:reg 3)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'SBB #x83 '(:reg 3)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)

    (add-to-implemented-opcodes-table 'AND #x80 '(:reg 4)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'AND #x81 '(:reg 4)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'AND #x82 '(:reg 4)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'AND #x83 '(:reg 4)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)

    (add-to-implemented-opcodes-table 'SUB #x80 '(:reg 5)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'SUB #x81 '(:reg 5)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'SUB #x82 '(:reg 5)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'SUB #x83 '(:reg 5)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)

    (add-to-implemented-opcodes-table 'XOR #x80 '(:reg 6)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'XOR #x81 '(:reg 6)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'XOR #x82 '(:reg 6)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'XOR #x83 '(:reg 6)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)

    (add-to-implemented-opcodes-table 'CMP #x80 '(:reg 7)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'CMP #x81 '(:reg 7)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'CMP #x82 '(:reg 7)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'CMP #x83 '(:reg 7)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)

    (add-to-implemented-opcodes-table 'TEST #xF6 '(:reg 0)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
    (add-to-implemented-opcodes-table 'TEST #xF7 '(:reg 0)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I))

  :body

  (b* ((ctx 'x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (lock? (eql #.*lock*
		   (prefixes-slice :group-1-prefix prefixes)))
       ((when (and lock? (eql operation #.*OP-CMP*)))
	;; CMP does not allow a LOCK prefix.
	(!!ms-fresh :lock-prefix prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (eql #.*addr-size-override*
		 (prefixes-slice :group-4-prefix prefixes)))

       (E-byte-operand? (or (eql opcode #x80)
			    (eql opcode #xF6)))
       ((the (integer 1 8) E-size)
	(select-operand-size E-byte-operand? rex-byte nil
			     prefixes))

       (imm-byte-operand? (or (eql opcode #x80)
			      (eql opcode #x83)
			      (eql opcode #xF6)))
       ((the (integer 1 4) imm-size)
	(select-operand-size imm-byte-operand? rex-byte t prefixes))

       ((mv flg0 E increment-RIP-by
	    (the (signed-byte #.*max-linear-address-size*) E-addr)
	    x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* E-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((mv ?flg1 (the (unsigned-byte 32) imm) x86)
	(rm-size imm-size temp-rip :x x86))
       ((when flg1)
	(!!ms-fresh :rm-size-error flg1))
       ;; Sign-extend imm:
       (imm
	(mbe :logic (loghead (ash E-size 3) (logext (ash imm-size 3) imm))
	     :exec (logand (case E-size
			     (1 #.*2^8-1*)
			     (2 #.*2^16-1*)
			     (4 #.*2^32-1*)
			     (8 #.*2^64-1*)
			     ;; Won't reach here.
			     (t 0))
			   (case imm-size
			     (1 (the (signed-byte 8)
				  (n08-to-i08
				   (the (unsigned-byte 8) imm))))
			     (2 (the (signed-byte 16)
				  (n16-to-i16
				   (the (unsigned-byte 16) imm))))
			     (4 (the (signed-byte 32)
				  (n32-to-i32
				   (the (unsigned-byte 32) imm))))
			     ;; Won't reach here.
			     (t 0)))))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip imm-size))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Everything above this point is just further decoding the
       ;; instruction and fetching operands.

       ;; Instruction Specification:

       ;; Computing the flags and the result:
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv result
	    (the (unsigned-byte 32) output-rflags)
	    (the (unsigned-byte 32) undefined-flags))
	(gpr-arith/logic-spec E-size operation E imm input-rflags))

       ;; Updating the x86 state with the result and eflags.
       ((mv flg1 x86)
	(if (or (eql operation #.*OP-CMP*)
		(eql operation #.*OP-TEST*))
	    ;; CMP and TEST modify just the flags.
	    (mv nil x86)
	  (x86-operand-to-reg/mem
	   E-size result
	   (the (signed-byte #.*max-linear-address-size*) E-addr)
	   rex-byte r/m mod x86)))
       ;; Note: If flg1 is non-nil, we bail out without changing the
       ;; x86 state.
       ((when flg1)
	(!!ms-fresh :x86-operand-to-reg/mem flg1))

       (x86 (write-user-rflags output-rflags undefined-flags x86))
       (x86 (!rip temp-rip x86)))

      x86))

(def-inst x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I
  :parents (one-byte-opcodes)

  :short "Operand Fetch and Execute for ADD, ADC, SUB, SBB, OR, AND,
  XOR, CMP, TEST: Addressing Mode = \(rAX, I\)"

  :long "<h3>Op/En = I: \[OP rAX, IMM\] or \[OP rAX, I\]</h3>

  <p>where @('rAX') is the destination operand and @('I') is the
  source operand.  Note that @('rAX') stands for AL/AX/EAX/RAX,
  depending on the operand size, and @('I') stands for immediate
  data.</p>

  \[OP rAX, IMM\]   Flags Affected<br/>
  04, 05: ADD        c p a z s o<br/>
  0C, 0D: OR           p   z s   \(o and c cleared, a undefined\)<br/>
  14, 15: ADC        c p a z s o<br/>
  1C, 1D: SBB        c p a z s o<br/>
  24, 25: AND          p   z s   \(o and c cleared, a undefined\)<br/>
  2C, 2D: SUB        c p a z s o<br/>
  34, 35: XOR          p   z s   \(o and c cleared, a undefined\)<br/>
  3C, 3D: CMP        c p a z s o<br/>
  A8, A9: TEST         p   z s   \(o and c cleared, a undefined\)<br/>"

  :operation t
  :returns (x86 x86p :hyp (x86p x86))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'ADD #x04 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'ADD #x05 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'OR #x0C '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'OR #x0D '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'ADC #x14 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'ADC #x15 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'SBB #x1C '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'SBB #x1D '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'AND #x24 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'AND #x25 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'SUB #x2C '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'SUB #x2D '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'XOR #x34 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'XOR #x35 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'CMP #x3C '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'CMP #x3D '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'TEST #xA8 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
    (add-to-implemented-opcodes-table 'TEST #xA9 '(:nil nil)
				      'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I))

  :body

  (b* ((ctx 'x86-add/adc/sub/sbb/or/and/xor/cmp-test-rAX-I)
       (lock (eql #.*lock*
		  (prefixes-slice :group-1-prefix prefixes)))
       ((when (and lock (eql operation #.*OP-CMP*)))
	;; CMP does not allow a LOCK prefix.
	(!!ms-fresh :lock-prefix prefixes))

       (byte-operand? (equal 0 (logand 1 opcode)))
       ((the (integer 1 8) operand-size)
	(select-operand-size byte-operand? rex-byte t prefixes))
       (rAX-size (if (logbitp #.*w* rex-byte)
		     8
		   operand-size))
       (rAX (rgfi-size rAX-size *rax* rex-byte x86))
       ((mv ?flg imm x86)
	(rm-size operand-size temp-rip :x x86))
       ((when flg)
	(!!ms-fresh :rm-size-error flg))

       ;; Sign-extend imm when required.
       (imm
	(if (and (not byte-operand?)
		 (equal rAX-size 8))
	    (the (unsigned-byte 64)
	      (n64
	       (the (signed-byte 32)
		 (n32-to-i32
		  (the (unsigned-byte 32) imm)))))
	  (the (unsigned-byte 32) imm)))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip operand-size))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Everything above this point is just further decoding the
       ;; instruction and fetching operands.

       ;; Instruction Specification:

       ;; Computing the flags and the result:
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv result
	    (the (unsigned-byte 32) output-rflags)
	    (the (unsigned-byte 32)  undefined-flags))
	(gpr-arith/logic-spec rAX-size operation rAX imm input-rflags))

       ;; Updating the x86 state with the result and eflags.
       (x86
	(if (or (eql operation #.*OP-CMP*)
		(eql operation #.*OP-TEST*))
	    ;; CMP and TEST modify just the flags.
	    x86
	  (!rgfi-size rAX-size *rax* result rex-byte x86)))

       (x86 (write-user-rflags output-rflags undefined-flags x86))
       (x86 (!rip temp-rip x86)))

      x86))

;; ======================================================================
;; INSTRUCTION: (one- and two- byte opcode maps)
;; push
;; ======================================================================

(def-inst x86-push-general-register
  :parents (one-byte-opcodes)

  :short "PUSH: 50+rw/rd"
  :long "<p>Op/En: O</p>
   <p><tt>50+rw/rd r16/r64</tt>: \[PUSH E\]</p>
   <p>Note that <tt>50+rd r32</tt> is N.E. in the 64-bit mode.</p>

<p>PUSH doesn't have a separate instruction semantic function, unlike
other opcodes like ADD, SUB, etc. I've just coupled the decoding with
the execution in this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #x50 '(:nil nil)
				      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x51 '(:nil nil)
				      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x52 '(:nil nil)
				      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x53 '(:nil nil)
				      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x54 '(:nil nil)
				      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x55 '(:nil nil)
				      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x56 '(:nil nil)
				      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x57 '(:nil nil)
				      'x86-push-general-register))

  :body

  (b* ((ctx 'x86-push-general-register)
       (lock (eql #.*lock*
		  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
	(!!ms-fresh :lock-prefix prefixes))

       (p3? (eql #.*operand-size-override*
		 (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if p3?
	    2
	  ;; 4-byte operand size is N.E. in 64-bit mode
	  ;; See http://www.x86-64.org/documentation/assembly.html
	  8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
	(!!ms-fresh :new-rsp-not-canonical new-rsp))

       ;; See "Z" in http://ref.x86asm.net/geek.html#x50
       (reg (mbe :logic (loghead 3 opcode)
		 :exec (the (unsigned-byte 3)
			 (logand #x07 opcode))))
       ;; See Intel Table 3.1, p.3-3, Vol. 2-A
       (val (rgfi-size operand-size (reg-index reg rex-byte #.*b*) rex-byte
		       x86))

       ;; Update the x86 state:

       ((mv flg x86)
	(wm-size operand-size
		 (the (signed-byte #.*max-linear-address-size*) new-rsp)
		 val x86))
       ((when flg) ;; Would also handle bad rsp values.
	(!!ms-fresh :SS-error-wm-size-error flg))

       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*) new-rsp) x86))
       (x86 (!rip temp-rip x86)))

      x86))

(def-inst x86-push-Ev
  :parents (one-byte-opcodes)

  :short "PUSH: FF/6 r/m"
  :long "<p>Op/En: M</p>
   <p><tt>FF/6 r/m</tt></p>
   <p>Note that <tt>FF/6 r/m32</tt> is N.E. in the 64-bit mode.</p>

<p>PUSH doesn't have a separate instruction semantic function,
unlike other opcodes like ADD, SUB, etc. I've just coupled the
decoding with the execution in this case.</p>

<p>This opcode belongs to Group 5, and it has an opcode
extension (ModR/m.reg = 6).</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #xFF '(:reg 6)
				      'x86-push-Ev))

  :body

  (b* ((ctx 'x86-push-Ev)
       (lock (eql #.*lock*
		  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
	(!!ms-fresh :lock-prefix prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (eql #.*operand-size-override*
		 (prefixes-slice :group-3-prefix prefixes)))
       (p4? (eql #.*addr-size-override*
		 (prefixes-slice :group-4-prefix prefixes)))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       ((the (integer 1 8) operand-size)
	(if p3?
	    2
	  ;; 4-byte operand size is N.E. in 64-bit mode
	  ;; See http://www.x86-64.org/documentation/assembly.html
	  8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
	(!!ms-fresh :new-rsp-not-canonical new-rsp))

       ((mv flg0 E (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?E-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* operand-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ increment-RIP-by temp-rip))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:

       ((mv flg x86)
	(wm-size operand-size
		 (the (signed-byte #.*max-linear-address-size*) new-rsp)
		 E x86))
       ((when flg) ;; Would also handle bad rsp values.
	(!!ms-fresh :SS-error-wm-size-error flg))

       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*) new-rsp) x86))
       (x86 (!rip temp-rip x86)))

      x86))

(def-inst x86-push-I

  :parents (one-byte-opcodes)

  :short "PUSH: 6A/68 ib/iw/id"

  :long "<p>Op/En: I</p>
   <p><tt>6A ib</tt>: PUSH imm8</p>
   <p><tt>68 iw</tt>: PUSH imm16</p>
   <p><tt>68 id</tt>: PUSH imm32</p>

<p>From the description of the PUSH instruction \(Intel Manual,
Vol. 2, Section 4.2\):</p>

<p><i> If the source operand is an immediate of size less than the
 operand size, a sign-extended value is pushed on the stack.</i></p>

<p>PUSH doesn't have a separate instruction semantic function,
unlike other opcodes like ADD, SUB, etc. I've just coupled the
decoding with the execution in this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #x68 '(:nil nil)
				      'x86-push-I)
    (add-to-implemented-opcodes-table 'PUSH #x6A '(:nil nil)
				      'x86-push-I))

  :body

  (b* ((ctx 'x86-push-I)
       (lock (eql #.*lock*
		  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
	(!!ms-fresh :lock-prefix prefixes))

       (p3? (eql #.*operand-size-override*
		 (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) imm-size)
	(if (equal opcode #x6A)
	    1
	  (if p3? 2 4)))
       ((the (integer 1 8) operand-size)
	(if p3?
	    2
	  ;; 4-byte operand size is N.E. in 64-bit mode
	  ;; See http://www.x86-64.org/documentation/assembly.html
	  8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
	(!!ms-fresh :new-rsp-not-canonical new-rsp))

       ((mv flg0 (the (signed-byte 32) imm) x86)
	(rim-size imm-size temp-rip :x x86))
       ((when flg0)
	(!!ms-fresh :imm-rim-size-error flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ imm-size temp-rip))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:

       ((mv flg1 x86)
	(wm-size operand-size
		 (the (signed-byte #.*max-linear-address-size*) new-rsp)
		 (mbe :logic (loghead (ash operand-size 3) imm)
		      :exec (logand
			     (case operand-size
			       (2 #.*2^16-1*)
			       (8 #.*2^64-1*))
			     (the (signed-byte 32) imm)))
		 x86))
       ((when flg1) ;; Would also handle "bad" rsp values.
	(!!ms-fresh :SS-exception-wm-size-error flg1))
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86 (!rip temp-rip x86)))

      x86))

(def-inst x86-push-segment-register
  :parents (two-byte-opcodes)

  :short "PUSH FS/GS"
  :long "<p><tt>0F A0</tt>: \[PUSH FS\]</p>
<p><tt>0F A8</tt>: \[PUSH GS\]</p>
   <p>Pushing other segment registers in the 64-bit mode is
   invalid.</p>

<p>If the source operand is a segment register \(16 bits\) and the
 operand size is 64-bits, a zero- extended value is pushed on the
 stack; if the operand size is 32-bits, either a zero-extended value
 is pushed on the stack or the segment selector is written on the
 stack using a 16-bit move. For the last case, all recent Core and
 Atom processors perform a 16-bit move, leaving the upper portion of
 the stack location unmodified.</p>

<p>PUSH doesn't have a separate instruction semantic function, unlike
other opcodes like ADD, SUB, etc. I've just coupled the decoding with
the execution in this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #x0FA0 '(:nil nil)
				      'x86-push-segment-register)
    (add-to-implemented-opcodes-table 'PUSH #x0FA8 '(:nil nil)
				      'x86-push-segment-register))

  :body

  (b* ((ctx 'x86-push-general-register)
       (lock (eql #.*lock*
		  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
	(!!ms-fresh :lock-prefix prefixes))

       (p3? (eql #.*operand-size-override*
		 (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if p3?
	    2
	  ;; 4-byte operand size is N.E. in 64-bit mode
	  ;; See http://www.x86-64.org/documentation/assembly.html
	  8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
	(!!ms-fresh :new-rsp-not-canonical new-rsp))

       ((the (unsigned-byte 16) val)
	(seg-visiblei (if (eql opcode #xA0) *FS* *GS*) x86))

       ;; Update the x86 state:

       ((mv flg x86)
	(wm-size operand-size
		 (the (signed-byte #.*max-linear-address-size*)
		   new-rsp)
		 ;; If operand-size is 64, val is zero-extended here
		 ;; automatically.
		 val x86))
       ((when flg) ;; Would also handle bad rsp values.
	(!!ms-fresh :SS-error-wm-size-error flg))

       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*) new-rsp) x86))
       (x86 (!rip temp-rip x86)))

      x86))

;; ======================================================================
;; INSTRUCTION: (one-byte opcode map)
;; pop
;; ======================================================================

(def-inst x86-pop-general-register
  :parents (one-byte-opcodes)

  :short "POP: 58+rw/rd"
  :long "<p>Op/En: O</p>
   <p><tt>58+rw/rd r16/r64</tt>: \[POP E\]</p>
   <p>Note that <tt>58+rd r32</tt> is N.E. in the 64-bit mode.</p>

<p>POP doesn't have a separate instruction semantic function, unlike
other opcodes like ADD, SUB, etc. I've just coupled the decoding with
the execution in this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'POP #x58 '(:nil nil)
				      'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x59 '(:nil nil)
				      'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5A '(:nil nil)
				      'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5B '(:nil nil)
				      'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5C '(:nil nil)
				      'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5D '(:nil nil)
				      'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5E '(:nil nil)
				      'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5F '(:nil nil)
				      'x86-pop-general-register))

  :body

  (b* ((ctx 'x86-pop-general-register)
       (lock (eql #.*lock*
		  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
	(!!ms-fresh :lock-prefix prefixes))

       (p3? (eql #.*operand-size-override*
		 (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if p3?
	    2
	  ;; 4-byte operand size is N.E. in 64-bit mode
	  ;; See http://www.x86-64.org/documentation/assembly.html
	  8))
       (rsp (rgfi *rsp* x86))
       ((when (not (canonical-address-p rsp)))
	(!!ms-fresh :rsp-not-canonical rsp))

       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
	(+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
       ((when (mbe :logic (not (canonical-address-p new-rsp))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       new-rsp))))
	(!!ms-fresh :ss-exception-new-rsp-not-canonical new-rsp))

       ((mv flg0 val x86)
	(rm-size operand-size rsp :r x86))
       ((when flg0) ;; #SS exception?
	(!!ms-fresh :rm-size-error flg0))

       ;; See "Z" in http://ref.x86asm.net/geek.html#x58.
       (reg (logand opcode #x07))
       ;; Update the x86 state:
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86
	;; See Intel Table 3.1, p.3-3, Vol. 2-A
	(!rgfi-size operand-size (reg-index reg rex-byte #.*b*)
		    val rex-byte x86))
       (x86 (!rip temp-rip x86)))

      x86))

(def-inst x86-pop-Ev
  :parents (one-byte-opcodes)

  :short "POP: 8F/0 r/m"

  :long "<p>Op/En: M</p>
   <p><tt>8F/0 r/m</tt></p>
   <p>Note that <tt>8F/0 r/m32</tt> is N.E. in the 64-bit mode.</p>

<p>POP doesn't have a separate instruction semantic function,
unlike other opcodes like ADD, SUB, etc. I've just coupled the
decoding with the execution in this case.</p>

<p>This opcode belongs to Group 1A, and it has an opcode
extension (ModR/m.reg = 0).</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'POP #x8F '(:reg 0) 'x86-pop-Ev)

  :body

  (b* ((ctx 'x86-pop-Ev)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3 (equal #.*operand-size-override*
		  (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       ((the (integer 1 8) operand-size)
	(if p3
	    2
	  ;; 4-byte operand size is N.E. in 64-bit mode
	  8))

       (rsp (rgfi *rsp* x86))
       ((when (not (canonical-address-p rsp)))
	(!!ms-fresh :rsp-not-canonical rsp))

       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
	(+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
       ;; Raise a #SS exception.
       ((when (mbe :logic (not (canonical-address-p new-rsp))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       new-rsp))))
	(!!ms-fresh :ss-exception-new-rsp-not-canonical new-rsp))

       ((mv flg0 val x86)
	(rm-size operand-size rsp :r x86))
       ((when flg0) ;; #SS exception?
	(!!ms-fresh :rm-size-error flg0))

       ((mv flg1 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
	(if (equal mod #b11)
	    (mv nil 0 0 x86)
	  (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86)))
       ((when flg1) ;; #SS exception?
	(!!ms-fresh :x86-effective-addr-error flg1))

       ((mv flg2 v-addr)
	(case p2
	  (0 (mv nil v-addr))
	  ;; I don't really need to check whether FS and GS base are
	  ;; canonical or not.  On the real machine, if the MSRs
	  ;; containing these bases are assigned non-canonical
	  ;; addresses, an exception is raised.
	  (#.*fs-override*
	   (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
		  (fs-base (n64-to-i64 nat-fs-base)))
	     (if (not (canonical-address-p fs-base))
		 (mv 'Non-Canonical-FS-Base fs-base)
	       (mv nil (+ fs-base v-addr)))))
	  (#.*gs-override*
	   (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
		  (gs-base (n64-to-i64 nat-gs-base)))
	     (if (not (canonical-address-p gs-base))
		 (mv 'Non-Canonical-GS-Base gs-base)
	       (mv nil (+ gs-base v-addr)))))
	  (t (mv 'Unidentified-P2 v-addr))))
       ((when flg2)
	(!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg2))
       ((when (not (canonical-address-p v-addr)))
	(!!ms-fresh :v-addr-not-canonical v-addr))

       ((mv flg3 x86)
	(x86-operand-to-reg/mem
	 operand-size val v-addr rex-byte r/m mod x86))
       ((when flg3)
	(!!ms-fresh :x86-operand-to-reg/mem flg2))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ increment-RIP-by temp-rip))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))

       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))


       ;; Update the x86 state:
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86 (!rip temp-rip x86)))

      x86))

;; (def-inst x86-pop-segment-register
;;   :parents (one-byte-opcodes)

;;   :short "POP FS/GS"
;;   :long "<p><tt>0F A1</tt>: \[POP FS\]</p>
;; <p><tt>0F A9</tt>: \[POP GS\]</p>
;;    <p>Popping other segment registers in the 64-bit mode is
;;    invalid.</p>

;; <p>If the source operand is a segment register \(16 bits\) and the
;;  operand size is 64-bits, a zero- extended value is pushed on the
;;  stack; if the operand size is 32-bits, either a zero-extended value
;;  is pushed on the stack or the segment selector is written on the
;;  stack using a 16-bit move. For the last case, all recent Core and
;;  Atom processors perform a 16-bit move, leaving the upper portion of
;;  the stack location unmodified.</p>

;; <p>POP doesn't have a separate instruction semantic function, unlike
;; other opcodes like ADD, SUB, etc. I've just coupled the decoding with
;; the execution in this case.</p>"

;;   :returns (x86 x86p :hyp (and (x86p x86)
;;                                (canonical-address-p temp-rip)))

;;   :guard-debug t

;;   :body

;;   (b* ((ctx 'x86-pop-Ev)
;;        (lock (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
;;        ((when lock)
;;         (!!ms-fresh :lock-prefix prefixes))
;;        (p2 (prefixes-slice :group-2-prefix prefixes))
;;        (p3 (equal #.*operand-size-override*
;;               (prefixes-slice :group-3-prefix prefixes)))

;;        (r/m (mrm-r/m modr/m))
;;        (mod (mrm-mod modr/m))

;;        ((the (integer 1 8) operand-size)
;;         (if p3
;;             2
;;           ;; 4-byte operand size is N.E. in 64-bit mode
;;           8))

;;        (rsp (rgfi *rsp* x86))
;;        ((when (not (canonical-address-p rsp)))
;;         (!!ms-fresh :rsp-not-canonical rsp))

;;        ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
;;         (+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
;;        ;; TO-DO@Shilpi: Raise a #SS exception.
;;        ((when (not (canonical-address-p new-rsp)))
;;         (!!ms-fresh :new-rsp-not-canonical new-rsp))

;;        ((mv flg0 val x86)
;;         (rm-size operand-size rsp :r x86))
;;        ((when flg0) ;; #SS exception?
;;         (!!ms-fresh :rm-size-error flg0))

;;        (p4 (equal #.*addr-size-override*
;;               (prefixes-slice :group-4-prefix prefixes)))
;;        ((mv flg1 v-addr (the (unsigned-byte 3) increment-RIP-by) x86)
;;         (if (equal mod #b11)
;;             (mv nil 0 0 x86)
;;           (x86-effective-addr p4 temp-rip rex-byte r/m mod sib 0 x86)))
;;        ((when flg1) ;; #SS exception?
;;         (!!ms-fresh :x86-effective-addr-error flg1))

;;        ((mv flg2 v-addr)
;;         (case p2
;;           (0 (mv nil v-addr))
;;           ;; TO-DO@Shilpi: I don't really need to check whether FS and
;;           ;; GS base are canonical or not.  On the real machine, if
;;           ;; the MSRs containing these bases are assigned
;;           ;; non-canonical addresses, an exception is raised.
;;           (#.*fs-override*
;;            (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
;;                   (fs-base (n64-to-i64 nat-fs-base)))
;;              (if (not (canonical-address-p fs-base))
;;                  (mv 'Non-Canonical-FS-Base fs-base)
;;                (mv nil (+ fs-base v-addr)))))
;;           (#.*gs-override*
;;            (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
;;                   (gs-base (n64-to-i64 nat-gs-base)))
;;              (if (not (canonical-address-p gs-base))
;;                  (mv 'Non-Canonical-GS-Base gs-base)
;;                (mv nil (+ gs-base v-addr)))))
;;           (t (mv 'Unidentified-P2 v-addr))))
;;        ((when flg2)
;;         (!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg2))
;;        ((when (not (canonical-address-p v-addr)))
;;         (!!ms-fresh :v-addr-not-canonical v-addr))

;;        ((mv flg3 x86)
;;         (x86-operand-to-reg/mem
;;          operand-size val v-addr rex-byte r/m mod x86))
;;        ((when flg3)
;;         (!!ms-fresh :x86-operand-to-reg/mem flg2))

;;        ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
;;         (+ increment-RIP-by temp-rip))
;;        ((when (not (canonical-address-p temp-rip)))
;;         (!!ms-fresh :virtual-memory-error temp-rip))

;;        ;; TO-DO@Shilpi: If the instruction goes beyond 15 bytes, stop. Change
;;        ;; to an exception later.
;;        ((when (> (- temp-rip start-rip) 15))
;;         (!!ms-fresh :instruction-length (- temp-rip start-rip)))

;;        ;; Update the x86 state:
;;        (x86 (!rgfi *rsp* new-rsp x86))
;;        (x86 (!rip temp-rip x86)))

;;       x86))

;; ======================================================================
;; INSTRUCTION: (one-byte opcode map)
;; jmp
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

(def-inst x86-near-jmp-Op/En-D

  ;; Op/En: D
  ;; E9: JMP rel32: Jump Near, relative, RIP = RIP + 32-bit
  ;;                displacement sign-extended to 64-bits
  ;; EB: JMP rel8: Jump Short, RIP = RIP + 8-bit displacement
  ;;                sign-extended to 64-bits

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))
  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'JMP #xE9 '(:nil nil)
				      'x86-near-jmp-Op/En-D)
    (add-to-implemented-opcodes-table 'JMP #xEB '(:nil nil)
				      'x86-near-jmp-Op/En-D))

  :body

  (b* ((ctx 'x86-near-jmp-Op/En-D)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       ((the (integer 0 4) offset-size)
	(case opcode
	  (#xEB 1)
	  (#xE9 4)
	  ;; Will cause an error in rim-size
	  (otherwise 0)))

       ((mv ?flg (the (signed-byte 32) offset) x86)
	(mbe :logic
	     (rim-size offset-size temp-rip :x x86)
	     :exec
	     (case offset-size
	       (1
		(mv-let (flag val x86)
			(rm08 temp-rip :x x86)
			(mv flag
			    (n08-to-i08 val)
			    x86)))
	       (4
		(mv-let (flag val x86)
			(rm32 temp-rip :x x86)
			(mv flag
			    (n32-to-i32 val)
			    x86)))
	       (otherwise
		(mv 'UNSUPPORTED-NBYTES 0 x86)))))

       ((when flg)
	(!!ms-fresh :rim-size-error flg))

       ((the (signed-byte #.*max-linear-address-size+1*) next-rip)
	(+ (the (integer 0 4) offset-size) temp-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ next-rip offset))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (or
			  (< (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip)
			     #.*-2^47*)
			  (<= #.*2^47*
			      (the (signed-byte
				    #.*max-linear-address-size+1*)
				temp-rip)))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; Update the x86 state:
       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-near-jmp-Op/En-M

  ;; Absolute indirect jump: RIP = r/m64
  ;; FF/4: JMP r/m64
  ;; Op/En: M

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'JMP #xFF '(:reg 4)
				    'x86-near-jmp-Op/En-M)

  :body

  (b* ((ctx 'x86-near-jmp-Op/En-M)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       ;; Note that the reg field serves as an opcode extension for
       ;; this instruction.  The reg field will always be 4 when this
       ;; function is called.
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg jmp-addr (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* 8 p2 p4? temp-rip rex-byte r/m
	 mod sib 0 x86))
       ((when flg)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes-error flg))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+2*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size+1*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Converting (unsigned-byte-p 64 jmp-addr) to a "good" address
       ;; in our world...
       (jmp-addr (n64-to-i64 jmp-addr))
       ((when (not (canonical-address-p jmp-addr)))
	(!!ms-fresh :virtual-memory-error jmp-addr))
       ;; Update the x86 state:
       (x86 (!rip jmp-addr x86)))
      x86))

(def-inst x86-far-jmp-Op/En-D

  :parents (one-byte-opcodes)
  :short "Absolute Indirect Jump: Far"
  :long "<p>Op/En: D</p>
<p><tt>FF/5: JMP m16:16 or m16:32 or m16:64</tt></p>

<p>Source: Intel Manuals \(Vol. 2A\) Instruction Set Reference: the
text below has been edited to contain information only about the
64-bit mode.</p>

<p><i>The JMP instruction cannot be used to perform
inter-privilege-level far jumps.</i> The processor always uses the
segment selector part of the far address to access the corresponding
descriptor in the GDT or LDT. The descriptor type and access rights
determine the type of jump to be performed.</p>

<p><b>Far Jump to a Conforming or Non-Conforming Code Segment:</b> If
the selected descriptor is for a code segment, a far jump to a code
segment at the same privilege level is performed. If the selected code
segment is at a different privilege level and the code segment is
non-conforming, a general-protection exception is generated.  The
target operand specifies an absolute far address indirectly with a
memory location \(m16:16 or m16:32 or m16:64\). The operand-size
attribute and the REX.w bit determine the size of the offset \(16 or
32 or 64 bits\) in the far address. The new code segment selector and
its descriptor are loaded into CS register, and the offset from the
instruction is loaded into the RIP register.</p>

<p><b>Far Jump through a Call Gate:</b> When executing a far jump
through a call gate, the segment selector specified by the target
operand identifies the call gate. The offset part of the target
operand is ignored. The processor then jumps to the code segment
specified in the call gate descriptor and begins executing the
instruction at the offset specified in the call gate. No stack switch
occurs. The target operand specifies the far address of the call gate
indirectly with a memory location \(m16:16 or m16:32 or m16:64\).</p>"

  :guard-hints (("Goal" :in-theory (e/d ()
					())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'JMP #xFF '(:reg 5)
				    'x86-far-jmp-Op/En-D)

  :prepwork

  ((local (include-book "centaur/gl/gl" :dir :system))

   (local
    (def-gl-thm far-jmp-conforming-code-segment-guard-helper-1
      :hyp (unsigned-byte-p 16 val16)
      :concl (equal (bitops::logsquash 2 val16)
		    (logand 65532 val16))
      :g-bindings (gl::auto-bindings
		   (:nat val16 16))))

   (local
    (def-gl-thm far-jmp-conforming-code-segment-guard-helper-2
      :hyp (unsigned-byte-p 16 val16)
      :concl (equal (logand -79228162495817593519834398721 (ash val16 96))
		    (logand 5192217630372331810936976494821375 (ash val16 96)))
      :g-bindings (gl::auto-bindings
		   (:nat val16 16))))

   (local
    (def-gl-thm far-jmp-non-conforming-code-segment-guard-helper-3
      :hyp (and (unsigned-byte-p 80 n80)
		(unsigned-byte-p 64 n64)
		(unsigned-byte-p 16 n16))
      :concl (equal
	      (logior n64
		      (ash (logtail 64 n80) 64)
		      (logand 5192217630372313364192902785269760 (ash n16 96)))
	      (logior
	       n64
	       (logand 5192296858534809181786422619668480
		       (logior (ash (logtail 64 n80) 64)
			       (logand 5192217630372331810936976494821375 (ash n16 96))))))
      :g-bindings (gl::auto-bindings
		   (:mix (:nat n80 80)
			 (:nat n64 80)
			 (:nat n16 80)))))

   (local
    (def-gl-thm far-jmp-call-gate-guard-helper-4
      :hyp (and (unsigned-byte-p 64 n64)
		(unsigned-byte-p 48 n48)
		(unsigned-byte-p 16 n16))
      :concl (equal
	      (logior n64 (ash (loghead 32 n48) 64)
		      (logand 5192217630372313364192902785269760 (ash n16 96)))
	      (logior
	       n64
	       (logand
		5192296858534809181786422619668480
		(logior
		 (ash (loghead 32 n48) 64)
		 (logand 5192217630372331810936976494821375 (ash n16 96))))))
      :g-bindings (gl::auto-bindings
		   (:mix (:nat n48 64)
			 (:nat n64 64)
			 (:nat n16 64))))))


  :body

  (b* ((ctx 'x86-far-jmp-Op/En-M)
       ;; If the lock prefix is used, then the #UD exception is
       ;; raised.
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))

       ;; [TO-DO@Shilpi]: Note that this exception was not mentioned
       ;; in the Intel Manuals, but I think that the reason for this
       ;; omission was that the JMP instruction reference sheet
       ;; mentioned direct addressing opcodes too (which are
       ;; unavailable in the 64-bit mode).
       ;; If the source operand is not a memory location, then #GP(0)
       ;; is raised.
       ((when (equal mod #b11))
	(!!ms-fresh :source-operand-not-memory-location mod))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       (offset-size
	;; Offset size can be 2, 4, or 8 bytes.
	(select-operand-size nil rex-byte nil prefixes))
       ((mv flg mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access*
	 ;; offset-size is the number of bytes of the
	 ;; offset.  We need two more bytes for the selector.
	 (the (integer 2 10) (+ 2 offset-size))
	 p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes-error flg))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((the (signed-byte #.*max-linear-address-size+2*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size+1*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       (selector (the (unsigned-byte 16) (n16 mem)))
       (offset (mbe :logic (part-select mem :low 16 :width
					(ash offset-size 3))
		    :exec (ash mem -16)))

       ;; Getting the selector's components:
       ((the (unsigned-byte 13) sel-index)
	(seg-sel-layout-slice :index selector))
       ((the (unsigned-byte 1) sel-ti)
	(seg-sel-layout-slice :ti selector))
       ((the (unsigned-byte 2) sel-rpl)
	(seg-sel-layout-slice :rpl selector))

       ;; Is the selector a null selector?  A null selector points to
       ;; the first entry in the GDT (sel-index=0, ti=0).
       ;; The exception #GP(0) is raised when the segment selector in
       ;; the destination operand is NULL.
       ((when (and (equal sel-ti 0)
		   (equal sel-index 0)))
	(!!ms-fresh :gp-nullselector 0))

       ((mv dt-base-addr dt-limit)
	(if (equal sel-ti 0)
	    ;; Selector references the GDT.
	    (b* ((gdtr (the (unsigned-byte 80) (stri *gdtr* x86)))
		 (gdtr-base (gdtr/idtr-layout-slice :base-addr gdtr))
		 (gdtr-limit (gdtr/idtr-layout-slice :limit gdtr)))
		(mv gdtr-base gdtr-limit))
	  ;; Selector references the LDT whose base address is in
	  ;; LDTR.
	  (b* ((ldtr-hidden (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86)))
	       (ldtr-base (hidden-seg-reg-layout-slice :base-addr ldtr-hidden))
	       (ldtr-limit (hidden-seg-reg-layout-slice :limit ldtr-hidden)))
	      (mv ldtr-base ldtr-limit))))

       ;; Is the limit of the selector within the descriptor table
       ;; limit?
       ;; The exception #GP(selector) is raised when offset is beyond
       ;; the code segment limit.
       ((when (< dt-limit sel-index))
	(!!ms-fresh :gp-selector-limit-check-failed
		    (list selector dt-base-addr dt-limit)))

       ;; Now that we know the segment selector is valid, we check if
       ;; the segment descriptor is valid.
       (descriptor-addr
	;; The index is scaled by 8.
	(+ dt-base-addr (the (unsigned-byte 16) (ash sel-index 3))))
       ((when (not (canonical-address-p descriptor-addr)))
	(!!ms-fresh :descriptor-addr-virtual-memory-error descriptor-addr))

       ;; Note that the code or data segment descriptors are 8 bytes
       ;; wide but all other descriptors are 16 bytes wide in the
       ;; 64-bit mode.
       ((mv flg (the (unsigned-byte 128) descriptor) x86)
	;; [TO-DO@Shilpi]: I believe I should use :x below and not :r.
	(rm-size 16 descriptor-addr :x x86))
       ((when flg)
	(!!ms-fresh :rm-size-error flg))

       ;; If segment type is neither a code segment (conforming or
       ;; non-conforming) nor a call gate, then #GP(selector) is
       ;; raised.
       ((mv flg code-or-call-gate? descriptor)
	(b* ((descriptor-64 (n64 descriptor))
	     ((mv valid? reason1)
	      ;; Note that the following predicate reports the
	      ;; descriptor to be invalid if the P flag of the
	      ;; descriptor is 0.
	      (ia32e-valid-code-segment-descriptor-p descriptor-64))
	     ((when valid?)
	      (mv nil 0 descriptor-64))
	     ((mv valid? reason2)
	      ;; Note that the following predicate reports the
	      ;; descriptor to be invalid if the P flag of the
	      ;; descriptor is 0.
	      (ia32e-valid-call-gate-segment-descriptor-p descriptor))
	     ((when valid?)
	      (mv nil 1 descriptor)))
	    (mv t (cons reason1 reason2) descriptor)))
       ((when flg)
	(!!ms-fresh
	 :either-both-code-segment-or-call-gate-are-absent-or-some-other-descriptor-is-present
	 (cons code-or-call-gate? descriptor))))

      (if (eql code-or-call-gate? 0) ;; Code Segment:

	  (if (equal (part-select
		      (code-segment-descriptor-layout-slice
		       :type descriptor)
		      :low 2 :width 1)
		     1)

	      ;; Conforming Code Segment:

	      (b* ((current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
		   (cpl (seg-sel-layout-slice :rpl current-cs-register))
		   (dpl (code-segment-descriptor-layout-slice
			 :dpl descriptor))
		   ;; Access is allowed to a conforming code segment
		   ;; when DPL <= CPL (numerically).  RPL is ignored
		   ;; for this privilege check.  If access is not
		   ;; allowed, #GP(segment-selector) is raised.
		   ((when (not (<= dpl cpl)))
		    (!!ms-fresh :privilege-check-fail
				(acons :dpl dpl
				       (acons :cpl cpl nil))))

		   ;; Trimming the offset based on the operand-size:
		   (jmp-addr
		    (case offset-size
		      (2 (n16 offset))
		      (4 (n32 offset))
		      (t offset)))

		   ;; #GP(0) is thrown if the target offset in destination is
		   ;; non-canonical.
		   ((when (not (canonical-address-p jmp-addr)))
		    (!!ms-fresh :target-offset-virtual-memory-error jmp-addr))

		   (new-cs-visible
		    (!seg-sel-layout-slice :rpl cpl selector))

		   (new-cs-hidden
		    (if (equal sel-ti 1)
			;; Load the hidden portions of the CS segment
			;; from the LDTR's hidden portion.
			(the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86))
		      ;; Descriptor was in GDT.
		      (!hidden-seg-reg-layout-slice
		       :base-addr dt-base-addr
		       (!hidden-seg-reg-layout-slice
			:limit dt-limit
			(!hidden-seg-reg-layout-slice
			 ;; Get attributes from the descriptor in GDT.
			 :attr (make-code-segment-attr-field descriptor)
			 0)))))

		   ;; Update x86 state:
		   (x86 (!seg-visiblei *cs* new-cs-visible x86))
		   (x86 (!seg-hiddeni  *cs* new-cs-hidden  x86))
		   (x86 (!rip jmp-addr x86)))
		  x86)

	    ;; Non-Conforming Code Segment:

	    (b* ((current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
		 (cpl (seg-sel-layout-slice :rpl current-cs-register))
		 (dpl (code-segment-descriptor-layout-slice
		       :dpl descriptor))
		 ;; Access is allowed to a conforming code segment
		 ;; when RPL <= CPL (numerically) and CPL = DPL. If
		 ;; access is not allowed, #GP(segment-selector) is
		 ;; raised.
		 ((when (not (and (<= sel-rpl cpl)
				  (equal cpl dpl))))
		  (!!ms-fresh :privilege-check-fail
			      (acons :dpl dpl
				     (acons :cpl cpl
					    (acons :rpl sel-rpl nil)))))

		 ;; Trimming the offset based on the operand-size:
		 (jmp-addr
		  (case offset-size
		    (2 (n16 offset))
		    (4 (n32 offset))
		    (t offset)))

		 ;; #GP(0) is thrown if the target offset in destination is
		 ;; non-canonical.
		 ((when (not (canonical-address-p jmp-addr)))
		  (!!ms-fresh :target-offset-virtual-memory-error jmp-addr))

		 (new-cs-visible
		  (!seg-sel-layout-slice :rpl cpl selector))

		 (new-cs-hidden
		  (if (equal sel-ti 1)
		      ;; Load the hidden portions of the CS segment
		      ;; from the LDTR's hidden portion.
		      (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86))
		    ;; Descriptor was in GDT.
		    (!hidden-seg-reg-layout-slice
		     :base-addr dt-base-addr
		     (!hidden-seg-reg-layout-slice
		      :limit dt-limit
		      (!hidden-seg-reg-layout-slice
		       ;; Get attributes from the descriptor in GDT.
		       :attr (make-code-segment-attr-field descriptor)
		       0)))))

		 ;; Update x86 state:
		 (x86 (!seg-visiblei *cs* new-cs-visible x86))
		 (x86 (!seg-hiddeni  *cs* new-cs-hidden  x86))
		 (x86 (!rip jmp-addr x86)))
		x86))

	;; Call Gate Descriptor:

	(b* ((current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
	     (cpl (seg-sel-layout-slice :rpl current-cs-register))
	     (dpl (call-gate-descriptor-layout-slice :dpl descriptor))

	     ;; Access is allowed when:
	     ;; 1. CPL <= Call gate's DPL
	     ;; 2. RPL <= Call gate's DPL
	     ;; 3. If the destination Code segment is conforming,
	     ;;    then: DPL of code segment <= CPL
	     ;;    If the destination Code segment is non-conforming,
	     ;;    then: DPL of code segment = CPL.
	     ;; If access is not allowed, #GP(segment-selector) is
	     ;; raised.
	     ;; Below, we check 1 and 2.  We will check for 3 after we
	     ;; read in the code segment descriptor.
	     ((when (not (and (<= cpl dpl)
			      (<= sel-rpl dpl))))
	      (!!ms-fresh :privilege-check-fail
			  (acons :dpl dpl
				 (acons :cpl cpl
					(acons :rpl sel-rpl nil)))))

	     (cs-selector
	      (call-gate-descriptor-layout-slice :selector descriptor))
	     ((the (unsigned-byte 13) cs-sel-index)
	      (seg-sel-layout-slice :index cs-selector))
	     ((the (unsigned-byte 1) cs-sel-ti)
	      (seg-sel-layout-slice :ti cs-selector))
	     ((the (unsigned-byte 2) cs-sel-rpl)
	      (seg-sel-layout-slice :rpl cs-selector))

	     ;; If the call gate's code segment selector is NULL,
	     ;; #GP(0) is raised.
	     ((when (and (equal cs-sel-ti 0)
			 (equal cs-sel-index 0)))
	      (!!ms-fresh :call-gate-code-segment-nullselector 0))

	     ;; Is the call gate code segment selector index outside
	     ;; the descriptor table limit?  If so, #GP(code segment
	     ;; selector) is raised.
	     ((mv cs-dt-base-addr cs-dt-limit)
	      (if (equal sel-ti 0)
		  ;; Code Segment Selector references the GDT.
		  (b* ((gdtr (the (unsigned-byte 80) (stri *gdtr* x86)))
		       (gdtr-base (gdtr/idtr-layout-slice :base-addr gdtr))
		       (gdtr-limit (gdtr/idtr-layout-slice :limit gdtr)))
		      (mv gdtr-base gdtr-limit))
		;; Code Segment Selector references the LDT whose base
		;; address is in LDTR.
		(b* ((ldtr-hidden (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86)))
		     (ldtr-base (hidden-seg-reg-layout-slice :base-addr ldtr-hidden))
		     (ldtr-limit (hidden-seg-reg-layout-slice :limit ldtr-hidden)))
		    (mv ldtr-base ldtr-limit))))
	     ((when (< cs-dt-limit cs-sel-index))
	      (!!ms-fresh :gp-selector-limit-check-failed
			  (list cs-selector cs-dt-base-addr cs-dt-limit)))

	     ;; Reading the code segment: we check if the code segment
	     ;; descriptor is valid.
	     (cs-descriptor-addr
	      ;; The index is scaled by 8.
	      (+ cs-dt-base-addr (the (unsigned-byte 16) (ash cs-sel-index 3))))
	     ((when (not (canonical-address-p cs-descriptor-addr)))
	      (!!ms-fresh :cs-descriptor-addr-virtual-memory-error cs-descriptor-addr))
	     ((mv flg (the (unsigned-byte 64) cs-descriptor) x86)
	      ;; [TO-DO@Shilpi]: I believe I should use :x below and not :r.
	      (rm-size 8 cs-descriptor-addr :x x86))
	     ((when flg)
	      (!!ms-fresh :rm-size-error flg))
	     ((mv valid? reason)
	      ;; Note that the following predicate reports the
	      ;; descriptor to be invalid if the P flag of the
	      ;; descriptor is 0.
	      (ia32e-valid-code-segment-descriptor-p cs-descriptor))
	     ((when (not valid?))
	      (!!ms-fresh :call-gate-code-segment-descriptor-invalid
			  (cons reason cs-descriptor)))

	     ;; Checking the privileges of the code segment:
	     (cs-dpl (code-segment-descriptor-layout-slice :dpl cs-descriptor))
	     (c-bit (part-select
		     (code-segment-descriptor-layout-slice
		      :type cs-descriptor)
		     :low 2 :width 1))
	     ((when (or (and ;; Conforming code segment
			 (equal c-bit 1)
			 (not (<= cs-dpl cpl)))
			(and ;; Conforming code segment
			 (equal c-bit 0)
			 (not (eql cs-dpl cpl)))))
	      (!!ms-fresh :privilege-check-fail
			  (acons :c-bit c-bit
				 (acons :cpl cpl
					(acons :cs-dpl cs-dpl nil)))))

	     (call-gate-offset15-0
	      (call-gate-descriptor-layout-slice :offset15-0 descriptor))
	     (call-gate-offset31-16
	      (call-gate-descriptor-layout-slice :offset31-16 descriptor))
	     (call-gate-offset63-32
	      (call-gate-descriptor-layout-slice :offset63-32 descriptor))
	     (call-gate-offset31-0
	      (mbe :logic (part-install call-gate-offset15-0
					(ash call-gate-offset31-16 16)
					:low 0 :width 16)
		   :exec
		   (the (unsigned-byte 32)
		     (logior (the (unsigned-byte 16) call-gate-offset15-0)
			     (the (unsigned-byte 32) (ash call-gate-offset31-16 16))))))
	     (call-gate-offset
	      (mbe :logic
		   (part-install call-gate-offset31-0
				 (ash call-gate-offset63-32 32)
				 :low 0 :width 32)
		   :exec
		   (the (unsigned-byte 64)
		     (logior (the (unsigned-byte 32) call-gate-offset31-0)
			     (the (unsigned-byte 64) (ash call-gate-offset63-32 32))))))

	     ;; Trimming the call gate offset based on the operand-size:
	     (jmp-addr
	      (case offset-size
		(2 (n16 call-gate-offset))
		(4 (n32 call-gate-offset))
		(t call-gate-offset)))

	     ;; #GP(0) is thrown if the target offset in destination is
	     ;; non-canonical.
	     ((when (not (canonical-address-p jmp-addr)))
	      (!!ms-fresh :target-offset-virtual-memory-error jmp-addr))

	     (new-cs-visible
	      (!seg-sel-layout-slice :rpl cpl cs-selector))

	     (new-cs-hidden
	      (if (equal cs-sel-ti 1)
		  ;; Load the hidden portions of the CS segment
		  ;; from the LDTR's hidden portion.
		  (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86))
		;; Descriptor was in GDT.
		(!hidden-seg-reg-layout-slice
		 :base-addr cs-dt-base-addr
		 (!hidden-seg-reg-layout-slice
		  :limit cs-dt-limit
		  (!hidden-seg-reg-layout-slice
		   ;; Get attributes from the descriptor in GDT.
		   :attr (make-code-segment-attr-field cs-descriptor)
		   0)))))

	     ;; Update x86 state:
	     (x86 (!seg-visiblei *cs* new-cs-visible x86))
	     (x86 (!seg-hiddeni  *cs* new-cs-hidden  x86))
	     (x86 (!rip jmp-addr x86)))
	    x86))))

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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'LEA #x8D '(:nil nil) 'x86-lea)

  :body


  (b* ((ctx 'x86-lea)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
		   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 2 8) register-size)
	(if (logbitp #.*w* rex-byte)
	    8
	  (if p3?
	      2
	    4)))

       ((mv ?flg0 (the (signed-byte 64) M) (the (unsigned-byte 3) increment-RIP-by) x86)
	(if (equal mod #b11)
	    ;; See "M" in http://ref.x86asm.net/#Instruction-Operand-Codes
	    (mv "Source operand is not a memory location" 0 0 x86)
	  (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86)))
       ((when flg0)
	(!!ms-fresh :x86-effective-addr-error flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ((mv flg1 M)
	(case p2
	  (0 (mv nil M))
	  ;; I don't really need to check whether FS and GS base are
	  ;; canonical or not.  On the real machine, if the MSRs
	  ;; containing these bases are assigned non-canonical
	  ;; addresses, an exception is raised.
	  (#.*fs-override*
	   (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
		  (fs-base (n64-to-i64 nat-fs-base)))
	     (if (not (canonical-address-p fs-base))
		 (mv 'Non-Canonical-FS-Base fs-base)
	       (mv nil (+ fs-base M)))))
	  (#.*gs-override*
	   (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
		  (gs-base (n64-to-i64 nat-gs-base)))
	     (if (not (canonical-address-p gs-base))
		 (mv 'Non-Canonical-GS-Base gs-base)
	       (mv nil (+ gs-base M)))))
	  (t (mv 'Unidentified-P2 M))))
       ((when flg1)
	(!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg1))

       (M (trunc register-size M))
       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*)
			M rex-byte x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: PUSHF/PUSHFQ
;; ======================================================================

(def-inst x86-pushf

  ;; #x9C: Op/En: NP
  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'PUSHF #x9C '(:nil nil) 'x86-pushf)

  :body

  (b* ((ctx 'x86-pushf)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p3? (equal #.*operand-size-override*
		   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if p3?
	    2
	  ;; 4-byte operand size is N.E. in 64-bit mode
	  8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
	(!!ms-fresh :new-rsp-not-canonical new-rsp))

       ((the (unsigned-byte 32) eflags) (rflags x86))

       ((the (unsigned-byte 32) eflags)
	(case operand-size
	  ;; Lower 16 bits are stored on the stack
	  (2 (logand #xffff eflags))
	  ;; VM and RF rflag bits are cleared in the image stored on the
	  ;; stack.  Also, bits from 22-63 are reserved, and hence,
	  ;; zeroed out.
	  (otherwise (logand #x3cffff eflags))))

       ;; Update the x86 state:
       ((mv flg x86)
	(wm-size operand-size
		 (the (signed-byte #.*max-linear-address-size*) new-rsp)
		 eflags x86))
       ;; Raise a #SS exception.
       ((when flg) ; Would also handle "bad" rsp values.
	(!!ms-fresh :wm-size-error flg))
       (x86 (!rip temp-rip x86))
       (x86 (!rgfi *rsp* new-rsp x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: POPF/POPFQ
;; ======================================================================

(def-inst x86-popf

  ;; #x9D
  ;; Op/En: NP

  ;; Intel Vol. 2B, p. 4-350 says: "In 64-bit mode, use REX.w to pop
  ;; the top of stack to RFLAGS.  POPFQ pops 64-bits from the stack,
  ;; loads the lower 32 bits into rflags, and zero-extends the upper
  ;; bits of eflags."

  ;; TO-DO@Shilpi: Since we do not support the CS segment in our model
  ;; yet, we do not have any notion of privileges.  For the time
  ;; being, I am going to assume that the CPL is 0.

  ;; 64-bit mode operation of x86-popf:

  ;; if cpl > 0 then

  ;;    if operand-size = 8 then

  ;;       if cpl > iopl then
  ;;          rflags := 64-bit-pop()
  ;;          IF, IOPL, RF, VIP, and all reserved bits are unaffected,
  ;;          VIP and VIF are cleared, all other non-reserved-bits can
  ;;          be modified.

  ;;       else

  ;;          rflags := 64-bit-pop()
  ;;          Same as above, but IF can be modified too.

  ;;       end if

  ;;    else (if operand-size = 2)
  ;;       rflags[15:0] := 16-bit-pop()
  ;;       IOPL and all reserved bits are unaffected, other
  ;;       non-reserved bits can be modified.

  ;;    end if

  ;; else (if cpl = 0)

  ;;    if operand-size = 8 then
  ;;       rflags := 64-bit-pop()
  ;;       RF, VM, and all reserved bits are unaffected, VIP and VIF
  ;;       are cleared, all other non-reserved flags can be modified.

  ;;    else (if operand-size = 2)
  ;;      eflags[15:0] := 16-bit-pop()
  ;;      All non-reserved flags can be modified

  ;;    end if

  ;; end if

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'POPF #x9D '(:nil nil) 'x86-popf)

  :body

  (b* ((ctx 'x86-popf)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p3? (equal #.*operand-size-override*
		   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if p3?
	    2
	  ;; 4-byte operand size is N.E. in 64-bit mode
	  8))
       (rsp (rgfi *rsp* x86))
       ((when (not (canonical-address-p rsp)))
	(!!ms-fresh :rsp-not-canonical rsp))
       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
	(+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
       ;; Raise a #SS exception.
       ((when (mbe :logic (not (canonical-address-p new-rsp))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       new-rsp))))
	(!!ms-fresh :ss-exception-new-rsp-not-canonical new-rsp))

       ((mv flg0 val x86)
	(rm-size operand-size rsp :r x86))
       ((when flg0) ;; #SS exception?
	(!!ms-fresh :rm-size-error flg0))

       ((the (unsigned-byte 32) val)
	;; All reserved bits should be unaffected.  This ensures that the bit 1
	;; of rflags is set, and bits 3, 5, 15, and 22-63 are cleared.
	(logior 2 (the (unsigned-byte 32) (logand #x3f7fd7 val))))

       ;; Update the x86 state:
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86
	(case operand-size
	  (2
	   ;; All non-reserved flags can be modified
	   (!rflags val x86))

	  (otherwise
	   ;; VIP and VIF cleared.  RF, VM unaffected.  Other non-reserved
	   ;; flags can be modified.
	   (let* ((rf (the (unsigned-byte 1) (flgi #.*rf* x86)))
		  (vm (the (unsigned-byte 1) (flgi #.*vm* x86)))
		  (x86 (!rflags val x86))
		  (x86 (!flgi #.*rf* rf x86))
		  (x86 (!flgi #.*vm* vm x86))
		  (x86 (!flgi #.*vip* 0 x86))
		  (x86 (!flgi #.*vif* 0 x86)))
	     x86))))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       (x86 (!rip temp-rip x86)))
      x86))

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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #x88 '(:nil nil)
				      'x86-mov-Op/En-MR)
    (add-to-implemented-opcodes-table 'MOV #x89 '(:nil nil)
				      'x86-mov-Op/En-MR))

  :body

  (b* ((ctx 'x86-mov-Op/En-MR)

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (the (unsigned-byte 8) (prefixes-slice :group-2-prefix prefixes)))
       (p3? (equal #.*operand-size-override*
		   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 1 8) operand-size)
	(if (equal opcode #x88)
	    1
	  (if (and (equal opcode #x89)
		   (logbitp #.*w* rex-byte))
	      8
	    (if p3?
		;; See Table 3-4, P. 3-26, Intel Vol. 1.
		2 ; 16-bit operand-size
	      4))))

       (register (rgfi-size operand-size (reg-index reg rex-byte #.*r*)
			    rex-byte x86))

       ((mv flg0 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
	(if (equal mod #b11)
	    (mv nil 0 0 x86)
	  (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86)))
       ((when flg0)
	(!!ms-fresh :x86-effective-addr-error flg0))
       ((mv flg1 v-addr)
	(case p2
	  (0 (mv nil v-addr))
	  ;; I don't really need to check whether FS and GS base are
	  ;; canonical or not.  On the real machine, if the MSRs
	  ;; containing these bases are assigned non-canonical
	  ;; addresses, an exception is raised.
	  (#.*fs-override*
	   (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
		  (fs-base (n64-to-i64 nat-fs-base)))
	     (if (not (canonical-address-p fs-base))
		 (mv 'Non-Canonical-FS-Base fs-base)
	       (mv nil (+ fs-base v-addr)))))
	  (#.*gs-override*
	   (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
		  (gs-base (n64-to-i64 nat-gs-base)))
	     (if (not (canonical-address-p gs-base))
		 (mv 'Non-Canonical-GS-Base gs-base)
	       (mv nil (+ gs-base v-addr)))))
	  (t (mv 'Unidentified-P2 v-addr))))
       ((when flg1)
	(!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg1))
       ((when (not (canonical-address-p v-addr)))
	(!!ms-fresh :v-addr-not-canonical v-addr))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))

       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:
       ((mv flg2 x86)
	(x86-operand-to-reg/mem operand-size register v-addr rex-byte
				r/m mod x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
	(!!ms-fresh :x86-operand-to-reg/mem flg2))
       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-mov-Op/En-RM

  ;; Op/En: RM
  ;; [OP REG, R/M]
  ;; 8A: MOV r8,  r/m8
  ;; 8A: MOV r16, r/m16
  ;; 8B: MOV r32, r/m32
  ;; 8B: MOV r64, r/m64

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #x8A '(:nil nil)
				      'x86-mov-Op/En-RM)
    (add-to-implemented-opcodes-table 'MOV #x8B '(:nil nil)
				      'x86-mov-Op/En-RM))
  :body

  (b* ((ctx 'x86-mov-Op/En-RM)

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
		   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if (equal opcode #x8A)
	    1
	  (if (and (equal opcode #x8B)
		   (logbitp #.*w* rex-byte))
	      8
	    (if p3?
		;; See Table 3-4, P. 3-26, Intel Vol. 1.
		2 ;; 16-bit operand-size
	      4))))

       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by) ?v-addr x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* operand-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))

       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*r*)
			reg/mem rex-byte x86))
       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-mov-Op/En-OI

  ;; Op/En: OI
  ;; [OP REG, IMM]
  ;; B0 + rb: MOV r8,  imm8
  ;; B8 + rw: MOV r16, imm16
  ;; B8 + rd: MOV r32, imm32
  ;; B8 + rd: MOV r64, imm64

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #xB0 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB1 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB2 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB3 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB4 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB5 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB6 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB7 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB8 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xB9 '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBA '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBB '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBC '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBD '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBE '(:nil nil)
				      'x86-mov-Op/En-OI)
    (add-to-implemented-opcodes-table 'MOV #xBF '(:nil nil)
				      'x86-mov-Op/En-OI))

  :body

  (b* ((ctx 'x86-mov-Op/En-OI)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       (p3? (equal #.*operand-size-override*
		   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if (and (<= #xB0 opcode) ;; B0+rb
		 (<= opcode #xB7))
	    1
	  (if (and (<= #xB8 opcode) ;; B8 +rw
		   (<= opcode #xBE) ;; CUONG: Change to bf?
		   (logbitp #.*w* rex-byte))
	      8
	    (if p3?
		;; See Table 3-4, P. 3-26, Intel Vol. 1.
		2 ; 16-bit operand-size
	      4))))

       ((mv flg0 imm x86)
	(rm-size operand-size temp-rip :x x86))
       ((when flg0)
	(!!ms-fresh :imm-rm-size-error flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip operand-size))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       (reg (the (unsigned-byte 3) (logand 7 opcode)))
       ;; Update the x86 state:
       ;; See Intel Table 3.1, p.3-3, Vol. 2-A
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*b*)
			imm rex-byte x86))
       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-mov-Op/En-MI

  ;; Op/En: MI
  ;; [OP R/M, IMM]
  ;; C6/0: MOV r/m8, imm8
  ;; C7/0: MOV r/m16, imm16
  ;; C7/0: MOV r/m32, imm32
  ;; C7/0: MOV r/m64, imm32

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOV #xC6 '(:reg 0)
				      'x86-mov-Op/En-MI)
    (add-to-implemented-opcodes-table 'MOV #xC7 '(:reg 0)
				      'x86-mov-Op/En-MI))

  :body

  (b* ((ctx 'x86-mov-Op/En-MI)
       (mod (mrm-mod modr/m))
       (r/m (mrm-r/m modr/m))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
		   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if (equal opcode #xC6)
	    1
	  (if p3?
	      ;; See Table 3-4, P. 3-26, Intel Vol. 1.
	      2 ;; 16-bit operand-size
	    4)))
       ((the (integer 1 8) reg/mem-size)
	(if (and (equal opcode #xC7)
		 (logbitp #.*w* rex-byte))
	    8
	  operand-size))

       ((mv flg0 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
	(if (equal mod #b11)
	    (mv nil 0 0 x86)
	  (x86-effective-addr p4? temp-rip rex-byte r/m mod sib
			      operand-size x86)))
       ((when flg0)
	(!!ms-fresh :x86-effective-addr-error flg0))
       ((mv flg1 v-addr)
	(case p2
	  (0 (mv nil v-addr))
	  ;; I don't really need to check whether FS and GS base are
	  ;; canonical or not.  On the real machine, if the MSRs
	  ;; containing these bases are assigned non-canonical
	  ;; addresses, an exception is raised.
	  (#.*fs-override*
	   (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
		  (fs-base (n64-to-i64 nat-fs-base)))
	     (if (not (canonical-address-p fs-base))
		 (mv 'Non-Canonical-FS-Base fs-base)
	       (mv nil (+ fs-base v-addr)))))
	  (#.*gs-override*
	   (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
		  (gs-base (n64-to-i64 nat-gs-base)))
	     (if (not (canonical-address-p gs-base))
		 (mv 'Non-Canonical-GS-Base gs-base)
	       (mv nil (+ gs-base v-addr)))))
	  (t (mv 'Unidentified-P2 v-addr))))
       ((when flg1)
	(!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg1))
       ((when (not (canonical-address-p v-addr)))
	(!!ms-fresh :v-addr-not-canonical v-addr))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((mv flg2 imm x86)
	(rm-size operand-size temp-rip :x x86))
       ((when flg2)
	(!!ms-fresh :imm-rm-size-error flg2))
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip operand-size))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))
       (imm (if (equal reg/mem-size 8)
		;; Sign-extended
		(n64 (n32-to-i32 imm))
	      imm))

       ;; Update the x86 state:
       ((mv flg3 x86)
	(x86-operand-to-reg/mem reg/mem-size imm v-addr rex-byte
				r/m mod x86))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg3)
	(!!ms-fresh :x86-operand-to-reg/mem flg3))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: CALL
;; ======================================================================

;; From Intel Vol. 1, 6-11:

;; In 64-bit mode, the operand size for all near branches (CALL, RET,
;; JCC, JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions
;; update the 64-bit RIP without the need for a REX operand-size
;; prefix.

;; The following aspects of near branches are controlled by the
;; effective operand size:

;; Truncation of the size of the instruction pointer Size of a stack
;; pop or push, due to a CALL or RET Size of a stack-pointer increment
;; or decrement, due to a CALL or RET Indirect-branch operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits
;; regardless of operand size prefixes (operand size prefixes are
;; silently ignored). However, the displacement field for relative
;; branches is still limited to 32 bits and the address size for near
;; branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they
;; also impact the address calculation for memory indirect
;; branches. Such addresses are 64 bits by default; but they can be
;; overridden to 32 bits by an address size prefix.

(def-inst x86-call-E8-Op/En-M

  ;; Call near, displacement relative to the next instruction
  ;; Op/En: M
  ;; E8 cd (CALL rel16/32)
  ;; Note E8 cw is N.S. in 64-bit mode.

  ;; The address-size override prefix will not have any effect here
  ;; since we have no memory operands.  I should check this once more.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'CALL #xE8 '(:nil nil) 'x86-call-E8-Op/En-M)

  :body

  (b* ((ctx 'x86-call-E8-Op/En-M)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       ((mv flg0 (the (signed-byte 32) rel32) x86)
	(rim32 temp-rip :x x86))
       ((when flg0)
	(!!ms-fresh :rim32-error flg0))
       ((the (signed-byte #.*max-linear-address-size+1*) next-rip)
	(+ 4 temp-rip))
       ((when (mbe :logic (not (canonical-address-p next-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       next-rip))))
	(!!ms-fresh :next-rip-invalid next-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) call-rip)
	(+ next-rip rel32))
       ((when (mbe :logic (not (canonical-address-p call-rip))
		   :exec (or
			  (< (the (signed-byte
				   #.*max-linear-address-size+1*)
			       call-rip) #.*-2^47*)
			  (<= #.*2^47*
			      (the (signed-byte
				    #.*max-linear-address-size+1*)
				call-rip)))))
	(!!ms-fresh :temp-rip-invalid call-rip))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp 8))
       ((when (not (canonical-address-p new-rsp)))
	(!!ms-fresh :invalid-new-rsp new-rsp))
       ;; Update the x86 state:
       ;; Push the return address on the stack.
       ((mv flg1 x86)
	(write-canonical-address-to-memory
	 (the (signed-byte #.*max-linear-address-size*) new-rsp)
	 next-rip  x86))
       ((when flg1)
	;; #SS/#GP exception?
	(!!ms-fresh :write-canonical-address-to-memory flg1))
       ;; Update the rip to point to the called procedure.
       (x86 (!rip call-rip x86))
       ;; Decrement the stack pointer.
       (x86 (!rgfi *rsp* new-rsp x86)))
      x86))

(def-inst x86-call-FF/2-Op/En-M

  ;; Call near, absolute indirect, address given in r/64.
  ;; Op/En: M
  ;; FF/2 r/m64
  ;; Note that FF/2 r/m16 and r/m32 are N.E. in 64-bit mode.

  :parents (one-byte-opcodes)
  :guard-debug t
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'CALL #xFF '(:reg 2)
				    'x86-call-FF/2-Op/En-M)

  :body

  (b* ((ctx ' x86-call-FF/2-Op/En-M)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       ;; Note that the reg field serves as an opcode extension for
       ;; this instruction.  The reg field will always be 2 when this
       ;; function is called.

       ((mv flg0 (the (unsigned-byte 64) call-rip) (the (unsigned-byte 3) increment-rip-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* 8 p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))
       ((the (signed-byte #.*max-linear-address-size+1*) next-rip)
	(+ temp-rip increment-rip-by))
       ((when (mbe :logic (not (canonical-address-p next-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       next-rip))))
	(!!ms-fresh :temp-rip-invalid next-rip))

       ;; Converting call-rip into a "good" address in our world...
       (call-rip (n64-to-i64 call-rip))
       ((when (not (canonical-address-p call-rip)))
	(!!ms-fresh :temp-rip-invalid call-rip))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp 8))
       ;; TO-DO@Shilpi: #SS/#GP exception?
       ((when (not (canonical-address-p new-rsp)))
	(!!ms-fresh :invalid-new-rsp new-rsp))
       ;; Update the x86 state:
       ;; Push the return address on the stack.
       ((mv flg1 x86)
	(write-canonical-address-to-memory
	 (the (signed-byte #.*max-linear-address-size*) new-rsp)
	 (the (signed-byte #.*max-linear-address-size*) next-rip)
	 x86))
       ((when flg1)
	(!!ms-fresh :write-canonical-address-to-memory flg1))
       ;; Update the rip to point to the called procedure.
       (x86 (!rip call-rip x86))
       ;; Decrement the stack pointer.
       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*) new-rsp) x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: RET
;; ======================================================================

;; From Intel Vol. 1, 6-11:

;; In 64-bit mode, the operand size for all near branches (CALL, RET,
;; JCC, JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions
;; update the 64-bit RIP without the need for a REX operand-size
;; prefix.

;; The following aspects of near branches are controlled by the
;; effective operand size:
;;   Truncation of the size of the instruction pointer Size of a stack
;;   pop or push, due to a CALL or RET Size of a stack-pointer
;;   increment or decrement, due to a CALL or RET Indirect-branch
;;   operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits
;; regardless of operand size prefixes (operand size prefixes are
;; silently ignored). However, the displacement field for relative
;; branches is still limited to 32 bits and the address size for near
;; branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they
;; also impact the address calculation for memory indirect
;; branches. Such addresses are 64 bits by default; but they can be
;; overridden to 32 bits by an address size prefix.

(def-inst x86-ret

  ;; Op/En: #xC2 iw: I:  Near return to calling procedure and pop imm16 bytes from
  ;;                     stack
  ;;        #xC3:    NP: Near return to calling procedure

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'RET #xC2 '(:nil nil) 'x86-ret)
    (add-to-implemented-opcodes-table 'RET #xC3 '(:nil nil) 'x86-ret))

  :body

  (b* ((ctx 'x86-ret)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (rsp (rgfi *rsp* x86))
       ;; #SS/#GP exception?
       ((when (not (canonical-address-p rsp)))
	(!!ms-fresh :old-rsp-invalid rsp))

       ((mv flg0 (the (signed-byte #.*max-linear-address-size+1*) new-rsp) x86)
	(if (equal opcode #xC3)
	    (mv nil (+ (the (signed-byte #.*max-linear-address-size*) rsp) 8) x86)
	  (b* (((mv flg0 (the (unsigned-byte 16) imm16) x86)
		(rm16 temp-rip :x x86)))
	      (mv flg0 (+ (the (signed-byte #.*max-linear-address-size*) rsp) imm16) x86))))
       ((when flg0)
	(!!ms-fresh :imm-rm16-error flg0))

       ;; #SS/#GP exception?
       ((when (mbe :logic (not (canonical-address-p new-rsp))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       new-rsp))))
	(!!ms-fresh :new-rsp-invalid new-rsp))
       ((mv flg (the (signed-byte 64) tos) x86)
	(rim64 rsp :r x86))
       ;; #SS/#GP exception?
       ((when flg)
	(!!ms-fresh :rim64-error flg))
       ;; #SS/#GP exception?
       ((when (not (canonical-address-p tos)))
	(!!ms-fresh :invalid-return-address tos))
       ;; Update the x86 state:
       ;; Increment the stack pointer.
       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*)
			   new-rsp) x86))
       ;; Update the rip to point to the return address.
       (x86 (!rip (the (signed-byte #.*max-linear-address-size*) tos) x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: LEAVE
;; ======================================================================

(def-inst x86-leave

  ;; The LEAVE instruction releases the stack frame set up by an
  ;; earlier ENTER instruction.

  ;; Op/En: NP
  ;; C9
  ;; RSP := RBP
  ;; rBP := Pop() (i.e. get bytes from the stack, also considering the
  ;; operand-size override prefix, and put them in rBP, and then
  ;; increment the stack pointer appropriately)

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'LEAVE #xC9 '(:nil nil)
				    'x86-leave)

  :body

  (b* ((ctx 'x86-leave)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p3 (equal #.*operand-size-override*
		  (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 2 8) pop-bytes)
	(if p3
	    2
	  8))
       (rbp (rgfi *rbp* x86))
       ((when (not (canonical-address-p rbp)))
	(!!ms-fresh :rbp-not-canonical rbp))
       ((mv flg val x86)
	(rm-size pop-bytes
		 (the (signed-byte #.*max-linear-address-size*) rbp)
		 :r x86))
       ((when flg) ;; Will catch "bad" rsp errors too
	(!!ms-fresh :rm-size-error flg))
       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
	(+ (the (signed-byte #.*max-linear-address-size*) rbp) pop-bytes))
       ((when (mbe :logic (not (canonical-address-p new-rsp))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       new-rsp))))
	(!!ms-fresh :invalid-rsp new-rsp))

       ;; Update the x86 state:
       ;; We chose to write the value val into the register using !rgfi-size
       ;; rather than !rgfi since val is a n64p value and !rgfi expects an i64p
       ;; value.

       (x86 (!rgfi-size pop-bytes *rbp* val rex-byte x86))
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: HLT
;; ======================================================================

;; TO-DO@Shilpi: I haven't specified the halt instruction correctly
;; --- halt can be called only in the supervisor mode.  For now, we
;; use the HALT instruction for convenience, e.g., when we want to
;; stop program execution.

(def-inst x86-hlt

  ;; Op/En: NP
  ;; F4

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'HLT #xF4 '(:nil nil) 'x86-hlt)

  :body

  (b* ((ctx 'x86-hlt)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       ;; Update the x86 state:

       ;; See p.3-481, Intel Vol. 2A. Instruction pointer is saved.
       ;; "If an interrupt ... is used to resume execution after a HLT
       ;; instruction, the saved instruction pointer points to the instruction
       ;; following the HLT instruction."
       (x86 (!rip temp-rip x86)))
      (!!ms-fresh :legal-halt :hlt)))

;; ======================================================================
;; INSTRUCTION: NOP
;; ======================================================================

(def-inst x86-nop

  ;; Note: With operand-size override prefix (#x66), the single byte
  ;; NOP instruction is equivalent to XCHG ax, ax.

  ;; Op/En: NP
  ;; 90

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'NOP #x90 '(:nil nil) 'x86-nop)

  :body


  (b* ((ctx 'x86-nop)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes)))
      ;; Update the x86 state:
      (!rip temp-rip x86)))

(def-inst x86-two-byte-nop

  ;; Op/En: NP
  ;; 0F 1F/0

  ;; The Intel manual (Vol. 2B, p. 4-162) has a note on the recommended
  ;; multi-byte NOP sequences, and the address-size override prefix is
  ;; absent from all of them.  However, since the operand for the
  ;; multi-byte NOP is an r/m operand, we account for the effect of that
  ;; prefix anyway.

  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'NOP #x0F1F '(:reg 0) 'x86-two-byte-nop)

  :body


  (b* ((ctx 'x86-two-byte-nop)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0 (the (signed-byte 64) ?v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
	(if (equal mod #b11)
	    (mv nil 0 0 x86)
	  (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86)))
       ((when flg0)
	(!!ms-fresh :x86-effective-addr flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :next-rip-invalid temp-rip))
       ;; Update the x86 state:
       (x86 (!rip temp-rip x86)))
      x86))

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

  ;; Note that opcode #x90 is XCHG rAX, rAX, i.e. NOP.  However, we
  ;; choose to model it separately as a NOP for the sake of execution
  ;; efficiency.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'XCHG #x86 '(:nil nil)
				      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x87 '(:nil nil)
				      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x91 '(:nil nil)
				      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x92 '(:nil nil)
				      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x93 '(:nil nil)
				      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x94 '(:nil nil)
				      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x95 '(:nil nil)
				      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x96 '(:nil nil)
				      'x86-xchg)
    (add-to-implemented-opcodes-table 'XCHG #x97 '(:nil nil)
				      'x86-xchg))
  :body

  (b* ((ctx 'x86-xchg)
       (lock (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when (and lock (equal opcode #x90)))
	(!!ms-fresh :lock-prefix prefixes))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       (reg (mrm-reg modr/m))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #x86))
       (reg/mem-size (select-operand-size select-byte-operand rex-byte nil
					  prefixes))

       ;; Fetch the first operand and put it in val1.
       ;; If the opcode is #x90+rw/rd, we let rax be the first operand.
       ;; For other opcodes, we let the operand specified by the r/m field to
       ;; be the first operand.
       ((mv flg0 val1 (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
	(if (equal (ash opcode -4) 9) ;; #x90+rw/rd
	    (mv nil (rgfi-size reg/mem-size *rax* rex-byte x86)
		0 0 x86)
	  (x86-operand-from-modr/m-and-sib-bytes
	   #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86)))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))
       ((when (mbe :logic (not (canonical-address-p v-addr))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       v-addr))))
	(!!ms-fresh :v-addr-not-canonical v-addr))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

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
	    (let ((x86 (!rgfi-size reg/mem-size *rax* val2 rex-byte
				   x86)))
	      (mv nil x86))
	  (x86-operand-to-reg/mem reg/mem-size val2
				  (the (signed-byte #.*max-linear-address-size*) v-addr)
				  rex-byte r/m mod x86)))
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

       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: LOOP
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

(def-inst x86-loop

  ;; E0: LOOPNE/LOOPNZ rel8
  ;; E1: LOOPE/LOOPZ rel8
  ;; E2: LOOP rel8

  ;; Intel Vol2A, p. 3-604 says:
  ;; "Performs the loop operation using the RCX, ECX or CX as a counter
  ;; (depending on whether address size is 64 bits, 32 bits, or 16
  ;; bits."

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'LOOP #xE0 '(:nil nil)
				      'x86-loop)
    (add-to-implemented-opcodes-table 'LOOP #xE1 '(:nil nil)
				      'x86-loop)
    (add-to-implemented-opcodes-table 'LOOP #xE2 '(:nil nil)
				      'x86-loop))

  :body

  (b* ((ctx 'x86-loop)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	;; CMP does not allow a LOCK prefix.
	(!!ms-fresh :lock-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 4 8) counter-size)
	(if p4?
	    4 ;; ECX is chosen
	  8   ;; RCX is chosen
	  ))
       (counter (rgfi-size counter-size *rcx* rex-byte x86))
       (counter (trunc counter-size (1- counter)))

       ((the (unsigned-byte 1) zf) (flgi #.*zf* x86))

       (branch-cond
	(if (equal opcode #xE2) ;; LOOP
	    (not (equal counter 0))
	  (if (equal opcode #xE1) ;; LOOPE/LOOPZ
	      (and (equal zf 1)
		   (not (equal counter 0)))
	    ;; #xE0: LOOPNE/LOOPNZ
	    (and (equal zf 0)
		 (not (equal counter 0))))))

       ((mv flg0 (the (signed-byte #.*max-linear-address-size+1*) rel8/temp-rip) x86)
	(if branch-cond
	    (rim-size 1 temp-rip :x x86)
	  (mv nil (1+ temp-rip) x86)))
       ((when flg0)
	(!!ms-fresh :rim-error flg0))

       ((the (signed-byte 51) temp-rip)
	(if branch-cond
	    (b* (((the (signed-byte 50) next-rip)
		  (1+ temp-rip))
		 ((the (signed-byte 51) temp-rip)
		  (+ next-rip rel8/temp-rip)))
		temp-rip)
	  rel8/temp-rip))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (or
			  (< (the (signed-byte 51) temp-rip) #.*-2^47*)
			  (<= #.*2^47* (the (signed-byte 51) temp-rip)))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; Update the x86 state:
       (x86 (!rip temp-rip x86)))
      x86))

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
      (#x0 (equal 1 (the (unsigned-byte 1) (flgi #.*of* x86))))
      (#x1 (equal 0 (the (unsigned-byte 1) (flgi #.*of* x86))))
      (#x2 (equal 1 (the (unsigned-byte 1) (flgi #.*cf* x86))))
      (#x3 (equal 0 (the (unsigned-byte 1) (flgi #.*cf* x86))))
      (#x4 (equal 1 (the (unsigned-byte 1) (flgi #.*zf* x86))))
      (#x5 (equal 0 (the (unsigned-byte 1) (flgi #.*zf* x86))))
      (#x6 (or (equal 1 (the (unsigned-byte 1) (flgi #.*cf* x86)))
	       (equal 1 (the (unsigned-byte 1) (flgi #.*zf* x86)))))
      (#x7 (and (equal 0 (the (unsigned-byte 1) (flgi #.*cf* x86)))
		(equal 0 (the (unsigned-byte 1) (flgi #.*zf* x86)))))
      (#x8 (equal 1 (the (unsigned-byte 1) (flgi #.*sf* x86))))
      (#x9 (equal 0 (the (unsigned-byte 1) (flgi #.*sf* x86))))
      (#xA (equal 1 (the (unsigned-byte 1) (flgi #.*pf* x86))))
      (#xB (equal 0 (the (unsigned-byte 1) (flgi #.*pf* x86))))
      (#xC (not (equal (the (unsigned-byte 1) (flgi #.*sf* x86))
		       (the (unsigned-byte 1) (flgi #.*of* x86)))))
      (#xD (equal (the (unsigned-byte 1) (flgi #.*sf* x86))
		  (the (unsigned-byte 1) (flgi #.*of* x86))))
      (#xE (or (equal 1 (the (unsigned-byte 1) (flgi #.*zf* x86)))
	       (not (equal (the (unsigned-byte 1) (flgi #.*sf* x86))
			   (the (unsigned-byte 1) (flgi #.*of* x86))))))
      (#xF (and (equal 0 (the (unsigned-byte 1) (flgi #.*zf* x86)))
		(equal (the (unsigned-byte 1) (flgi #.*sf* x86))
		       (the (unsigned-byte 1) (flgi #.*of* x86)))))
      (otherwise ;; will not be reached
       nil))))

(def-inst x86-one-byte-jcc

  ;; Jump (short) if condition is met

  ;; Intel Vol. 2A, p. 3-554 says: "In 64-bit mode, operand size is
  ;; fixed at 64 bits. JMP Short is RIP + 8-bit offset sign extended to
  ;; 64 bits."

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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'JO #x70 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JNO #x71 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JC #x72 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JNC #x73 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JZ #x74 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JNZ #x75 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JBE #x76 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JNBE #x77 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JS #x78 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JNS #x79 '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JP #x7A '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JNP #x7B '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JL #x7C '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JNL #x7D '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JLE #x7E '(:nil nil)
				      'x86-one-byte-jcc)
    (add-to-implemented-opcodes-table 'JNLE #x7F '(:nil nil)
				      'x86-one-byte-jcc))
  :body

  (b* ((ctx 'x86-one-byte-jcc)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       (branch-cond (jcc/cmovcc/setcc-spec opcode x86))
       ((mv ?flg (the (signed-byte #.*max-linear-address-size+1*) rel8/next-rip) x86)
	(if branch-cond
	    (rim-size 1 temp-rip :x x86)
	  (mv nil (+ 1 temp-rip) x86)))
       ((when flg)
	(!!ms-fresh :rim-size-error flg))
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(if branch-cond
	    (+ (+ 1 temp-rip) ;; rip of the next instruction
	       rel8/next-rip) ;; rel8
	  rel8/next-rip)      ;; next-rip
	)
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (or
			  (< (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip)
			     #.*-2^47*)
			  (<= #.*2^47*
			      (the (signed-byte
				    #.*max-linear-address-size+1*)
				temp-rip)))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; Update the x86 state:
       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-two-byte-jcc

  ;; Jump (near) if condition is met

  ;; Intel Vol. 2A, p. 3-554 says: "In 64-bit mode, operand size is
  ;; fixed at 64 bits. JMP Short is RIP + 32-bit offset sign extended to
  ;; 64 bits."

  ;; Two-byte Jcc: The operand-size is forced to a 64-bit operand size
  ;; when in 64-bit mode (prefixes that change operand size are ignored
  ;; for this instruction in 64-bit mode).  See Intel Manual, Vol. 2C,
  ;; p. A-8.

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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'JO #x0F80 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JNO #x0F81 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JC #x0F82 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JNC #x0F83 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JZ #x0F84 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JNZ #x0F85 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JBE #x0F86 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JNBE #x0F87 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JS #x0F88 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JNS #x0F89 '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JP #x0F8A '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JNP #x0F8B '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JL #x0F8C '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JNL #x0F8D '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JLE #x0F8E '(:nil nil)
				      'x86-two-byte-jcc)
    (add-to-implemented-opcodes-table 'JNLE #x0F8F '(:nil nil)
				      'x86-two-byte-jcc))

  :body

  ;; Note: Here opcode is the second byte of the two byte opcode.

  (b* ((ctx 'x86-two-byte-jcc)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       (branch-cond (jcc/cmovcc/setcc-spec opcode x86))
       ((mv ?flg (the (signed-byte #.*max-linear-address-size+1*)
		   rel32/next-rip)
	    x86)
	(if branch-cond
	    (rim-size 4 temp-rip :x x86) ;; rel32
	  (mv nil (+ 4 temp-rip) x86)))  ;; next-rip
       ((when flg)
	(!!ms-fresh :rim-size-error flg))
       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(if branch-cond
	    (+ (the (signed-byte #.*max-linear-address-size+1*)
		 (+ 4 temp-rip)) ;; rip of the next instruction
	       rel32/next-rip)   ;; rel32
	  rel32/next-rip)        ;; next-rip
	)

       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (or
			  (< (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip)
			     #.*-2^47*)
			  (<= #.*2^47*
			      (the (signed-byte
				    #.*max-linear-address-size+1*)
				temp-rip)))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ;; Update the x86 state:
       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-jrcxz

  ;; Jump (short) if condition is met

  ;; E3 cb: JECXZ rel8 Jump short if ECX is 0
  ;; E3 cb: JRCXZ rel8 Jump short if RCX is 0

  ;; The register checked is determined by the address-size attribute.

  ;; Jump short: RIP = RIP + 8-bit offset sign-extended to 64-bits

  ;; Op/En: D

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'JRCXZ #xE3 '(:nil nil) 'x86-jrcxz)

  :body

  (b* ((ctx 'x86-jrcxz)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       (register-size (if p4? 4 8))
       (branch-cond
	(equal (rgfi-size register-size *rcx* rex-byte x86) 0))
       ((mv ?flg (the (signed-byte #.*max-linear-address-size+1*) rel8/next-rip) x86)
	(if branch-cond
	    (rim-size 1 temp-rip :x x86)
	  (mv nil (+ 1 temp-rip) x86)))
       ((when flg)
	(!!ms-fresh :rim-size-error flg))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(if branch-cond
	    (+ (the (signed-byte #.*max-linear-address-size+1*)
		 (+ 1 temp-rip)) ;; rip of the next instruction
	       rel8/next-rip)    ;; rel8
	  rel8/next-rip)         ;; next-rip
	)
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (or
			  (< (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip)
			     #.*-2^47*)
			  (<= #.*2^47*
			      (the (signed-byte
				    #.*max-linear-address-size+1*)
				temp-rip)))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; Update the x86 state:
       (x86 (!rip temp-rip x86)))
      x86))

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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CMOVO #x0F40 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVNO #x0F41 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVC #x0F42 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVNC #x0F43 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVZ #x0F44 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVNZ #x0F45 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVBE #x0F46 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVNBE #x0F40F4 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVS #x0F48 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVNS #x0F49 '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVP #x0F4A '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVNP #x0F4B '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVL #x0F4C '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVNL #x0F4D '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVLE #x0F4E '(:nil nil)
				      'x86-cmovcc)
    (add-to-implemented-opcodes-table 'CMOVNLE #x0F4F '(:nil nil)
				      'x86-cmovcc))

  :body

  ;; Note, opcode here denotes the second byte of the two-byte opcode.

  (b* ((ctx 'x86-cmovcc)

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))

       ((the (integer 1 8) operand-size)
	(select-operand-size nil rex-byte nil prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* operand-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       (branch-cond (jcc/cmovcc/setcc-spec opcode x86))

       ;; Update the x86 state:
       (x86
	(if branch-cond
	    (!rgfi-size operand-size (reg-index reg rex-byte #.*r*)
			reg/mem rex-byte x86)
	  x86))
       (x86 (!rip temp-rip x86)))
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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'SETO #x0F90 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETNO #x0F91 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETC #x0F92 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETNC #x0F93 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETZ #x0F94 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETNZ #x0F95 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETBE #x0F96 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETNBE #x0F97 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETS #x0F98 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETNS #x0F99 '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETP #x0F9A '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETNP #x0F9B '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETL #x0F9C '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETNL #x0F9D '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETLE #x0F9E '(:nil nil)
				      'x86-setcc)
    (add-to-implemented-opcodes-table 'SETNLE #x0F9F '(:nil nil)
				      'x86-setcc))

  :body

  ;; Note, opcode here denotes the second byte of the two-byte opcode.

  (b* ((ctx 'x86-setcc)

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       ((mv flg0 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
	(if (equal mod #b11)
	    (mv nil 0 0 x86)
	  (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86)))
       ((when flg0)
	(!!ms-fresh :x86-effective-addr-error flg0))
       ((mv flg1 v-addr)
	(case p2
	  (0 (mv nil v-addr))
	  ;; I don't really need to check whether FS and GS base are
	  ;; canonical or not.  On the real machine, if the MSRs
	  ;; containing these bases are assigned non-canonical
	  ;; addresses, an exception is raised.
	  (#.*fs-override*
	   (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
		  (fs-base (n64-to-i64 nat-fs-base)))
	     (if (not (canonical-address-p fs-base))
		 (mv 'Non-Canonical-FS-Base fs-base)
	       (mv nil (+ fs-base v-addr)))))
	  (#.*gs-override*
	   (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
		  (gs-base (n64-to-i64 nat-gs-base)))
	     (if (not (canonical-address-p gs-base))
		 (mv 'Non-Canonical-GS-Base gs-base)
	       (mv nil (+ gs-base v-addr)))))
	  (t (mv 'Unidentified-P2 v-addr))))
       ((when flg1)
	(!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg1))
       ((when (not (canonical-address-p v-addr)))
	(!!ms-fresh :v-addr-not-canonical v-addr))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       (branch-cond (jcc/cmovcc/setcc-spec opcode x86))

       ;; Update the x86 state:
       (val (if branch-cond 1 0))
       ((mv flg2 x86)
	(x86-operand-to-reg/mem 1 val
				(the (signed-byte
				      #.*max-linear-address-size+1*) v-addr)
				rex-byte r/m mod x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
	(!!ms-fresh :x86-operand-to-reg/mem flg2))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: MOVSXD/MOVSLQ
;; ======================================================================

(def-inst x86-one-byte-movsxd

  ;; Op/En: RM
  ;; [OP REG, R/M]
  ;; #x63: MOVSX  r16, r/m16 (Move word to word)
  ;;       MOVSXD r32, r/m32 (Move doubleword to doubleword)
  ;;       MOVSXD r64, r/m32 (Move doubleword to quadword with sign-extension)

  ;; I am not very confident about MOVSX's second operand being r/m16.
  ;; I haven't yet come across this instruction used with an
  ;; address-size override prefix.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'MOVSXD #x63 '(:nil nil) 'x86-one-byte-movsxd)

  :body

  (b* ((ctx 'x86-one-byte-movsxd)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       ((the (integer 1 8) reg/mem-size)
	(select-operand-size nil rex-byte t prefixes))
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change
       ;; to an exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       (register-size (if (logbitp #.*w* rex-byte)
			  8
			reg/mem-size))
       (reg/mem (if (equal register-size 8)
		    (n64 (n32-to-i32 reg/mem)) ;; sign-extended
		  reg/mem))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*) reg/mem
			rex-byte x86))
       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-two-byte-movsxd

  ;; Op/En: RM
  ;; [OP REG, R/M]

  ;; #x0F BE: MOVSX r16/32/64, r/m8
  ;; (Move byte to word/doubleword/quadword with sign-extension)

  ;; #x0F BF: MOVSX r16/32/64, r/m16
  ;; (Move word to word/doubleword/quadword with sign-extension)

  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32
					       n08-to-i08
					       n16-to-i16
					       n32-to-i32
					       n64-to-i64)
					())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOVSXD #x0FBE '(:nil nil)
				      'x86-two-byte-movsxd)
    (add-to-implemented-opcodes-table 'MOVSXD #x0FBF '(:nil nil)
				      'x86-two-byte-movsxd))
  :body

  (b* ((ctx 'x86-two-byte-movsxd)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       (reg/mem-size (if (equal opcode #xBE) 1 2))

       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       (register-size (select-operand-size nil rex-byte nil prefixes))
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
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: MOVZX
;; ======================================================================

(def-inst x86-movzx

  ;; Op/En: RM
  ;; [OP REG, R/M]

  ;; #x0F B6: MOVZX r16/32/64, r/m8
  ;; (Move byte to word/doubleword/quadword with zero-extension)

  ;; #x0F B7: MOVSX r16/32/64, r/m16
  ;; (Move word to word/doubleword/quadword with zero-extension)

  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MOVZX #x0FB6 '(:nil nil)
				      'x86-movzx)
    (add-to-implemented-opcodes-table 'MOVZX #x0FB7 '(:nil nil)
				      'x86-movzx))
  :body

  (b* ((ctx 'x86-movzx)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       (reg/mem-size (if (equal opcode #xB6) 1 2))
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ((the (integer 1 8) register-size)
	(select-operand-size nil rex-byte nil prefixes))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size (reg-index reg rex-byte #.*r*) reg/mem
			rex-byte x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: CMPXCHG
;; ======================================================================

(def-inst x86-cmpxchg

  ;; Op/En: MR
  ;; 0F B0: CMPXCHG r/m8, r8
  ;; 0F B1: CMPXCHG r/m16/32/64, r16/32/64

  :parents (two-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CMPXCHG #x0FB0 '(:nil nil)
				      'x86-cmpxchg)
    (add-to-implemented-opcodes-table 'CMPXCHG #x0FB1 '(:nil nil)
				      'x86-cmpxchg))
  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-cmpxchg)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       (reg (mrm-reg modr/m))
       ;; If the lock prefix is used but the destination is not a memory
       ;; operand, then the #UD exception is raised.
       ((when (and lock? (equal mod #b11)))
	(!!ms-fresh :lock-prefix-but-destination-not-a-memory-operand
		    prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xB0))
       ((the (integer 1 8) reg/mem-size)
	(select-operand-size select-byte-operand rex-byte nil prefixes))
       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))

       ;; Fetch the first (destination) operand:
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

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
	      (x86-operand-to-reg/mem reg/mem-size register
				      (the (signed-byte #.*max-linear-address-size*) v-addr)
				      rex-byte r/m mod x86))
	  ;; rAX != reg/mem or ZF == 0
	  ;; Put the destination operand into the accumulator.
	  (let ((x86 (!rgfi-size reg/mem-size *rax* reg/mem rex-byte x86)))
	    (mv nil x86))))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg1)
	(!!ms-fresh :x86-operand-to-reg/mem-error flg1))

       (x86 (!rip temp-rip x86)))
      x86))

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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CMC #xF5 '(:nil nil)
				      'x86-cmc/clc/stc/cld/std)
    (add-to-implemented-opcodes-table 'CLC #xF8 '(:nil nil)
				      'x86-cmc/clc/stc/cld/std)
    (add-to-implemented-opcodes-table 'STC #xF9 '(:nil nil)
				      'x86-cmc/clc/stc/cld/std)
    (add-to-implemented-opcodes-table 'CLD #xFC '(:nil nil)
				      'x86-cmc/clc/stc/cld/std)
    (add-to-implemented-opcodes-table 'STD #xFD '(:nil nil)
				      'x86-cmc/clc/stc/cld/std))

  :body

  (b* ((ctx 'x86-cmc/clc/stc/cld/std)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       (x86 (case opcode
	      (#xF5 ;; CMC
	       (let* ((cf (the (unsigned-byte 1)
			    (flgi #.*cf* x86)))
		      (not-cf (if (equal cf 1) 0 1)))
		 (!flgi #.*cf* not-cf x86)))
	      (#xF8 ;; CLC
	       (!flgi #.*cf* 0 x86))
	      (#xF9 ;; STC
	       (!flgi #.*cf* 1 x86))
	      (#xFC ;; CLD
	       (!flgi #.*df* 0 x86))
	      (otherwise ;; #xFD STD
	       (!flgi #.*df* 1 x86))))

       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: BT
;; ======================================================================

(def-inst x86-bt-0F-BA

  ;; 0F BA/4: BT r/m16/32/64, imm8

  ;; If the bitBase is a register, the BitOffset can be in the range 0
  ;; to [15, 31, 63] depending on the mode and register size.  If the
  ;; bitBase is a memory address and bitOffset is an immediate operand,
  ;; then also the bitOffset can be in the range 0 to [15, 31, 63].

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :prepwork ((local (include-book "rtl/rel9/lib/top" :dir :system)))

  :implemented
  (add-to-implemented-opcodes-table 'BT #x0FBA '(:reg 4) 'x86-bt-0F-BA)

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-bt-0f-ba)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       ((the (integer 1 8) operand-size)
	(select-operand-size nil rex-byte nil prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0 bitBase (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* operand-size p2 p4? temp-rip rex-byte r/m mod sib 1 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))
       ((mv flg1 (the (unsigned-byte 8) bitOffset) x86)
	(rm-size 1 temp-rip :x x86))
       ((when flg1)
	(!!ms-fresh :rm-size-error flg1))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ 1 temp-rip))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ((the (integer 0 64) bitOffset)
	(mod bitOffset (the (integer 0 64) (ash operand-size 3))))

       ;; Update the x86 state:
       ;; CF affected. ZF unchanged. PF, AF, SF, and OF undefined.
       (x86
	(let* ((x86 (!flgi #.*cf* (the (unsigned-byte 1) (acl2::logbit bitOffset bitBase)) x86))
	       (x86 (!flgi-undefined #.*pf* x86))
	       (x86 (!flgi-undefined #.*af* x86))
	       (x86 (!flgi-undefined #.*sf* x86))
	       (x86 (!flgi-undefined #.*of* x86)))
	  x86))

       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-bt-0F-A3

  ;; 0F A3: BT r/m16/32/64, r16/32/64

  ;; If the bitBase is a register operand, the bitOffset can be in the
  ;; range 0 to [15, 31, 63] depending on the mode and register size.
  ;; If the bitBase is a memory address and bitOffset is a register
  ;; operand, the bitOffset can be:

  ;; Operand Size   Register bitOffset
  ;;      2          -2^15 to 2^15-1
  ;;      4          -2^31 to 2^31-1
  ;;      8          -2^63 to 2^63-1

  :parents (two-byte-opcodes)
  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :guard-hints (("Goal" :in-theory (e/d (n08-to-i08
					 n16-to-i16
					 n32-to-i32
					 n64-to-i64)
					())))
  :prepwork ((local (include-book "rtl/rel9/lib/top" :dir :system)))

  :implemented
  (add-to-implemented-opcodes-table 'BT #x0FA3 '(:nil nil) 'x86-bt-0F-A3)

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-bt-0f-a3)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))

       ((the (integer 1 8) operand-size)
	(select-operand-size nil rex-byte nil prefixes))
       (bitOffset (rgfi-size operand-size (reg-index reg rex-byte #.*r*)
			     rex-byte x86))
       ((mv flg0 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
	(if (equal mod #b11)
	    (mv nil 0 0 x86)
	  (let ((p4? (equal #.*addr-size-override*
			    (prefixes-slice :group-4-prefix prefixes))))
	    (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86))))
       ((when flg0)
	(!!ms-fresh :x86-effective-addr-error flg0))
       ((mv flg1 v-addr)
	(case p2
	  (0 (mv nil v-addr))
	  ;; I don't really need to check whether FS and GS base are
	  ;; canonical or not.  On the real machine, if the MSRs
	  ;; containing these bases are assigned non-canonical
	  ;; addresses, an exception is raised.
	  (#.*fs-override*
	   (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
		  (fs-base (n64-to-i64 nat-fs-base)))
	     (if (not (canonical-address-p fs-base))
		 (mv 'Non-Canonical-FS-Base fs-base)
	       (mv nil (+ fs-base v-addr)))))
	  (#.*gs-override*
	   (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
		  (gs-base (n64-to-i64 nat-gs-base)))
	     (if (not (canonical-address-p gs-base))
		 (mv 'Non-Canonical-GS-Base gs-base)
	       (mv nil (+ gs-base v-addr)))))
	  (t (mv 'Unidentified-P2 v-addr))))
       ((when flg1)
	(!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg1))
       ((when (not (canonical-address-p v-addr)))
	(!!ms-fresh :Non-Canonical-V-Addr v-addr))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ((mv flg2 bitOffset bitBase x86)
	(if (equal mod #b11)
	    ;; bitBase is a register operand.
	    (mv nil (mod bitOffset (ash operand-size 3))
		(rgfi-size operand-size (reg-index r/m rex-byte #.*b*) rex-byte
			   x86)
		x86)
	  ;; bitBase is a memory operand.
	  (b* ((bitOffset-int (case operand-size
				(1 (n08-to-i08 bitOffset))
				(2 (n16-to-i16 bitOffset))
				(4 (n32-to-i32 bitOffset))
				(t (n64-to-i64 bitOffset))))
	       (bitOffset-int-abs (abs bitOffset-int))
	       (byte-v-addr (+ (the (signed-byte
				     #.*max-linear-address-size*) v-addr)
			       (floor bitOffset-int 8)))
	       (bitNumber (mod bitOffset-int-abs 8))
	       ((mv flg1 byte x86)
		(if (canonical-address-p byte-v-addr)
		    (rm-size 1 byte-v-addr :r x86)
		  (mv (cons 'virtual-address-error byte-v-addr) 0 x86))))
	      (mv flg1 bitNumber byte x86))))
       ((when flg2)
	(!!ms-fresh :rm-size-error flg2))

       ;; Update the x86 state:
       ;; CF affected. ZF unchanged. PF, AF, SF, and OF undefined.
       (x86
	(let* ((x86 (!flgi #.*cf*
			   (the (unsigned-byte 1) (acl2::logbit bitOffset bitBase))
			   x86))
	       (x86 (!flgi-undefined #.*pf* x86))
	       (x86 (!flgi-undefined #.*af* x86))
	       (x86 (!flgi-undefined #.*sf* x86))
	       (x86 (!flgi-undefined #.*of* x86)))
	  x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: SAHF
;; ======================================================================

(def-inst x86-sahf

  ;; Opcode: #x9E

  ;; TO-DO@Shilpi: The following instruction is valid in 64-bit mode
  ;; only if the CPUID.80000001H:ECX.LAHF-SAHF[bit0] = 1.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'SAHF #x9E '(:nil nil) 'x86-sahf)

  :body

  (b* ((ctx 'x86-sahf)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       ((the (unsigned-byte 16) ax)
	(mbe :logic (rgfi-size 2 *rax* rex-byte x86)
	     :exec (rr16 *rax* x86)))
       ((the (unsigned-byte 8) ah) (ash ax -8))
       ;; Bits 1, 3, and 5 of eflags are unaffected, with the values remaining
       ;; 1, 0, and 0, respectively.
       ((the (unsigned-byte 8) ah) (logand #b11010111 (logior #b10 ah)))
       ;; Update the x86 state:
       (x86 (!rflags ah x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: LAHF
;; ======================================================================

(def-inst x86-lahf

  ;; Opcode: #x9F

  ;; TO-DO@Shilpi: The following instruction is valid in 64-bit mode
  ;; only if the CPUID.80000001H:ECX.LAHF-LAHF[bit0] = 1.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'LAHF #x9F '(:nil nil) 'x86-lahf)

  :body

  (b* ((ctx 'x86-lahf)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       ((the (unsigned-byte 8) ah)
	(logand #xff (the (unsigned-byte 32) (rflags x86))))
       ((the (unsigned-byte 16) ax)
	(mbe :logic (rgfi-size 2 *rax* rex-byte x86)
	     :exec (rr16 *rax* x86)))
       ((the (unsigned-byte 16) ax) (logior (logand #xff00 ax) ah))
       ;; Update the x86 state:
       (x86 (mbe :logic (!rgfi-size 2 *rax* ax rex-byte x86)
		 :exec (wr16 *rax* ax x86)))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: MOVS/MOVSB/MOVSW/MOVSD/MOVSQ
;; ======================================================================

(def-inst x86-movs

  ;; A4 MOVSB: Move  byte from address (R/E)SI to (R/E)DI
  ;; A5 MOVSW: Move  word from address (R/E)SI to (R/E)DI
  ;; A5 MOVSD: Move dword from address (R/E)SI to (R/E)DI
  ;; A5 MOVSQ: Move qword from address (R/E)SI to (R/E)DI

  ;; After the move operation, the (E)SI and (E)DI registers are
  ;; incremented or decremented automatically according to the setting
  ;; of the DF flag in the EFLAGS register.  If the DF flag is 0, the
  ;; registers are incremented; if the DF flag is 1, the registers are
  ;; decremented.

  ;; The following repeat prefixes can be used in conjunction with a
  ;; count in the ECX register to cause a string instruction to
  ;; repeat:
  ;; REP (F3): Repeats a string operation until the rCX register
  ;; equals 0.
  ;; REPE/REPZ (F3): Repeats a string operation until the rCX register
  ;; equals 0 or the ZF is cleared.
  ;; REPNE/REPNZ (F2): Repeats a string operation until the rCX
  ;; register equals 0 or the ZF is set to 1.

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSHF #xA4 '(:nil nil)
				      'x86-movs)
    (add-to-implemented-opcodes-table 'PUSHF #xA5 '(:nil nil)
				      'x86-movs))

  :body

  (b* ((ctx 'x86-movs)
       (group-1-prefix (the (unsigned-byte 8) (prefixes-slice :group-1-prefix prefixes)))
       (lock? (equal #.*lock* group-1-prefix))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((the (unsigned-byte 1) df) (flgi #.*df* x86))

       ((the (integer 4 8) counter/addr-size)
	(if p4?
	    4 ;; ECX is chosen
	  8   ;; RCX is chosen
	  ))

       (select-byte-operand (equal #xA4 opcode))
       ((the (integer 1 8) operand-size)
	(select-operand-size select-byte-operand rex-byte nil prefixes))

       (src-addr (if p4?
		     (rgfi-size counter/addr-size *rsi* rex-byte x86)
		   (rgfi *rsi* x86)))

       ((when (and (not p4?)
		   ;; A 32-bit address is always canonical.
		   (not (canonical-address-p src-addr))))
	(!!ms-fresh :src-addr-not-canonical src-addr))

       ((mv flg0 src x86)
	(rm-size operand-size
		 (the (signed-byte
		       #.*max-linear-address-size*) src-addr)
		 :r x86))
       ((when flg0)
	(!!ms-fresh :src-rm-size-error flg0))

       (dst-addr (if p4?
		     (rgfi-size counter/addr-size *rdi* rex-byte x86)
		   (rgfi *rdi* x86)))

       ((when (and (not p4?)
		   ;; A 32-bit address is always canonical.
		   (not (canonical-address-p dst-addr))))
	(!!ms-fresh :dst-addr-not-canonical dst-addr))
       (original-dst-addr dst-addr)

       ;; A repeating string operation can be suspended by an exception or
       ;; interrupt. When this happens, the state of the register is preserved
       ;; to allow the string operation to be resumed upon a return from the
       ;; exception or interrupt handler.

       ((mv (the (signed-byte #.*max-linear-address-size+1*) src-addr)
	    (the (signed-byte #.*max-linear-address-size+1*) dst-addr))

	(case operand-size
	  (1 (if (equal df 0)
		 (mv (+ 1 (the (signed-byte #.*max-linear-address-size*)
			    src-addr))
		     (+ 1
			(the (signed-byte #.*max-linear-address-size*)
			  dst-addr)))
	       (mv (+ -1
		      (the (signed-byte #.*max-linear-address-size*)
			src-addr))
		   (+ -1
		      (the (signed-byte #.*max-linear-address-size*)
			dst-addr)))))

	  (2 (if (equal df 0)
		 (mv (+ 2 (the (signed-byte #.*max-linear-address-size*)
			    src-addr))
		     (+ 2 (the (signed-byte #.*max-linear-address-size*)
			    dst-addr)))
	       (mv (+ -2 (the (signed-byte #.*max-linear-address-size*)
			   src-addr))
		   (+ -2 (the (signed-byte #.*max-linear-address-size*)
			   dst-addr)))))

	  (4 (if (equal df 0)
		 (mv (+ 4 (the (signed-byte #.*max-linear-address-size*)
			    src-addr))
		     (+ 4 (the (signed-byte #.*max-linear-address-size*)
			    dst-addr)))
	       (mv (+ -4 (the (signed-byte #.*max-linear-address-size*)
			   src-addr))
		   (+ -4 (the (signed-byte #.*max-linear-address-size*)
			   dst-addr)))))
	  (otherwise (if (equal df 0)
			 (mv (+ 2 (the (signed-byte #.*max-linear-address-size*)
				    src-addr))
			     (+ 2 (the (signed-byte #.*max-linear-address-size*)
				    dst-addr)))
		       (mv (+ -2 (the (signed-byte #.*max-linear-address-size*)
				   src-addr))
			   (+ -2 (the (signed-byte #.*max-linear-address-size*)
				   dst-addr)))))))

       ;; Update the x86 state:
       ((mv flg1 x86)
	(wm-size operand-size original-dst-addr src x86))
       ;; Note: If flg1 is non-nil, we bail out without changing the x86 state.
       ((when flg1)
	(!!ms-fresh :wm-size-error flg1))

       ;; REP prefix: Updating rCX and RIP:

       (x86 (case group-1-prefix
	      (#.*repe*
	       (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
		      (counter (trunc counter/addr-size (1- counter))))
		 (if (or (equal counter 0)
			 (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 0))
		     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
			    (x86 (!rip temp-rip x86)))
		       x86)
		   (let* ((x86 (!rip temp-rip x86)))
		     x86))))
	      (#.*repne*
	       (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
		      (counter (trunc counter/addr-size (1- counter))))
		 (if (or (equal counter 0)
			 (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 1))
		     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
			    (x86 (!rip temp-rip x86)))
		       x86)
		   (let* ((x86 (!rip temp-rip x86)))
		     x86))))
	      (otherwise ;; no rep prefix present
	       (!rip temp-rip x86))))

       ;; Updating rSI and rDI:
       (x86 (if p4?
		(!rgfi-size counter/addr-size *rsi*
			    (n32 (the (signed-byte
				       #.*max-linear-address-size+1*) src-addr))
			    rex-byte x86)
	      (!rgfi *rsi* (the (signed-byte
				 #.*max-linear-address-size+1*)
			     src-addr) x86)))
       (x86 (if p4?
		(!rgfi-size counter/addr-size *rdi*
			    (n32 (the
				     (signed-byte
				      #.*max-linear-address-size+1*)
				   dst-addr))
			    rex-byte x86)
	      (!rgfi *rdi* (the (signed-byte
				 #.*max-linear-address-size+1*)
			     dst-addr) x86))))
      x86))

;; ======================================================================
;; INSTRUCTION: CMPS/CMPSB/CMPSW/CMPSD/CMPSQ
;; ======================================================================

(def-inst x86-cmps

  ;; A6 CMPSB: Compare  byte from address (R/E)SI to (R/E)DI
  ;; A7 CMPSW: Compare  word from address (R/E)SI to (R/E)DI
  ;; A7 CMPSD: Compare dword from address (R/E)SI to (R/E)DI
  ;; A7 CMPSQ: Compare qword from address (R/E)SI to (R/E)DI

  ;; After the compare operation, the (E)SI and (E)DI registers are
  ;; incremented or decremented automatically according to the setting
  ;; of the DF flag in the EFLAGS register.  If the DF flag is 0, the
  ;; registers are incremented; if the DF flag is 1, the registers are
  ;; decremented.

  ;; The following repeat prefixes can be used in conjunction with a
  ;; count in the ECX register to cause a string instruction to
  ;; repeat:
  ;; REP (F3): Repeats a string operation until the rCX register
  ;; equals 0.
  ;; REPE/REPZ (F3): Repeats a string operation until the rCX register
  ;; equals 0 or the ZF is cleared.
  ;; REPNE/REPNZ (F2): Repeats a string operation until the rCX
  ;; register equals 0 or the ZF is set to 1.

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CMPS #xA6 '(:nil nil)
				      'x86-cmps)
    (add-to-implemented-opcodes-table 'CMPS #xA7 '(:nil nil)
				      'x86-cmps))

  :body

  (b* ((ctx 'x86-cmps)
       (group-1-prefix (the (unsigned-byte 8) (prefixes-slice :group-1-prefix prefixes)))
       (lock? (equal #.*lock* group-1-prefix))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((the (unsigned-byte 1) df) (flgi #.*df* x86))
       ((the (integer 4 8) counter/addr-size)
	(if p4?
	    4 ;; ECX is chosen
	  8   ;; RCX is chosen
	  ))

       (select-byte-operand (equal #xA6 opcode))
       ((the (integer 1 8) operand-size)
	(select-operand-size select-byte-operand rex-byte nil prefixes))

       (src-addr (if p4?
		     (rgfi-size counter/addr-size *rsi* rex-byte x86)
		   (rgfi *rsi* x86)))
       ((when (and (not p4?)
		   ;; A 32-bit address is always canonical.
		   (not (canonical-address-p src-addr))))
	(!!ms-fresh :src-addr-not-canonical src-addr))
       ((mv flg0 src x86)
	(rm-size operand-size src-addr :r x86))
       ((when flg0)
	(!!ms-fresh :src-rm-size-error flg0))

       (dst-addr (if p4?
		     (rgfi-size counter/addr-size *rdi* rex-byte x86)
		   (rgfi *rdi* x86)))
       ((when (and (not p4?)
		   ;; A 32-bit address is always canonical.
		   (not (canonical-address-p dst-addr))))
	(!!ms-fresh :dst-addr-not-canonical dst-addr))
       ((mv flg0 dst x86)
	(rm-size operand-size dst-addr :r x86))
       ((when flg0)
	(!!ms-fresh :dst-rm-size-error flg0))

       ;; From the AMD Manual: "To perform the comparison, the instruction
       ;; subtracts the second operand from the first operand and sets the
       ;; status flags in the same manner as the SUB instruction, but does not
       ;; alter the first operand. The two operands must be of the same size."

       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv ?result
	    (the (unsigned-byte 32) output-rflags)
	    (the (unsigned-byte 32) undefined-flags))
	(gpr-arith/logic-spec operand-size #.*OP-SUB* dst src input-rflags))

       ;; Update the x86 state:

       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ;; A repeating string operation can be suspended by an exception or
       ;; interrupt. When this happens, the state of the register is preserved
       ;; to allow the string operation to be resumed upon a return from the
       ;; exception or interrupt handler.

       ((mv (the (signed-byte #.*max-linear-address-size+1*) src-addr)
	    (the (signed-byte #.*max-linear-address-size+1*) dst-addr))
	(case operand-size
	  (1 (if (equal df 0)
		 (mv (+ (the (signed-byte
			      #.*max-linear-address-size+1*) src-addr) 1)
		     (+ (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 1))
	       (mv (- (the (signed-byte #.*max-linear-address-size+1*)
			src-addr) 1)
		   (- (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 1))))
	  (2 (if (equal df 0)
		 (mv (+ (the (signed-byte
			      #.*max-linear-address-size+1*) src-addr) 2)
		     (+ (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 2))
	       (mv (- (the (signed-byte #.*max-linear-address-size+1*)
			src-addr) 2)
		   (- (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 2))))
	  (4 (if (equal df 0)
		 (mv (+ (the (signed-byte
			      #.*max-linear-address-size+1*) src-addr) 4)
		     (+ (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 4))
	       (mv (- (the (signed-byte #.*max-linear-address-size+1*)
			src-addr) 4)
		   (- (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 4))))
	  (otherwise (if (equal df 0)
			 (mv (+ (the (signed-byte
				      #.*max-linear-address-size+1*) src-addr) 2)
			     (+ (the (signed-byte #.*max-linear-address-size+1*) dst-addr) 2))
		       (mv (- (the (signed-byte
				    #.*max-linear-address-size+1*) src-addr) 2)
			   (- (the (signed-byte
				    #.*max-linear-address-size+1*) dst-addr) 2))))))

       ;; REP prefix: Updating rCX and RIP:

       (x86 (case group-1-prefix
	      (#.*repe*
	       (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
		      (counter (trunc counter/addr-size (1- counter))))
		 (if (or (equal counter 0)
			 (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 0))
		     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
			    (x86 (!rip temp-rip x86)))
		       x86)
		   (let* ((x86 (!rip temp-rip x86)))
		     x86))))
	      (#.*repne*
	       (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
		      (counter (trunc counter/addr-size (1- counter))))
		 (if (or (equal counter 0)
			 (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 1))
		     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
			    (x86 (!rip temp-rip x86)))
		       x86)
		   (let* ((x86 (!rip temp-rip x86)))
		     x86))))
	      (otherwise ;; no rep prefix present
	       (!rip temp-rip x86))))

       ;; Updating rSI and rDI:

       (x86 (if p4?
		(!rgfi-size counter/addr-size *rsi*
			    (n32 (the (signed-byte
				       #.*max-linear-address-size+1*) src-addr))
			    rex-byte x86)
	      (!rgfi *rsi* (the (signed-byte
				 #.*max-linear-address-size+1*)
			     src-addr) x86)))
       (x86 (if p4?
		(!rgfi-size counter/addr-size *rdi*
			    (n32 (the
				     (signed-byte
				      #.*max-linear-address-size+1*)
				   dst-addr))
			    rex-byte x86)
	      (!rgfi *rdi* (the (signed-byte
				 #.*max-linear-address-size+1*)
			     dst-addr) x86))))
      x86))

;; ======================================================================
;; INSTRUCTION: STOS/STOSB/STOSW/STOSD/STOSQ
;; ======================================================================

(def-inst x86-stos

  ;; AA STOSB:             Store AL at address EDI or RDI
  ;; AB STOSW/STOSD/STOSQ: Store AX/EAX/RDX at address EDI or RDI

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSHF #xAA '(:nil nil)
				      'x86-stos)
    (add-to-implemented-opcodes-table 'PUSHF #xAB '(:nil nil)
				      'x86-stos))

  :body

  (b* ((ctx 'x86-stos)
       (group-1-prefix (the (unsigned-byte 8) (prefixes-slice :group-1-prefix prefixes)))
       (lock? (equal #.*lock* group-1-prefix))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((the (unsigned-byte 1) df) (flgi #.*df* x86))
       ((the (integer 4 8) counter/addr-size)
	(if p4?
	    4 ;; EDI and ECX are chosen.
	  8   ;; RDI and RDX are chosen.
	  ))

       (dst-addr
	(if p4?
	    (rgfi-size counter/addr-size *rdi* rex-byte x86)
	  (rgfi *rdi* x86)))
       ((when (and (not p4?)
		   ;; A 32-bit address is always canonical.
		   (not (canonical-address-p dst-addr))))
	(!!ms-fresh :dst-addr-not-canonical dst-addr))

       (select-byte-operand (equal #xAA opcode))
       ((the (integer 1 8) operand-size)
	(select-operand-size select-byte-operand rex-byte nil prefixes))

       (rAX (rgfi-size operand-size *rax* rex-byte x86))

       ;; Update the x86 state:

       ;; Writing rAX to the memory:
       ((mv flg0 x86)
	(wm-size operand-size dst-addr rAX x86))
       ((when flg0)
	(!!ms-fresh :wm-size-error flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) dst-addr)
	(case operand-size
	  (1 (if (equal df 0)
		 (+ 1 (the (signed-byte
			    #.*max-linear-address-size*) dst-addr))
	       (+ -1 (the (signed-byte
			   #.*max-linear-address-size*) dst-addr))))
	  (2 (if (equal df 0)
		 (+ 2 (the (signed-byte
			    #.*max-linear-address-size*) dst-addr))
	       (+ -2 (the (signed-byte
			   #.*max-linear-address-size*) dst-addr))))
	  (4 (if (equal df 0)
		 (+ 4 (the (signed-byte
			    #.*max-linear-address-size*) dst-addr))
	       (+ -4 (the (signed-byte
			   #.*max-linear-address-size*) dst-addr))))
	  (otherwise (if (equal df 0)
			 (+ 8 (the (signed-byte
				    #.*max-linear-address-size*) dst-addr))
		       (+ -8 (the (signed-byte
				   #.*max-linear-address-size*) dst-addr))))))

       ;; REPE/REPNE prefixes: updating the counter rCX and the RIP:

       (x86 (case group-1-prefix
	      (#.*repe*
	       (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
		      (counter (trunc counter/addr-size (1- counter))))
		 (if (or (equal counter 0)
			 (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 0))
		     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
			    (x86 (!rip temp-rip x86)))
		       x86)
		   (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86)))
		     x86))))
	      (#.*repne*
	       (let* ((counter (rgfi-size counter/addr-size *rcx* rex-byte x86))
		      (counter (trunc counter/addr-size (1- counter))))
		 (if (or (equal counter 0)
			 (equal (the (unsigned-byte 1) (flgi #.*zf* x86)) 1))
		     (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86))
			    (x86 (!rip temp-rip x86)))
		       x86)
		   (let* ((x86 (!rgfi-size counter/addr-size *rcx* counter rex-byte x86)))
		     x86))))
	      (otherwise ;; no rep prefix present
	       (!rip temp-rip x86))))

       ;; Updating the rDI:
       (x86 (if p4?
		(!rgfi-size counter/addr-size *rdi*
			    (n32 (the
				     (signed-byte
				      #.*max-linear-address-size+1*)
				   dst-addr))
			    rex-byte x86)
	      (!rgfi *rdi* (the (signed-byte
				 #.*max-linear-address-size+1*)
			     dst-addr) x86))))

      x86))

;; ======================================================================
;; INSTRUCTION: INC/DEC
;; ======================================================================

(local
 (defthm logsquash-and-logand-32
   (implies (unsigned-byte-p 32 x)
	    (equal (bitops::logsquash 1 x)
		   (logand 4294967294 x)))
   :hints (("Goal" :in-theory (e/d (bitops::logsquash)
				   (bitops::logand-with-negated-bitmask))))))

(def-inst x86-inc/dec-FE-FF

  ;; FE/0,1: INC/DEC r/m8
  ;; FF/0,1: INC/DEC r/m16, r/m32, r/m64

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'INC #xFE '(:reg 0)
				      'x86-inc/dec-FE-FF)
    (add-to-implemented-opcodes-table 'DEC #xFE '(:reg 1)
				      'x86-inc/dec-FE-FF)
    (add-to-implemented-opcodes-table 'INC #xFF '(:reg 0)
				      'x86-inc/dec-FE-FF)
    (add-to-implemented-opcodes-table 'DEC #xFF '(:reg 1)
				      'x86-inc/dec-FE-FF))

  :body

  (b* ((ctx 'x86-inc/dec-FE-FF)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))
       (select-byte-operand (equal 0 (logand 1 opcode)))
       ((the (integer 1 8) r/mem-size)
	(select-operand-size
	 select-byte-operand rex-byte nil prefixes))

       ((mv flg0 r/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* r/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Computing the flags and the result:
       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((the (unsigned-byte 1) old-cf)
	(rflags-slice :cf input-rflags))
       ((mv result output-rflags undefined-flags)
	(gpr-arith/logic-spec r/mem-size
			      (if (eql reg 0)
				  ;; INC
				  #.*OP-ADD*
				;; DEC
				#.*OP-SUB*)
			      r/mem 1 input-rflags))

       ;; Updating the x86 state:
       ;; CF is unchanged.
       (output-rflags (the (unsigned-byte 32)
			(!rflags-slice :cf old-cf output-rflags)))
       (x86 (write-user-rflags output-rflags undefined-flags x86))


       ((mv flg1 x86)
	(x86-operand-to-reg/mem r/mem-size result
				(the (signed-byte #.*max-linear-address-size*) v-addr)
				rex-byte r/m mod x86))
       ((when flg1)
	(!!ms-fresh :x86-operand-to-reg/mem flg1))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: NOT/NEG
;; ======================================================================

(def-inst x86-not/neg-F6-F7

  ;; F6/2: NOT r/m8
  ;; F7/2: NOT r/m16, r/m32, r/m64

  ;; F6/3: NEG r/m8
  ;; F7/3: NEG r/m16, r/m32, r/m64

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'NOT #xF6 '(:reg 2)
				      'x86-not/neg-F6-F7)
    (add-to-implemented-opcodes-table 'NOT #xF6 '(:reg 3)
				      'x86-not/neg-F6-F7)
    (add-to-implemented-opcodes-table 'NEG #xF7 '(:reg 2)
				      'x86-not/neg-F6-F7)
    (add-to-implemented-opcodes-table 'NEG #xF7 '(:reg 3)
				      'x86-not/neg-F6-F7))
  :body

  (b* ((ctx 'x86-not/neg-F6-F7)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal 0 (logand 1 opcode)))
       ((the (integer 0 8) r/mem-size)
	(select-operand-size select-byte-operand rex-byte nil
			     prefixes))
       ((mv flg0 r/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* r/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Computing the flags and the result:

       ((the (unsigned-byte 32) input-rflags) (rflags x86))
       ((mv result
	    (the (unsigned-byte 32) output-rflags)
	    (the (unsigned-byte 32) undefined-flags))
	(case reg
	  (3
	   ;; (NEG x) = (SUB 0 x)
	   (gpr-arith/logic-spec r/mem-size #.*OP-SUB* 0 r/mem input-rflags))
	  (otherwise
	   ;; NOT (and some other instructions not specified yet)
	   (mv (trunc r/mem-size (lognot r/mem)) 0 0))))

       ;; Updating the x86 state:
       (x86
	(if (eql reg 3)
	    (let* ( ;; CF is special for NEG.
		   (cf (the (unsigned-byte 1) (if (equal 0 r/mem) 0 1)))
		   (output-rflags
		    (the (unsigned-byte 32)
		      (!rflags-slice :cf cf output-rflags)))
		   (x86 (write-user-rflags output-rflags undefined-flags x86)))
	      x86)
	  x86))
       ((mv flg1 x86)
	(x86-operand-to-reg/mem
	 r/mem-size result (the (signed-byte #.*max-linear-address-size*) v-addr)
	 rex-byte r/m mod x86))
       ((when flg1)
	(!!ms-fresh :x86-operand-to-reg/mem flg1))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: CBW/CWDE/CDQE/CLTQ
;; ======================================================================

(def-inst x86-cbw/cwd/cdqe

  ;; Op/En: NP

  ;; #x98: CBW:   AX  := Sign-extended AL
  ;; #x98: CWDE:  EAX := Sign-extended AX
  ;; #x98: CDQE:  RAX := Sign-extended EAX

  :parents (one-byte-opcodes)
  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :guard-hints (("Goal" :in-theory (e/d (n08-to-i08
					 n16-to-i16
					 n32-to-i32
					 n64-to-i64)
					())))
  :implemented
  (add-to-implemented-opcodes-table 'CBW #x98 '(:nil nil)
				    'x86-cbw/cwd/cdqe)

  :body

  (b* ((ctx 'x86-cbw/cwd/cdqe)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       ((the (integer 1 8) register-size)
	(select-operand-size nil rex-byte nil prefixes))
       ((the (integer 1 4) src-size) (ash register-size -1))
       ((the (unsigned-byte 32) src)
	(mbe :logic
	     (rgfi-size src-size *rax* rex-byte x86)
	     :exec
	     (case src-size
	       (1 (rr08 *rax* rex-byte x86))
	       (2 (rr16 *rax* x86))
	       (4 (rr32 *rax* x86))
	       (otherwise 0))))
       (dst (if (logbitp (the (integer 0 32)
			   (1- (the (integer 0 32) (ash src-size 3))))
			 src)
		(trunc register-size (case src-size
				       (1 (n08-to-i08 src))
				       (2 (n16-to-i16 src))
				       (t (n32-to-i32 src))))
	      src))
       ;; Update the x86 state:
       (x86 (!rgfi-size register-size *rax* dst rex-byte x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: CWD/CDQ/CQO
;; ======================================================================

(def-inst x86-cwd/cdq/cqo

  ;; Op/En: NP

  ;; #x99: CWD:  DX:AX   := Sign-extended AX
  ;; #x99: CDQ:  EDX:EAX := Sign-extended EAX
  ;; #x99: CQO:  RDX:RAX := Sign-extended RAX

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'CWD #x99 '(:nil nil) 'x86-cwd/cdq/cqo)

  :body

  (b* ((ctx 'x86-cwd/cdq/cqo)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       ((the (integer 1 8) src-size)
	(select-operand-size nil rex-byte nil prefixes))
       (src (rgfi-size src-size *rax* rex-byte x86))
       (rDX (if (logbitp (1- (ash src-size 3)) src)
		(trunc src-size -1)
	      0))
       ;; Update the x86 state:
       (x86 (!rgfi-size src-size *rdx* rDX rex-byte x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: SYSCALL
;; ======================================================================

(def-inst x86-syscall-programmer-level-mode

  ;; Fast System Call to privilege level 0 system procedures.
  ;; Op/En: NP
  ;; 0F 05: SYSCALL

  ;; Note: No segment register updates/accesses here since we do not
  ;; support segments at this time.

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (programmer-level-mode x86)
			       (canonical-address-p temp-rip)))

  ;; Since this function does not specify the actual semantics of the
  ;; SYSCALL instruction, we do not add anything to the
  ;; implemented-opcodes-table, and we prefer to do that for the
  ;; "true" instruction semantic function x86-syscall instead.
  :implemented
  (make-event
   (value (quote
	   (value-triple
	    (cw "~%~%Nothing added to the implemented-opcodes-table.~%~%~%")))))

  :guard-hints (("Goal" :in-theory (e/d () (msri-is-n64p))
		 :use ((:instance msri-is-n64p (i 0)))))

  :body

  (b* ((ctx 'x86-syscall-programmer-level-mode)
       ;; 64-bit mode exceptions
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce) (ia32_efer-slice :ia32_efer-sce ia32-efer))
       ((the (unsigned-byte 1) ia32-efer-lma) (ia32_efer-slice :ia32_efer-lma ia32-efer))
       ((when (mbe :logic (or (zp ia32-efer-sce)
			      (zp ia32-efer-lma))
		   :exec (or (equal 0 ia32-efer-sce)
			     (equal 0 ia32-efer-lma))))
	(!!ms-fresh :ia32-efer-sce-or-lma=0 (cons 'ia32_efer ia32-efer)))

       ;; Update the x86 state:

       ;; SYSCALL saves the rip of the instruction following SYSCALL
       ;; to rcx.
       (x86 (!rgfi *rcx* temp-rip x86)) ;; SYSCALL

       ;; rcx is supposed to be destroyed by the kernel for security
       ;; reasons and sometimes, I see -1 in rcx after a syscall
       ;; instruction.

       ;; (x86 (!rgfi *rcx* -1 x86))

       ;; SYSCALL saves RFLAGS into R11 and then masks it using the
       ;; IA32_FMASK MSR. However, SYSRET loads the flags from R11
       ;; after masking it such that RF and VM are cleared and bit 2
       ;; is set. So, I'm just changing the flags accordingly at the
       ;; end of this semantic function.

       ((the (unsigned-byte 32) eflags) (rflags x86))

       ;; IMPORTANT NOTE:
       ;; r11 is also destroyed by the kernel, but all I've seen so
       ;; far is that the value for flags stored in r11 has the trap
       ;; flag set (bit 8, zero-based indexing). However, when flags
       ;; are restored from r11 by the sysret, the trap flag is not
       ;; set.

       ;; Also note that the Jan'13 Intel Manual says (Sec. 3.4.3.3,
       ;; V-1): "They (system flags, of which TF is one) should not be
       ;; modified by application programs."

       ((the (unsigned-byte 32) eflags)
	(!rflags-slice :tf 1 eflags))

       (x86 (wr64 *r11* eflags x86)) ;; SYSCALL

       (rax (rr64 *rax* x86))

       ;; See
       ;; http://lxr.free-electrons.com/source/arch/x86/include/asm/syscall.h#L24.
       ;; "Only the low 32 bits of orig_ax are meaningful, so we
       ;; return int.  This importantly ignores the high bits on
       ;; 64-bit, so comparisons
       ;; sign-extend the low 32 bits."

       ((the (unsigned-byte 32) eax) (n32 rax))

       (x86 (case eax
	      (#.*SYS_read* ;; Read
	       (x86-syscall-read x86))
	      (#.*SYS_write* ;; Write
	       (x86-syscall-write x86))
	      (#.*SYS_open* ;; Open
	       (x86-syscall-open x86))
	      (#.*SYS_close* ;; Close
	       (x86-syscall-close x86))
	      (#.*SYS_stat* ;; Stat
	       (x86-syscall-stat x86))
	      (#.*SYS_lstat* ;; Lstat
	       (x86-syscall-lstat x86))
	      (#.*SYS_fstat* ;; Fstat
	       (x86-syscall-fstat x86))
	      (#.*SYS_lseek* ;; Lseek
	       (x86-syscall-lseek x86))
	      (#.*SYS_dup* ;; Dup
	       (x86-syscall-dup x86))
	      (#.*SYS_dup2* ;; Dup2
	       (x86-syscall-dup2 x86))
	      (#.*SYS_fcntl* ;; Fcntl
	       (x86-syscall-fcntl x86))
	      (#.*SYS_truncate* ;; Truncate
	       (x86-syscall-truncate x86))
	      (#.*SYS_ftruncate* ;; Ftruncate
	       (x86-syscall-ftruncate x86))
	      (#.*SYS_link* ;; Link
	       (x86-syscall-link x86))
	      (#.*SYS_unlink* ;; Unlink
	       (x86-syscall-unlink x86))
	      #+(and linux (not darwin))
	      (#.*SYS_fadvise64* ;; Fadvise64
	       (x86-syscall-fadvise64 x86))
	      #+(and linux (not darwin))
	      (#.*SYS_dup3* ;; Dup3
	       (x86-syscall-dup3 x86))
	      (t
	       (let* ((x86
		       (!ms (list "Unimplemented syscall"
				  'RAX rax
				  'RIP (rip x86))
			    x86)))
		 x86))))

       ;; (- (cw "~%~%X86-SYSCALL: If SYSCALL does not return the result you ~
       ;;         expected, then you might want to check whether these ~
       ;;         books were compiled using X86ISA_EXEC set to t. See ~
       ;;         :doc build-instructions.~%~%"))


       ((when (ms x86))
	(!!ms-fresh :x86-syscall (ms x86)))

       ;; Clear RF, VM. Reserved bits retain their fixed values. Set
       ;; bit 2.

       (x86 (!flgi #.*rf* 0 x86))
       (x86 (!flgi #.*vm* 0 x86)) ;; SYSRET

       ;; SYSCALL loads a new rip from the ia32_lstar (64-bit
       ;; mode). Upon return, SYSRET copies the value saved in rcx to
       ;; the rip. Here, we cheat and directly assign temp-rip to rip.

       (x86 (!rip temp-rip x86))) ;; SYSRET
      x86))

(local
 (defthm msri-!rgfi
   (equal (msri i (!rgfi j v x86))
	  (msri i x86))
   :hints (("Goal" :in-theory (e/d (msri !rgfi) ())))))

(local
 (defthm msri-!rflags
   (equal (msri i (!rflags v x86))
	  (msri i x86))
   :hints (("Goal" :in-theory (e/d (msri !rflags) ())))))

(local
 (defthm msri-!rip
   (equal (msri i (!rip v x86))
	  (msri i x86))
   :hints (("Goal" :in-theory (e/d (msri !rip) ())))))

(local
 (defthm seg-visiblei-!seg-hiddeni
   (equal (seg-visiblei i (!seg-hiddeni j v x86))
	  (seg-visiblei i x86))
   :hints (("Goal" :in-theory (e/d (seg-visiblei !seg-hiddeni) ())))))

(local
 (defthm seg-visiblei-!rgfi
   (equal (seg-visiblei i (!rgfi j v x86))
	  (seg-visiblei i x86))
   :hints (("Goal" :in-theory (e/d (seg-visiblei !rgfi) ())))))

(local
 (defthm seg-visiblei-!rflags
   (equal (seg-visiblei i (!rflags v x86))
	  (seg-visiblei i x86))
   :hints (("Goal" :in-theory (e/d (seg-visiblei !rflags) ())))))

(local
 (defthm seg-visiblei-!rip
   (equal (seg-visiblei i (!rip v x86))
	  (seg-visiblei i x86))
   :hints (("Goal" :in-theory (e/d (seg-visiblei !rip) ())))))

(local
 (defthm seg-hiddeni-!seg-visiblei
   (equal (seg-hiddeni i (!seg-visiblei j v x86))
	  (seg-hiddeni i x86))
   :hints (("Goal" :in-theory (e/d (!seg-visiblei seg-hiddeni) ())))))

(local
 (defthm seg-hiddeni-!rgfi
   (equal (seg-hiddeni i (!rgfi j v x86))
	  (seg-hiddeni i x86))
   :hints (("Goal" :in-theory (e/d (seg-hiddeni !rgfi) ())))))

(local
 (defthm seg-hiddeni-!rflags
   (equal (seg-hiddeni i (!rflags v x86))
	  (seg-hiddeni i x86))
   :hints (("Goal" :in-theory (e/d (seg-hiddeni !rflags) ())))))

(local
 (defthm seg-hiddeni-!rip
   (equal (seg-hiddeni i (!rip v x86))
	  (seg-hiddeni i x86))
   :hints (("Goal" :in-theory (e/d (seg-hiddeni !rip) ())))))

(def-inst x86-syscall

  ;; Fast System Call to privilege level 0 system procedures.
  ;; Op/En: NP
  ;; 0F 05: SYSCALL

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (not (programmer-level-mode x86))
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'SYSCALL #x0F05 '(:nil nil)
				    'x86-syscall)

  :guard-hints (("Goal" :in-theory (e/d (n64-to-i64 wr64)
					())))

  :body

  (b* ((ctx 'x86-syscall)
       ;; 64-bit mode exceptions
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce) (ia32_efer-slice :ia32_efer-sce ia32-efer))
       ((the (unsigned-byte 1) ia32-efer-lma) (ia32_efer-slice :ia32_efer-lma ia32-efer))
       ((when (mbe :logic (or (zp ia32-efer-sce)
			      (zp ia32-efer-lma))
		   :exec (or (equal 0 ia32-efer-sce)
			     (equal 0 ia32-efer-lma))))
	(!!ms-fresh :ia32-efer-sce-or-lma=0 (cons 'ia32_efer ia32-efer)))
       (cs-hidden-descriptor (seg-hiddeni *cs* x86))
       (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden-descriptor))
       (cs.l (code-segment-descriptor-attributes-layout-slice :l cs-attr))
       ((when (not (equal cs.l 1)))
	(!!ms-fresh :cs.l!=1 (cons 'cs-hidden-descriptor cs-hidden-descriptor)))

       ;; Update the x86 state:

       ;; SYSCALL saves the rip of the instruction following SYSCALL
       ;; to rcx.
       ;; RCX <- RIP
       (x86 (!rgfi *rcx* temp-rip x86))

       ;; RIP <- IA32_LSTAR
       (lstar (msri *ia32_lstar-idx* x86))
       (lstar-addr (n64-to-i64 lstar))
       ((when (not (canonical-address-p lstar-addr)))
	(!!ms-fresh :lstar-not-canonical lstar))
       (x86 (!rip lstar-addr x86))

       ;; R11 <- RFLAGS
       ;; Shilpi: The AMD manual says that R11 contains the rflags
       ;; value with RF cleared but the Intel manual is silent about
       ;; this.
       ((the (unsigned-byte 32) eflags) (rflags x86))
       (x86 (wr64 *r11* eflags x86))

       ;; RFLAGS <- RFLAGS AND NOT(IA32_FMASK)
       ;; Shilpi: The AMD manual says that RFLAGS.RF is cleared but
       ;; the Intel manual is silent about this.
       (fmask (msri *ia32_fmask-idx* x86))
       (not-fmask (lognot fmask))
       (new-eflags (the (unsigned-byte 32) (logand eflags not-fmask)))
       (x86 (!rflags new-eflags x86))

       ;; CS.Selector <- IA32_STAR[47:32] AND FFFCH
       ;; OS provides CS; RPL forced to 0.
       (star (msri *ia32_star-idx* x86))
       (new-cs-selector
	(the (unsigned-byte 16)
	  (logand (part-select star :low 32 :high 47)
		  #xfffc)))
       (x86 (!seg-visiblei *cs* new-cs-selector x86))

       ;; From the Intel Vol. 2, Instruction Reference SYSCALL:

       ;;    SYSCALL loads the CS and SS selectors with values derived
       ;;    from bits 47:32 of the IA32_STAR MSR. However, the CS and
       ;;    SS descriptor caches are not loaded from the descriptors
       ;;    (in GDT or LDT) referenced by those selectors. Instead,
       ;;    the descriptor caches are loaded with fixed values. See
       ;;    the Operation section for details. It is the
       ;;    responsibility of OS software to ensure that the
       ;;    descriptors (in GDT or LDT) referenced by those selector
       ;;    values correspond to the fixed values loaded into the
       ;;    descriptor caches; the SYSCALL instruction does not
       ;;    ensure this correspondence.

       ;; (* Set rest of CS to a fixed value *)

       ;; CS.Base   <- 0;       (* Flat segment *)
       ;; CS.Limit  <- FFFFFH;  (* With 4-KByte granularity, implies a 4-GByte limit *)
       (cs-hidden-descriptor
	(!hidden-seg-reg-layout-slice
	 :base-addr 0
	 (!hidden-seg-reg-layout-slice
	  :limit #xfffff cs-hidden-descriptor)))

       ;; CS.Type <- 11;   (* Execute/read code, accessed *)
       ;; CS.S    <- 1;
       ;; CS.DPL  <- 0;
       ;; CS.P    <- 1;
       ;; CS.L    <- 1;   (* Entry is to 64-bit mode *)
       ;; CS.D    <- 0;   (* Required if CS.L = 1 *)
       ;; CS.G    <- 1;   (* 4-KByte granularity *)
       (cs-attr
	(!code-segment-descriptor-attributes-layout-slice
	 :type 11
	 (!code-segment-descriptor-attributes-layout-slice
	  :s 1
	  (!code-segment-descriptor-attributes-layout-slice
	   :dpl 0
	   (!code-segment-descriptor-attributes-layout-slice
	    :p 1
	    (!code-segment-descriptor-attributes-layout-slice
	     :l 1
	     (!code-segment-descriptor-attributes-layout-slice
	      :d 0
	      (!code-segment-descriptor-attributes-layout-slice
	       :g 1
	       cs-attr))))))))

       (cs-hidden-descriptor
	(!hidden-seg-reg-layout-slice
	 :attr cs-attr cs-hidden-descriptor))

       (x86 (!seg-hiddeni *cs* cs-hidden-descriptor x86))


       ;; CPL     <- 0;
       (current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
       (current-cs-register (!seg-sel-layout-slice :rpl 0 current-cs-register))
       (x86 (!seg-visiblei *cs* current-cs-register x86))

       ;; SS.Selector <- IA32_STAR[47:32] + 8; (* SS just above CS *)
       (new-ss-selector
	(+ (part-select star :low 32 :high 47) 8))
       ;; Shilpi: How do we know that new-ss-selector fits in 16
       ;; bytes? Neither the Intel nor the AMD manuals say anything
       ;; about truncating this value to fit in 16 bits.  So, I'm
       ;; going to raise an error when it doesn't, just so we're aware
       ;; that a "bad" situation happened.
       ((when (not (n16p new-ss-selector)))
	(!!ms-fresh :new-ss-selector-too-large new-ss-selector))
       (x86 (!seg-visiblei *ss* new-ss-selector x86))

       ;; (* Set rest of SS to a fixed value *)
       ;; SS.Base  <-  0;      (* Flat segment *)
       ;; SS.Limit <-  FFFFFH; (* With 4-KByte granularity, implies a 4-GByte limit *)
       (ss-hidden-descriptor (seg-hiddeni *ss* x86))
       (ss-hidden-descriptor
	(!hidden-seg-reg-layout-slice
	 :base-addr 0
	 (!hidden-seg-reg-layout-slice
	  :limit #xfffff ss-hidden-descriptor)))
       (ss-attr (hidden-seg-reg-layout-slice :attr ss-hidden-descriptor))

       ;; SS.Type  <-  3;      (* Read/write data, accessed *)
       ;; SS.S     <-  1;
       ;; SS.DPL   <-  0;
       ;; SS.P     <-  1;
       ;; SS.B     <-  1;      (* 32-bit stack segment *)
       ;; SS.G     <-  1;      (* 4-KByte granularity *)
       (ss-attr
	(!data-segment-descriptor-attributes-layout-slice
	 :type 3
	 (!data-segment-descriptor-attributes-layout-slice
	  :s 1
	  (!data-segment-descriptor-attributes-layout-slice
	   :dpl 0
	   (!data-segment-descriptor-attributes-layout-slice
	    :p 1
	    (!data-segment-descriptor-attributes-layout-slice
	     :d/b 1
	     (!data-segment-descriptor-attributes-layout-slice
	      :g 1
	      ss-attr)))))))

       (ss-hidden-descriptor
	(!hidden-seg-reg-layout-slice
	 :attr ss-attr ss-hidden-descriptor))

       (x86 (!seg-hiddeni *ss* ss-hidden-descriptor x86)))

      x86))

;; ======================================================================
;; INSTRUCTION: SYSRET
;; ======================================================================

(local (include-book "centaur/gl/gl" :dir :system))

(local
 (def-gl-thm x86-sysret-guard-helper-1
   :hyp (unsigned-byte-p 16 seg-visiblei)
   :concl (equal (bitops::logsquash 2 seg-visiblei)
		 (logand 65532 seg-visiblei))
   :g-bindings (gl::auto-bindings
		(:nat seg-visiblei    16))))

(local
 (def-gl-thm x86-sysret-guard-helper-2
   :hyp (unsigned-byte-p 64 msri)
   :concl (and
	   (equal (logior 3 (+ 16 (logtail 48 msri)))
		  (logior 3
			  (bitops::logsquash
			   2
			   (+ 16 (logtail 48 msri)))))
	   (equal (logior 3 (+ 8 (logtail 48 msri)))
		  (logior 3
			  (bitops::logsquash 2 (+ 8 (logtail 48 msri))))))
   :g-bindings (gl::auto-bindings
		(:nat msri    64))))

(def-inst x86-sysret

  :parents (two-byte-opcodes)

  :short "Return from fast system call to user code at privilege level
  3"

  :long "<p>Op/En: NP<br/>
REX.W + 0F 07: SYSRET</p>

<p>SYSRET when REX.W is not set is not supported because 0F 07 \(as
  opposed to REX.W + 0F 07\) returns to compatibility mode, not 64-bit
  mode.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
			       (not (programmer-level-mode x86))
			       (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'SYSRET #x0F07 '(:nil nil)
				    'x86-sysret)

  :guard-hints (("Goal" :in-theory (e/d (n64-to-i64 wr64)
					(unsigned-byte-p
					 signed-byte-p))))

  :body

  (b* ((ctx 'x86-sysret)

       ((when (not (logbitp #.*w* rex-byte)))
	(!!ms-fresh :unsupported-sysret-because-rex.w!=1 rex-byte))

       ;; 64-bit mode exceptions

       ;; If the LOCK prefix is used...
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))

       ;; If SCE or LMA = 0...
       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce) (ia32_efer-slice :ia32_efer-sce ia32-efer))
       ((the (unsigned-byte 1) ia32-efer-lma) (ia32_efer-slice :ia32_efer-lma ia32-efer))
       ((when (mbe :logic (or (zp ia32-efer-sce)
			      (zp ia32-efer-lma))
		   :exec (or (equal 0 ia32-efer-sce)
			     (equal 0 ia32-efer-lma))))
	(!!ms-fresh :ia32-efer-sce-or-lma=0 (cons 'ia32_efer ia32-efer)))

       ;; If CPL != 0...
       (current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
       (cpl (seg-sel-layout-slice :rpl current-cs-register))
       ((when (not (equal 0 cpl)))
	(!!ms-fresh :cpl!=0 (cons 'cs-register current-cs-register)))

       ;; If RCX contains a non-canonical address...
       (rcx (rgfi *rcx* x86))
       ((when (not (canonical-address-p rcx)))
	(!!ms-fresh :rcx-non-canonical rcx))

       ;; Update the x86 state:

       ;; Return to 64-bit mode
       (x86 (!rip rcx x86))

       ;; (* Clear RF, VM, reserved bits; set bit 2 *)
       ;; RFLAGS   (R11 & 3C7FD7H) | 2;
       (r11 (n32 (rgfi *r11* x86)))
       (x86 (!rflags (logior (logand r11 #x3c7fd7) 2) x86))

       ;; CS.Selector   IA32_STAR[63:48]+16;
       (star (msri *ia32_star-idx* x86))
       (new-cs-selector
	(+ (part-select star :low 48 :high 63)
	   16))
       ;; Shilpi: How do we know that new-cs-selector fits in 16
       ;; bytes?
       ((when (not (n16p new-cs-selector)))
	(!!ms-fresh :new-cs-selector-too-large new-cs-selector))
       ;; CS.Selector   CS.Selector OR 3;  (* RPL forced to 3 *)
       (new-cs-selector
	(mbe :logic (logior new-cs-selector 3)
	     :exec (!seg-sel-layout-slice :rpl 3 new-cs-selector)))
       (x86 (!seg-visiblei *cs* new-cs-selector x86))

       ;; (* Set rest of CS to a fixed value *)
       ;; CS.Base  <-  0;      (* Flat segment *)
       ;; CS.Limit <- FFFFFH;  (* With 4-KByte granularity, implies a 4-GByte limit *)
       (cs-hidden-descriptor (seg-hiddeni *cs* x86))
       (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden-descriptor))
       (cs-hidden-descriptor
	(!hidden-seg-reg-layout-slice
	 :base-addr 0
	 (!hidden-seg-reg-layout-slice
	  :limit #xfffff cs-hidden-descriptor)))

       ;; CS.Type <- 11;          (* Execute/read code, accessed *)
       ;; CS.S    <- 1;
       ;; CS.DPL  <- 3;
       ;; CS.P    <- 1;
       ;; (* Return to 64-Bit Mode *)
       ;; CS.L    <- 1;           (* 64-bit code segment *)
       ;; CS.D    <- 0;           (* Required if CS.L = 1 *)
       ;; CS.G    <- 1;           (* 4-KByte granularity *)
       (cs-attr
	(!code-segment-descriptor-attributes-layout-slice
	 :type 11
	 (!code-segment-descriptor-attributes-layout-slice
	  :s 1
	  (!code-segment-descriptor-attributes-layout-slice
	   :dpl 3
	   (!code-segment-descriptor-attributes-layout-slice
	    :p 1
	    (!code-segment-descriptor-attributes-layout-slice
	     :l 1
	     (!code-segment-descriptor-attributes-layout-slice
	      :d 0
	      (!code-segment-descriptor-attributes-layout-slice
	       :g 1
	       cs-attr))))))))

       (cs-hidden-descriptor
	(!hidden-seg-reg-layout-slice
	 :attr cs-attr cs-hidden-descriptor))

       (x86 (!seg-hiddeni *cs* cs-hidden-descriptor x86))

       ;; CPL <- 0;
       (current-cs-register (!seg-sel-layout-slice :rpl 0 current-cs-register))
       (x86 (!seg-visiblei *cs* current-cs-register x86))

       ;; SS.Selector <- (IA32_STAR[63:48] + 8) OR 3; (* RPL forced to 3 *)
       (new-ss-selector
	(+ (part-select star :low 48 :high 63) 8))
       ;; Shilpi: How do we know that new-ss-selector fits in 16
       ;; bytes?
       ((when (not (n16p new-ss-selector)))
	(!!ms-fresh :new-ss-selector-too-large new-ss-selector))
       (new-ss-selector
	(mbe :logic (logior new-ss-selector 3)
	     :exec (!seg-sel-layout-slice :rpl 3 new-ss-selector)))
       (x86 (!seg-visiblei *ss* new-ss-selector x86))

       ;; (* Set rest of SS to a fixed value *)
       ;; SS.Base  <- 0;           (* Flat segment *)
       ;; SS.Limit <- FFFFFH;      (* With 4-KByte granularity, implies a 4-GByte limit *)
       (ss-hidden-descriptor (seg-hiddeni *ss* x86))
       (ss-attr (hidden-seg-reg-layout-slice :attr ss-hidden-descriptor))
       (ss-hidden-descriptor
	(!hidden-seg-reg-layout-slice
	 :base-addr 0
	 (!hidden-seg-reg-layout-slice
	  :limit #xfffff ss-hidden-descriptor)))

       ;; SS.Type  <- 3;           (* Read/write data, accessed *)
       ;; SS.S     <- 1;
       ;; SS.DPL   <- 3;
       ;; SS.P     <- 1;
       ;; SS.B     <- 1;           (* 32-bit stack segment*)
       ;; SS.G     <- 1;           (* 4-KByte granularity *)

       (ss-attr
	(!data-segment-descriptor-attributes-layout-slice
	 :type 3
	 (!data-segment-descriptor-attributes-layout-slice
	  :s 1
	  (!data-segment-descriptor-attributes-layout-slice
	   :dpl 3
	   (!data-segment-descriptor-attributes-layout-slice
	    :p 1
	    (!data-segment-descriptor-attributes-layout-slice
	     :d/b 1
	     (!data-segment-descriptor-attributes-layout-slice
	      :g 1
	      ss-attr)))))))

       (ss-hidden-descriptor
	(!hidden-seg-reg-layout-slice
	 :attr ss-attr ss-hidden-descriptor))

       (x86 (!seg-hiddeni *ss* ss-hidden-descriptor x86)))

      x86))

;; ======================================================================
;; INSTRUCTION: RDRAND
;; ======================================================================

(def-inst x86-rdrand

  ;; 0F C7:
  ;; Opcode Extensions:
  ;; Bits 5,4,3 of the ModR/M byte (reg): 110
  ;; Bits 7,6 of the ModR/M byte (mod):    11

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip))
		:hints (("Goal" :in-theory (e/d (hw_rnd_gen
						 hw_rnd_gen-logic)
						(force (force))))))
  :implemented
  (add-to-implemented-opcodes-table 'RDRAND #x0FC7 '(:reg 6 :mod 3)
				    'x86-rdrand)

  :long
  "<p>Note from the Intel Manual (Sept. 2013, Vol. 1, Section 7.3.17):</p>

<p><em>Under heavy load, with multiple cores executing RDRAND in
parallel, it is possible, though unlikely, for the demand of random
numbers by software processes or threads to exceed the rate at which
the random number generator hardware can supply them. This will lead
to the RDRAND instruction returning no data transitorily. The RDRAND
instruction indicates the occurrence of this rare situation by
clearing the CF flag.</em></p>

<p>See <a
href='http://software.intel.com/en-us/articles/intel-digital-random-number-generator-drng-software-implementation-guide/'>Intel's
Digital Random Number Generator Guide</a> for more details.</p>"

  :body

  (b* ((ctx 'x86-rdrand)
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       (rep (prefixes-slice :group-2-prefix prefixes))
       (rep-p (or (equal #.*repe* rep)
		  (equal #.*repne* rep)))
       ((when (or lock? rep-p))
	(!!ms-fresh :lock-prefix-or-rep-p prefixes))
       (p3? (equal #.*operand-size-override*
		   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
	(if p3?
	    2
	  (if (logbitp #.*w* rex-byte)
	      8
	    4)))
       ((mv rand-and-cf x86)
	(HW_RND_GEN operand-size x86))

       ;; (- (cw "~%~%HW_RND_GEN: If RDRAND does not return the result you ~
       ;;         expected (or returned an error), then you might want to check whether these ~
       ;;         books were compiled using x86isa_exec set to t. See ~
       ;;         :doc build-instructions.~%~%"))

       ((when (ms x86))
	(!!ms-fresh :x86-rdrand (ms x86)))
       ((when (or (not (consp rand-and-cf))
		  (not (unsigned-byte-p (ash operand-size 3) (car rand-and-cf)))
		  (not (unsigned-byte-p 1 (cdr rand-and-cf)))))
	(!!ms-fresh :x86-rdrand-ill-formed-outputs (ms x86)))

       (rand (car rand-and-cf))
       (cf (cdr rand-and-cf))

       ;; Update the x86 state:
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*r*)
			rand rex-byte x86))
       (x86 (let* ((x86 (!flgi #.*cf* cf x86))
		   (x86 (!flgi #.*pf* 0 x86))
		   (x86 (!flgi #.*af* 0 x86))
		   (x86 (!flgi #.*zf* 0 x86))
		   (x86 (!flgi #.*sf* 0 x86))
		   (x86 (!flgi #.*of* 0 x86)))
	      x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR
;; ======================================================================

(def-inst x86-sal/sar/shl/shr/rcl/rcr/rol/ror
  :guard (not (equal (mrm-reg modr/m) 6))

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip))
		:hints (("Goal" :in-theory (e/d () (force (force))))))

  :long
  "<p>
  Op/En: MI<br/>
  C0/0: ROL r/m8, imm8<br/>
  C0/1: ROR r/m8,imm8<br/>
  C0/2: RCL r/m8, imm8<br/>
  C0/3: RCR r/m8, imm8<br/>
  C0/4: SAL/SHL r/m8 imm8<br/>
  C0/5: SHR r/m8 imm8<br/>
  C0/7: SAR r/m8 imm8<br/>
  C1/0: ROL r/m16, r/m32, or r/m64, imm8<br/>
  C1/1: ROR r/m16, r/m32, or r/m64, imm8<br/>
  C1/2: RCL r/m16, r/m32, or r/m64, imm8<br/>
  C1/3: RCR r/m16, r/m32, or r/m64, imm8<br/>
  C1/4: SAL/SHL r/m8 r/m16 or r/m64 imm8<br/>
  C1/5: SHR r/m16 r/m32 or r/m64 imm8<br/>
  C1/7: SAR r/m16 r/m32 or r/m64 imm8<br/>
  </p>

  <p>
  Op/En: M1<br/>
  D0/0: ROL r/m8, 1<br/>
  D0/1: ROR r/m8, 1<br/>
  D0/2: RCL r/m8, 1<br/>
  D0/3: RCR r/m8, 1<br/>
  D0/4: SAL/SHL r/m8 1<br/>
  D0/5: SHR r/m8 1<br/>
  D0/7: SAR r/m8 1<br/>
  D1/0: ROL r/m16, r/m32, or r/m64, 1<br/>
  D1/1: ROR r/m16, r/m32, or r/m64, 1<br/>
  D1/2: RCL r/m16, r/m32, or r/m64, 1<br/>
  D1/3: RCR r/m16, r/m32, or r/m64, 1<br/>
  D1/4: SAL/SHL r/m16 r/m32 or r/m64 1<br/>
  D1/5: SHR r/m16 r/m32 or r/m64 1<br/>
  D1/7: SAR r/m16 r/m32 or r/m64 1<br/>
  </p>

  <p>
  Op/En: MC<br/>
  D2/0: ROL r/m8, CL<br/>
  D2/1: ROR r/m8, CL<br/>
  D2/2: RCL r/m8, CL<br/>
  D2/3: RCR r/m8, CL<br/>
  D2/4: SAL/SHL r/m8 CL<br/>
  D2/5: SHR r/m8 CL<br/>
  D2/7: SAR r/m8, CL<br/>
  D3/0: ROL r/m16, r/m32, or r/m64, CL<br/>
  D3/1: ROR r/m16, r/m32, or r/m64, CL<br/>
  D3/2: RCL r/m16, r/m32, or r/m64, CL<br/>
  D3/3: RCR r/m16, r/m32, or r/m64, CL<br/>
  D3/4: SAL/SHL r/m16 r/m32 or r/m64 CL<br/>
  D3/5: SHR r/m16 r/m32 or r/m64 CL<br/>
  D3/7: SAR r/m16 r/m32 or r/m64 CL<br/>
  </p>"

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'ROL #xC0 '(:reg 0)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xC0 '(:reg 1)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xC0 '(:reg 2)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xC0 '(:reg 3)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xC0 '(:reg 4)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xC0 '(:reg 5)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xC0 '(:reg 7)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xC1 '(:reg 0)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xC1 '(:reg 1)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xC1 '(:reg 2)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xC1 '(:reg 3)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xC1 '(:reg 4)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xC1 '(:reg 5)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xC1 '(:reg 7)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xD0 '(:reg 0)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xD0 '(:reg 1)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xD0 '(:reg 2)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xD0 '(:reg 3)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xD0 '(:reg 4)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xD0 '(:reg 5)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xD0 '(:reg 7)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xD1 '(:reg 0)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xD1 '(:reg 1)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xD1 '(:reg 2)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xD1 '(:reg 3)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xD1 '(:reg 4)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xD1 '(:reg 5)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xD1 '(:reg 7)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xD2 '(:reg 0)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xD2 '(:reg 1)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xD2 '(:reg 2)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xD2 '(:reg 3)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xD2 '(:reg 4)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xD2 '(:reg 5)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xD2 '(:reg 7)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xD3 '(:reg 0)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xD3 '(:reg 1)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xD3 '(:reg 2)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xD3 '(:reg 3)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xD3 '(:reg 4)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xD3 '(:reg 5)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xD3 '(:reg 7)
				      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror))

  :body

  (b* ((ctx 'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
       (lock (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
	(!!ms-fresh :lock-prefix prefixes))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       (reg (mrm-reg modr/m))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4 (equal #.*addr-size-override*
		  (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (or (equal opcode #xC0)
				(equal opcode #xD0)
				(equal opcode #xD2)))
       ((the (integer 0 8) ?reg/mem-size)
	(select-operand-size select-byte-operand rex-byte nil
			     prefixes))

       ((mv flg0 ?reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4 temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ increment-RIP-by temp-rip))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((mv flg1 shift/rotate-by x86)
	(case opcode
	  ((#xD0 #xD1)
	   (mv nil 1 x86))
	  ((#xD2 #xD3)
	   (mv nil (rr08 *rcx* rex-byte x86) x86))
	  ((#xC0 #xC1)
	   (rm-size 1 temp-rip :x x86))
	  (otherwise ;; will not be reached
	   (mv nil 0 x86))))
       ((when flg1)
	(!!ms-fresh :rm-size-error flg1))

       (countMask (if (logbitp #.*w* rex-byte)
		      #x3F
		    #x1F))
       (shift/rotate-by (logand countMask shift/rotate-by))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(if (or (equal opcode #xC0)
		(equal opcode #xC1))
	    (+ temp-rip 1)
	  temp-rip))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Computing the flags and the result:
       (input-rflags (the (unsigned-byte 32) (rflags x86)))

       ((mv result
	    (the (unsigned-byte 32) output-rflags)
	    (the (unsigned-byte 32) undefined-flags))
	(case reg
	  (0
	   ;; ROL
	   (rol-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
	  (1
	   ;; ROR
	   (ror-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
	  (2
	   ;; RCL
	   (rcl-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
	  (3
	   ;; RCR
	   (rcr-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
	  (4
	   ;; SAL/SHL
	   (sal/shl-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
	  (5
	   ;; SHR
	   (shr-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
	  (7
	   ;; SAR
	   (sar-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
	  ;; The guard for this function will ensure that we don't
	  ;; reach here.
	  (otherwise
	   (mv 0 0 0))))

       ;; Update the x86 state:

       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ((mv flg2 x86)
	(x86-operand-to-reg/mem reg/mem-size
				;; TO-DO@Shilpi: Remove this trunc.
				(trunc reg/mem-size result)
				(the (signed-byte #.*max-linear-address-size*) v-addr)
				rex-byte r/m mod x86))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
	(!!ms-fresh :x86-operand-to-reg/mem flg2))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: MUL
;; ======================================================================

(def-inst x86-mul

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip))
		:hints (("Goal" :in-theory (e/d () (force (force))))))

  ;; Note that the reg field serves as an opcode extension for this
  ;; instruction.  The reg field will always be 4 when this function
  ;; is called.

  :guard (equal (mrm-reg modr/m) 4)

  :long
  "<h4>Op/En: M</h4>

  <p>F6/4: MUL r/m8:  AX := AL \* r/m8</p>
  <p>F7/4: MUL r/m16: DX:AX := AX \* r/m16<br/>
	MUL r/m32: EDX:EAX := EAX \* r/m32<br/>
	MUL r/m64: RDX:RAX := RAX \* r/m64<br/></p>"

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MUL #xF6 '(:reg 4)
				      'x86-mul)
    (add-to-implemented-opcodes-table 'MUL #xF7 '(:reg 4)
				      'x86-mul))
  :body

  (b* ((ctx 'x86-mul)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
	(select-operand-size
	 select-byte-operand rex-byte nil prefixes))

       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

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
	    (let* ((x86 (!flgi #.*cf* 0 x86))
		   (x86 (!flgi-undefined #.*pf* x86))
		   (x86 (!flgi-undefined #.*af* x86))
		   (x86 (!flgi-undefined #.*zf* x86))
		   (x86 (!flgi-undefined #.*sf* x86))
		   (x86 (!flgi #.*of* 0 x86)))
	      x86)
	  (let* ((x86 (!flgi #.*cf* 1 x86))
		 (x86 (!flgi-undefined #.*pf* x86))
		 (x86 (!flgi-undefined #.*af* x86))
		 (x86 (!flgi-undefined #.*zf* x86))
		 (x86 (!flgi-undefined #.*sf* x86))
		 (x86 (!flgi #.*of* 1 x86)))
	    x86)))

       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: IMUL
;; ======================================================================

(def-inst x86-imul-Op/En-M

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip))
		:hints (("Goal" :in-theory (e/d () (force (force))))))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'IMUL #xF6 '(:reg 5)
				      'x86-imul-Op/En-M)
    (add-to-implemented-opcodes-table 'IMUL #xF7 '(:reg 5)
				      'x86-imul-Op/En-M))


  ;; Note that the reg field serves as an opcode extension for this
  ;; instruction.  The reg field will always be 5 when this function is
  ;; called.

  :guard (equal (mrm-reg modr/m) 5)

  :long
  "<h4>Op/En: M</h4>

  <p>F6/5: <br/>
     IMUL r/m8:  AX      := AL  \* r/m8<br/><br/>

     F7/5: <br/>
     IMUL r/m16: DX:AX   := AX  \* r/m16<br/>
     IMUL r/m32: EDX:EAX := EAX \* r/m32<br/>
     IMUL r/m64: RDX:RAX := RAX \* r/m64<br/></p>"

  :body

  (b* ((ctx 'x86-imul-Op/En-M)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
	(select-operand-size select-byte-operand rex-byte nil prefixes))


       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by) ?v-addr x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Computing the result:
       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))
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
	(let* ((x86 (!flgi #.*cf* cf-and-of x86))
	       (x86 (!flgi-undefined #.*pf* x86))
	       (x86 (!flgi-undefined #.*af* x86))
	       (x86 (!flgi-undefined #.*zf* x86))
	       (x86 (!flgi-undefined #.*sf* x86))
	       (x86 (!flgi #.*of* cf-and-of x86)))
	  x86))

       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-imul-Op/En-RM

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip))
		:hints (("Goal" :in-theory (e/d () (force (force))))))

  :implemented
  (add-to-implemented-opcodes-table 'IMUL #x0FAF '(:nil nil)
				    'x86-imul-Op/En-RM)

  :long
  "<h4>Op/En: RM</h4>

  <p>0F AF:<br/>
     IMUL r16, r/m16: r16 := r16 \* r/m16 <br/>
     IMUL r32, r/m32: r32 := r32 \* r/m32 <br/>
     IMUL r64, r/m64: r64 := r64 \* r/m64 <br/> </p>"

  :body

  (b* ((ctx 'x86-imul-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 1 8) reg/mem-size)
	(select-operand-size nil rex-byte nil prefixes))

       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       (register (rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*)
			    rex-byte x86))

       ;; Computing the result:
       ((mv ?product-high product-low ?product (the (unsigned-byte 1) cf-and-of))
	(imul-spec reg/mem-size reg/mem register))

       ;; Updating the x86 state:
       (x86
	(!rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*)
		    product-low rex-byte x86))

       (x86
	(let* ((x86 (!flgi #.*cf* cf-and-of x86))
	       (x86 (!flgi-undefined #.*pf* x86))
	       (x86 (!flgi-undefined #.*af* x86))
	       (x86 (!flgi-undefined #.*zf* x86))
	       (x86 (!flgi-undefined #.*sf* x86))
	       (x86 (!flgi #.*of* cf-and-of x86)))
	  x86))

       (x86 (!rip temp-rip x86)))
      x86))

(def-inst x86-imul-Op/En-RMI

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip))
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

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSHF #x69 '(:nil nil)
				      'x86-imul-Op/En-RMI)
    (add-to-implemented-opcodes-table 'PUSHF #x6B '(:nil nil)
				      'x86-imul-Op/En-RMI))

  :body

  (b* ((ctx 'x86-imul-Op/En-RMI)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 1 8) reg/mem-size)
	(select-operand-size nil rex-byte nil prefixes))

       ((the (integer 1 4) imm-size)
	(if (equal opcode #x6B)
	    1
	  ;; opcode = #x69
	  (if (equal reg/mem-size 2)
	      2
	    4)))

       ((mv flg0 reg/mem
	    (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib imm-size x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((mv flg1 (the (unsigned-byte 32) imm) x86)
	(rm-size imm-size temp-rip :x x86))
       ((when flg1)
	(!!ms-fresh :rim-size-error flg1))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip imm-size))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ;; Computing the result:
       ((mv ?product-high product-low ?product (the (unsigned-byte 1) cf-and-of))
	(imul-spec reg/mem-size reg/mem imm))

       ;; Updating the x86 state:
       (x86
	(!rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*)
		    product-low rex-byte x86))


       (x86
	(let* ((x86 (!flgi #.*cf* cf-and-of x86))
	       (x86 (!flgi-undefined #.*pf* x86))
	       (x86 (!flgi-undefined #.*af* x86))
	       (x86 (!flgi-undefined #.*zf* x86))
	       (x86 (!flgi-undefined #.*sf* x86))
	       (x86 (!flgi #.*of* cf-and-of x86)))
	  x86))

       (x86 (!rip temp-rip x86)))
      x86))

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
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
	(select-operand-size select-byte-operand rex-byte nil prefixes))
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((when (equal reg/mem 0))
	;; Change to a #DE exception later.
	(!!ms-fresh :DE-exception-source-operand-zero reg/mem))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

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

       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: IDIV
;; ======================================================================

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
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
	(select-operand-size select-byte-operand rex-byte nil
			     prefixes))
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 #.*rgf-access* reg/mem-size p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ;; Change to a #DE exception later.
       ((when (equal reg/mem 0))
	(!!ms-fresh :DE-exception-source-operand-zero reg/mem))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

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

       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: CMPSS/CMPSD
;; ======================================================================

(def-inst x86-cmpss/cmpsd-Op/En-RMI

  ;; Shilpi to Cuong: Put as many type decl. as necessary --- look at
  ;; (disassemble$ x86-cmpss/cmpsd-Op/En-RMI) to figure out where you
  ;; need them.

  :parents (two-byte-opcodes fp-opcodes)
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CMPSD #x0FC2
				      '(:misc
					(eql #.*mandatory-f2h* (prefixes-slice :group-1-prefix prefixes)))
				      'x86-cmpss/cmpsd-Op/En-RMI)
    (add-to-implemented-opcodes-table 'CMPSS #x0FC2
				      '(:misc
					(eql #.*mandatory-f3h* (prefixes-slice :group-1-prefix prefixes)))
				      'x86-cmpss/cmpsd-Op/En-RMI))

  :short "Compare scalar single/double precision floating-point values"

  :long
  "<h3>Op/En = RMI: \[OP XMM, XMM/M, IMM\]</h3>
  F3 0F C2: CMPSS xmm1, xmm2/m32, imm8<br/>
  F2 0F C2: CMPSD xmm1, xmm2/m64, imm8<br/>"

  :sp/dp t

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-cmpss/cmpsd-Op/En-RMI)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock*
		  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
	(!!ms-fresh :lock-prefix prefixes))

       ((the (integer 4 8) operand-size)
	(if (equal sp/dp #.*OP-DP*) 8 4))

       (xmm-index ;; Shilpi: Type Decl.?
	(reg-index reg rex-byte #.*r*))
       (xmm
	(xmmi-size operand-size xmm-index x86))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
		 (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0 xmm/mem (the (integer 0 4) increment-RIP-by) ?v-addr x86)
	(x86-operand-from-modr/m-and-sib-bytes #.*xmm-access* operand-size
					       p2 p4? temp-rip
					       rex-byte r/m mod sib 1 x86))

       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((mv flg1 (the (unsigned-byte 8) imm) x86)
	(rm-size 1 (the (signed-byte #.*max-linear-address-size*) temp-rip) :x x86))

       ((when flg1)
	(!!ms-fresh :rm-size-error flg1))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(1+ temp-rip))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
	(-
	 (the (signed-byte #.*max-linear-address-size*)
	   temp-rip)
	 (the (signed-byte #.*max-linear-address-size*)
	   start-rip)))
       ((when (< 15 addr-diff))
	(!!ms-fresh :instruction-length addr-diff))

       ((mv flg2 result (the (unsigned-byte 32) mxcsr))
	(if (equal sp/dp #.*OP-DP*)
	    (dp-sse-cmp (n02 imm) xmm xmm/mem (mxcsr x86))
	  (sp-sse-cmp (n02 imm) xmm xmm/mem (mxcsr x86))))

       ((when flg2)
	(if (equal sp/dp #.*OP-DP*)
	    (!!ms-fresh :dp-cmp flg2)
	  (!!ms-fresh :sp-cmp flg2)))

       ;; Update the x86 state:
       (x86 (!mxcsr mxcsr x86))

       (x86 (!xmmi-size operand-size xmm-index result x86))

       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: LGDT
;; ======================================================================

(def-inst x86-lgdt

  :parents (privileged-opcodes two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :long "<h3>Op/En = M: \[OP m16@('&')m64\]</h3>

  <p>In 64-bit mode, the instruction's operand size is fixed at 8+2
  bytes (an 8-byte base and a 2-byte limit).</p>

  <p>\[OP  M\]<br/>
  0F 01/2: LGDT m16@('&')64</p>

  <p><b>TO-DO:</b> If a memory address referencing the SS segment is in
  a non-canonical form, raise the SS exception.</p>"

  :implemented
  (add-to-implemented-opcodes-table 'LGDT #x0F01 '(:reg 2)
				    'x86-lgdt)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-lgdt)
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       ;; If the current privilege level is not 0, the #GP exception
       ;; is raised.
       (cs-segment (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
       (cpl (the (unsigned-byte 2) (seg-sel-layout-slice :rpl cs-segment)))
       ((when (not (equal cpl 0)))
	(!!ms-fresh :cpl-not-zero cpl))
       ;; If the source operand is not a memory location, then #GP is
       ;; raised.
       ((when (equal mod #b11))
	(!!ms-fresh :source-operand-not-memory-location mod))
       ;; If the lock prefix is used, then the #UD exception is
       ;; raised.
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ;; Fetch the memory operand:
       ((mv flg0 mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 0 10 p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ;; Load the memory operand in the GDTR register.
       (gdtr-limit
	(!gdtr/idtr-layout-slice :limit
				 (part-select mem :low 0 :width 16)
				 0))
       (gdtr
	(!gdtr/idtr-layout-slice :base-addr
				 (part-select mem :low 16 :width 64)
				 gdtr-limit))

       ;; Update the x86 state:
       (x86 (!stri *gdtr* gdtr x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: LIDT
;; ======================================================================

(def-inst x86-lidt

  :parents (privileged-opcodes two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :long "<h3>Op/En = M: \[OP m16@('&')m64\]</h3>

  <p>In 64-bit mode, the instruction's operand size is fixed at 8+2
  bytes (an 8-byte base and a 2-byte limit).</p>

  <p>\[OP  M\]<br/>
  0F 01/3: LIDT m16@('&')64</p>

  <p><b>TO-DO:</b> If a memory address referencing the SS segment is in
  a non-canonical form, raise the SS exception.</p>"

  :implemented
  (add-to-implemented-opcodes-table 'LIDT #x0F01 '(:reg 3)
				    'x86-lidt)

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-lidt)
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       ;; If the current privilege level is not 0, the #GP exception
       ;; is raised.
       (cs-segment (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
       (cpl (the (unsigned-byte 2) (seg-sel-layout-slice :rpl cs-segment)))
       ((when (not (equal cpl 0)))
	(!!ms-fresh :cpl-not-zero cpl))
       ;; If the source operand is not a memory location, then #GP is
       ;; raised.
       ((when (equal mod #b11))
	(!!ms-fresh :source-operand-not-memory-location mod))
       ;; If the lock prefix is used, then the #UD exception is
       ;; raised.
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ;; Fetch the memory operand:
       ((mv flg0 mem (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 0 10 p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ;; Load the memory operand in the IDTR register.
       (idtr-limit
	(!gdtr/idtr-layout-slice :limit
				 (part-select mem :low 0 :width 16)
				 0))
       (idtr
	(!gdtr/idtr-layout-slice :base-addr
				 (part-select mem :low 16 :width 64)
				 idtr-limit))

       ;; Update the x86 state:
       (x86 (!stri *idtr* idtr x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: LLDT
;; ======================================================================

(def-inst x86-lldt

  :parents (privileged-opcodes two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (rim08
					 rim32
					 ia32e-valid-ldt-segment-descriptor-p)
					())))
  :implemented
  (add-to-implemented-opcodes-table 'LLDT #x0F00 '(:reg 2) 'x86-lldt)

  :long "<h3>Op/En = M: \[OP r/m16\]</h3>
  \[OP  M\]<br/>
  0F 00/2: LLDT r/m16<br/>

  <p>If bits 2-15 of the source operand are 0, LDTR is marked invalid
and the LLDT instruction completes silently. However, all subsequent
references to descriptors in the LDT (except by the LAR, VERR, VERW or
LSL instructions) cause a general protection exception.</p>

<p>The operand-size attribute has no effect on this instruction. In
64-bit mode, the operand size is fixed at 16 bits.</p>

<p><b>TO-DO:</b> If a memory address referencing the SS segment is in
a non-canonical form, raise the SS exception.</p>"

  :prepwork

  ((local (include-book "centaur/gl/gl" :dir :system))

   (local
    (def-gl-thm x86-lldt-guard-helper-1
      :hyp (unsigned-byte-p 16 y)
      :concl (equal (logand -79228162495817593519834398721 (ash y 96))
		    (ash y 96))
      :g-bindings `((y (:g-number ,(gl-int 0 1 17))))
      :rule-classes (:rewrite :linear)))

   (local
    (def-gl-thm x86-lldt-guard-helper-2
      :hyp (and (unsigned-byte-p 128 n128)
		(unsigned-byte-p 16 n16))
      :concl (equal
	      (logior
	       (loghead 16 (logtail 16 n128))
	       (ash (loghead 8 (logtail 32 n128)) 16)
	       (logand 5192217630372313364192902785269760 (ash n16 96))
	       (ash
		(logior (loghead 16 n128)
			(ash (loghead 4 (logtail 48 n128)) 16))
		64)
	       (ash
		(logior (loghead 8 (logtail 56 n128))
			(ash (loghead 32 (logtail 64 n128)) 8))
		24))
	      (logior (loghead 16 (logtail 16 n128))
		      (ash (loghead 8 (logtail 32 n128)) 16)
		      (ash
		       (logior (loghead 8 (logtail 56 n128))
			       (ash (loghead 32 (logtail 64 n128)) 8))
		       24)
		      (logand
		       5192296858534809181786422619668480
		       (logior
			(logand 5192217630372331810936976494821375 (ash n16 96))
			(ash (logior (loghead 16 n128)
				     (ash (loghead 4 (logtail 48 n128))
					  16)) 64)))))
      :g-bindings (gl::auto-bindings
		   (:mix (:nat n128 128)
			 (:nat n16 128)))))

   (local
    (def-gl-thm x86-lldt-guard-helper-3
      :hyp (and (unsigned-byte-p 128 n128)
		(unsigned-byte-p 16 n16))
      :concl (equal
	      (logior
	       (ash n16 96)
	       (ash
		(logior (loghead 16 n128)
			(ash (loghead 4 (logtail 48 n128))
			     16))
		64))
	      (logior
	       (logand
		5192217630372331810936976494821375 (ash n16 96))
	       (ash
		(logior (loghead 16 n128)
			(ash (loghead 4 (logtail 48 n128))
			     16))
		64)))
      :g-bindings (gl::auto-bindings
		   (:mix (:nat n128 128)
			 (:nat n16 128))))))

  :returns (x86 x86p :hyp (and (x86p x86)
			       (canonical-address-p temp-rip)))

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-lldt)
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       ;; If the current privilege level is not 0, the #GP exception
       ;; is raised.
       (cs-segment (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
       (cpl (the (unsigned-byte 2) (seg-sel-layout-slice :rpl cs-segment)))
       ((when (not (equal cpl 0)))
	(!!ms-fresh :cpl-not-zero cpl))
       ;; If the lock prefix is used, then the #UD exception is
       ;; raised.
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
	(!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ;; Fetch the memory operand:
       ((mv flg0 selector (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 0 2 p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
	(+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
		   :exec (<= #.*2^47*
			     (the (signed-byte
				   #.*max-linear-address-size+1*)
			       temp-rip))))
	(!!ms-fresh :virtual-memory-error temp-rip))

       ;; Getting the selector's components:
       ((the (unsigned-byte 13) sel-index)
	(seg-sel-layout-slice :index selector))
       ((the (unsigned-byte 1) sel-ti)
	(seg-sel-layout-slice :ti selector))
       ((the (unsigned-byte 2) sel-rpl)
	(seg-sel-layout-slice :rpl selector))

       ;; Determining whether the selector valid...

       ;; Does the selector point to the GDT?
       ((when (equal sel-ti 1))
	(!!ms-fresh :gp-selector-does-not-point-to-GDT selector))

       ;; Is the limit of the selector within the GDTR limit?
       ;; Getting the GDTR base and limit:
       ((the (unsigned-byte 80) gdtr)
	(stri *gdtr* x86))
       ((the (unsigned-byte 64) gdtr-base)
	(gdtr/idtr-layout-slice  :base-addr gdtr))
       ((the (unsigned-byte 16) gdtr-limit)
	(gdtr/idtr-layout-slice :limit gdtr))
       ;; Source: Intel Vol. 3A, Section 3.5.1:
       ;; "The limit value for the GDT is expressed in bytes. As with
       ;; segments, the limit value is added to the base address to
       ;; get the address of the last valid byte. A limit value of 0
       ;; results in exactly one valid byte. Because segment descrip-
       ;; tors are always 8 bytes long, the GDT limit should always be
       ;; one less than an integral multiple of eight (that is, 8N
       ;; 1)."
       ((when (< gdtr-limit sel-index))
	(!!ms-fresh :gp-selector-limit-check-failed (cons selector gdtr)))

       ;; Is the selector a null selector?  A null selector points to
       ;; the first entry in the GDT (sel-index=0, ti=0).

       ;; Source: Intel Vol. 2A, Instruction Set Reference (LLDT):
       ;; "LDTR is marked invalid and the LLDT instruction completes
       ;; silently. However, all subsequent references to descriptors
       ;; in the LDT (except by the LAR, VERR, VERW or LSL
       ;; instructions) cause a general protection exception (#GP)."

       ;; [Shilpi]: I believe that when the manuals tell us to mark
       ;; the LDTR invalid, we just have to load the selector into the
       ;; visible portion of LDTR and leave the hidden portion
       ;; unmodified.
       ((when (equal sel-index 0))
	(let* ((x86 (!ssr-visiblei *ldtr* selector x86)))
	  x86))

       ;; Now that we know the segment selector is valid, we check if
       ;; the segment descriptor is valid.

       (descriptor-addr
	;; The index is scaled by 8.
	(+ gdtr-base (the (unsigned-byte 16) (ash sel-index 3))))
       ((when (not (canonical-address-p descriptor-addr)))
	(!!ms-fresh :descriptor-addr-virtual-memory-error descriptor-addr))

       ((mv flg (the (unsigned-byte 128) descriptor) x86)
	;; [TO-DO@Shilpi]: I believe I should use :x below and not :r.
	(rm-size 16 descriptor-addr :x x86))
       ((when flg)
	(!!ms-fresh :rm-size-error flg))

       ((mv descriptor-valid? reason)
	(ia32e-valid-ldt-segment-descriptor-p descriptor))
       ((when (not descriptor-valid?))
	(!!ms-fresh :invalid-segment-descriptor reason))

       ;; LDTR Base:
       (ldtr-base15-0  (system-segment-descriptor-layout-slice :base15-0  descriptor))
       (ldtr-base23-16 (system-segment-descriptor-layout-slice :base23-16 descriptor))
       (ldtr-base31-24 (system-segment-descriptor-layout-slice :base31-24 descriptor))
       (ldtr-base63-32 (system-segment-descriptor-layout-slice :base63-32 descriptor))
       ((the (unsigned-byte 40) ldtr-base63-24)
	(part-install
	 ldtr-base31-24
	 (ash ldtr-base63-32 8)
	 :low 0 :width 8))
       ((the (unsigned-byte 24) ldtr-base23-0)
	(part-install ldtr-base15-0
		      (ash ldtr-base23-16 16)
		      :low 0 :width 16))
       ((the (unsigned-byte 64) ldtr-base)
	(part-install ldtr-base23-0
		      (ash ldtr-base63-24 24)
		      :low 0 :width 24))

       ;; LDTR Limit:
       (ldtr-limit15-0  (system-segment-descriptor-layout-slice :limit15-0   descriptor))
       (ldtr-limit19-16 (system-segment-descriptor-layout-slice :limit19-16  descriptor))
       (ldtr-limit      (part-install ldtr-limit15-0
				      (ash ldtr-limit19-16 16)
				      :low 0 :width 16))

       ;; LDTR Attributes:
       (ldtr-attr (the (unsigned-byte 16)
		    (make-system-segment-attr-field descriptor)))

       ;; LDTR Hidden:
       (ldtr-hidden
	(!hidden-seg-reg-layout-slice
	 :base-addr
	 ldtr-base
	 (!hidden-seg-reg-layout-slice
	  :limit
	  ldtr-limit
	  (!hidden-seg-reg-layout-slice
	   :attr
	   ldtr-attr
	   0))))

       ;; Update the x86 state:
       ;; Load the visible and hidden portions of the LDTR register:
       (x86
	(!ssr-visiblei *ldtr* selector x86))
       (x86
	(!ssr-hiddeni *ldtr* ldtr-hidden x86))
       (x86 (!rip temp-rip x86)))
      x86))

;; ======================================================================

;; To see the rules in the instruction-decoding-and-spec-rules
;; ruleset:

(define show-inst-decoding-and-spec-fn
  ((state))
  :mode :program
  (let ((world (w state)))
    (ruleset-theory 'instruction-decoding-and-spec-rules)))

(defmacro show-inst-decoding-and-spec-ruleset ()
  `(show-inst-decoding-and-spec-fn state))

;; ======================================================================
