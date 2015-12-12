;; Author:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "utilities")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection decoding-utilities
  :parents (utils)
  :short "<b>@('x86')-specific decoding constants and utilities</b>"
  :long "<p>The constant @('*Z-addressing-method-info*') contains
  interpretation of codes for addressing method, as described in Intel
  Manual, Volume 2, Appendix A.2.1.</p>

<p>The constants @('*one-byte-opcode-map-lst*') and
@('*two-byte-opcode-map-lst*') contains information presented in the
opcode maps, as describe in Intel Manual, Volume 2, Appendix A-2.</p>

<p>An array @('*64-bit-mode-one-byte-has-modr/m-ar*') is created by
  the function @(see 64-bit-compute-modr/m-map) for the efficient
  look-up of modr/m-related information from
  @('*one-byte-opcode-map-lst*').</p>

<p>@('*Z-addressing-method-info*'):</p>
  @(`(:code *Z-addressing-method-info*)`)

<p>@('*one-byte-opcode-map-lst*'):</p>
  @(`(:code *one-byte-opcode-map-lst*)`)"

  )

;; ======================================================================

;; Addressing Info:

(defconst *Z-addressing-method-info*

  ;; See Intel Vol. 2, Appendix A.2.1

  ;; (assoc :modr/m? (cdr (assoc 'A *Z-addressing-method-info*)))

  (list

   ;; A Direct address: the instruction has no ModR/M byte; the
   ;; address of the operand is encoded in the instruction. No base
   ;; register index register or scaling factor can be applied (for
   ;; example far JMP (EA)).

   '(A (:modr/m? . nil) (:vex . nil))

   ;; B The VEX.vvvv field of the VEX prefix selects a general purpose
   ;; register.

   '(B (:modr/m? . nil) (:vex . t))

   ;; C The reg field of the ModR/M byte selects a control register
   ;; (for example MOV (0F20 0F22)).

   '(C (:modr/m? . t) (:vex . nil))

   ;; D The reg field of the ModR/M byte selects a debug register (for
   ;; example MOV (0F210F23)).

   '(D (:modr/m? . t) (:vex . nil))

   ;; E A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either a general-purpose register or a
   ;; memory address. If it is a memory address the address is
   ;; computed from a segment register and any of the following
   ;; values: a base register an index register a scaling factor a
   ;; displacement.

   '(E (:modr/m? . t) (:vex . nil))

   ;; F EFLAGS/RFLAGS Register.

   '(F (:modr/m? . nil) (:vex . nil))

   ;; G The reg field of the ModR/M byte selects a general register
   ;; (for example AX (000)).

   '(G (:modr/m? . t) (:vex . nil))

   ;; H The VEX.vvvv field of the VEX prefix selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand
   ;; type. For legacy SSE encodings this operand does not exist
   ;; changing the instruction to destructive form.

   '(H (:modr/m? . nil) (:vex . t))

   ;; I Immediate data: the operand value is encoded in subsequent
   ;; bytes of the instruction.

   '(I (:modr/m? . nil) (:vex . nil))

   ;; J The instruction contains a relative offset to be added to the
   ;; instruction pointer register (for example JMP (0E9) LOOP).

   '(J (:modr/m? . nil) (:vex . nil))

   ;; L The upper 4 bits of the 8-bit immediate selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand
   ;; type. (the MSB is ignored in 32-bit mode)

   '(L (:modr/m? . nil) (:vex . t))

   ;; M The ModR/M byte may refer only to memory (for example BOUND
   ;; LES LDS LSS LFS LGS CMPXCHG8B).

   '(M (:modr/m? . t) (:vex . nil))

   ;; N The R/M field of the ModR/M byte selects a packed-quadword MMX
   ;; technology register.

   '(N (:modr/m? . t) (:vex . nil))

   ;; O The instruction has no ModR/M byte. The offset of the operand
   ;; is coded as a word or double word (depending on address size
   ;; attribute) in the instruction. No base register index register
   ;; or scaling factor can be applied (for example MOV (A0 A3)).

   '(O (:modr/m? . nil) (:vex . nil))

   ;; P The reg field of the ModR/M byte selects a packed quadword MMX
   ;; technology register.

   '(P (:modr/m? . t) (:vex . nil))

   ;; Q A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either an MMX technology register or a
   ;; memory address. If it is a memory address the address is
   ;; computed from a segment register and any of the following
   ;; values: a base register an index register a scaling factor and a
   ;; displacement.

   '(Q (:modr/m? . t) (:vex . nil))

   ;; R The R/M field of the ModR/M byte may refer only to a general
   ;; register (for example MOV (0F20-0F23)).

   '(R (:modr/m? . t) (:vex . nil))

   ;; S The reg field of the ModR/M byte selects a segment register
   ;; (for example MOV (8C8E)).

   '(S (:modr/m? . t) (:vex . nil))

   ;; U The R/M field of the ModR/M byte selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand type.

   '(U (:modr/m? . t) (:vex . t))

   ;; V The reg field of the ModR/M byte selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand type.

   '(V (:modr/m? . t) (:vex . t))

   ;; W A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either a 128-bit XMM register a 256-bit
   ;; YMM register (determined by operand type) or a memory
   ;; address. If it is a memory address the address is computed from
   ;; a segment register and any of the following values: a base
   ;; register an index register a scaling factor and a displacement.

   '(W (:modr/m? . t) (:vex . t))

   ;; X Memory addressed by the DS:rSI register pair (for example MOVS
   ;; CMPS OUTS or LODS).

   '(X (:modr/m? . nil) (:vex . nil))

   ;; Y Memory addressed by the ES:rDI register pair (for example MOVS
   ;; CMPS INS STOS or SCAS).

   '(Y (:modr/m? . nil) (:vex . nil))

   ))


;; See Intel Vol. 2, Appendix A.2.2

#||

A.2.2 Codes for Operand Type

The following abbreviations are used to document operand types:

a  Two one-word operands in memory or two double-word operands in
   memory, depending on operand-size attribute (used only by the BOUND
   instruction).

b  Byte, regardless of operand-size attribute.

c  Byte or word, depending on operand-size attribute.

d  Doubleword, regardless of operand-size attribute.

dq Double-quadword, regardless of operand-size attribute.

p  32-bit, 48-bit, or 80-bit pointer, depending on operand-size
   attribute. pd 128-bit or 256-bit packed double-precision
   floating-point data.

pi Quadword MMX technology register (for example: mm0).

ps 128-bit or 256-bit packed single-precision floating-point data.

q  Quadword, regardless of operand-size attribute.

qq Quad-Quadword (256-bits), regardless of operand-size attribute. s
   6-byte or 10-byte pseudo-descriptor.

sd Scalar element of a 128-bit double-precision floating data.

ss Scalar element of a 128-bit single-precision floating data.

si Doubleword integer register (for example: eax).

v  Word, doubleword or quadword (in 64-bit mode), depending on
   operand-size attribute.

w  Word, regardless of operand-size attribute.

x  dq or qq based on the operand-size attribute.

y  Doubleword or quadword (in 64-bit mode), depending on operand-size
   attribute.

z  Word for 16-bit operand-size or doubleword for 32 or 64-bit
   operand-size.

||#

#||

See Intel Manuals, Volume 2, Appendix A.2.5

Table A-1. Superscripts Utilized in Opcode Tables

1A: Bits 5, 4, and 3 of ModR/M byte used as an opcode extension (refer
    to Section A.4,  Opcode Extensions For One-Byte And Two-byte
    Opcodes ).

1B: Use the 0F0B opcode (UD2 instruction) or the 0FB9H opcode when
    deliberately trying to generate an invalid opcode exception (#UD).

1C: Some instructions use the same two-byte opcode. If the instruction
    has variations, or the opcode represents different instructions,
    the ModR/M byte will be used to differentiate the instruction. For
    the value of the ModR/M byte needed to decode the instruction, see
    Table A-6.

i64: The instruction is invalid or not encodable in 64-bit mode. 40
     through 4F (single-byte INC and DEC) are REX prefix combinations
     when in 64-bit mode (use FE/FF Grp 4 and 5 for INC and DEC).

o64: Instruction is only available when in 64-bit mode.

d64: When in 64-bit mode, instruction defaults to 64-bit operand size
     and cannot encode 32-bit operand size.

f64: The operand size is forced to a 64-bit operand size when in
     64-bit mode (prefixes that change operand size are ignored for
     this instruction in 64-bit mode).

v:  VEX form only exists. There is no legacy SSE form of the
    instruction. For Integer GPR instructions it means VEX prefix
    required.

v1: VEX128 & SSE forms only exist (no VEX256), when can t be inferred
    from the data size.

||#

;; ======================================================================

;; Opcode Maps:

(defconst *one-byte-opcode-map-lst*

  '(
    #|       -------------------------------        |#

    #| 00 |# (("ADD" 2 (E b)  (G b))
              ("ADD" 2 (E v)  (G v))
              ("ADD" 2 (G b)  (E b))
              ("ADD" 2 (G v)  (E v))
              ("ADD" 2 (:AL)  (I b))
              ("ADD" 2 (:rAX) (I z))
              ((:i64 . ("PUSH ES" 0)))
              ((:i64 . ("POP ES"  0)))
              ("OR" 2 (E b)  (G b))
              ("OR" 2 (E v)  (G v))
              ("OR" 2 (G b)  (E b))
              ("OR" 2 (G v)  (E v))
              ("OR" 2 (:AL)  (I b))
              ("OR" 2 (:rAX) (I z))
              ((:i64 . ("PUSH CS" 0)))
              (:2-byte-escape))

    #| 10 |# (("ADC" 2 (E b) (G b))
              ("ADC" 2 (E v) (G v))
              ("ADC" 2 (G b) (E b))
              ("ADC" 2 (G v) (E v))
              ("ADC" 2 (:AL) (I b))
              ("ADC" 2 (:rAX) (I z))
              ((:i64 . ("PUSH SS" 0)))
              ((:i64 . ("POP SS" 0)))
              ("SBB" 2 (E b) (G b))
              ("SBB" 2 (E v) (G v))
              ("SBB" 2 (G b) (E b))
              ("SBB" 2 (G v) (E v))
              ("SBB" 2 (:AL) (I b))
              ("SBB" 2 (:rAX) (I z))
              ((:i64 . ("PUSH DS" 0)))
              ((:i64 . ("POP DS" 0))))

    #| 20 |# (("AND" 2 (E b) (G b))
              ("AND" 2 (E v) (G v))
              ("AND" 2 (G b) (E b))
              ("AND" 2 (G v) (E v))
              ("AND" 2 (:AL) (I b))
              ("AND" 2 (:rAX) (I z))
              (:prefix-ES)
              ((:i64 . ("DAA" 0)))
              ("SUB" 2 (E b) (G b))
              ("SUB" 2 (E v) (G v))
              ("SUB" 2 (G b) (E b))
              ("SUB" 2 (G v) (E v))
              ("SUB" 2 (:AL) (I b))
              ("SUB" 2 (:rAX) (I z))
              (:prefix-CS)
              ((:i64 . ("DAS" 0))))

    #| 30 |# (("XOR" 2 (E b) (G b))
              ("XOR" 2 (E v) (G v))
              ("XOR" 2 (G b) (E b))
              ("XOR" 2 (G v) (E v))
              ("XOR" 2 (:AL) (I b))
              ("XOR" 2 (:rAX) (I z))
              (:prefix-SS)
              ((:i64 . ("AAA" 0)))
              ("CMP" 2 (E b) (G b))
              ("CMP" 2 (E v) (G v))
              ("CMP" 2 (G b) (E b))
              ("CMP" 2 (G v) (E v))
              ("CMP" 2 (:AL) (I b))
              ("CMP" 2 (:rAX) (I z))
              (:prefix-DS)
              ((:i64 . ("AAS" 0))))

    #| 40 |# (((:o64  . (:rex))       (:i64 . ("INC"  2 (:eAX))))
              ((:o64  . (:rex-b))     (:i64 . ("INC"  2 (:eCX))))
              ((:o64  . (:rex-x))     (:i64 . ("INC"  2 (:eDX))))
              ((:o64  . (:rex-xb))    (:i64 . ("INC"  2 (:eBX))))
              ((:o64  . (:rex-r))     (:i64 . ("INC"  2 (:eSP))))
              ((:o64  . (:rex-rb))    (:i64 . ("INC"  2 (:eBP))))
              ((:o64  . (:rex-rx))    (:i64 . ("INC"  2 (:eSI))))
              ((:o64  . (:rex-rxb))   (:i64 . ("INC"  2 (:eDI))))
              ((:o64  . (:rex-w))     (:i64 . ("DEC"  2 (:eAX))))
              ((:o64  . (:rex-wb))    (:i64 . ("DEC"  2 (:eCX))))
              ((:o64  . (:rex-wx))    (:i64 . ("DEC"  2 (:eDX))))
              ((:o64  . (:rex-wxb))   (:i64 . ("DEC"  2 (:eBX))))
              ((:o64  . (:rex-wr))    (:i64 . ("DEC"  2 (:eSP))))
              ((:o64  . (:rex-wrb))   (:i64 . ("DEC"  2 (:eBP))))
              ((:o64  . (:rex-wrx))   (:i64 . ("DEC"  2 (:eSI))))
              ((:o64  . (:rex-wrxb))  (:i64 . ("DEC"  2 (:eDI)))))

    #| 50 |# (((:d64 . ("PUSH" 1 (:rAX/r8))))
              ((:d64 . ("PUSH" 1 (:rCX/r9))))
              ((:d64 . ("PUSH" 1 (:rDX/r10))))
              ((:d64 . ("PUSH" 1 (:rBX/r11))))
              ((:d64 . ("PUSH" 1 (:rSP/r11))))
              ((:d64 . ("PUSH" 1 (:rBP/r13))))
              ((:d64 . ("PUSH" 1 (:rSI/r14))))
              ((:d64 . ("PUSH" 1 (:rDI/r15))))
              ((:d64 . ("POP"  1 (:rAX/r8))))
              ((:d64 . ("POP"  1 (:rCX/r9))))
              ((:d64 . ("POP"  1 (:rDX/r10))))
              ((:d64 . ("POP"  1 (:rBX/r11))))
              ((:d64 . ("POP"  1 (:rSP/r11))))
              ((:d64 . ("POP"  1 (:rBP/r13))))
              ((:d64 . ("POP"  1 (:rSI/r14))))
              ((:d64 . ("POP"  1 (:rDI/r15)))))

    #| 60 |# (((:i64 . ("PUSHA/PUSHAD" 0)))
              ((:i64 . ("POPA/POPAD"   0)))
              ((:i64 . ("BOUND"  2 (G v) (M a))))
              ((:o64 . ("MOVSXD" 2 (G v) (E v)))
               (:i64 . ("ARPL"   2 (E w) (G w))))
              (:prefix-FS)
              (:prefix-GS)
              (:prefix-OpSize)
              (:prefix-AddrSize)
              ((:d64 . ("PUSH" 1 (I z))))
              ("IMUL"  3 (G v) (E v) (I z))
              ((:d64 . ("PUSH" 1 (I b))))
              ("IMUL"  3 (G v) (E v) (I b))
              ("INS/INSB" 2 (Y b) (D x))
              ("INS/INSW/INSD" 2 (Y z) (D x))
              ("OUTS/OUTSB" 2 (Y b) (D x))
              ("OUTS/OUTSW/OUTSD" 2 (Y z) (D x)))

    #| 70 |# (((:f64 . ("JO" 1 (J b))))
              ((:f64 . ("JNO" 1 (J b))))
              ((:f64 . ("JB/NAE/C" 1 (J b))))
              ((:f64 . ("JNB/AE/NC" 1 (J b))))
              ((:f64 . ("JZ/E" 1 (J b))))
              ((:f64 . ("JNZ/NE" 1 (J b))))
              ((:f64 . ("JBE/NA" 1 (J b))))
              ((:f64 . ("JNBE/A" 1 (J b))))
              ((:f64 . ("JS" 1 (J b))))
              ((:f64 . ("JNS" 1 (J b))))
              ((:f64 . ("JP/PE" 1 (J b))))
              ((:f64 . ("JNP/PO" 1 (J b))))
              ((:f64 . ("JL/NGE" 1 (J b))))
              ((:f64 . ("JNL/GE" 1 (J b))))
              ((:f64 . ("JLE/NG" 1 (J b))))
              ((:f64 . ("JNLE/G" 1 (J b)))))

    #| 80 |#  (("ImmGrp1" 2 (E b) (I b) :1a)
               ("ImmGrp1" 2 (E v) (I z) :1a)
               ((:i64 . ("ImmGrp1" 2 (E v) (I z) :1a)))
               ("ImmGrp1" 2 (E v) (I b) :1a)
               ("TEST" 2 (E b) (G b))
               ("TEST" 2 (E v) (G v))
               ("XCHG" 2 (E b) (G b))
               ("XCHG" 2 (E v) (G v))
               ("MOV" 2 (E b) (G b))
               ("MOV" 2 (E v) (G v))
               ("MOV" 2 (G b) (E b))
               ("MOV" 2 (G v) (E v))
               ("MOV" 2 (E v) (S w))
               ("LEA" 2 (G v) (M))
               ("MOV" 2 (S w) (E w))
               ((:d64 . ("Grp1a" 1 (E v) :1a))))

    #| 90 |# (("XCHG" 1 (:r8))
              ("XCHG" 2 (:rCX) (:r9))
              ("XCHG" 2 (:rDX) (:r10))
              ("XCHG" 2 (:rBX) (:r11))
              ("XCHG" 2 (:rSP) (:r12))
              ("XCHG" 2 (:rBP) (:r13))
              ("XCHG" 2 (:rSI) (:14))
              ("XCHG" 2 (:rDI) (:15))
              ("CBW/CWDE/CDQE" 0)
              ("CWD/CDQ/CQO" 0)
              ((:i64 . ("CALL" 1 (A p))))
              ("FWAIT/WAIT" 0)
              ((:d64 . ("PUSHQ"  1 (F v)))
               (:i64 . ("PUSHFD" 1 (F v))))
              ((:d64 . ("POPQ"   1 (F v)))
               (:i64 . ("POPFD"  1 (F v))))
              ("SAHF" 0)
              ("LAHF" 0))

    #| a0 |# (("MOV" 2 (:AL) (O b))
              ("MOV" 2 (:rAX) (O v))
              ("MOV" 2 (O b) (:AL))
              ("MOV" 2 (O v) (:rAX))
              ("MOVS/B" 2 (Y b) (X b))
              ("MOVS/W/D/Q" 2 (Y v) (X v))
              ("CMPS/B" 2 (Y b) (X b))
              ("CMPS/W/D/Q" 2 (Y v) (X v))
              ("TEST" 2 (:AL) (I b))
              ("TEST" 2 (:rAX) (I z))
              ("STOS/B" 2 (Y b) (:AL))
              ("STOS/W/D/Q" 2 (Y v) (:rAX))
              ("LODS/B" 2 (:AL) (X b))
              ("LODS/W/D/Q" 2 (:rAX) (X v))
              ("SCAS/B" 2 (:AL) (Y b))
              ("SCAS/W/D/Q" 2 (:rAX) (Y v)))

    #| b0 |# (("MOV" 2  (:AL/r8L)  (I b))
              ("MOV" 2  (:CL/r9L)  (I b))
              ("MOV" 2  (:DL/r10L) (I b))
              ("MOV" 2  (:BL/r11L) (I b))
              ("MOV" 2  (:AH/r12L) (I b))
              ("MOV" 2  (:CH/r13L) (I b))
              ("MOV" 2  (:DH/r14L) (I b))
              ("MOV" 2  (:BH/r15L) (I b))
              ("MOV" 2  (:rA/r8)   (I v))
              ("MOV" 2  (:rC/r9)   (I v))
              ("MOV" 2  (:rD/r10)  (I v))
              ("MOV" 2  (:rB/r11)  (I v))
              ("MOV" 2  (:rS/r12)  (I v))
              ("MOV" 2  (:rB/r13)  (I v))
              ("MOV" 2  (:rS/r14)  (I v))
              ("MOV" 2  (:rD/r15)  (I v)))

    #| c0 |# (("ShftGrp2" 2 (E b) (I b) :1a)
              ("ShftGrp2" 2 (E v) (I v) :1a)
              ((:f64 . ("RET" 1 (I w))))
              ((:f64 . ("RET" 0)))
              ((:i64 . ("LES" 2 (G z) (M p) :vex)))
              ((:i64 . ("LDS" 2 (G z) (M p) :vex)))
              ("Grp11" 2 (E b) (I b) :1a)
              ("Grp11" 2 (E v) (I z) :1a)
              ("ENTER" 2 (I w) (I b))
              ((:d64 . ("LEAVE" 0)))
              ("RET" 1 (I w))
              ("RET" 0)
              ("INT 3" 0)
              ("INT" 1 (I b))
              ((:i64 . ("INTO" 0)))
              ("IRET/D/Q" 0))

    #| d0 |# (("ShftGrp2" 2 (E b) (1) :1a)
              ("ShftGrp2" 2 (E v) (1) :1a)
              ("ShftGrp2" 2 (E b) (:CL) :1a)
              ("ShftGrp2" 2 (E v) (:CL) :1a)
              ((:i64 . ("AAM" 1 (I b))))
              ((:i64 . ("AAD" 1 (I b))))
              (:none)
              ("XLAT/XLATB" 0)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| e0 |# (((:f64 . ("LOOPNE/LOOPNZ" 1 (J b))))
              ((:f64 . ("LOOPE/LOOPZ" 1 (J b))))
              ((:f64 . ("LOOP" 1 (J b))))
              ((:f64 . ("JrCXZ" 1 (J b))))
              ("IN" 2 (:AL) (I b))
              ("IN" 2 (:eAX) (I b))
              ("OUT" 2 (I b) (:AL))
              ("OUT" 2 (I b) (:eAX))
              ((:f64 . ("CALL" 1 (J z))))
              ((:f64 . ("JMP"  1 (J z))))
              ((:i64 . ("JMP"  1 (A p))))
              ((:f64 . ("JMP"  1 (J b))))
              ("IN" 2  (:AL) (:DX))
              ("IN" 2  (:eAX) (:DX))
              ("OUT" 2 (:DX) (:AL))
              ("OUT" 2 (:DX) (:eAX)))

    #| f0 |# ((:prefix-Lock)
              (:none)
              (:prefix-REPNE)
              (:prefix-REP/REPE)
              ("HLT" 0)
              ("CMC" 0)
              ("UnaryGrp3" 1 (E b) :1a)
              ("UnaryGrp3" 1 (E v) :1a)
              ("CLC" 0)
              ("STC" 0)
              ("CLI" 0)
              ("STI" 0)
              ("CLD" 0)
              ("STD" 0)
              ("Grp4" 1 (E b) :1a)
              ("Grp5" 1 (E v) :1a))

    #|       -------------------------------        |#
    ))

(defconst *two-byte-opcode-map-lst*
  ;; First byte is 0x0F.

  '(
    #|       -------------------------------        |#

    #| 00 |# (("Grp 6" 0 :1a)
              ("Grp 7" 0 :1a)
              ("LAR" 2 (G v) (E w))
              ("LSL" 2 (G v) (E w))
              (:none)
              ((:o64 . ("SYSCALL" 0)))
              ("CLTS" 0)
              ((:o64 . ("SYSRET" 0)))
    #| 08 |#  ("INVD" 0)
              ("WBINVD" 0)
              (:none)
              ("UD2" 0)
              (:none)
              ("prefetchw(/1)" 1 (E v))
              (:none)
              (:none))

    #| 10 |# (((:no-prefix . ("VMOVUPS"    2 (V ps) (W ps)))
               (:66        . ("VMOVUPD"    2 (V pd) (W pd)))
               (:F3        . ("VMOVSS"     3 (V x)  (H x)  (W ss)))
               (:F2        . ("VMOVSD"     3 (V x)  (H x)  (W sd))))

              ((:no-prefix . ("VMOVUPS"    2 (W ps) (V ps)))
               (:66        . ("VMOVUPD"    2 (W pd) (V pd)))
               (:F3        . ("VMOVSS"     3 (W ss) (H x)  (V ss)))
               (:F2        . ("VMOVSD"     3 (W sd) (H x)  (V sd))))

              ((:no-prefix . ("VMOVLPS"    3 (V q)  (H q)  (M q)))
               (:no-prefix . ("VMOVHLPS"   3 (V q)  (H q)  (U q)))
               (:66        . ("VMOVLPD"    3 (V q)  (H q)  (M q)))
               (:F3        . ("VMOVSLDUP"  2 (V x)  (W x)))
               (:F2        . ("VMOVDDUP"   2 (V x)  (W x))))

              ((:no-prefix . ("VMOVLPS"    2 (M q)  (V q)))
               (:66        . ("VMOVLPD"    2 (M q)  (V q))))

              ((:no-prefix . ("VUNPCKLPS"  3 (V x)  (H x)  (W x)))
               (:66        . ("VUNPCKLPD"  3 (V x)  (H x)  (W x))))

              ((:no-prefix . ("VUNPCKHPS"  3 (V x)  (H x)  (W x)))
               (:66        . ("VUNPCKHPD"  3 (V x)  (H x)  (W x))))

              ((:no-prefix . ("VMOVHPS"    3 (V dq)  (H q)  (M q)))
               (:no-prefix . ("VMOVLHPS"   3 (V dq)  (H q)  (U q)))
               (:66        . ("VMOVHPD"    3 (V dq)  (H q)  (M q)))
               (:F3        . ("VMOVSHDUP"  2 (V x)   (W x))))

              ((:no-prefix . ("VMOVHPS"    2 (M q)  (V q)))
               (:66        . ("VMOVHPD"    2 (M q)  (V q))))

    #| 18 |#  ("Grp 16" 0 :1a)

              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none)
              ("NOP" 1 (E v)))

    #| 20 |# (("MOV" 2 (R d) (C d))
              ("MOV" 2 (R d) (D d))
              ("MOV" 2 (C d) (R d))
              ("MOV" 2 (D d) (R d))
              (:none)
              (:none)
              (:none)
              (:none)

    #| 28 |#  ((:no-prefix . ("VMOVAPS"    2 (V ps)  (W ps)))
               (:66        . ("VMOVAPD"    2 (V pd)  (W pd))))

              ((:no-prefix . ("VMOVAPS"    2 (W ps)  (V ps)))
               (:66        . ("VMOVAPD"    2 (W pd)  (V pd))))

              ((:no-prefix . ("CVTPI2PS"   2 (V ps)  (Q pi)))
               (:66        . ("CVTPI2PD"   2 (V pd)  (Q pi)))
               (:F3        . ("VCVTSI2SS"  3 (V ss)  (H ss)  (E y)))
               (:F2        . ("VCVTSI2SD"  3 (V sd)  (H sd)  (E y))))

              ((:no-prefix . ("VMOVNTPS"   2 (M ps)  (V ps)))
               (:66        . ("VMOVNTPD"   2 (M pd)  (V pd))))

              ((:no-prefix . ("CVTTPS2PI"  2 (P pi)  (W ps)))
               (:66        . ("CVTTPD2PI"  2 (P pi)  (W pd)))
               (:F3        . ("VCVTTSS2SI" 2 (G y)   (W ss)))
               (:F2        . ("VCVTTSD2SI" 2 (G y)   (W sd))))

              ((:no-prefix . ("CVTPS2PI"   2 (P pi)  (W ps)))
               (:66        . ("CVTPD2PI"   2 (Q pi)  (W pd)))
               (:F3        . ("VCVTSS2SI"  2 (G y)   (W ss)))
               (:F2        . ("VCVTSD2SI"  2 (G y)   (W sd))))

              ((:no-prefix . ("VUCOMISS"   2 (V ss)  (W ss)))
               (:66        . ("VUCOMISD"   2 (V sd)  (W sd))))

              ((:no-prefix . ("VCOMISS"    2 (V ss)  (W ss)))
               (:66        . ("VCOMISD"    2 (V sd)  (W sd)))))

    #| 30 |# (("WRMSR" 0)
              ("RDTSC" 0)
              ("RDMSR" 0)
              ("RDPMC" 0)
              ("SYSENTER" 0)
              ("SYSEXIT" 0)
              (:none)
              ("GETSEC" 0)
    #| 38 |#  (:3-byte-escape)
              (:none)
              (:3-byte-escape)
              (:none)
              (:none)
              (:none)
              (:none)
              (:none))

    #| 40 |# (("CMOVO" 2 (G v) (E v))
              ("CMOVNO" 2 (G v) (E v))
              ("CMOVB/C/NAE" 2 (G v) (E v))
              ("CMOVAE/NB/NC" 2 (G v) (E v))
              ("CMOVE/Z" 2 (G v) (E v))
              ("CMOVNE/NZ" 2 (G v) (E v))
              ("CMOVBE/NA" 2 (G v) (E v))
              ("CMOVA/NBE" 2 (G v) (E v))
    #| 48 |#  ("CMOVS" 2 (G v) (E v))
              ("CMOVNS" 2 (G v) (E v))
              ("CMOVP/PE" 2 (G v) (E v))
              ("CMOVNP/PO" 2 (G v) (E v))
              ("CMOVL/NGE" 2 (G v) (E v))
              ("CMOVNL/GE" 2 (G v) (E v))
              ("CMOVLE/NG" 2 (G v) (E v))
              ("CMOVNLE/G" 2 (G v) (E v)))

    #| 50 |# (((:no-prefix . ("VMOVMSKPS"  2 (G y)  (U ps)))
               (:66        . ("VMOVMSKPD"  2 (G y)  (U pd))))

              ((:no-prefix . ("VSQRTPS"    2 (V ps)  (W ps)))
               (:66        . ("VSQRTPD"    2 (V pd)  (W pd)))
               (:F3        . ("VSQRTSS"    3 (V ss)  (H ss)  (W ss)))
               (:F2        . ("VSQETSD"    3 (V sd)  (H sd)  (W sd))))

              ((:no-prefix . ("VRSQRTPS"   2 (V ps)  (W ps)))
               (:F3        . ("VRSQRTSS"   3 (V ss)  (H ss)  (W ss))))

              ((:no-prefix . ("VRCPPS"     2 (V ps)  (W ps)))
               (:F3        . ("VRCPSS"     3 (V ss)  (H ss)  (W ss))))

              ((:no-prefix . ("VANDPS"     3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VANDPD"     3 (V pd)  (H pd)  (W pd))))

              ((:no-prefix . ("VANDNPS"    3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VANDNPD"    3 (V pd)  (H pd)  (W pd))))

              ((:no-prefix . ("VORPS"      3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VORPD"      3 (V pd)  (H pd)  (W pd))))

              ((:no-prefix . ("VXORPS"     3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VXORPD"     3 (V pd)  (H pd)  (W pd))))

   #| 58 |#   ((:no-prefix . ("VADDPS"     3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VADDPD"     3 (V pd)  (H pd)  (W pd)))
               (:F3        . ("VADDSS"     3 (V ss)  (H ss)  (W ss)))
               (:F2        . ("VADDSD"     3 (V sd)  (H sd)  (W sd))))

              ((:no-prefix . ("VMULPS"     3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VMULPD"     3 (V pd)  (H pd)  (W pd)))
               (:F3        . ("VMULSS"     3 (V ss)  (H ss)  (W ss)))
               (:F2        . ("VMULSD"     3 (V sd)  (H sd)  (W sd))))

              ((:no-prefix . ("VCVTPS2PD"  2 (V pd)  (W ps)))
               (:66        . ("VCVTPD2PS"  2 (V ps)  (W pd)))
               (:F3        . ("VCVTSS2SD"  3 (V sd)  (H x)   (W ss)))
               (:F2        . ("VCVTSD2SS"  3 (V ss)  (H x)   (W sd))))

              ((:no-prefix . ("VCVTDQ2PS"  2 (V ps)  (W dq)))
               (:66        . ("VCVTPS2DQ"  2 (V dq)  (W ps)))
               (:F3        . ("VCVTTPS2DQ" 2 (V dq)  (W ps))))

              ((:no-prefix . ("VSUBPS"     3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VSUBPD"     3 (V pd)  (H pd)  (W pd)))
               (:F3        . ("VSUBSS"     3 (V ss)  (H ss)  (W ss)))
               (:F2        . ("VSUBSD"     3 (V sd)  (H sd)  (W sd))))

              ((:no-prefix . ("VMINPS"     3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VMINPD"     3 (V pd)  (H pd)  (W pd)))
               (:F3        . ("VMINSS"     3 (V ss)  (H ss)  (W ss)))
               (:F2        . ("VMINSD"     3 (V sd)  (H sd)  (W sd))))

              ((:no-prefix . ("VDIVPS"     3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VDIVPD"     3 (V pd)  (H pd)  (W pd)))
               (:F3        . ("VDIVSS"     3 (V ss)  (H ss)  (W ss)))
               (:F2        . ("VDIVSD"     3 (V sd)  (H sd)  (W sd))))

              ((:no-prefix . ("VMAXPS"     3 (V ps)  (H ps)  (W ps)))
               (:66        . ("VMAXPD"     3 (V pd)  (H pd)  (W pd)))
               (:F3        . ("VMAXSS"     3 (V ss)  (H ss)  (W ss)))
               (:F2        . ("VMAXSD"     3 (V sd)  (H sd)  (W sd)))))

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
               (:F3        . ("VMOVDQU"     2 (V x)  (W x)))))

    #| 70 |# (((:no-prefix . ("PSHUFW"      3 (P q)   (Q q)   (I b)))
               (:66        . ("VPSHUFD"     3 (V x)   (W x)   (I b)))
               (:F3        . ("VPSHUFHW"    3 (V x)   (W x)   (I b)))
               (:F2        . ("VPSHUFLW"    3 (V x)   (W x)   (I b))))

              ("Grp12" 0 :1a)

              ("Grp13" 0 :1a)

              ("Grp14" 0 :1a)

              ((:no-prefix . ("PCMPEQB"     2 (P q)   (Q q)))
               (:66        . ("VPCMPEQB"    3 (V x)   (H x)  (W x))))

              ((:no-prefix . ("PCMPEQW"     2 (P q)   (Q q)))
               (:66        . ("VPCMPEQW"    3 (V x)   (H x)  (W x))))

              ((:no-prefix . ("PCMPEQD"     2 (P q)   (Q q)))
               (:66        . ("VPCMPEQD"    3 (V x)   (H x)  (W x))))

              ("EMMS/VZEROUPPER/VZEROALL" 0)

    #| 78 |#  ("VMREAD" 2  (E y)  (G y))

              ("VMWRITE" 2  (E y)  (G y))

              (:none)

              (:none)

              ((:66        . ("VHADDPD"     3 (V pd)   (H pd)  (W pd)))
               (:F2        . ("VHADDPS"     3 (V ps)   (H ps)  (W ps))))

              ((:66        . ("VHSUBPD"     3 (V pd)   (H pd)  (W pd)))
               (:F2        . ("VHSUBPS"     3 (V ps)   (H ps)  (W ps))))

              ((:no-prefix . ("MOVD/Q"      2 (E y)    (P d)))
               (:66        . ("VMOVD/Q"     2 (E y)    (V y)))
               (:F3        . ("VMOVQ"       2 (V q)    (W q))))

              ((:no-prefix . ("MOVQ"        2 (Q q)    (P q)))
               (:66        . ("VMOVDQA"     2 (W x)    (V x)))
               (:F3        . ("VMOVQU"      2 (W x)    (V x)))))

    #| 80 |#  (((:f64 . ("JO" 1 (J z))))
               ((:f64 . ("JNO" 1 (J z))))
               ((:f64 . ("JB/NAE/C" 1 (J z))))
               ((:f64 . ("JNB/AE/NC" 1 (J z))))
               ((:f64 . ("JZ/E" 1 (J z))))
               ((:f64 . ("JNZ/NE" 1 (J z))))
               ((:f64 . ("JBE/NA" 1 (J z))))
               ((:f64 . ("JNBE/A" 1 (J z))))
    #| 88 |#   ((:f64 . ("JS" 1 (J z))))
               ((:f64 . ("JNS" 1 (J z))))
               ((:f64 . ("JP/PE" 1 (J z))))
               ((:f64 . ("JNP/PO" 1 (J z))))
               ((:f64 . ("JL/NGE" 1 (J z))))
               ((:f64 . ("JNL/GE" 1 (J z))))
               ((:f64 . ("JLE/NG" 1 (J z))))
               ((:f64 . ("JNLE/G" 1 (J z)))))

    #| 90 |# (("SETO" 1 (E b))
              ("SETNO" 1 (E b))
              ("SETB/NAE/C" 1 (E b))
              ("SETNB/AE/NC" 1 (E b))
              ("SETZ/E" 1 (E b))
              ("SETNZ/NE" 1 (E b))
              ("SETBE/NA" 1 (E b))
              ("SETNBE/A" 1 (E b))
    #| 98 |#  ("SETS" 1 (E b))
              ("SETNS" 1 (E b))
              ("SETP/PE" 1 (E b))
              ("SETNP/PO" 1 (E b))
              ("SETL/NGE" 1 (E b))
              ("SETNL/GE" 1 (E b))
              ("SETLE/NG" 1 (E b))
              ("SETNLE/G" 1 (E b)))

    #| a0 |# (((:d64 . ("PUSH"  1 (:FS))))
              ((:d64 . ("POP"  1 (:FS))))
              ("CPUID" 0)
              ("BT" 2 (E v) (G v))
              ("SHLD" 3 (E v) (G v) (I b))
              ("SHLD" 3 (E v) (G v) (:CL))
              (:none)
              (:none)
    #| a8 |#  ((:d64 . ("PUSH"  1 (:GS))))
              ((:d64 . ("POP"  1 (:GS))))
              ("RSM" 0)
              ("BTS" 2 (E v) (G v))
              ("SHRD" 3 (E v) (G v) (I b))
              ("SHRD" 3 (E v) (G v) (:CL))
              ("Grp15" 0 :1a :1c)
              ("IMUL" 2 (G v) (E v)))

    #| b0 |# (("CMPXCHG" 2 (E b) (G b))
              ("CMPXCHG" 2 (E v) (G v))
              ("LSS" 2 (G v) (M p))
              ("BTR" 2 (E v) (G v))
              ("LFS" 2 (G v) (M p))
              ("LGS" 2 (G v) (M p))
              ("MOVZX" 2 (G v) (E b))
              ("MOVZX" 2 (G v) (E w))

    #| b8 |#  ((:no-prefix . ("JMPE"   0))
               (:F3        . ("POPCNT" 2 (G v) (E v))))

              (("Grp10" 0 :1a)
               ("InvalidOpcode" 0 :1b))

              (("Grp8" 2 (E v) (I b) :1a))

              ("BTC" 2 (E v) (G v))

              ((:no-prefix . ("BSF"   2 (G v) (E v)))
               (:F3        . ("TZCNT" 2 (G v) (E v))))

              ((:no-prefix . ("BSR"   2 (G v) (E v)))
               (:F3        . ("LZCNT" 2 (G v) (E v))))

              ("MOVSX" 2 (G v) (E b))
              ("MOVSX" 2 (G v) (E w)))

    #| c0 |# (("XADD"     2 (E b)  (G b))

              ("XADD"     2 (E v)  (G v))

              ((:no-prefix . ("VCMPPS"     4 (V ps)  (H ps)  (W ps)  (I b)))
               (:66        . ("VCMPPD"     4 (V pd)  (H pd)  (W pd)  (I b)))
               (:F3        . ("VCMPSS"     4 (V ss)  (H ss)  (W ss)  (I b)))
               (:F2        . ("VCMPSD"     4 (V sd)  (H sd)  (W sd)  (I b))))

              ("MOVNTI"     2 (M y)   (G y))

              ((:no-prefix . ("PINSRW"     3 (P q)   (R y)  (I b)))
               (:no-prefix . ("PINSRW"     3 (P q)   (M w)  (I b)))
               (:66        . ("VPINSRW"    4 (V dq)  (H dq) (R y)  (I b)))
               (:66        . ("VPINSRW"    4 (V dq)  (H dq) (M w)  (I b))))

              ((:no-prefix . ("PEXTRW"     3 (G d)   (N q)  (I b)))
               (:66        . ("VPEXTRW"    3 (G d)   (U dq) (I b))))

              ((:no-prefix . ("VSHUFPS"    4 (V ps)  (H ps)  (W ps)  (I b)))
               (:66        . ("VPEXTRW"    4 (V pd)  (H pd)  (W pd)  (I b))))

              ("Grp9" 0 :1a)

    #| c8 |#  ("BSWAP" 1 (:RAX/EAX/R8/R8D))
              ("BSWAP" 1 (:RCX/ECX/R9/R9D))
              ("BSWDP" 1 (:RDX/EDX/R10/R10D))
              ("BSWBP" 1 (:RBX/EBX/R11/R11D))
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
             (:66        . ("VPMOVMSKB" 2 (G d)   (U x))))

  #| d8 |#  ((:no-prefix . ("PSUBUSB"   2 (P q)   (Q q)))
             (:66        . ("VPSUBUSB"  3 (V x)   (H x)  (W x))))

            ((:no-prefix . ("PSUBUSW"   2 (P q)   (Q q)))
             (:66        . ("VPSUBUSW"  3 (V x)   (H x)  (W x))))

            ((:no-prefix . ("PMINUB"    2 (P q)   (Q q)))
             (:66        . ("VPMINUB"   3 (V x)   (H x)  (W x))))

            ((:no-prefix . ("PAND"      2 (P q)   (Q q)))
             (:66        . ("VPAND"     3 (V x)   (H x)  (W x))))

            ((:no-prefix . ("PADDUSB"   2 (P q)   (Q q)))
             (:66        . ("VPADDUSB"  3 (V x)   (H x)  (W x))))

            ((:no-prefix . ("PADDUSW"   2 (P q)   (Q q)))
             (:66        . ("VPADDUSW"  3 (V x)   (H x)  (W x))))

            ((:no-prefix . ("PMAXUB"    2 (P q)   (Q q)))
             (:66        . ("VPMAXUB"   3 (V x)   (H x)  (W x))))

            ((:no-prefix . ("PANDN"     2 (P q)   (Q q)))
             (:66        . ("VPANDN"    3 (V x)   (H x)  (W x)))))

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
             (:66        . ("VPOR" 3 (V x)  (H x)  (W x))))

            ((:no-prefix . ("PADDSB"  2 (P q)  (Q q)))
             (:66        . ("VPADDSB" 3 (V x)  (H x)  (W x))))

            ((:no-prefix . ("PADDSW"  2 (P q)  (Q q)))
             (:66        . ("VPADDSW" 3 (V x)  (H x)  (W x))))

            ((:no-prefix . ("PMAXSW"  2 (P q)  (Q q)))
             (:66        . ("VPMAXSW" 3 (V x)  (H x)  (W x))))

            ((:no-prefix . ("PXOR"  2 (P q)  (Q q)))
             (:66        . ("VPXOR" 3 (V x)  (H x)  (W x)))))

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

            (:none))

  #|       -------------------------------        |#
  ))

(defn opcode-row-recognizer (lst)
  ;; A "row" refers to one row of an Intel opcode map (Intel manuals,
  ;; Volume 2, Appendix A); e.g., opcodes 0x00 to 0x0F form one row of
  ;; the one-byte opcode map.
  (if (atom lst)
      (eq lst nil)
    (and ;; (car lst): information about one opcode
     (consp (car lst))
     (alistp (car lst))
     ;; caar: one opcode
     (true-listp (caar lst))
     (or
      ;; A "simple" opcode
      (and (stringp (car (caar lst))) ;; Opcode
           (natp (cadr (caar lst)))   ;; Number of Operands
           ;; Number of operands <= addressing info. of all operands
           (<= (cadr (caar lst)) (len (cddr (caar lst)))))

      ;; :2-byte-escape, :3-byte-escape, or :rex, etc. --- just the
      ;; keyword without any other information
      (and (keywordp (car (caar lst)))
           (equal (len (caar lst)) 1))

      ;; A set of opcodes (different for different modes and prefixes)
      (and (alistp (caar lst))
           (subsetp (strip-cars (caar lst))
                    '(:i64 :o64 :d64 :f64 :no-prefix :66 :F3 :F2))
           (opcode-row-recognizer (list (strip-cdrs (caar lst))))))
     (opcode-row-recognizer (cdr lst)))))

(defn opcode-map-info-recognizer (lst)
  (if (atom lst)
      (eq lst nil)
    (and ;; car: one row of the opcode map
     (opcode-row-recognizer (list (car lst)))
     (opcode-map-info-recognizer (cdr lst)))))

(defthm len-one-byte-map
  (equal (len *one-byte-opcode-map-lst*) 16)
  :rule-classes nil)

(defthm recognizer-one-byte-map
  (opcode-map-info-recognizer *one-byte-opcode-map-lst*))

(defthm len-two-byte-map
  (equal (len *two-byte-opcode-map-lst*) 16)
  :rule-classes nil)

(defthm recognizer-two-byte-map
  (opcode-map-info-recognizer *two-byte-opcode-map-lst*))

;; ModR/M Decoding:

(define any-modr/m-operand?
  ((op_num :type (integer 0 *))
   (op_list)
   (bool))
  :guard (alistp op_list)
  :parents (decoding-utilities)
  :short "Returns @('t') if at least one operand of an opcode requires
  a @('ModR/M') byte"
  (b* (((when (not (equal (len op_list) op_num)))
        (er hard? "Expected length of ~x0 was 1." op_list)))

      (if (zp op_num)
          bool
        (b* ((char (caar op_list))
             (this-opcode-modr/m?
              (cdr (assoc :modr/m?
                          (cdr (assoc
                                char
                                *Z-addressing-method-info*))))))
            (any-modr/m-operand? (1- op_num)
                                 (cdr op_list)
                                 (or this-opcode-modr/m? bool))))))

(define compute-modr/m-for-an-opcode
  (opcode-info)
  ;; Example invocations:
  ;; (compute-modr/m-for-an-opcode '("ADD" 2 (E b)  (G b)))
  ;; (compute-modr/m-for-an-opcode '(:2-byte-escape))
  :guard (true-listp opcode-info)
  :short "Returns @('1') if a <i>simple</i> opcode requires a
  @('ModR/M') byte"
  :long "<p>We call an opcode available across all modes and prefixes
  as a 'simple' opcode.</p>"
  :parents (decoding-utilities)
  (if (or (not (true-listp opcode-info))
          (endp opcode-info))

      0

    (b* ( ;; (- (cw "~%Opcode info: ~x0~%~%" opcode-info))
         (first-elem (car opcode-info))
         ;; (- (cw "~% First elem: ~x0 ~%" first-elem))
         )

        (cond

         ;; "Normal" instructions
         ((stringp first-elem)
          (b* ( ;; (- (cw "~%Stringp~%"))
               ((when (< (len opcode-info) 2))
                (er hard? 'compute-modr/m-for-an-opcode
                    "Len of column info field is < 2: ~x0."
                    opcode-info))

               (op_num (nth 1 opcode-info))
               ((when (not (natp op_num)))
                (er hard? 'compute-modr/m-for-an-opcode
                    "We expected an op_num in this column ~x0." opcode-info))

               (op_list (take op_num (nthcdr 2 opcode-info)))
               ((when (not (alistp op_list)))
                (er hard? 'compute-modr/m-for-an-opcode
                    "We expected an op_list here: ~x0." opcode-info))

               (modr/m? (any-modr/m-operand? op_num op_list nil))
               ;; (- (cw "Val: ~x0~%" modr/m?))
               )

              (acl2::bool->bit modr/m?)))

         ;; No instructions/prefixes/escape bytes
         ((keywordp first-elem)
          (b* ( ;; (- (cw "~%keywordp~%"))
               ((when (not (member first-elem
                                   '(:none :unimplemented
                                           :3-byte-escape
                                           :2-byte-escape :prefix-ES
                                           :prefix-CS :prefix-SS :prefix-DS
                                           :prefix-FS :prefix-GS :prefix-OpSize
                                           :prefix-AddrSize
                                           :prefix-Lock :prefix-REPNE
                                           :prefix-REP/REPE :rex :rex-b
                                           :rex-xb :rex-r :rex-rb
                                           :rex-rx :rex-rxb :rex-w
                                           :rex-wb :rex-wx :rex-wxb
                                           :rex-wr :rex-wrb :rex-wrx
                                           :rex-wrxb :rex-x))))
                (er hard? 'compute-modr/m-for-an-opcode
                    "Disallowed keyword: ~x0 in ~x1"
                    first-elem
                    opcode-info)))
              0))

         ;; All else is not supported yet.
         (t
          (er hard? 'compute-modr/m-for-an-opcode
              "Opcode info: ~x0~%" opcode-info))))))

(define compute-modr/m-for-opcode-row-no-modes
  (row-info row-modr/m)
  :guard (and (true-list-listp row-info)
              (true-listp row-modr/m))
  :short "ModR/M byte detection for a row of simple opcodes"
  :long "<p>This function @('compute-modr/m-for-opcode-row-no-modes')
  simply calls @(see compute-modr/m-for-an-opcode) recursively. It
  returns a list of 1s and 0s corresponding to the presence or absence
  of ModR/M byte for each opcode in a simple opcode row in the Intel
  opcode maps.</p>"
  :parents (decoding-utilities)
  (if (mbt (and (true-list-listp row-info)
                (true-listp row-modr/m)))

      (if (endp row-info)
          row-modr/m
        (b* ((opcode-info (car row-info))
             (modr/m (compute-modr/m-for-an-opcode opcode-info)))
            (compute-modr/m-for-opcode-row-no-modes
             (cdr row-info) (cons modr/m row-modr/m))))
    nil))

(local
 (defthm delete-assoc-equal-thm
   (implies (and (alistp column-info)
                 (consp column-info))
            (alistp (delete-assoc-equal :i64 column-info)))
   :hints (("Goal" :in-theory (e/d (delete-assoc-equal) ())))))

(define 64-bit-compute-modr/m-for-an-opcode
  (opcode-info)
  ;; Example invocations:
  ;; (64-bit-compute-modr/m-for-an-opcode '((:o64 . ("MOVSXD" 2 (G v) (E v))) (:i64 . ("ARPL"   2 (E w) (G w)))))
  ;; (64-bit-compute-modr/m-for-an-opcode '((:no-prefix "PADDD" 2 (P q) (Q q)) (:66 "VPADDD" 3 (V x) (H x) (W x))))

  ;; Note: this function is sort of shoddy for the mandatory prefix
  ;; cases. For example, if the opcode info is something like the
  ;; following:

  ;; '((:no-prefix "FOO" 1 (A q)) (:66 "BAR" 2 (A x) (G x)))

  ;; then this function will return 1, indicating that a ModR/M byte
  ;; should be present for this opcode. However, opcode FOO does not
  ;; require a ModR/M byte while BAR does. To be correct, this
  ;; function should also take in the mandatory prefix of the opcode
  ;; under consideration to figure out the right answer. Anyway, for
  ;; now, this function works for the one- and two-byte opcode maps
  ;; (which is all I've implemented so far) because every opcode that
  ;; has different addressing styles for different mandatory prefixes
  ;; uses a ModR/M byte to fetch one of its opcodes at least.

  :guard (alistp opcode-info)
  :short "Returns @('1') if an opcode requires a @('ModR/M') byte in the 64-bit mode"
  :parents (decoding-utilities)
  (if (or (not (alistp opcode-info))
          (not (subsetp (strip-cars opcode-info)
                        '(:i64 :o64 :d64 :f64 :no-prefix :66 :F3 :F2)))
          (endp opcode-info))

      0

    (b* ( ;; (- (cw "~%Opcode info: ~x0~%~%" opcode-info))
         (stripped-invalid-opcodes (delete-assoc :i64 opcode-info))
         ;; (- (cw "~%64-bit-mode-modr/m?:~%"))
         ;; Early exit when stripped-invalid-opcodes is nil.
         ((when (not (consp stripped-invalid-opcodes)))
          0)
         (mode-opcode-row (strip-cdrs stripped-invalid-opcodes))
         ;; (- (cw "~%Mode-opcode-row: ~x0 ~%" mode-opcode-row))
         ((when (not (true-list-listp mode-opcode-row)))
          (er hard? '64-bit-compute-modr/m-for-an-opcode
              "True-list-listp expected: ~x0."
              mode-opcode-row))
         (modr/m-vals
          (compute-modr/m-for-opcode-row-no-modes mode-opcode-row nil))
         ;; (- (cw "~%Vals: ~x0 ~%" modr/m-vals))
         )
        (if (member 1 modr/m-vals)
            1
          0))))

(define 64-bit-compute-modr/m-for-opcode-row (row-info row-modr/m)
  :guard (and (true-list-listp row-info)
              (true-listp row-modr/m))
  :short "Returns a list of 1s and 0s corresponding to the presence or
  absence of ModR/M byte for each opcode in a opcode row in the Intel
  opcode maps"
  :parents (decoding-utilities)
  (if (mbt (and (true-list-listp row-info)
                (true-listp row-modr/m)))

      (if (endp row-info)
          row-modr/m
        (let ((opcode-info (car row-info)))

          (if (alistp opcode-info)
              (64-bit-compute-modr/m-for-opcode-row
               (cdr row-info)
               (cons (64-bit-compute-modr/m-for-an-opcode opcode-info)
                     row-modr/m))

            (64-bit-compute-modr/m-for-opcode-row
             (cdr row-info)
             (cons (compute-modr/m-for-an-opcode opcode-info)
                   row-modr/m)))))
    nil))

(define 64-bit-compute-modr/m-map-1 (row-number opcode-map-lst)
  :guard (and (natp row-number)
              (true-listp opcode-map-lst))
  :short "Returns a list of 1s and 0s corresponding to the
  presence or absence of ModR/M byte for each opcode in the Intel
  opcode maps"
  :long "<p>This function is used by @(see
  64-bit-compute-modr/m-map).</p>"
  :parents (decoding-utilities)
  ;; Example invocation:
  ;; (64-bit-compute-modr/m-map-1 16 *one-byte-opcode-map-lst*)
  (if (mbt (and (natp row-number)
                (true-listp opcode-map-lst)))

      (if (zp row-number)
          nil
        (b* ( ;; (- (cw "~%Row number: ~x0~%~%" row-number))
             (row-info (nth (1- row-number) opcode-map-lst))
             ((when (not (true-list-listp row-info)))
              (er hard? "Expected: true-list-listp: ~x0" row-info))
             (row-column-info
              (64-bit-compute-modr/m-for-opcode-row row-info nil)))
            (append
             row-column-info
             (64-bit-compute-modr/m-map-1
              (1- row-number) opcode-map-lst))))
    nil))

(define 64-bit-compute-modr/m-map (opcode-map-lst)
  :guard (true-listp opcode-map-lst)
  :short "Returns a list of 1s and 0s corresponding to the
  presence or absence of ModR/M byte for each opcode in the Intel
  opcode maps"
  :long "<p>An opcode @('x') requires a @('ModR/M') byte if there
  exists a 1 in the position @('x') of the list computed by this
  function.</p>"
  :parents (decoding-utilities)
  ;; Example invocation:
  ;; (64-bit-compute-modr/m-map *one-byte-opcode-map-lst*)
  (reverse (64-bit-compute-modr/m-map-1
            (len opcode-map-lst)
            opcode-map-lst)))

(defconst *64-bit-mode-one-byte-has-modr/m-ar*
  (list-to-array '64-bit-mode-one-byte-has-modr/m
                 (ints-to-booleans
                  (64-bit-compute-modr/m-map
                   *one-byte-opcode-map-lst*))))

(defconst *64-bit-mode-two-byte-has-modr/m-ar*
  (list-to-array '64-bit-mode-two-byte-has-modr/m
                 (ints-to-booleans
                  (64-bit-compute-modr/m-map
                   *two-byte-opcode-map-lst*))))


;; Prefix byte decoding:

(define compute-prefix-byte-group-code-of-one-opcode (opcode-info)
  :guard (true-listp opcode-info)
  :short "Takes in information of a single opcode from an opcode map and
  figures out if it is a prefix byte; if so, the prefix group number
  is returned."
  :long "<p>The return value @('0') corresponds to \"not a prefix\" and
  @('1'), @('2'), @('3') and @('4') correspond to the prefix group of
  byte.</p>"
  :parents (decoding-utilities)
  (if (or (not (true-listp opcode-info))
          (endp opcode-info))

      0

    (b* ( ;; (- (cw "~%Opcode info: ~x0~%~%" opcode-info))
         (first-elem (car opcode-info))
         ;; (- (cw "~% First elem: ~x0 ~%" first-elem))
         )

        (cond

         ((keywordp first-elem)

          (case first-elem

            (:prefix-Lock       1) ;; #xF0
            (:prefix-REPNE      1) ;; #xF2
            (:prefix-REP/REPE   1) ;; #xF3

            (:prefix-ES         2) ;; #x26
            (:prefix-CS         2) ;; #x2E
            (:prefix-SS         2) ;; #x36
            (:prefix-DS         2) ;; #x3E
            (:prefix-FS         2) ;; #x64
            (:prefix-GS         2) ;; #x65

            (:prefix-OpSize     3) ;; #x66

            (:prefix-AddrSize   4) ;; #x67

            ((:rex :rex-b
                   :rex-xb :rex-r :rex-rb
                   :rex-rx :rex-rxb :rex-w
                   :rex-wb :rex-wx :rex-wxb
                   :rex-wr :rex-wrb :rex-wrx
                   :rex-wrxb :rex-x
                   :none :2-byte-escape)
             0)

            (t
             (er hard? 'compute-prefix-byte-group-code-of-one-opcode
                 "Opcode info: ~x0~%" opcode-info))))

         (t 0)))))


(define compute-prefix-byte-group-code-from-opcode-row
  (row-info row-prefix)
  :guard (and (true-list-listp row-info)
              (true-listp row-prefix))
  :short "Takes in a single opcode row from an opcode map and returns
  prefix byte info for each of the opcodes in that row"
  :parents (decoding-utilities)

  (if (mbt (and (true-list-listp row-info)
                (true-listp row-prefix)))

      (if (endp row-info)
          row-prefix
        (let ((opcode-info (car row-info)))
          (compute-prefix-byte-group-code-from-opcode-row
           (cdr row-info)
           (cons (compute-prefix-byte-group-code-of-one-opcode opcode-info)
                 row-prefix))))

    nil))


(define compute-prefix-byte-group-code-1 (row-number opcode-map-lst)
  :guard (and (natp row-number)
              (true-listp opcode-map-lst))

  :parents (decoding-utilities)
  (if (mbt (and (natp row-number)
                (true-listp opcode-map-lst)))

      (if (zp row-number)
          nil
        (b* ( ;; (- (cw "~%Row number: ~x0~%~%" row-number))
             (row-info (nth (1- row-number) opcode-map-lst))
             ((when (not (true-list-listp row-info)))
              (er hard? "Expected: true-list-listp: ~x0" row-info))
             (row-column-info
              (compute-prefix-byte-group-code-from-opcode-row row-info nil)))
            (append
             row-column-info
             (compute-prefix-byte-group-code-1
              (1- row-number) opcode-map-lst))))
    nil))

(define compute-prefix-byte-group-code (opcode-map-lst)
  :guard (true-listp opcode-map-lst)
  :short "Returns prefix byte information for an input opcode map"

  :long "<p>Source: Intel Manuals, Vol. 2, Section 2.1.1.</p>

 <p>The value @('0') corresponds to \"not a prefix\" and @('1'),
  @('2'), @('3') and @('4') correspond to the prefix group of
  byte.</p>"

  :parents (decoding-utilities)
  (reverse (compute-prefix-byte-group-code-1
            (len opcode-map-lst)
            opcode-map-lst)))

(defconst *one-byte-prefixes-group-code-info-ar*
  (list-to-array 'one-byte-prefixes-group-code-info
                 (compute-prefix-byte-group-code
                  *one-byte-opcode-map-lst*)))

(define get-one-byte-prefix-array-code
  ((byte :type (unsigned-byte 8)))
  :returns (code natp
                 :hyp (force (unsigned-byte-p 8 byte))
                 :rule-classes :type-prescription)
  (aref1 'one-byte-prefixes-group-code-info
         *one-byte-prefixes-group-code-info-ar* byte)

  ///

  (defthm upper-bound-get-one-byte-prefix-array-code
    (<= (get-one-byte-prefix-array-code x) 4)))

;; ======================================================================

(defsection ModRM-and-SIB-decoding

  :parents (decoding-utilities)

  :short "Functions to detect and decode ModR/M and SIB bytes"

  (local (xdoc::set-default-parents ModRM-and-SIB-decoding))

  (define x86-one-byte-opcode-ModR/M-p
    ((opcode :type (unsigned-byte 8)))
    :inline t
    :short "Returns a boolean saying whether the given opcode in the
    one-byte opcode map expects a ModR/M byte."
    :returns (bool booleanp :hyp (n08p opcode))
    (aref1 '64-bit-mode-one-byte-has-modr/m
           *64-bit-mode-one-byte-has-modr/m-ar* opcode))

  (define x86-two-byte-opcode-ModR/M-p
    ((opcode :type (unsigned-byte 8) "Second byte of the two-byte opcode"))
    :short "Returns a boolean saying whether the two-byte opcode
    expects a ModR/M byte."
    :returns (bool booleanp :hyp (n08p opcode))
    (aref1 '64-bit-mode-two-byte-has-modr/m
           *64-bit-mode-two-byte-has-modr/m-ar* opcode))


  ;; We assume ModR/M is an unsigned-byte 8.
  (defmacro mrm-r/m (ModR/M)
    `(n03 ,ModR/M))

  (defmacro mrm-reg (ModR/M)
    `(mbe :logic (part-select ,ModR/M :low 3 :width 3)
          :exec (logand 7 (ash ,ModR/M -3))))

  (defmacro mrm-mod (ModR/M)
    `(mbe :logic (part-select ,ModR/M :low 6 :width 2)
          :exec (ash ,ModR/M -6)))

  (define x86-decode-SIB-p
    ((ModR/M :type (unsigned-byte 8)))
    :short "If ModR/M.mod is not #x11 and ModR/M.r/m is #x100, then SIB is expected."
    :returns (bool booleanp :hyp (n08p ModR/M))
    (let* ((r/m (mrm-r/m ModR/M))
           (mod (mrm-mod ModR/M)))
      (declare (type (unsigned-byte 8) r/m mod))
      (and (int= r/m 4)
           (not (int= mod 3)))))

  ;; We assume sib is an unsigned-byte 8.
  (defmacro sib-base (sib)
    `(n03 ,sib))

  (defmacro sib-index (sib)
    `(mbe :logic (part-select ,sib :low 3 :width 3)
          :exec (logand 7 (ash ,sib -3))))

  (defmacro sib-scale (sib)
    `(mbe :logic (part-select ,sib :low 6 :width 2)
          :exec (ash ,sib -6)))

  )

;; ======================================================================

(defsection prefixes-decoding

  :parents (decoding-utilities)

  :short "Functions to detect and decode ModR/M and SIB bytes"

  (defconst *prefixes-layout*
    '((:num-prefixes      0  3) ;; Number of prefixes
      (:group-1-prefix    3  8) ;; Lock, Repeat prefix
      (:group-2-prefix   11  8) ;; Segment Override prefix
      (:group-3-prefix   19  8) ;; Operand-Size Override prefix
      (:group-4-prefix   27  8) ;; Address-Size Override prefix
      (:next-byte        35  8) ;; Byte following the prefixes
      ))

  (defthm prefixes-table-ok
    (layout-constant-alistp *prefixes-layout* 0 43)
    :rule-classes nil)

  (defmacro prefixes-slice (flg prefixes)
    (slice flg prefixes 43 *prefixes-layout*))

  (defmacro !prefixes-slice (flg val reg)
    (!slice flg val reg 43 *prefixes-layout*))

  )

;; ======================================================================
