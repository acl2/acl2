;; Author:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "utilities")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

;; TO-DO@Shilpi: Give an example...

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

   '(L (:modr/m? . nil) (:vex . nil))

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

   '(U (:modr/m? . t) (:vex . nil))

   ;; V The reg field of the ModR/M byte selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand type.

   '(V (:modr/m? . t) (:vex . nil))

   ;; W A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either a 128-bit XMM register a 256-bit
   ;; YMM register (determined by operand type) or a memory
   ;; address. If it is a memory address the address is computed from
   ;; a segment register and any of the following values: a base
   ;; register an index register a scaling factor and a displacement.

   '(W (:modr/m? . t) (:vex . nil))

   ;; X Memory addressed by the DS:rSI register pair (for example MOVS
   ;; CMPS OUTS or LODS).

   '(X (:modr/m? . nil) (:vex . nil))

   ;; Y Memory addressed by the ES:rDI register pair (for example MOVS
   ;; CMPS INS STOS or SCAS).

   '(Y (:modr/m? . nil) (:vex . nil))

   ))

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
	      ("INVD" 0)
	      ("WBINVD" 0)
	      (:none)
	      (:unimplemented)
	      (:none)
	      ("prefetchw(/1)" 1 (E v))
	      (:none)
	      (:none))

    #| 10 |# ((:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      ("NOP" 1 (E v)))

    #| 20 |# (("MOV" 2 (R d) (C d))
	      ("MOV" 2 (R d) (D d))
	      ("MOV" 2 (C d) (R d))
	      ("MOV" 2 (D d) (R d))
	      (:none)
	      (:none)
	      (:none)
	      (:none)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented))

    #| 30 |# (("WRMSR" 0)
	      ("RDTSC" 0)
	      ("RDMSR" 0)
	      ("RDPMC" 0)
	      ("SYSENTER" 0)
	      ("SYSEXIT" 0)
	      (:none)
	      ("GETSEC" 0)
	      (:3-byte-escape)
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
	      ("CMOVS" 2 (G v) (E v))
	      ("CMOVNS" 2 (G v) (E v))
	      ("CMOVP/PE" 2 (G v) (E v))
	      ("CMOVNP/PO" 2 (G v) (E v))
	      ("CMOVL/NGE" 2 (G v) (E v))
	      ("CMOVNL/GE" 2 (G v) (E v))
	      ("CMOVLE/NG" 2 (G v) (E v))
	      ("CMOVNLE/G" 2 (G v) (E v)))

    #| 50 |# ((:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented))

    #| 60 |# ((:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented))

    #| 70 |# ((:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented))

    #| 80 |#  (((:f64 . ("JO" 1 (J z))))
	       ((:f64 . ("JNO" 1 (J z))))
	       ((:f64 . ("JB/NAE/C" 1 (J z))))
	       ((:f64 . ("JNB/AE/NC" 1 (J z))))
	       ((:f64 . ("JZ/E" 1 (J z))))
	       ((:f64 . ("JNZ/NE" 1 (J z))))
	       ((:f64 . ("JBE/NA" 1 (J z))))
	       ((:f64 . ("JNBE/A" 1 (J z))))
	       ((:f64 . ("JS" 1 (J z))))
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
	      ("SETS" 1 (E b))
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
	      ((:d64 . ("PUSH"  1 (:GS))))
	      ((:d64 . ("POP"  1 (:GS))))
	      ("RSM" 0)
	      ("BTS" 2 (E v) (G v))
	      ("SHRD" 3 (E v) (G v) (I b))
	      ("SHRD" 3 (E v) (G v) (:CL))
	      (:unimplemented)
	      ("IMUL" 2 (G v) (E v)))

    #| b0 |# (("CMPXCHG" 2 (E b) (G b))
	      ("CMPXCHG" 2 (E v) (G v))
	      ("LSS" 2 (G v) (M p))
	      ("BTR" 2 (E v) (G v))
	      ("LFS" 2 (G v) (M p))
	      ("LGS" 2 (G v) (M p))
	      ("MOVZX" 2 (G v) (E b))
	      ("MOVZX" 2 (G v) (E w))
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      ("BTC" 2 (E v) (G v))
	      (:unimplemented)
	      (:unimplemented)
	      ("MOVSX" 2 (G v) (E b))
	      ("MOVSX" 2 (G v) (E w)))

    #| c0 |# ((:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented))

    #| d0 |# ((:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented))

    #| e0 |# ((:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented))

    #| f0 |# ((:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented)
	      (:unimplemented))

    #|       -------------------------------        |#
    ))

(defn opcode-row-recognizer (lst)
  (if (atom lst)
      (eq lst nil)
    (and ;; lst: one row of the opcode map
     (consp (car lst))
     (alistp (car lst))
     ;; caar: one opcode
     (true-listp (caar lst))
     (or
      (and (stringp (car (caar lst))) ;; Opcode
	   (natp (cadr (caar lst)))   ;; Number of Operands
	   ;; Addressing info of all operands
	   (<= (cadr (caar lst)) (len (cddr (caar lst)))))
      ;; :2-byte-escape or :rex, etc.
      (keywordp (car (caar lst)))
      (and (alistp (caar lst))
	   (subsetp (strip-cars (caar lst))
		    '(:i64 :o64 :d64 :f64))
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
  :long "<p>We call an opcode available across all modes of the x86
  processor as a 'simple' opcode.</p>"
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
  :short "Returns a list of 1s and 0s corresponding to the presence or
  absence of ModR/M byte for each opcode in a simple opcode row in the
  Intel opcode maps"
  :long "<p>As described in @(see compute-modr/m-for-an-opcode), a
  simple opcode is the one that is available across all modes of the
  x86 processor.  This function
  @('compute-modr/m-for-opcode-row-no-modes') simply calls @(see
  compute-modr/m-for-an-opcode) recursively.</p>"
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
  ;; Example invocation:
  ;; (64-bit-compute-modr/m-for-an-opcode '((:o64 . ("MOVSXD" 2 (G v) (E v))) (:i64 . ("ARPL"   2 (E w) (G w)))))
  :guard (alistp opcode-info)
  :short "Returns @('1') if an opcode requires a @('ModR/M') byte in the 64-bit mode"
  :parents (decoding-utilities)
  (if (or (not (alistp opcode-info))
	  (not (subsetp (strip-cars opcode-info)
			'(:i64 :o64 :d64 :f64)))
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
